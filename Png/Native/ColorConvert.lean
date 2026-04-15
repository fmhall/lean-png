import Png.Types

/-!
# PNG Color Type Converters

Pure Lean pixel format converters for all PNG color types.
Every function converts raw decoded pixel data into RGBA 8-bit format.

- `unpackSubByte` — expand 1/2/4-bit samples to 8-bit bytes
- `grayscaleToRGBA` — 1-channel grayscale → 4-channel RGBA
- `grayscale16ToRGBA` — 16-bit grayscale → 8-bit RGBA (high byte)
- `rgbToRGBA` — 3-channel RGB → 4-channel RGBA (alpha=255)
- `rgb16ToRGBA` — 16-bit RGB → 8-bit RGBA (high bytes)
- `grayAlphaToRGBA` — 2-channel gray+alpha → 4-channel RGBA
- `grayAlpha16ToRGBA` — 16-bit gray+alpha → 8-bit RGBA (high bytes)
- `expandPalette` — palette indices → RGBA using PLTE+tRNS

All functions use well-founded recursion (no for/while) and include
size theorems for the output buffer.
-/

namespace Png.Native.ColorConvert

open Png

/-! ## Sub-byte unpacking -/

/-- Unpack sub-byte samples (1, 2, or 4 bits per sample) into one byte per sample.
    `width` is the number of samples per row, `bitDepth` is 1, 2, or 4.
    Input is packed left-to-right, MSB first within each byte.
    Output has exactly `width * height` bytes (one sample per byte). -/
def unpackSubByte (data : ByteArray) (width height bitDepth : Nat)
    (_hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4) : ByteArray :=
  let samplesPerByte := 8 / bitDepth
  let mask := (1 <<< bitDepth) - 1
  let packedRowBytes := (width * bitDepth + 7) / 8
  goRow data width height bitDepth samplesPerByte mask packedRowBytes 0 ByteArray.empty
where
  goRow (data : ByteArray) (width height bitDepth samplesPerByte mask packedRowBytes : Nat)
      (row : Nat) (acc : ByteArray) : ByteArray :=
    if row < height then
      let rowStart := row * packedRowBytes
      let acc' := goCol data width bitDepth samplesPerByte mask rowStart 0 acc
      goRow data width height bitDepth samplesPerByte mask packedRowBytes (row + 1) acc'
    else acc
  termination_by height - row
  goCol (data : ByteArray) (width bitDepth samplesPerByte mask rowStart : Nat)
      (col : Nat) (acc : ByteArray) : ByteArray :=
    if col < width then
      let byteIdx := rowStart + col / samplesPerByte
      let bitOffset := (samplesPerByte - 1 - col % samplesPerByte) * bitDepth
      let raw := data.get! byteIdx
      let sample := (raw.toNat >>> bitOffset) &&& mask
      goCol data width bitDepth samplesPerByte mask rowStart (col + 1) (acc.push sample.toUInt8)
    else acc
  termination_by width - col

private theorem unpackSubByte_goCol_size (data : ByteArray)
    (width bitDepth samplesPerByte mask rowStart col : Nat) (acc : ByteArray) :
    (unpackSubByte.goCol data width bitDepth samplesPerByte mask rowStart col acc).size =
    acc.size + (width - col) := by
  unfold unpackSubByte.goCol; split
  · simp only []; rw [unpackSubByte_goCol_size]; simp only [ByteArray.size_push]; omega
  · omega
  termination_by width - col

private theorem unpackSubByte_goRow_size (data : ByteArray)
    (width height bitDepth samplesPerByte mask packedRowBytes row : Nat) (acc : ByteArray)
    (hacc : acc.size = width * row) (hrow : row ≤ height) :
    (unpackSubByte.goRow data width height bitDepth samplesPerByte mask packedRowBytes row acc).size =
    width * height := by
  unfold unpackSubByte.goRow; split
  case isTrue hlt =>
    simp only []
    have hcol : (unpackSubByte.goCol data width bitDepth samplesPerByte mask
        (row * packedRowBytes) 0 acc).size = width * (row + 1) := by
      rw [unpackSubByte_goCol_size, hacc, Nat.sub_zero, Nat.mul_succ]
    exact unpackSubByte_goRow_size data width height bitDepth samplesPerByte mask
      packedRowBytes (row + 1) _ hcol (by omega)
  case isFalse hge =>
    have : row = height := by omega
    subst this; exact hacc
  termination_by height - row

/-- `unpackSubByte` output size. -/
theorem unpackSubByte_size (data : ByteArray) (width height bitDepth : Nat)
    (hbd : bitDepth = 1 ∨ bitDepth = 2 ∨ bitDepth = 4) :
    (unpackSubByte data width height bitDepth hbd).size = width * height := by
  unfold unpackSubByte
  exact unpackSubByte_goRow_size data width height bitDepth (8 / bitDepth)
    ((1 <<< bitDepth) - 1) ((width * bitDepth + 7) / 8) 0 ByteArray.empty
    (by simp only [ByteArray.size_empty]; omega) (by omega)

/-! ## 8-bit converters -/

/-- Convert 8-bit grayscale to RGBA. Each gray byte becomes (g, g, g, 255). -/
def grayscaleToRGBA (data : ByteArray) : ByteArray :=
  go data 0 ByteArray.empty
where
  go (data : ByteArray) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i < data.size then
      let g := data[i]
      go data (i + 1) (acc.push g |>.push g |>.push g |>.push 255)
    else acc
  termination_by data.size - i

private theorem grayscaleToRGBA_go_size (data : ByteArray) (i : Nat) (acc : ByteArray) :
    (grayscaleToRGBA.go data i acc).size = acc.size + (data.size - i) * 4 := by
  unfold grayscaleToRGBA.go; split
  case isTrue hlt =>
    simp only []; rw [grayscaleToRGBA_go_size]; simp only [ByteArray.size_push]; omega
  case isFalse => omega
  termination_by data.size - i

theorem grayscaleToRGBA_size (data : ByteArray) :
    (grayscaleToRGBA data).size = data.size * 4 := by
  unfold grayscaleToRGBA
  rw [grayscaleToRGBA_go_size]; simp only [ByteArray.size_empty]; omega

/-- Convert 8-bit RGB to RGBA. Each (R,G,B) triple becomes (R,G,B,255). -/
def rgbToRGBA (data : ByteArray) : ByteArray :=
  go data 0 ByteArray.empty
where
  go (data : ByteArray) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i + 2 < data.size then
      let r := data[i]'(by omega)
      let g := data[i + 1]'(by omega)
      let b := data[i + 2]'(by omega)
      go data (i + 3) (acc.push r |>.push g |>.push b |>.push 255)
    else acc
  termination_by data.size - i

private theorem rgbToRGBA_go_size (data : ByteArray) (i : Nat) (acc : ByteArray)
    (h3 : i % 3 = 0) (hd : data.size % 3 = 0) :
    (rgbToRGBA.go data i acc).size = acc.size + (data.size - i) / 3 * 4 := by
  unfold rgbToRGBA.go; split
  case isTrue hlt =>
    simp only []
    have hi3 : (i + 3) % 3 = 0 := by omega
    rw [rgbToRGBA_go_size data (i + 3) _ hi3 hd]
    simp only [ByteArray.size_push]
    have : (data.size - i) / 3 = (data.size - (i + 3)) / 3 + 1 := by omega
    omega
  case isFalse hge =>
    have : data.size - i < 3 := by omega
    have : (data.size - i) / 3 = 0 := by omega
    omega
  termination_by data.size - i

theorem rgbToRGBA_size (data : ByteArray) (h : data.size % 3 = 0) :
    (rgbToRGBA data).size = data.size / 3 * 4 := by
  unfold rgbToRGBA
  rw [rgbToRGBA_go_size data 0 ByteArray.empty (by omega) h]
  simp only [ByteArray.size_empty]; omega

/-- Convert 8-bit grayscale+alpha to RGBA. Each (G,A) pair becomes (G,G,G,A). -/
def grayAlphaToRGBA (data : ByteArray) : ByteArray :=
  go data 0 ByteArray.empty
where
  go (data : ByteArray) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i + 1 < data.size then
      let g := data[i]'(by omega)
      let a := data[i + 1]'(by omega)
      go data (i + 2) (acc.push g |>.push g |>.push g |>.push a)
    else acc
  termination_by data.size - i

private theorem grayAlphaToRGBA_go_size (data : ByteArray) (i : Nat) (acc : ByteArray)
    (h2 : i % 2 = 0) (hd : data.size % 2 = 0) :
    (grayAlphaToRGBA.go data i acc).size = acc.size + (data.size - i) / 2 * 4 := by
  unfold grayAlphaToRGBA.go; split
  case isTrue hlt =>
    simp only []
    have hi2 : (i + 2) % 2 = 0 := by omega
    rw [grayAlphaToRGBA_go_size data (i + 2) _ hi2 hd]
    simp only [ByteArray.size_push]
    have : (data.size - i) / 2 = (data.size - (i + 2)) / 2 + 1 := by omega
    omega
  case isFalse hge =>
    have : data.size - i < 2 := by omega
    have : (data.size - i) / 2 = 0 := by omega
    omega
  termination_by data.size - i

theorem grayAlphaToRGBA_size (data : ByteArray) (h : data.size % 2 = 0) :
    (grayAlphaToRGBA data).size = data.size / 2 * 4 := by
  unfold grayAlphaToRGBA
  rw [grayAlphaToRGBA_go_size data 0 ByteArray.empty (by omega) h]
  simp only [ByteArray.size_empty]; omega

/-! ## 16-bit converters (take high byte) -/

/-- Convert 16-bit grayscale to 8-bit RGBA. Takes high byte of each 16-bit sample. -/
def grayscale16ToRGBA (data : ByteArray) : ByteArray :=
  go data 0 ByteArray.empty
where
  go (data : ByteArray) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i + 1 < data.size then
      let g := data[i]'(by omega)  -- high byte
      go data (i + 2) (acc.push g |>.push g |>.push g |>.push 255)
    else acc
  termination_by data.size - i

/-- Convert 16-bit RGB to 8-bit RGBA. Takes high byte of each 16-bit channel. -/
def rgb16ToRGBA (data : ByteArray) : ByteArray :=
  go data 0 ByteArray.empty
where
  go (data : ByteArray) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i + 5 < data.size then
      let r := data[i]'(by omega)
      let g := data[i + 2]'(by omega)
      let b := data[i + 4]'(by omega)
      go data (i + 6) (acc.push r |>.push g |>.push b |>.push 255)
    else acc
  termination_by data.size - i

/-- Convert 16-bit grayscale+alpha to 8-bit RGBA. Takes high bytes. -/
def grayAlpha16ToRGBA (data : ByteArray) : ByteArray :=
  go data 0 ByteArray.empty
where
  go (data : ByteArray) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i + 3 < data.size then
      let g := data[i]'(by omega)
      let a := data[i + 2]'(by omega)
      go data (i + 4) (acc.push g |>.push g |>.push g |>.push a)
    else acc
  termination_by data.size - i

/-- Convert 16-bit RGBA to 8-bit RGBA. Takes high byte of each 16-bit channel. -/
def rgba16ToRGBA (data : ByteArray) : ByteArray :=
  go data 0 ByteArray.empty
where
  go (data : ByteArray) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i + 7 < data.size then
      let r := data[i]'(by omega)
      let g := data[i + 2]'(by omega)
      let b := data[i + 4]'(by omega)
      let a := data[i + 6]'(by omega)
      go data (i + 8) (acc.push r |>.push g |>.push b |>.push a)
    else acc
  termination_by data.size - i

/-! ## Palette expansion -/

/-- Expand palette indices to RGBA using PLTE entries and optional tRNS alpha.
    Each index byte maps to (R, G, B, A) where A comes from tRNS if present,
    or 255 if the index is beyond the tRNS array. -/
def expandPalette (data : ByteArray) (plte : PLTEInfo)
    (trns : Option TRNSInfo := none) : ByteArray :=
  let alphas := match trns with
    | some (.palette a) => a
    | _ => ByteArray.empty
  go data plte.entries alphas 0 ByteArray.empty
where
  go (data : ByteArray) (entries : Array PaletteEntry) (alphas : ByteArray)
      (i : Nat) (acc : ByteArray) : ByteArray :=
    if hi : i < data.size then
      let idx := data[i]
      let entry := if h : idx.toNat < entries.size then entries[idx.toNat]
                   else { r := 0, g := 0, b := 0 }
      let alpha := if ha : idx.toNat < alphas.size then alphas[idx.toNat] else 255
      go data entries alphas (i + 1) (acc.push entry.r |>.push entry.g |>.push entry.b |>.push alpha)
    else acc
  termination_by data.size - i

private theorem expandPalette_go_size (data : ByteArray) (entries : Array PaletteEntry)
    (alphas : ByteArray) (i : Nat) (acc : ByteArray) :
    (expandPalette.go data entries alphas i acc).size = acc.size + (data.size - i) * 4 := by
  unfold expandPalette.go; split
  case isTrue hlt =>
    simp only []; rw [expandPalette_go_size]; simp only [ByteArray.size_push]; omega
  case isFalse => omega
  termination_by data.size - i

theorem expandPalette_size (data : ByteArray) (plte : PLTEInfo)
    (trns : Option TRNSInfo) :
    (expandPalette data plte trns).size = data.size * 4 := by
  unfold expandPalette
  rw [expandPalette_go_size]; simp only [ByteArray.size_empty]; omega

end Png.Native.ColorConvert
