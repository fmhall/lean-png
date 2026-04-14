import Png.Types

/-!
# Adam7 Interlacing (Native Lean)

Pure Lean implementation of Adam7 interlacing as defined by the PNG
specification. Adam7 defines 7 passes over the image grid, each
sampling pixels at specific row/column offsets and strides.

## Pass Layout

| Pass | Row start | Row stride | Col start | Col stride |
|------|-----------|------------|-----------|------------|
| 1    | 0         | 8          | 0         | 8          |
| 2    | 0         | 8          | 4         | 8          |
| 3    | 4         | 8          | 0         | 4          |
| 4    | 0         | 4          | 2         | 4          |
| 5    | 2         | 4          | 0         | 2          |
| 6    | 0         | 2          | 1         | 2          |
| 7    | 1         | 2          | 0         | 1          |

Provides sub-image extraction (7 passes), pixel scatter (place sub-image
pixels into full image), and coordinate conversion functions.

See `Png/Spec/InterlaceCorrect.lean` for specification theorems.
-/

namespace Png.Native.Interlace

open Png

/-! ## Adam7 Constants -/

/-- Row start offset for each of the 7 Adam7 passes. -/
def adam7RowStart (p : Fin 7) : Nat :=
  match p with
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 4 | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 2 | ⟨5, _⟩ => 0 | ⟨6, _⟩ => 1

/-- Row stride (vertical spacing) for each of the 7 Adam7 passes. -/
def adam7RowStride (p : Fin 7) : Nat :=
  match p with
  | ⟨0, _⟩ => 8 | ⟨1, _⟩ => 8 | ⟨2, _⟩ => 8 | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 4 | ⟨5, _⟩ => 2 | ⟨6, _⟩ => 2

/-- Column start offset for each of the 7 Adam7 passes. -/
def adam7ColStart (p : Fin 7) : Nat :=
  match p with
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 4 | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 0 | ⟨5, _⟩ => 1 | ⟨6, _⟩ => 0

/-- Column stride (horizontal spacing) for each of the 7 Adam7 passes. -/
def adam7ColStride (p : Fin 7) : Nat :=
  match p with
  | ⟨0, _⟩ => 8 | ⟨1, _⟩ => 8 | ⟨2, _⟩ => 4 | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 2 | ⟨5, _⟩ => 2 | ⟨6, _⟩ => 1

/-! ## Stride positivity

These lemmas are needed for termination proofs and division well-definedness. -/

theorem adam7RowStride_pos (p : Fin 7) : adam7RowStride p > 0 := by
  match p with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
    simp only [adam7RowStride]; omega

theorem adam7ColStride_pos (p : Fin 7) : adam7ColStride p > 0 := by
  match p with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
    simp only [adam7ColStride]; omega

theorem adam7RowStart_lt_stride (p : Fin 7) : adam7RowStart p < adam7RowStride p := by
  match p with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
    simp only [adam7RowStart, adam7RowStride]; omega

theorem adam7ColStart_lt_stride (p : Fin 7) : adam7ColStart p < adam7ColStride p := by
  match p with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
    simp only [adam7ColStart, adam7ColStride]; omega

/-! ## Sub-Image Dimensions -/

/-- Width of the sub-image for pass `p` given full image width `width`.
    This is the number of columns sampled by this pass. -/
def passWidth (p : Fin 7) (width : Nat) : Nat :=
  if width ≤ adam7ColStart p then 0
  else (width - adam7ColStart p + adam7ColStride p - 1) / adam7ColStride p

/-- Height of the sub-image for pass `p` given full image height `height`.
    This is the number of rows sampled by this pass. -/
def passHeight (p : Fin 7) (height : Nat) : Nat :=
  if height ≤ adam7RowStart p then 0
  else (height - adam7RowStart p + adam7RowStride p - 1) / adam7RowStride p

/-! ## Coordinate Conversion -/

/-- Convert a full-image row to a sub-image row for pass `p`.
    Assumes the row belongs to this pass (i.e., `r % rowStride = rowStart`). -/
def toSubRow (p : Fin 7) (r : Nat) : Nat :=
  (r - adam7RowStart p) / adam7RowStride p

/-- Convert a full-image column to a sub-image column for pass `p`.
    Assumes the column belongs to this pass (i.e., `c % colStride = colStart`). -/
def toSubCol (p : Fin 7) (c : Nat) : Nat :=
  (c - adam7ColStart p) / adam7ColStride p

/-- Convert a sub-image row to a full-image row for pass `p`. -/
def fromSubRow (p : Fin 7) (sr : Nat) : Nat :=
  sr * adam7RowStride p + adam7RowStart p

/-- Convert a sub-image column to a full-image column for pass `p`. -/
def fromSubCol (p : Fin 7) (sc : Nat) : Nat :=
  sc * adam7ColStride p + adam7ColStart p

/-! ## Pixel Access Helpers

PngImage stores RGBA pixels as a flat ByteArray:
`pixels[4 * (row * width + col) + channel]` where channel 0=R, 1=G, 2=B, 3=A. -/

/-- Get a 4-byte RGBA pixel from the image at (row, col).
    Returns `(0, 0, 0, 0)` if out of bounds. -/
def getPixel (pixels : ByteArray) (width : Nat) (row col : Nat) : UInt8 × UInt8 × UInt8 × UInt8 :=
  let idx := 4 * (row * width + col)
  if h : idx + 3 < pixels.size then
    (pixels[idx]'(by omega),
     pixels[idx + 1]'(by omega),
     pixels[idx + 2]'(by omega),
     pixels[idx + 3]'(by omega))
  else (0, 0, 0, 0)

/-- Copy a 4-byte RGBA pixel into a ByteArray at offset `idx`. -/
def setPixelAt (pixels : ByteArray) (idx : Nat)
    (pixel : UInt8 × UInt8 × UInt8 × UInt8) : ByteArray :=
  if idx + 3 < pixels.size then
    let pixels := pixels.set! idx pixel.1
    let pixels := pixels.set! (idx + 1) pixel.2.1
    let pixels := pixels.set! (idx + 2) pixel.2.2.1
    let pixels := pixels.set! (idx + 3) pixel.2.2.2
    pixels
  else pixels

/-! ## Sub-Image Extraction

Extract the 7 sub-images from a full image. Each sub-image contains
only the pixels belonging to its pass. -/

/-- Build a sub-image for pass `p` by iterating over all sub-image pixels
    and copying them from the full image.
    Uses well-founded recursion on the linear pixel index. -/
def extractPass (image : PngImage) (p : Fin 7) : PngImage :=
  let w := image.width.toNat
  let subW := passWidth p w
  let subH := passHeight p (image.height.toNat)
  let totalPixels := subW * subH
  let buf := go image.pixels w p subW 0 totalPixels ByteArray.empty
  { width := subW.toUInt32, height := subH.toUInt32, pixels := buf }
where
  /-- Iterate over linear pixel indices `i` in `[i, total)`, extracting
      each pixel from the full image into the output buffer. -/
  go (srcPixels : ByteArray) (srcWidth : Nat) (p : Fin 7)
      (subW : Nat) (i total : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ total then out
    else
      let sr := i / subW
      let sc := if subW > 0 then i % subW else 0
      let fullRow := fromSubRow p sr
      let fullCol := fromSubCol p sc
      let pixel := getPixel srcPixels srcWidth fullRow fullCol
      let out := out.push pixel.1
      let out := out.push pixel.2.1
      let out := out.push pixel.2.2.1
      let out := out.push pixel.2.2.2
      go srcPixels srcWidth p subW (i + 1) total out
  termination_by total - i

/-- Extract all 7 Adam7 sub-images from a full image. -/
def adam7Extract (image : PngImage) : Array PngImage :=
  go 0 #[]
where
  go (p : Nat) (acc : Array PngImage) : Array PngImage :=
    if h : p < 7 then
      go (p + 1) (acc.push (extractPass image ⟨p, h⟩))
    else acc
  termination_by 7 - p

/-! ## Sub-Image Scatter

Place sub-image pixels back into a full image. -/

/-- Scatter pixels from pass `p`'s sub-image into the full image buffer.
    Iterates over all sub-image pixel indices. -/
def scatterPass (buf : ByteArray) (fullWidth : Nat)
    (subImage : PngImage) (p : Fin 7) : ByteArray :=
  let subW := subImage.width.toNat
  let subH := subImage.height.toNat
  let totalPixels := subW * subH
  go buf fullWidth subImage.pixels subW p 0 totalPixels
where
  go (buf : ByteArray) (fullWidth : Nat) (subPixels : ByteArray)
      (subW : Nat) (p : Fin 7) (i total : Nat) : ByteArray :=
    if i ≥ total then buf
    else
      let sr := i / subW
      let sc := if subW > 0 then i % subW else 0
      let fullRow := fromSubRow p sr
      let fullCol := fromSubCol p sc
      let dstIdx := 4 * (fullRow * fullWidth + fullCol)
      let srcIdx := 4 * i
      let pixel : UInt8 × UInt8 × UInt8 × UInt8 :=
        if h : srcIdx + 3 < subPixels.size then
          (subPixels[srcIdx]'(by omega),
           subPixels[srcIdx + 1]'(by omega),
           subPixels[srcIdx + 2]'(by omega),
           subPixels[srcIdx + 3]'(by omega))
        else (0, 0, 0, 0)
      let buf := setPixelAt buf dstIdx pixel
      go buf fullWidth subPixels subW p (i + 1) total
  termination_by total - i

/-- Scatter all 7 sub-images into a new full-size image. -/
def adam7Scatter (subImages : Array PngImage) (width height : Nat) : PngImage :=
  let totalBytes := width * height * 4
  let buf := ByteArray.mk (Array.replicate totalBytes 0)
  let buf := go subImages buf width 0
  { width := width.toUInt32, height := height.toUInt32, pixels := buf }
where
  go (subImages : Array PngImage) (buf : ByteArray) (fullWidth : Nat)
      (p : Nat) : ByteArray :=
    if h : p < 7 then
      if hp : p < subImages.size then
        let buf := scatterPass buf fullWidth subImages[p] ⟨p, h⟩
        go subImages buf fullWidth (p + 1)
      else
        go subImages buf fullWidth (p + 1)
    else buf
  termination_by 7 - p

end Png.Native.Interlace
