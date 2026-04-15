import Png.Native.Chunk
import Png.Native.Filter
import Png.Native.Idat
import Png.Native.ColorConvert
import Png.Native.Interlace

/-!
# PNG Decoder

Pure Lean PNG decoder for all PNG images supporting all color types,
including Adam7-interlaced images.

Chains: PNG bytes → chunk parse → extract IDAT → decompress → unfilter → color convert → PngImage.

Each decompressed scanline is prefixed by a 1-byte filter type, per PNG specification §9.
For interlaced images, the decompressed stream contains 7 sub-images concatenated,
each with its own filter-byte-prefixed scanlines.
-/

namespace Png.Native.Decode

open Png
open Png.Native.Filter
open Png.Native.ColorConvert
open Png.Native.Interlace
open Png.Idat

/-- Find the first chunk with a given chunk type. Uses well-founded recursion. -/
def findChunk (chunks : Array PngChunk) (ct : ChunkType) : Option PngChunk :=
  go chunks ct 0
where
  go (chunks : Array PngChunk) (ct : ChunkType) (i : Nat) : Option PngChunk :=
    if h : i < chunks.size then
      if chunks[i].chunkType == ct then some chunks[i]
      else go chunks ct (i + 1)
    else none
  termination_by chunks.size - i

/-- Unfilter all scanlines from decompressed IDAT data.
    Each scanline starts with a 1-byte filter type, followed by `scanlineBytes` of pixel data.
    `bpp` is the bytes-per-pixel used for the filter predictor (minimum 1).
    `scanlineBytes` is the number of data bytes per row (without the filter byte).
    Returns the reconstructed raw pixel data (without filter bytes). -/
def unfilterScanlines (decompressed : ByteArray) (width height : UInt32)
    (bpp scanlineBytes : Nat) : Except String ByteArray :=
  let rowStride := 1 + scanlineBytes  -- filter byte + pixel data
  if hsz : decompressed.size = height.toNat * rowStride then
    .ok (go decompressed width height bpp scanlineBytes rowStride 0
      ByteArray.empty (ByteArray.mk (Array.replicate scanlineBytes 0)) hsz (by omega))
  else
    .error s!"decompressed size {decompressed.size} != expected {height.toNat * rowStride}"
where
  go (decompressed : ByteArray) (width height : UInt32) (bpp scanlineBytes rowStride : Nat)
      (r : Nat) (result priorRow : ByteArray)
      (hsz : decompressed.size = height.toNat * rowStride)
      (hrs : rowStride ≥ 1) : ByteArray :=
    if hr : r < height.toNat then
      let rowStart := r * rowStride
      have : rowStart < decompressed.size := by
        rw [hsz]; exact Nat.mul_lt_mul_of_pos_right hr hrs
      let ftByte := decompressed[rowStart]
      let ft := FilterType.ofUInt8 ftByte
      let filteredRow := decompressed.extract (rowStart + 1) (rowStart + 1 + scanlineBytes)
      let rawRow := unfilterRow ft bpp filteredRow priorRow
      go decompressed width height bpp scanlineBytes rowStride (r + 1) (result ++ rawRow) rawRow hsz hrs
    else result
  termination_by height.toNat - r

/-- Scale sub-byte sample values to 8-bit range.
    For bitDepth 1: 0→0, 1→255; bitDepth 2: 0→0, 1→85, 2→170, 3→255;
    bitDepth 4: 0→0, ..., 15→255. Uses well-founded recursion. -/
def scaleSubByte (data : ByteArray) (bitDepth : Nat) : ByteArray :=
  let scale := match bitDepth with
    | 1 => 255
    | 2 => 85
    | 4 => 17
    | _ => 1
  go data scale 0 ByteArray.empty
where
  go (data : ByteArray) (scale : Nat) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i < data.size then
      let v := data[i]
      go data scale (i + 1) (acc.push (v.toNat * scale).toUInt8)
    else acc
  termination_by data.size - i

/-- Scale a tRNS gray value to 8-bit given the image's bit depth.
    For sub-byte depths (1,2,4), apply the same scale factor as pixel data.
    For 8-bit, truncate to low byte. For 16-bit, take high byte. -/
private def scaleTrnsGray (gray : UInt16) (bitDepth : UInt8) : UInt8 :=
  match bitDepth with
  | 1 => (gray.toNat * 255).toUInt8
  | 2 => (gray.toNat * 85).toUInt8
  | 4 => (gray.toNat * 17).toUInt8
  | 8 => gray.toUInt8
  | 16 => (gray >>> 8).toUInt8
  | _ => gray.toUInt8

/-- Scale a tRNS RGB value to 8-bit given the image's bit depth.
    For 8-bit, truncate. For 16-bit, take high byte. -/
private def scaleTrnsRGB (val : UInt16) (bitDepth : UInt8) : UInt8 :=
  match bitDepth with
  | 16 => (val >>> 8).toUInt8
  | _ => val.toUInt8

/-- Apply tRNS color-key transparency to RGBA pixels.
    For grayscale: if sample matches transparent value, set alpha to 0.
    For RGB: if (R,G,B) matches transparent triple, set alpha to 0.
    The bitDepth parameter is needed to properly scale tRNS values.
    Uses well-founded recursion. -/
def applyTrnsKey (pixels : ByteArray) (trns : TRNSInfo) (bitDepth : UInt8) : ByteArray :=
  match trns with
  | .grayscale gray =>
    let grayByte := scaleTrnsGray gray bitDepth
    goGray pixels grayByte 0 ByteArray.empty
  | .rgb r g b =>
    let rByte := scaleTrnsRGB r bitDepth
    let gByte := scaleTrnsRGB g bitDepth
    let bByte := scaleTrnsRGB b bitDepth
    goRGB pixels rByte gByte bByte 0 ByteArray.empty
  | _ => pixels  -- palette tRNS handled separately
where
  goGray (pixels : ByteArray) (transGray : UInt8) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i + 3 < pixels.size then
      let r := pixels[i]'(by omega)
      let g := pixels[i + 1]'(by omega)
      let b := pixels[i + 2]'(by omega)
      let a := pixels[i + 3]'(by omega)
      -- For grayscale→RGBA, R=G=B=gray. Check if the gray matches the transparent value.
      let a' := if r == transGray then 0 else a
      goGray pixels transGray (i + 4) (acc.push r |>.push g |>.push b |>.push a')
    else acc
  termination_by pixels.size - i
  goRGB (pixels : ByteArray) (transR transG transB : UInt8) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i + 3 < pixels.size then
      let r := pixels[i]'(by omega)
      let g := pixels[i + 1]'(by omega)
      let b := pixels[i + 2]'(by omega)
      let a := pixels[i + 3]'(by omega)
      let a' := if r == transR && g == transG && b == transB then 0 else a
      goRGB pixels transR transG transB (i + 4) (acc.push r |>.push g |>.push b |>.push a')
    else acc
  termination_by pixels.size - i

/-- Unpack sub-byte samples (1, 2, or 4 bits) or return an error for unsupported depths. -/
private def unpackSubByteOrError (rawPixels : ByteArray) (width height : Nat)
    (bitDepth : UInt8) (label : String) : Except String ByteArray :=
  if _h : bitDepth = 1 then
    pure (unpackSubByte rawPixels width height 1 (Or.inl rfl))
  else if _h : bitDepth = 2 then
    pure (unpackSubByte rawPixels width height 2 (Or.inr (Or.inl rfl)))
  else if _h : bitDepth = 4 then
    pure (unpackSubByte rawPixels width height 4 (Or.inr (Or.inr rfl)))
  else .error s!"unsupported bit depth {bitDepth} for {label}"

/-- Optionally apply tRNS color-key transparency after conversion to RGBA. -/
private def applyTrnsOpt (rgba : ByteArray) (trns : Option TRNSInfo)
    (bitDepth : UInt8) : ByteArray :=
  match trns with | some t => applyTrnsKey rgba t bitDepth | none => rgba

/-- Convert raw unfiltered pixel data to RGBA 8-bit format based on color type and bit depth.
    For palette images, requires a PLTE chunk and optional tRNS chunk.
    For grayscale/RGB with tRNS, applies color-key transparency. -/
def convertToRGBA (rawPixels : ByteArray) (colorType : ColorType) (bitDepth : UInt8)
    (width height : Nat) (plte : Option PLTEInfo) (trns : Option TRNSInfo)
    : Except String ByteArray :=
  match colorType, bitDepth with
  | .rgba, 8 => pure rawPixels
  | .rgba, 16 => pure (rgba16ToRGBA rawPixels)
  | .rgb, 8 => pure (applyTrnsOpt (rgbToRGBA rawPixels) trns 8)
  | .rgb, 16 => pure (applyTrnsOpt (rgb16ToRGBA rawPixels) trns 16)
  | .grayscale, 8 => pure (applyTrnsOpt (grayscaleToRGBA rawPixels) trns 8)
  | .grayscale, 16 => pure (applyTrnsOpt (grayscale16ToRGBA rawPixels) trns 16)
  | .grayscaleAlpha, 8 => pure (grayAlphaToRGBA rawPixels)
  | .grayscaleAlpha, 16 => pure (grayAlpha16ToRGBA rawPixels)
  | .grayscale, bd => do
    let unpacked ← unpackSubByteOrError rawPixels width height bd "grayscale"
    pure (applyTrnsOpt (grayscaleToRGBA (scaleSubByte unpacked bd.toNat)) trns bd)
  | .palette, bd =>
    match plte with
    | none => .error "palette color type requires PLTE chunk"
    | some plteInfo => do
      let pixels ← if bd == 8 then pure rawPixels
        else unpackSubByteOrError rawPixels width height bd "palette"
      pure (expandPalette pixels plteInfo trns)
  | _, _ => .error s!"unsupported color type / bit depth combination"

/-- Compute the scanline byte count for a sub-image pass.
    `passScanlineBytes = (passWidth * channels * bitDepth + 7) / 8` -/
def passScanlineBytes (pw : Nat) (colorType : ColorType) (bitDepth : UInt8) : Nat :=
  (pw * IHDRInfo.channels colorType * bitDepth.toNat + 7) / 8

/-- Compute the total decompressed size for a single Adam7 pass.
    Empty passes (width=0 or height=0) contribute 0 bytes.
    Non-empty passes contribute `passHeight * (1 + passScanlineBytes)`. -/
def passDecompressedSize (pw ph : Nat) (colorType : ColorType) (bitDepth : UInt8) : Nat :=
  if pw == 0 || ph == 0 then 0
  else ph * (1 + passScanlineBytes pw colorType bitDepth)

/-- Decode a single Adam7 pass sub-image from its portion of the decompressed stream.
    Returns RGBA pixel data for this pass. Skips empty passes. -/
def decodePass (passData : ByteArray) (pw ph : Nat)
    (colorType : ColorType) (bitDepth : UInt8) (bpp : Nat)
    (plte : Option PLTEInfo) (trns : Option TRNSInfo) : Except String PngImage := do
  if pw == 0 || ph == 0 then
    pure { width := 0, height := 0, pixels := ByteArray.empty }
  else
    let slBytes := passScanlineBytes pw colorType bitDepth
    let rawPixels ← unfilterScanlines passData pw.toUInt32 ph.toUInt32 bpp slBytes
    let pixels ← convertToRGBA rawPixels colorType bitDepth pw ph plte trns
    pure { width := pw.toUInt32, height := ph.toUInt32, pixels }

/-- Decode all 7 Adam7 passes from the decompressed IDAT stream.
    Splits the stream into per-pass regions, decodes each, and scatters
    the sub-images into the full-size output. -/
def decodeInterlaced (ihdr : IHDRInfo) (decompressed : ByteArray)
    (plte : Option PLTEInfo) (trns : Option TRNSInfo) : Except String PngImage :=
  let bpp := ihdr.bytesPerPixel
  let w := ihdr.width.toNat
  let h := ihdr.height.toNat
  go ihdr decompressed plte trns bpp w h 0 0 #[]
where
  go (ihdr : IHDRInfo) (decompressed : ByteArray)
      (plte : Option PLTEInfo) (trns : Option TRNSInfo)
      (bpp w h : Nat) (p offset : Nat) (subImages : Array PngImage)
      : Except String PngImage :=
    if hp : p < 7 then
      let pw := passWidth ⟨p, hp⟩ w
      let ph := passHeight ⟨p, hp⟩ h
      let passSize := passDecompressedSize pw ph ihdr.colorType ihdr.bitDepth
      if offset + passSize > decompressed.size then
        .error s!"interlaced IDAT: pass {p} needs {passSize} bytes at offset {offset}, but only {decompressed.size - offset} available"
      else
        let passData := decompressed.extract offset (offset + passSize)
        match decodePass passData pw ph ihdr.colorType ihdr.bitDepth bpp plte trns with
        | .error e => .error e
        | .ok subImg =>
          go ihdr decompressed plte trns bpp w h (p + 1) (offset + passSize) (subImages.push subImg)
    else
      .ok (adam7Scatter subImages w h)
  termination_by 7 - p

/-- Decode PNG file bytes to a PngImage.
    Supports all PNG images including Adam7-interlaced, with all color types. -/
def decodePng (data : ByteArray) : Except String PngImage := do
  -- 1. Parse chunks (validates PNG signature internally)
  let chunks ← parseChunks data
  if h : chunks.size = 0 then
    throw "no chunks found"
  else
  -- 2. Extract and validate IHDR
  let firstChunk := chunks[0]
  if !firstChunk.isIHDR then
    throw "first chunk is not IHDR"
  let ihdr ← IHDRInfo.fromBytes firstChunk.data
  -- 3. Check interlace method
  if ihdr.interlaceMethod != .none then do
    -- Adam7 interlaced path
    let plte ← match ihdr.colorType with
      | .palette =>
        match findChunk chunks ChunkType.PLTE with
        | none => throw "palette color type but no PLTE chunk found"
        | some plteChunk => pure (some (← PLTEInfo.fromBytes plteChunk.data))
      | _ => pure none
    let trns ← match ihdr.colorType with
      | .grayscaleAlpha | .rgba => pure none
      | _ => match findChunk chunks ChunkType.tRNS with
        | some trnsChunk => pure (some (← TRNSInfo.fromBytes trnsChunk.data ihdr.colorType))
        | none => pure none
    let decompressed ← extractAndDecompress chunks
    decodeInterlaced ihdr decompressed plte trns
  else
  -- Non-interlaced path (unchanged)
  -- 4. Compute bytes-per-pixel for filter and scanline bytes
  let bpp := ihdr.bytesPerPixel
  let scanlineBytes := ihdr.scanlineBytes
  -- 5. Extract and decompress IDAT data
  let decompressed ← extractDecompressValidate ihdr chunks
  -- 6. Unfilter scanlines
  let rawPixels ← unfilterScanlines decompressed ihdr.width ihdr.height bpp scanlineBytes
  -- 7. For palette images, find PLTE and optional tRNS chunks
  let plte ← match ihdr.colorType with
    | .palette =>
      match findChunk chunks ChunkType.PLTE with
      | none => throw "palette color type but no PLTE chunk found"
      | some plteChunk => pure (some (← PLTEInfo.fromBytes plteChunk.data))
    | _ => pure none
  let trns ← match ihdr.colorType with
    | .grayscaleAlpha | .rgba => pure none  -- tRNS not applicable
    | _ => match findChunk chunks ChunkType.tRNS with
      | some trnsChunk => pure (some (← TRNSInfo.fromBytes trnsChunk.data ihdr.colorType))
      | none => pure none
  -- 8. Convert to RGBA 8-bit
  let pixels ← convertToRGBA rawPixels ihdr.colorType ihdr.bitDepth
    ihdr.width.toNat ihdr.height.toNat plte trns
  pure { width := ihdr.width, height := ihdr.height, pixels }

end Png.Native.Decode
