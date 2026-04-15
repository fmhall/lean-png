import Png.Native.Chunk
import Png.Native.Filter
import Png.Native.Idat

/-!
# PNG Decoder

Pure Lean PNG decoder for non-interlaced RGBA 8-bit images.

Chains: PNG bytes → chunk parse → extract IDAT → decompress → unfilter → PngImage.

Each decompressed scanline is prefixed by a 1-byte filter type, per PNG specification §9.
-/

namespace Png.Native.Decode

open Png
open Png.Native.Filter
open Png.Idat

/-- Unfilter all scanlines from decompressed IDAT data.
    Each scanline starts with a 1-byte filter type, followed by `scanlineBytes` of pixel data.
    Returns the reconstructed raw pixel data (without filter bytes). -/
def unfilterScanlines (decompressed : ByteArray) (width height : UInt32)
    (bpp : Nat) : Except String ByteArray :=
  let scanlineBytes := width.toNat * bpp
  let rowStride := 1 + scanlineBytes  -- filter byte + pixel data
  if decompressed.size != height.toNat * rowStride then
    .error s!"decompressed size {decompressed.size} != expected {height.toNat * rowStride}"
  else
    .ok (go decompressed width height bpp scanlineBytes rowStride 0
      ByteArray.empty (ByteArray.mk (Array.replicate scanlineBytes 0)))
where
  go (decompressed : ByteArray) (width height : UInt32) (bpp scanlineBytes rowStride : Nat)
      (r : Nat) (result priorRow : ByteArray) : ByteArray :=
    if r < height.toNat then
      let rowStart := r * rowStride
      let ftByte := decompressed.get! rowStart
      let ft := FilterType.ofUInt8 ftByte
      let filteredRow := decompressed.extract (rowStart + 1) (rowStart + 1 + scanlineBytes)
      let rawRow := unfilterRow ft bpp filteredRow priorRow
      go decompressed width height bpp scanlineBytes rowStride (r + 1) (result ++ rawRow) rawRow
    else result
  termination_by height.toNat - r

/-- Decode PNG file bytes to a PngImage.
    Supports non-interlaced RGBA 8-bit images. -/
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
  -- 3. Validate: non-interlaced only
  if ihdr.interlaceMethod != .none then
    throw "interlaced images not supported"
  -- 4. For now, only support 8-bit RGBA
  if ihdr.bitDepth != 8 || ihdr.colorType != .rgba then
    throw "only 8-bit RGBA images are supported"
  let bpp := 4  -- RGBA 8-bit
  -- 5. Extract and decompress IDAT data
  let decompressed ← extractDecompressValidate ihdr chunks
  -- 6. Unfilter scanlines
  let pixels ← unfilterScanlines decompressed ihdr.width ihdr.height bpp
  pure { width := ihdr.width, height := ihdr.height, pixels }

end Png.Native.Decode
