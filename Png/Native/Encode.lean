import Png.Native.Chunk
import Png.Native.Filter
import Png.Native.Idat
import Png.Native.Interlace

/-!
# PNG Encoder

Pure Lean PNG encoder for non-interlaced and Adam7-interlaced RGBA 8-bit images.

Chains: image pixels → filter scanlines → compress IDAT → chunk framing → PNG bytes.

The filter type byte is prepended to each scanline before compression,
per PNG specification §9.

For interlaced images, the 7 Adam7 sub-images are extracted, each is
filtered independently, and the filtered data is concatenated before
compression.
-/

namespace Png.Native.Encode

open Png
open Png.Native.Filter
open Png.Idat

/-- Filter strategy: which filter type to use for each row.
    Simple strategies use a fixed filter type for all rows. -/
inductive FilterStrategy where
  | fixed : FilterType → FilterStrategy
  deriving Repr, BEq

/-- The "always use None" strategy. -/
def FilterStrategy.none : FilterStrategy := .fixed .none

/-- The "always use Sub" strategy. -/
def FilterStrategy.sub : FilterStrategy := .fixed .sub

/-- The "always use Up" strategy. -/
def FilterStrategy.up : FilterStrategy := .fixed .up

/-- Get the filter type for a given row index. -/
def FilterStrategy.getFilterType (strategy : FilterStrategy) (_row : Nat) : FilterType :=
  match strategy with
  | .fixed ft => ft

/-- Build an IHDR chunk for an RGBA 8-bit non-interlaced image. -/
def mkIHDRChunk (width height : UInt32) : PngChunk :=
  let ihdr : IHDRInfo := {
    width, height
    bitDepth := 8
    colorType := .rgba
    compressionMethod := 0
    filterMethod := 0
    interlaceMethod := .none
  }
  { chunkType := ChunkType.IHDR, data := ihdr.toBytes }

/-- Build an IEND chunk. -/
def mkIENDChunk : PngChunk :=
  { chunkType := ChunkType.IEND, data := ByteArray.empty }

/-- Extract row `r` from RGBA pixel data.
    Each row is `width * 4` bytes (RGBA). -/
def extractRow (pixels : ByteArray) (width : UInt32) (r : Nat) : ByteArray :=
  let rowBytes := width.toNat * 4
  let start := r * rowBytes
  pixels.extract start (start + rowBytes)

/-- Filter all scanlines, prepending the filter type byte to each row.
    Returns the concatenated filtered data ready for compression. -/
def filterScanlines (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy) : ByteArray :=
  let bpp := 4  -- RGBA 8-bit
  let rowBytes := width.toNat * bpp
  go pixels width height strategy bpp 0 ByteArray.empty (ByteArray.mk (Array.replicate rowBytes 0))
where
  go (pixels : ByteArray) (width height : UInt32) (strategy : FilterStrategy)
      (bpp : Nat) (r : Nat) (result priorRow : ByteArray) : ByteArray :=
    if r < height.toNat then
      let rawRow := extractRow pixels width r
      let ft := strategy.getFilterType r
      let filteredRow := filterRow ft bpp rawRow priorRow
      let result' := (result.push ft.toUInt8) ++ filteredRow
      go pixels width height strategy bpp (r + 1) result' rawRow
    else result
  termination_by height.toNat - r

/-- Serialize an array of chunks by concatenating their serialized forms. -/
def serializeChunks (chunks : Array PngChunk) : ByteArray :=
  go chunks 0 ByteArray.empty
where
  go (chunks : Array PngChunk) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i < chunks.size then
      go chunks (i + 1) (acc ++ chunks[i].serialize)
    else acc
  termination_by chunks.size - i

/-- Encode a PngImage to PNG file bytes.
    Assumes RGBA 8-bit, non-interlaced. -/
def encodePng (image : PngImage) (strategy : FilterStrategy := .none) : ByteArray :=
  -- 1. Build chunks
  let ihdrChunk := mkIHDRChunk image.width image.height
  -- 2. Filter scanlines
  let filteredData := filterScanlines image.pixels image.width image.height strategy
  -- 3. Compress and split into IDAT chunks
  let idatChunks := compressAndSplit filteredData
  -- 4. IEND
  let iendChunk := mkIENDChunk
  -- 5. Assemble: PNG signature + serialized chunks
  pngSignature ++ ihdrChunk.serialize ++ serializeChunks idatChunks ++ iendChunk.serialize

open Png.Native.Interlace

/-- Build an IHDR chunk for an RGBA 8-bit Adam7-interlaced image. -/
def mkIHDRChunkInterlaced (width height : UInt32) : PngChunk :=
  let ihdr : IHDRInfo := {
    width, height
    bitDepth := 8
    colorType := .rgba
    compressionMethod := 0
    filterMethod := 0
    interlaceMethod := .adam7
  }
  { chunkType := ChunkType.IHDR, data := ihdr.toBytes }

/-- Filter scanlines for a single sub-image (pass) and append the result.
    Uses `filterScanlines` with the sub-image's own width/height.
    Empty passes (width=0 or height=0) contribute nothing. -/
def filterPass (subImage : PngImage) (strategy : FilterStrategy) : ByteArray :=
  if subImage.width == 0 || subImage.height == 0 then ByteArray.empty
  else filterScanlines subImage.pixels subImage.width subImage.height strategy

/-- Filter all 7 Adam7 passes and concatenate the results.
    Uses well-founded recursion. -/
def filterAllPasses (subImages : Array PngImage) (strategy : FilterStrategy) : ByteArray :=
  go subImages strategy 0 ByteArray.empty
where
  go (subImages : Array PngImage) (strategy : FilterStrategy)
      (p : Nat) (acc : ByteArray) : ByteArray :=
    if h : p < 7 then
      let passData :=
        if hp : p < subImages.size then
          filterPass subImages[p] strategy
        else ByteArray.empty
      go subImages strategy (p + 1) (acc ++ passData)
    else acc
  termination_by 7 - p

/-- Encode a PngImage to PNG file bytes with Adam7 interlacing.
    Assumes RGBA 8-bit. -/
def encodePngInterlaced (image : PngImage) (strategy : FilterStrategy := .none) : ByteArray :=
  -- 1. Build IHDR with interlaceMethod = .adam7
  let ihdrChunk := mkIHDRChunkInterlaced image.width image.height
  -- 2. Extract 7 sub-images
  let subImages := adam7Extract image
  -- 3. For each sub-image: filter scanlines, concatenate all filtered data
  let filteredData := filterAllPasses subImages strategy
  -- 4. Compress and split into IDAT chunks
  let idatChunks := compressAndSplit filteredData
  -- 5. IEND + assemble
  pngSignature ++ ihdrChunk.serialize ++ serializeChunks idatChunks ++ mkIENDChunk.serialize

end Png.Native.Encode
