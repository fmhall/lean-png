import Png.Native.Chunk
import Zip.Native.Gzip
import Zip.Spec.ZlibCorrect

/-!
# IDAT Decompression Pipeline

Concatenate IDAT chunk data, decompress via lean-zip's zlib inflate,
and compress/split raw pixel data into IDAT chunks.

PNG IDAT data is zlib-compressed (RFC 1950). The decompressed stream
for non-interlaced images has size `height * (1 + scanlineBytes)`,
where the `+1` accounts for the filter type byte at the start of each row.

## References

- PNG Specification SS 4.1.3 (IDAT)
- PNG Specification SS 10 (Compression)
-/

namespace Png.Idat

/-- Default maximum IDAT chunk data size (65536 bytes, matching common encoders). -/
def defaultChunkSize : Nat := 65536

/-- Extract and concatenate `.data` from all IDAT chunks in a chunk list.
    Chunks are concatenated in order; non-IDAT chunks are skipped. -/
def extractIdatData (chunks : Array PngChunk) : ByteArray :=
  go chunks 0 ByteArray.empty
where
  go (chunks : Array PngChunk) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i < chunks.size then
      let chunk := chunks[i]
      let acc' := if chunk.isIDAT then acc ++ chunk.data else acc
      go chunks (i + 1) acc'
    else acc
  termination_by chunks.size - i

/-- Decompress concatenated IDAT data via zlib (RFC 1950).
    Uses the proof-friendly `decompressSingle` so roundtrip theorems compose
    with lean-zip's `zlib_decompressSingle_compress`.
    Returns the raw pixel data (filter-type bytes + pixel bytes per row). -/
def decompressIdat (zlibData : ByteArray)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) :
    Except String ByteArray :=
  Zip.Native.ZlibDecode.decompressSingle zlibData maxOutputSize

/-- Compress raw pixel data to zlib format. -/
def compressIdat (rawData : ByteArray) (level : UInt8 := 1) : ByteArray :=
  Zip.Native.ZlibEncode.compress rawData level

/-- Split a byte array into IDAT chunks of at most `chunkSize` bytes each. -/
def splitIntoIdatChunks (zlibData : ByteArray)
    (chunkSize : Nat := defaultChunkSize) : Array PngChunk :=
  if zlibData.size == 0 then
    -- PNG requires at least one IDAT chunk even if empty
    #[{ chunkType := ChunkType.IDAT, data := ByteArray.empty }]
  else if hcs : chunkSize = 0 then
    #[{ chunkType := ChunkType.IDAT, data := zlibData }]
  else
    go zlibData chunkSize (by omega) 0 #[]
where
  go (zlibData : ByteArray) (chunkSize : Nat) (hcs : chunkSize > 0) (offset : Nat)
      (acc : Array PngChunk) : Array PngChunk :=
    if h : offset < zlibData.size then
      let thisSize := min chunkSize (zlibData.size - offset)
      let data := zlibData.extract offset (offset + thisSize)
      have : zlibData.size - (offset + thisSize) < zlibData.size - offset := by omega
      go zlibData chunkSize hcs (offset + thisSize) (acc.push { chunkType := ChunkType.IDAT, data })
    else acc
  termination_by zlibData.size - offset

/-- Compress raw pixel data and split into IDAT chunks. -/
def compressAndSplit (rawData : ByteArray) (level : UInt8 := 1)
    (chunkSize : Nat := defaultChunkSize) : Array PngChunk :=
  let zlibData := compressIdat rawData level
  splitIntoIdatChunks zlibData chunkSize

/-- Validate that decompressed IDAT size matches IHDR expectations
    for a non-interlaced image. Expected size is
    `height * (1 + scanlineBytes)` where `+1` is for the filter byte. -/
def validateIdatSize (ihdr : IHDRInfo) (decompressedData : ByteArray) : Bool :=
  decompressedData.size == ihdr.expectedIdatSize

/-- Full IDAT extraction + decompression pipeline from a chunk array.
    Returns the decompressed pixel data. -/
def extractAndDecompress (chunks : Array PngChunk)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) :
    Except String ByteArray := do
  let zlibData := extractIdatData chunks
  if zlibData.size == 0 then
    throw "IDAT: no IDAT data found"
  decompressIdat zlibData maxOutputSize

/-- Full pipeline: extract IDAT data, decompress, and validate size
    against the IHDR. -/
def extractDecompressValidate (ihdr : IHDRInfo) (chunks : Array PngChunk)
    (maxOutputSize : Nat := 1024 * 1024 * 1024) :
    Except String ByteArray := do
  let raw ← extractAndDecompress chunks maxOutputSize
  if !validateIdatSize ihdr raw then
    throw s!"IDAT: decompressed size {raw.size} does not match expected {ihdr.expectedIdatSize}"
  pure raw

end Png.Idat
