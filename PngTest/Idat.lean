import Png.Native.Idat
import PngTest.Helpers

/-!
# IDAT Pipeline Tests

Tests for IDAT data extraction, zlib compression/decompression roundtrip,
size validation, chunk splitting, and edge cases.
-/

namespace PngTest.Idat

open Png PngTest
open Png.Idat

/-! ## Compress/decompress roundtrip -/

def testRoundtripSmall : IO Unit := do
  -- Synthetic pixel data: 4x2 RGBA with filter bytes
  -- Each row: 1 filter byte + 4*4 pixel bytes = 17 bytes
  let row := ByteArray.mk #[0, -- filter type None
    255, 0, 0, 255,   -- red pixel
    0, 255, 0, 255,   -- green pixel
    0, 0, 255, 255,   -- blue pixel
    255, 255, 0, 255]  -- yellow pixel
  let rawData := row ++ row  -- 2 rows
  let compressed := compressIdat rawData
  check (compressed.size > 0) "compressed data is empty"
  match decompressIdat compressed with
  | .ok decompressed =>
    check (decompressed == rawData)
      s!"roundtrip mismatch: got {decompressed.size} bytes, expected {rawData.size}"
  | .error e => throw (.userError s!"decompression failed: {e}")

def testRoundtripLarger : IO Unit := do
  -- 100x100 grayscale: each row is 1 filter byte + 100 pixels = 101 bytes
  let mut rawData := ByteArray.empty
  for i in [:100] do
    -- Filter byte
    rawData := rawData.push 0
    -- 100 pixel bytes with a gradient pattern
    for j in [:100] do
      rawData := rawData.push ((i * 100 + j) % 256).toUInt8
  let compressed := compressIdat rawData
  match decompressIdat compressed with
  | .ok decompressed =>
    check (decompressed == rawData)
      s!"large roundtrip mismatch: {decompressed.size} vs {rawData.size}"
  | .error e => throw (.userError s!"large decompression failed: {e}")

/-! ## Size validation -/

def testSizeValidation : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 4, height := 2, bitDepth := 8
    colorType := .rgba, compressionMethod := 0
    filterMethod := 0, interlaceMethod := .none
  }
  -- Expected: 2 * (1 + 4*4) = 2 * 17 = 34
  check (ihdr.expectedIdatSize == 34)
    s!"expectedIdatSize: got {ihdr.expectedIdatSize}, expected 34"
  -- Correct size
  let goodData := ByteArray.mk (Array.replicate 34 0)
  check (validateIdatSize ihdr goodData) "correct size rejected"
  -- Wrong size
  let badData := ByteArray.mk (Array.replicate 33 0)
  check (!validateIdatSize ihdr badData) "wrong size accepted"

def testSizeValidationGrayscale : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 10, height := 5, bitDepth := 8
    colorType := .grayscale, compressionMethod := 0
    filterMethod := 0, interlaceMethod := .none
  }
  -- Expected: 5 * (1 + 10) = 55
  check (ihdr.expectedIdatSize == 55)
    s!"grayscale expectedIdatSize: got {ihdr.expectedIdatSize}, expected 55"

def testSizeValidationRGB16 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 3, height := 2, bitDepth := 16
    colorType := .rgb, compressionMethod := 0
    filterMethod := 0, interlaceMethod := .none
  }
  -- scanlineBytes = 3 * 2 * 3 / 8 rounded up = 18
  -- Expected: 2 * (1 + 18) = 38
  check (ihdr.expectedIdatSize == 38)
    s!"RGB16 expectedIdatSize: got {ihdr.expectedIdatSize}, expected 38"

/-! ## Empty image edge case -/

def testEmptyData : IO Unit := do
  -- Empty IDAT data should fail decompression
  match decompressIdat ByteArray.empty with
  | .ok _ => throw (.userError "decompressing empty data should fail")
  | .error _ => pure ()  -- expected

def testNoIdatChunks : IO Unit := do
  -- Extract from chunks with no IDAT
  let ihdr : PngChunk := { chunkType := ChunkType.IHDR, data := ByteArray.mk (Array.replicate 13 0) }
  let iend : PngChunk := { chunkType := ChunkType.IEND, data := ByteArray.empty }
  let result := extractIdatData #[ihdr, iend]
  check (result.size == 0) s!"no-IDAT extraction should be empty, got {result.size}"

def testExtractAndDecompressNoIdat : IO Unit := do
  -- extractAndDecompress should fail when there are no IDAT chunks
  let ihdr : PngChunk := { chunkType := ChunkType.IHDR, data := ByteArray.mk (Array.replicate 13 0) }
  let iend : PngChunk := { chunkType := ChunkType.IEND, data := ByteArray.empty }
  match extractAndDecompress #[ihdr, iend] with
  | .ok _ => throw (.userError "extractAndDecompress should fail with no IDAT")
  | .error _ => pure ()  -- expected

/-! ## Multi-chunk splitting and reassembly -/

def testSplitSmallChunks : IO Unit := do
  -- Use incompressible random-looking data so compressed output is large enough to split
  let mut rawData := ByteArray.empty
  for i in [:500] do
    rawData := rawData.push ((i * 137 + 43) % 256).toUInt8
  let compressed := compressIdat rawData
  let chunks := splitIntoIdatChunks compressed 16  -- 16-byte chunks
  -- Compressed output of 500 bytes of varied data should exceed 16 bytes
  check (chunks.size > 1)
    s!"expected multiple chunks, got {chunks.size} (compressed size={compressed.size})"
  -- All chunks should be IDAT
  for chunk in chunks do
    check (chunk.isIDAT) "split chunk is not IDAT"
  -- Each chunk should be at most 16 bytes
  for chunk in chunks do
    check (chunk.data.size ≤ 16)
      s!"chunk data size {chunk.data.size} exceeds 16"
  -- Reassembly should recover the compressed data
  let reassembled := extractIdatData chunks
  check (reassembled == compressed)
    s!"reassembled size {reassembled.size} != compressed size {compressed.size}"

def testSplitSingleChunk : IO Unit := do
  -- Data small enough to fit in one chunk
  let data := ByteArray.mk #[1, 2, 3, 4, 5]
  let chunks := splitIntoIdatChunks data 1000
  check (chunks.size == 1) s!"expected 1 chunk, got {chunks.size}"
  check (chunks[0]!.data == data) "single chunk data mismatch"

def testSplitEmptyData : IO Unit := do
  -- Empty data should still produce one (empty) IDAT chunk
  let chunks := splitIntoIdatChunks ByteArray.empty
  check (chunks.size == 1) s!"expected 1 chunk for empty data, got {chunks.size}"
  check (chunks[0]!.isIDAT) "empty split chunk is not IDAT"
  check (chunks[0]!.data.size == 0) "empty split chunk should have 0 bytes"

def testFullPipelineRoundtrip : IO Unit := do
  -- Compress, split, extract, decompress = identity
  let rawData := ByteArray.mk (Array.replicate 200 0xAB)
  let chunks := compressAndSplit rawData 1 32  -- small chunks
  -- All chunks are IDAT
  for chunk in chunks do
    check (chunk.isIDAT) "compressAndSplit chunk is not IDAT"
  -- Full roundtrip
  match extractAndDecompress chunks with
  | .ok recovered =>
    check (recovered == rawData)
      s!"full pipeline roundtrip failed: {recovered.size} vs {rawData.size}"
  | .error e => throw (.userError s!"full pipeline decompression failed: {e}")

def testCompressAndSplitDefault : IO Unit := do
  -- Test with default chunk size
  let rawData := ByteArray.mk (Array.replicate 50 0)
  let chunks := compressAndSplit rawData
  check (chunks.size ≥ 1) "compressAndSplit produced no chunks"
  let reassembled := extractIdatData chunks
  match decompressIdat reassembled with
  | .ok decompressed =>
    check (decompressed == rawData)
      s!"default split roundtrip failed: {decompressed.size} vs {rawData.size}"
  | .error e => throw (.userError s!"default split decompression failed: {e}")

/-! ## IDAT extraction with mixed chunks -/

def testExtractSkipsNonIdat : IO Unit := do
  let idat1 : PngChunk := { chunkType := ChunkType.IDAT, data := ByteArray.mk #[1, 2, 3] }
  let text : PngChunk := { chunkType := 0x74455874, data := ByteArray.mk #[99] }
  let idat2 : PngChunk := { chunkType := ChunkType.IDAT, data := ByteArray.mk #[4, 5] }
  let result := extractIdatData #[idat1, text, idat2]
  check (result == ByteArray.mk #[1, 2, 3, 4, 5])
    s!"extraction with mixed chunks failed, got {result.size} bytes"

/-! ## Test runner -/

def runAll : IO Unit := do
  let tests : Array (String × IO Unit) := #[
    ("roundtrip small",              testRoundtripSmall),
    ("roundtrip larger",             testRoundtripLarger),
    ("size validation RGBA",         testSizeValidation),
    ("size validation grayscale",    testSizeValidationGrayscale),
    ("size validation RGB16",        testSizeValidationRGB16),
    ("empty data",                   testEmptyData),
    ("no IDAT chunks",              testNoIdatChunks),
    ("extractAndDecompress no IDAT", testExtractAndDecompressNoIdat),
    ("split small chunks",           testSplitSmallChunks),
    ("split single chunk",           testSplitSingleChunk),
    ("split empty data",             testSplitEmptyData),
    ("full pipeline roundtrip",      testFullPipelineRoundtrip),
    ("compress and split default",   testCompressAndSplitDefault),
    ("extract skips non-IDAT",       testExtractSkipsNonIdat)
  ]
  let mut passed := 0
  let mut failed := 0
  for (name, test) in tests do
    try
      test
      IO.println s!"  pass: {name}"
      passed := passed + 1
    catch e =>
      IO.eprintln s!"  FAIL: {name}: {e}"
      failed := failed + 1
  IO.println s!"IDAT tests: {passed} passed, {failed} failed"
  if failed > 0 then
    throw (.userError s!"{failed} IDAT test(s) failed")

end PngTest.Idat
