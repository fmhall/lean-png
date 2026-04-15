import Png.Native.Chunk

/-!
# Chunk Framing Tests

Tests for PNG signature validation, chunk parsing/serialization,
IHDR parsing, CRC32 validation, and chunk sequence validity.
-/

namespace PngTest.Chunk

open Png

/-- Helper: assert condition with message. -/
def check (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure ()
  else throw (.userError s!"FAIL: {msg}")

/-! ## PNG Signature tests -/

def testSignatureValid : IO Unit := do
  let sig := pngSignature
  let data := sig ++ ByteArray.mk #[0, 0, 0, 0]
  check (validateSignature data) "valid PNG signature rejected"

def testSignatureInvalid : IO Unit := do
  let bad := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0]
  check (!validateSignature bad) "invalid signature accepted"

def testSignatureTooShort : IO Unit := do
  let short := ByteArray.mk #[137, 80, 78]
  check (!validateSignature short) "short signature accepted"

/-! ## Big-endian read/write roundtrip -/

def testUInt32BERoundtrip : IO Unit := do
  let vals := #[(0 : UInt32), 1, 255, 256, 65535, 0x12345678, 0xFFFFFFFF]
  for v in vals do
    let encoded := writeUInt32BE v
    check (encoded.size == 4) s!"writeUInt32BE produced {encoded.size} bytes, expected 4"
    let decoded := readUInt32BE encoded 0
    check (decoded == v) s!"UInt32BE roundtrip failed for {v}: got {decoded}"

/-! ## Chunk serialize/parse roundtrip -/

def testChunkRoundtrip : IO Unit := do
  let chunk : PngChunk := {
    chunkType := ChunkType.IDAT
    data := ByteArray.mk #[1, 2, 3, 4, 5]
  }
  let serialized := chunk.serialize
  check (serialized.size == 17) s!"serialized size {serialized.size} != 17"
  match parseChunk serialized 0 with
  | .ok result =>
    check (result.chunk.chunkType == chunk.chunkType)
      s!"chunk type mismatch: {ChunkType.toString result.chunk.chunkType}"
    check (result.chunk.data == chunk.data) "chunk data mismatch"
    check (result.offset == serialized.size)
      s!"offset {result.offset} != {serialized.size}"
  | .error e => throw (.userError s!"parse failed: {e}")

def testChunkEmptyData : IO Unit := do
  let chunk : PngChunk := {
    chunkType := ChunkType.IEND
    data := ByteArray.empty
  }
  let serialized := chunk.serialize
  check (serialized.size == 12) s!"IEND serialized size {serialized.size} != 12"
  match parseChunk serialized 0 with
  | .ok result =>
    check (result.chunk == chunk) "IEND roundtrip mismatch"
  | .error e => throw (.userError s!"IEND parse failed: {e}")

def testChunkCrcMismatch : IO Unit := do
  let chunk : PngChunk := {
    chunkType := ChunkType.IDAT
    data := ByteArray.mk #[1, 2, 3]
  }
  let mut serialized := chunk.serialize
  -- Corrupt the last byte (part of CRC)
  serialized := serialized.set! (serialized.size - 1)
    (serialized[serialized.size - 1]! ^^^ 0xFF)
  match parseChunk serialized 0 with
  | .ok _ => throw (.userError "corrupted CRC was accepted")
  | .error _ => pure ()  -- expected

/-! ## IHDR tests -/

def testIHDRRoundtrip : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 640
    height := 480
    bitDepth := 8
    colorType := .rgba
    compressionMethod := 0
    filterMethod := 0
    interlaceMethod := .none
  }
  let bytes := ihdr.toBytes
  check (bytes.size == 13) s!"IHDR toBytes size {bytes.size} != 13"
  match IHDRInfo.fromBytes bytes with
  | .ok parsed =>
    check (parsed.width == ihdr.width) s!"width mismatch: {parsed.width}"
    check (parsed.height == ihdr.height) s!"height mismatch: {parsed.height}"
    check (parsed.bitDepth == ihdr.bitDepth) "bitDepth mismatch"
    check (parsed.colorType == ihdr.colorType) "colorType mismatch"
    check (parsed.interlaceMethod == ihdr.interlaceMethod) "interlaceMethod mismatch"
  | .error e => throw (.userError s!"IHDR parse failed: {e}")

def testIHDRZeroWidth : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 0, height := 480, bitDepth := 8
    colorType := .rgba, compressionMethod := 0
    filterMethod := 0, interlaceMethod := .none
  }
  match IHDRInfo.fromBytes ihdr.toBytes with
  | .ok _ => throw (.userError "zero-width IHDR accepted")
  | .error _ => pure ()

def testIHDRBytesPerPixel : IO Unit := do
  -- RGBA 8-bit: 4 channels * 1 byte = 4
  let rgba8 : IHDRInfo := {
    width := 1, height := 1, bitDepth := 8
    colorType := .rgba, compressionMethod := 0
    filterMethod := 0, interlaceMethod := .none
  }
  check (rgba8.bytesPerPixel == 4) s!"RGBA8 bpp {rgba8.bytesPerPixel} != 4"
  -- Grayscale 8-bit: 1 channel * 1 byte = 1
  let gray8 : IHDRInfo := {
    width := 1, height := 1, bitDepth := 8
    colorType := .grayscale, compressionMethod := 0
    filterMethod := 0, interlaceMethod := .none
  }
  check (gray8.bytesPerPixel == 1) s!"Gray8 bpp {gray8.bytesPerPixel} != 1"
  -- RGB 16-bit: 3 channels * 2 bytes = 6
  let rgb16 : IHDRInfo := {
    width := 1, height := 1, bitDepth := 16
    colorType := .rgb, compressionMethod := 0
    filterMethod := 0, interlaceMethod := .none
  }
  check (rgb16.bytesPerPixel == 6) s!"RGB16 bpp {rgb16.bytesPerPixel} != 6"

/-! ## Chunk type classification -/

def testChunkTypeClassification : IO Unit := do
  check (ChunkType.isCritical ChunkType.IHDR) "IHDR not critical"
  check (ChunkType.isCritical ChunkType.IDAT) "IDAT not critical"
  check (ChunkType.isCritical ChunkType.IEND) "IEND not critical"
  check (ChunkType.isCritical ChunkType.PLTE) "PLTE not critical"
  -- Ancillary chunks have lowercase first letter; e.g. "tEXt" = 0x74455874
  let tEXt : ChunkType := 0x74455874
  check (ChunkType.isAncillary tEXt) "tEXt not ancillary"

def testChunkTypeToString : IO Unit := do
  check (ChunkType.toString ChunkType.IHDR == "IHDR") "IHDR toString"
  check (ChunkType.toString ChunkType.IDAT == "IDAT") "IDAT toString"
  check (ChunkType.toString ChunkType.IEND == "IEND") "IEND toString"

/-! ## Chunk sequence validity -/

def testValidChunkSequence : IO Unit := do
  let ihdr : PngChunk := { chunkType := ChunkType.IHDR, data := ByteArray.mk (Array.replicate 13 0) }
  let idat : PngChunk := { chunkType := ChunkType.IDAT, data := ByteArray.mk #[1] }
  let iend : PngChunk := { chunkType := ChunkType.IEND, data := ByteArray.empty }
  -- Valid: IHDR, IDAT, IEND
  check (validChunkSequence #[ihdr, idat, iend]) "basic valid sequence rejected"
  -- Valid: IHDR, IDAT, IDAT, IEND (contiguous IDATs)
  check (validChunkSequence #[ihdr, idat, idat, iend]) "contiguous IDATs rejected"
  -- Invalid: empty
  check (!validChunkSequence #[]) "empty sequence accepted"
  -- Invalid: no IHDR first
  check (!validChunkSequence #[idat, iend]) "no-IHDR sequence accepted"
  -- Invalid: no IEND last
  check (!validChunkSequence #[ihdr, idat]) "no-IEND sequence accepted"

def testIdatContiguity : IO Unit := do
  let ihdr : PngChunk := { chunkType := ChunkType.IHDR, data := ByteArray.mk (Array.replicate 13 0) }
  let idat : PngChunk := { chunkType := ChunkType.IDAT, data := ByteArray.mk #[1] }
  let iend : PngChunk := { chunkType := ChunkType.IEND, data := ByteArray.empty }
  let text : PngChunk := { chunkType := 0x74455874, data := ByteArray.mk #[0] }
  -- Invalid: IDAT, non-IDAT, IDAT (non-contiguous)
  check (!validChunkSequence #[ihdr, idat, text, idat, iend])
    "non-contiguous IDATs accepted"

/-! ## Multi-chunk parse -/

def testParseMultipleChunks : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 1, height := 1, bitDepth := 8
    colorType := .grayscale, compressionMethod := 0
    filterMethod := 0, interlaceMethod := .none
  }
  let ihdrChunk : PngChunk := { chunkType := ChunkType.IHDR, data := ihdr.toBytes }
  let iendChunk : PngChunk := { chunkType := ChunkType.IEND, data := ByteArray.empty }
  let pngData := pngSignature ++ ihdrChunk.serialize ++ iendChunk.serialize
  match parseChunks pngData with
  | .ok chunks =>
    check (chunks.size == 2) s!"expected 2 chunks, got {chunks.size}"
    check (chunks[0]!.isIHDR) "first chunk not IHDR"
    check (chunks[1]!.isIEND) "last chunk not IEND"
  | .error e => throw (.userError s!"parseChunks failed: {e}")

def testParseIHDR : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 320, height := 240, bitDepth := 8
    colorType := .rgb, compressionMethod := 0
    filterMethod := 0, interlaceMethod := .adam7
  }
  let ihdrChunk : PngChunk := { chunkType := ChunkType.IHDR, data := ihdr.toBytes }
  let iendChunk : PngChunk := { chunkType := ChunkType.IEND, data := ByteArray.empty }
  let pngData := pngSignature ++ ihdrChunk.serialize ++ iendChunk.serialize
  match parseIHDR pngData with
  | .ok parsed =>
    check (parsed.width == 320) s!"width {parsed.width} != 320"
    check (parsed.height == 240) s!"height {parsed.height} != 240"
    check (parsed.colorType == .rgb) "colorType not RGB"
    check (parsed.interlaceMethod == .adam7) "interlace not Adam7"
  | .error e => throw (.userError s!"parseIHDR failed: {e}")

/-! ## PLTE tests -/

def testPLTERoundtrip : IO Unit := do
  let plte : PLTEInfo := {
    entries := #[
      { r := 255, g := 0, b := 0 },
      { r := 0, g := 255, b := 0 },
      { r := 0, g := 0, b := 255 }
    ]
  }
  let bytes := plte.toBytes
  check (bytes.size == 9) s!"PLTE toBytes size {bytes.size} != 9"
  match PLTEInfo.fromBytes bytes with
  | .ok parsed =>
    check (parsed.entries.size == 3) s!"parsed {parsed.entries.size} entries, expected 3"
    check (parsed.entries[0]! == { r := 255, g := 0, b := 0 }) "entry 0 mismatch"
    check (parsed.entries[1]! == { r := 0, g := 255, b := 0 }) "entry 1 mismatch"
    check (parsed.entries[2]! == { r := 0, g := 0, b := 255 }) "entry 2 mismatch"
  | .error e => throw (.userError s!"PLTE parse failed: {e}")

def testPLTESingleEntry : IO Unit := do
  let plte : PLTEInfo := { entries := #[{ r := 128, g := 64, b := 32 }] }
  match PLTEInfo.fromBytes plte.toBytes with
  | .ok parsed =>
    check (parsed.entries.size == 1) "single entry PLTE size mismatch"
    check (parsed == plte) "single entry PLTE roundtrip mismatch"
  | .error e => throw (.userError s!"PLTE single entry parse failed: {e}")

def testPLTEMaxEntries : IO Unit := do
  -- 256 entries (maximum allowed)
  let entries := Array.replicate 256 ({ r := 42, g := 84, b := 126 } : PaletteEntry)
  let plte : PLTEInfo := { entries }
  let bytes := plte.toBytes
  check (bytes.size == 768) s!"PLTE 256 entries size {bytes.size} != 768"
  match PLTEInfo.fromBytes bytes with
  | .ok parsed =>
    check (parsed.entries.size == 256) s!"parsed {parsed.entries.size} entries, expected 256"
  | .error e => throw (.userError s!"PLTE 256 entries parse failed: {e}")

def testPLTEEmpty : IO Unit := do
  match PLTEInfo.fromBytes ByteArray.empty with
  | .ok _ => throw (.userError "empty PLTE accepted")
  | .error _ => pure ()

def testPLTEBadLength : IO Unit := do
  -- 4 bytes is not divisible by 3
  match PLTEInfo.fromBytes (ByteArray.mk #[1, 2, 3, 4]) with
  | .ok _ => throw (.userError "PLTE with 4 bytes accepted")
  | .error _ => pure ()

/-! ## tRNS tests -/

def testTRNSGrayscale : IO Unit := do
  let trns := TRNSInfo.grayscale 1000
  let bytes := trns.toBytes
  check (bytes.size == 2) s!"tRNS grayscale size {bytes.size} != 2"
  match TRNSInfo.fromBytes bytes .grayscale with
  | .ok parsed =>
    check (parsed == trns) "tRNS grayscale roundtrip mismatch"
  | .error e => throw (.userError s!"tRNS grayscale parse failed: {e}")

def testTRNSRgb : IO Unit := do
  let trns := TRNSInfo.rgb 100 200 300
  let bytes := trns.toBytes
  check (bytes.size == 6) s!"tRNS RGB size {bytes.size} != 6"
  match TRNSInfo.fromBytes bytes .rgb with
  | .ok parsed =>
    check (parsed == trns) "tRNS RGB roundtrip mismatch"
  | .error e => throw (.userError s!"tRNS RGB parse failed: {e}")

def testTRNSPalette : IO Unit := do
  let alphas := ByteArray.mk #[255, 128, 0, 64]
  let trns := TRNSInfo.palette alphas
  match TRNSInfo.fromBytes alphas .palette with
  | .ok parsed =>
    check (parsed == trns) "tRNS palette roundtrip mismatch"
  | .error e => throw (.userError s!"tRNS palette parse failed: {e}")

def testTRNSRgbaRejected : IO Unit := do
  match TRNSInfo.fromBytes (ByteArray.mk #[0, 0]) .rgba with
  | .ok _ => throw (.userError "tRNS accepted for RGBA")
  | .error _ => pure ()

def testTRNSGrayscaleAlphaRejected : IO Unit := do
  match TRNSInfo.fromBytes (ByteArray.mk #[0, 0]) .grayscaleAlpha with
  | .ok _ => throw (.userError "tRNS accepted for grayscale+alpha")
  | .error _ => pure ()

def testTRNSGrayscaleBadSize : IO Unit := do
  match TRNSInfo.fromBytes (ByteArray.mk #[0, 0, 0]) .grayscale with
  | .ok _ => throw (.userError "tRNS grayscale with 3 bytes accepted")
  | .error _ => pure ()

/-! ## Test runner -/

def runAll : IO Unit := do
  let tests : Array (String × IO Unit) := #[
    ("signature valid",         testSignatureValid),
    ("signature invalid",       testSignatureInvalid),
    ("signature too short",     testSignatureTooShort),
    ("UInt32BE roundtrip",      testUInt32BERoundtrip),
    ("chunk roundtrip",         testChunkRoundtrip),
    ("chunk empty data",        testChunkEmptyData),
    ("chunk CRC mismatch",      testChunkCrcMismatch),
    ("IHDR roundtrip",          testIHDRRoundtrip),
    ("IHDR zero width",         testIHDRZeroWidth),
    ("IHDR bytesPerPixel",      testIHDRBytesPerPixel),
    ("chunk type classification", testChunkTypeClassification),
    ("chunk type toString",     testChunkTypeToString),
    ("valid chunk sequence",    testValidChunkSequence),
    ("IDAT contiguity",         testIdatContiguity),
    ("parse multiple chunks",   testParseMultipleChunks),
    ("parse IHDR",              testParseIHDR),
    ("PLTE roundtrip",          testPLTERoundtrip),
    ("PLTE single entry",       testPLTESingleEntry),
    ("PLTE max entries",        testPLTEMaxEntries),
    ("PLTE empty",              testPLTEEmpty),
    ("PLTE bad length",         testPLTEBadLength),
    ("tRNS grayscale",          testTRNSGrayscale),
    ("tRNS RGB",                testTRNSRgb),
    ("tRNS palette",            testTRNSPalette),
    ("tRNS RGBA rejected",      testTRNSRgbaRejected),
    ("tRNS gray+alpha rejected", testTRNSGrayscaleAlphaRejected),
    ("tRNS grayscale bad size", testTRNSGrayscaleBadSize)
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
  IO.println s!"Chunk tests: {passed} passed, {failed} failed"
  if failed > 0 then
    throw (.userError s!"{failed} chunk test(s) failed")

end PngTest.Chunk
