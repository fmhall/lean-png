import Png.Native.Decode
import Png.FFI

/-!
# Native Decode Tests

Tests that the generalized native decoder handles all PNG color types
correctly by comparing against FFI (libpng) decode results.

For each non-interlaced PngSuite image:
- Decode with FFI (reference)
- Decode with native decoder
- Verify pixel buffers match

Also includes synthetic tests that build raw PNG bytes in memory and
decode them natively.
-/

namespace PngTest.NativeDecode

open Png
open Png.Native.Decode

def check (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure ()
  else throw (.userError s!"FAIL: {msg}")

/-! ## PngSuite native vs FFI conformance -/

/-- Test a single PngSuite image: native decode must match FFI decode.
    Interlaced images are skipped (native decoder does not support interlace). -/
private def testNativeVsFFI (path : String) (fname : String) : IO Bool := do
  -- Read raw bytes
  let data ← IO.FS.readBinFile path
  -- Attempt native decode
  match decodePng data with
  | .error nativeErr =>
    -- If FFI also fails, that's fine (corrupt image)
    match ← Png.FFI.decodeMemory data with
    | .error _ =>
      IO.println s!"  SKIP (both fail)     {fname}"
      return true
    | .ok ffiImg =>
      -- Native failed but FFI succeeded: might be interlaced or unsupported
      -- Check if interlaced
      match Png.parseIHDR data with
      | .ok ihdr =>
        if ihdr.interlaceMethod != .none then
          IO.println s!"  SKIP (interlaced)    {fname}"
          return true
        else
          IO.eprintln s!"  FAIL (native error)  {fname}: {nativeErr} (FFI got {ffiImg.width}x{ffiImg.height})"
          return false
      | .error _ =>
          IO.println s!"  SKIP (parse error)   {fname}"
          return true
  | .ok nativeImg =>
    -- Native succeeded, verify against FFI
    match ← Png.FFI.decodeMemory data with
    | .error ffiErr =>
      IO.eprintln s!"  FAIL (FFI error)     {fname}: {ffiErr}"
      return false
    | .ok ffiImg =>
      if nativeImg.width != ffiImg.width || nativeImg.height != ffiImg.height then
        IO.eprintln s!"  FAIL (dim mismatch)  {fname}: native={nativeImg.width}x{nativeImg.height} ffi={ffiImg.width}x{ffiImg.height}"
        return false
      if nativeImg.pixels != ffiImg.pixels then
        IO.eprintln s!"  FAIL (pixel diff)    {fname}: native_size={nativeImg.pixels.size} ffi_size={ffiImg.pixels.size}"
        return false
      IO.println s!"  PASS                 {fname}"
      return true

/-- Run native vs FFI tests over PngSuite non-interlaced basic images. -/
def runPngSuiteNative : IO (Nat × Nat × Nat) := do
  let dir := "testdata/pngsuite"
  let entries ← do
    try
      let items ← System.FilePath.readDir dir
      pure items.toList
    catch _ =>
      IO.eprintln s!"  SKIP: directory {dir} not found"
      return (0, 0, 1)
  -- Filter to valid PngSuite images (skip corrupt 'x' prefix files)
  let pngFiles := entries.filter fun e =>
    e.fileName.endsWith ".png" && !e.fileName.startsWith "x"
  let pngFiles := pngFiles.mergeSort fun a b =>
    a.fileName < b.fileName
  if pngFiles.isEmpty then
    IO.eprintln s!"  SKIP: no .png files in {dir}"
    return (0, 0, 1)
  let mut passed := 0
  let mut failed := 0
  let mut skipped := 0
  for entry in pngFiles do
    let data ← IO.FS.readBinFile entry.path.toString
    match Png.parseIHDR data with
    | .error _ => skipped := skipped + 1
    | .ok _ =>
      let ok ← testNativeVsFFI entry.path.toString entry.fileName
      if ok then passed := passed + 1
      else failed := failed + 1
  return (passed, failed, skipped)

/-! ## Synthetic color type tests -/

/-- Build a minimal valid PNG from raw components.
    This constructs the PNG byte stream directly. -/
private def buildMinimalPng (ihdr : IHDRInfo) (plteData : Option ByteArray := none)
    (trnsData : Option ByteArray := none) (rawPixelData : ByteArray) : ByteArray := Id.run do
  -- Filter all rows with None filter (prepend 0x00 per row)
  let scanlineBytes := ihdr.scanlineBytes
  let numRows := ihdr.height.toNat
  let mut filtered := ByteArray.empty
  for r in [:numRows] do
    filtered := filtered.push 0  -- None filter
    let rowStart := r * scanlineBytes
    let rowEnd := rowStart + scanlineBytes
    filtered := filtered ++ rawPixelData.extract rowStart rowEnd
  -- Compress
  let zlibData := Png.Idat.compressIdat filtered
  -- Build chunks
  let ihdrChunk : PngChunk := { chunkType := ChunkType.IHDR, data := ihdr.toBytes }
  let mut chunks := ByteArray.empty
  chunks := chunks ++ ihdrChunk.serialize
  -- PLTE if provided
  if let some plte := plteData then
    let plteChunk : PngChunk := { chunkType := ChunkType.PLTE, data := plte }
    chunks := chunks ++ plteChunk.serialize
  -- tRNS if provided
  if let some trns := trnsData then
    let trnsChunk : PngChunk := { chunkType := ChunkType.tRNS, data := trns }
    chunks := chunks ++ trnsChunk.serialize
  -- IDAT
  let idatChunk : PngChunk := { chunkType := ChunkType.IDAT, data := zlibData }
  chunks := chunks ++ idatChunk.serialize
  -- IEND
  let iendChunk : PngChunk := { chunkType := ChunkType.IEND, data := ByteArray.empty }
  chunks := chunks ++ iendChunk.serialize
  return Png.pngSignature ++ chunks

/-- Test native decode of a synthetic grayscale 8-bit image. -/
def testGrayscale8 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 2, height := 2, bitDepth := 8, colorType := .grayscale,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- 2x2 grayscale: [0, 128, 255, 64]
  let raw := ByteArray.mk #[0, 128, 255, 64]
  let png := buildMinimalPng ihdr (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"grayscale 8-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 2 && img.height == 2) "dimensions mismatch"
    -- Expected RGBA: (0,0,0,255), (128,128,128,255), (255,255,255,255), (64,64,64,255)
    let expected := ByteArray.mk #[0, 0, 0, 255, 128, 128, 128, 255,
                                    255, 255, 255, 255, 64, 64, 64, 255]
    check (img.pixels == expected) s!"pixel mismatch: got {img.pixels.size} bytes"

/-- Test native decode of a synthetic RGB 8-bit image. -/
def testRgb8 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 2, height := 1, bitDepth := 8, colorType := .rgb,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- 2x1 RGB: red, green
  let raw := ByteArray.mk #[255, 0, 0, 0, 255, 0]
  let png := buildMinimalPng ihdr (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"RGB 8-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 2 && img.height == 1) "dimensions mismatch"
    let expected := ByteArray.mk #[255, 0, 0, 255, 0, 255, 0, 255]
    check (img.pixels == expected) "pixel mismatch"

/-- Test native decode of a synthetic gray+alpha 8-bit image. -/
def testGrayAlpha8 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 2, height := 1, bitDepth := 8, colorType := .grayscaleAlpha,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- 2x1 gray+alpha: (128, 200), (64, 100)
  let raw := ByteArray.mk #[128, 200, 64, 100]
  let png := buildMinimalPng ihdr (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"gray+alpha 8-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 2 && img.height == 1) "dimensions mismatch"
    let expected := ByteArray.mk #[128, 128, 128, 200, 64, 64, 64, 100]
    check (img.pixels == expected) "pixel mismatch"

/-- Test native decode of a synthetic RGBA 8-bit image. -/
def testRgba8 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 1, height := 1, bitDepth := 8, colorType := .rgba,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  let raw := ByteArray.mk #[10, 20, 30, 40]
  let png := buildMinimalPng ihdr (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"RGBA 8-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 1 && img.height == 1) "dimensions mismatch"
    check (img.pixels == raw) "pixel mismatch"

/-- Test native decode of a synthetic palette 8-bit image. -/
def testPalette8 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 3, height := 1, bitDepth := 8, colorType := .palette,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- Palette: [red, green, blue]
  let plteData := ByteArray.mk #[255, 0, 0, 0, 255, 0, 0, 0, 255]
  -- Indices: [0, 1, 2]
  let raw := ByteArray.mk #[0, 1, 2]
  let png := buildMinimalPng ihdr (plteData := some plteData) (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"palette 8-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 3 && img.height == 1) "dimensions mismatch"
    let expected := ByteArray.mk #[255, 0, 0, 255, 0, 255, 0, 255, 0, 0, 255, 255]
    check (img.pixels == expected) "pixel mismatch"

/-- Test native decode of a synthetic palette 8-bit image with tRNS. -/
def testPalette8WithTrns : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 2, height := 1, bitDepth := 8, colorType := .palette,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  let plteData := ByteArray.mk #[255, 0, 0, 0, 255, 0]
  let trnsData := ByteArray.mk #[128, 64]
  let raw := ByteArray.mk #[0, 1]
  let png := buildMinimalPng ihdr (plteData := some plteData) (trnsData := some trnsData) (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"palette+tRNS decode failed: {e}")
  | .ok img =>
    check (img.width == 2 && img.height == 1) "dimensions mismatch"
    let expected := ByteArray.mk #[255, 0, 0, 128, 0, 255, 0, 64]
    check (img.pixels == expected) "pixel mismatch"

/-- Test native decode of a synthetic grayscale 16-bit image. -/
def testGrayscale16 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 1, height := 1, bitDepth := 16, colorType := .grayscale,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- 16-bit gray: high=200, low=50
  let raw := ByteArray.mk #[200, 50]
  let png := buildMinimalPng ihdr (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"grayscale 16-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 1 && img.height == 1) "dimensions mismatch"
    -- Takes high byte
    let expected := ByteArray.mk #[200, 200, 200, 255]
    check (img.pixels == expected) "pixel mismatch"

/-- Test native decode of a synthetic RGB 16-bit image. -/
def testRgb16 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 1, height := 1, bitDepth := 16, colorType := .rgb,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- R=100/0, G=150/0, B=200/0
  let raw := ByteArray.mk #[100, 0, 150, 0, 200, 0]
  let png := buildMinimalPng ihdr (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"RGB 16-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 1 && img.height == 1) "dimensions mismatch"
    let expected := ByteArray.mk #[100, 150, 200, 255]
    check (img.pixels == expected) "pixel mismatch"

/-- Test native decode of a synthetic gray+alpha 16-bit image. -/
def testGrayAlpha16 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 1, height := 1, bitDepth := 16, colorType := .grayscaleAlpha,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- G=180/0, A=90/0
  let raw := ByteArray.mk #[180, 0, 90, 0]
  let png := buildMinimalPng ihdr (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"gray+alpha 16-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 1 && img.height == 1) "dimensions mismatch"
    let expected := ByteArray.mk #[180, 180, 180, 90]
    check (img.pixels == expected) "pixel mismatch"

/-- Test native decode of a synthetic RGBA 16-bit image. -/
def testRgba16 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 1, height := 1, bitDepth := 16, colorType := .rgba,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- R=10/0, G=20/0, B=30/0, A=40/0
  let raw := ByteArray.mk #[10, 0, 20, 0, 30, 0, 40, 0]
  let png := buildMinimalPng ihdr (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"RGBA 16-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 1 && img.height == 1) "dimensions mismatch"
    let expected := ByteArray.mk #[10, 20, 30, 40]
    check (img.pixels == expected) "pixel mismatch"

/-- Test native decode of a synthetic palette 4-bit image. -/
def testPalette4 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 2, height := 1, bitDepth := 4, colorType := .palette,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- Palette: [red, green]
  let plteData := ByteArray.mk #[255, 0, 0, 0, 255, 0]
  -- 4-bit packed: indices 0 and 1 → byte 0x01
  let raw := ByteArray.mk #[0x01]
  let png := buildMinimalPng ihdr (plteData := some plteData) (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"palette 4-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 2 && img.height == 1) "dimensions mismatch"
    let expected := ByteArray.mk #[255, 0, 0, 255, 0, 255, 0, 255]
    check (img.pixels == expected) "pixel mismatch"

/-- Test native decode of a synthetic grayscale 1-bit image. -/
def testGrayscale1 : IO Unit := do
  let ihdr : IHDRInfo := {
    width := 8, height := 1, bitDepth := 1, colorType := .grayscale,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- 1-bit packed: 0b10110100 = 0xB4 → samples: 1,0,1,1,0,1,0,0
  let raw := ByteArray.mk #[0xB4]
  let png := buildMinimalPng ihdr (rawPixelData := raw)
  match decodePng png with
  | .error e => throw (.userError s!"grayscale 1-bit decode failed: {e}")
  | .ok img =>
    check (img.width == 8 && img.height == 1) "dimensions mismatch"
    -- Each 1/0 becomes scaled gray: 1→255, 0→0 (1-bit scale factor = 255)
    let expected := ByteArray.mk #[
      255, 255, 255, 255,  0, 0, 0, 255,  255, 255, 255, 255,  255, 255, 255, 255,
      0, 0, 0, 255,  255, 255, 255, 255,  0, 0, 0, 255,  0, 0, 0, 255]
    check (img.pixels == expected) s!"pixel mismatch: got size {img.pixels.size}"

/-! ## Corrupt PngSuite rejection tests -/

/-- Verify that all 14 corrupt PngSuite files (prefix 'x') are rejected
    by the native decoder. Each must return `.error`, not `.ok`. -/
def runCorruptPngSuite : IO (Nat × Nat) := do
  let dir := "testdata/pngsuite"
  let entries ← do
    try
      let items ← System.FilePath.readDir dir
      pure items.toList
    catch _ =>
      IO.eprintln s!"  SKIP: directory {dir} not found"
      return (0, 0)
  let corruptFiles := entries.filter fun e =>
    e.fileName.startsWith "x" && e.fileName.endsWith ".png"
  let corruptFiles := corruptFiles.mergeSort fun a b =>
    a.fileName < b.fileName
  if corruptFiles.isEmpty then
    IO.eprintln s!"  SKIP: no corrupt .png files in {dir}"
    return (0, 0)
  let mut passed := 0
  let mut failed := 0
  for entry in corruptFiles do
    let data ← IO.FS.readBinFile entry.path
    match Png.Native.Decode.decodePng data with
    | .error _ =>
      IO.println s!"  pass (rejected)      {entry.fileName}"
      passed := passed + 1
    | .ok _ =>
      IO.eprintln s!"  FAIL: {entry.fileName} was accepted (should be rejected)"
      failed := failed + 1
  return (passed, failed)

/-! ## Test runner -/

def runAll : IO Unit := do
  IO.println "--- Synthetic color type tests ---"
  let syntheticTests : Array (String × IO Unit) := #[
    ("grayscale 8-bit",         testGrayscale8),
    ("RGB 8-bit",               testRgb8),
    ("gray+alpha 8-bit",        testGrayAlpha8),
    ("RGBA 8-bit",              testRgba8),
    ("palette 8-bit",           testPalette8),
    ("palette 8-bit + tRNS",    testPalette8WithTrns),
    ("grayscale 16-bit",        testGrayscale16),
    ("RGB 16-bit",              testRgb16),
    ("gray+alpha 16-bit",       testGrayAlpha16),
    ("RGBA 16-bit",             testRgba16),
    ("palette 4-bit",           testPalette4),
    ("grayscale 1-bit",         testGrayscale1)
  ]
  let mut passed := 0
  let mut failed := 0
  for (name, test) in syntheticTests do
    try
      test
      IO.println s!"  pass: {name}"
      passed := passed + 1
    catch e =>
      IO.eprintln s!"  FAIL: {name}: {e}"
      failed := failed + 1
  IO.println s!"Synthetic tests: {passed} passed, {failed} failed"
  if failed > 0 then
    throw (.userError s!"{failed} synthetic test(s) failed")
  IO.println ""
  IO.println "--- PngSuite native vs FFI ---"
  let (suitePass, suiteFail, suiteSkip) ← runPngSuiteNative
  IO.println s!"PngSuite native: {suitePass} passed, {suiteFail} failed, {suiteSkip} skipped"
  if suiteFail > 0 then
    throw (.userError s!"{suiteFail} PngSuite native test(s) failed")
  IO.println ""
  IO.println "--- Corrupt PngSuite rejection ---"
  let (corruptPass, corruptFail) ← runCorruptPngSuite
  IO.println s!"Corrupt PngSuite: {corruptPass} rejected (pass), {corruptFail} accepted (fail)"
  if corruptFail > 0 then
    throw (.userError s!"{corruptFail} corrupt PngSuite file(s) were incorrectly accepted")

end PngTest.NativeDecode
