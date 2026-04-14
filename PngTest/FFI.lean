import Png.Types
import Png.FFI

/-!
# FFI Tests

Basic tests for the libpng FFI bindings:
- Encode a known pixel buffer, decode it back, check roundtrip
- Extract IHDR from encoded PNG and verify fields
- Decode from memory
- Edge cases: 1x1 image, larger image
-/

open Png Png.FFI

/-- Make a solid-color RGBA pixel buffer. -/
private def solidPixels (w h : Nat) (r g b a : UInt8) : ByteArray := Id.run do
  let mut arr := ByteArray.empty
  for _ in [:w * h] do
    arr := arr.push r
    arr := arr.push g
    arr := arr.push b
    arr := arr.push a
  return arr

/-- Make a gradient RGBA pixel buffer (each pixel has unique values). -/
private def gradientPixels (w h : Nat) : ByteArray := Id.run do
  let mut arr := ByteArray.empty
  for y in [:h] do
    for x in [:w] do
      arr := arr.push (x % 256).toUInt8       -- R
      arr := arr.push (y % 256).toUInt8       -- G
      arr := arr.push ((x + y) % 256).toUInt8 -- B
      arr := arr.push 255                      -- A
  return arr

/-- Assert two ByteArrays are equal, printing first difference on failure. -/
private def assertBytesEq (label : String) (a b : ByteArray) : IO Bool := do
  if a.size != b.size then
    IO.eprintln s!"  FAIL {label}: size mismatch ({a.size} vs {b.size})"
    return false
  for i in [:a.size] do
    if a.get! i != b.get! i then
      IO.eprintln s!"  FAIL {label}: byte {i} differs ({a.get! i} vs {b.get! i})"
      return false
  return true

/-- Test: encode and decode a 1x1 red pixel. -/
def test1x1Roundtrip : IO Bool := do
  IO.println "  test1x1Roundtrip"
  let pixels := solidPixels 1 1 255 0 0 255
  let img : PngImage := { width := 1, height := 1, pixels }
  match ← FFI.encode img with
  | .error e =>
    IO.eprintln s!"  FAIL encode: {e}"
    return false
  | .ok pngBytes =>
    match ← FFI.decodeMemory pngBytes with
    | .error e =>
      IO.eprintln s!"  FAIL decode: {e}"
      return false
    | .ok decoded =>
      if decoded.width != 1 || decoded.height != 1 then
        IO.eprintln s!"  FAIL dimensions: {decoded.width}x{decoded.height}"
        return false
      assertBytesEq "pixels" pixels decoded.pixels

/-- Test: encode and decode a 16x16 gradient image. -/
def test16x16Roundtrip : IO Bool := do
  IO.println "  test16x16Roundtrip"
  let pixels := gradientPixels 16 16
  let img : PngImage := { width := 16, height := 16, pixels }
  match ← FFI.encode img with
  | .error e =>
    IO.eprintln s!"  FAIL encode: {e}"
    return false
  | .ok pngBytes =>
    match ← FFI.decodeMemory pngBytes with
    | .error e =>
      IO.eprintln s!"  FAIL decode: {e}"
      return false
    | .ok decoded =>
      if decoded.width != 16 || decoded.height != 16 then
        IO.eprintln s!"  FAIL dimensions: {decoded.width}x{decoded.height}"
        return false
      assertBytesEq "pixels" pixels decoded.pixels

/-- Test: IHDR extraction from encoded PNG in memory. -/
def testIHDRMemory : IO Bool := do
  IO.println "  testIHDRMemory"
  let pixels := solidPixels 8 4 0 128 255 255
  let img : PngImage := { width := 8, height := 4, pixels }
  match ← FFI.encode img with
  | .error e =>
    IO.eprintln s!"  FAIL encode: {e}"
    return false
  | .ok pngBytes =>
    match ← FFI.readIHDRMemory pngBytes with
    | .error e =>
      IO.eprintln s!"  FAIL readIHDR: {e}"
      return false
    | .ok ihdr =>
      let mut ok := true
      if ihdr.width != 8 then
        IO.eprintln s!"  FAIL width: {ihdr.width}"
        ok := false
      if ihdr.height != 4 then
        IO.eprintln s!"  FAIL height: {ihdr.height}"
        ok := false
      if ihdr.bitDepth != 8 then
        IO.eprintln s!"  FAIL bitDepth: {ihdr.bitDepth}"
        ok := false
      if ihdr.colorType != .rgba then
        IO.eprintln s!"  FAIL colorType: {repr ihdr.colorType}"
        ok := false
      if ihdr.interlaceMethod != .none then
        IO.eprintln s!"  FAIL interlace: {repr ihdr.interlaceMethod}"
        ok := false
      return ok

/-- Test: encode to file, decode from file, verify roundtrip. -/
def testFileRoundtrip : IO Bool := do
  IO.println "  testFileRoundtrip"
  let pixels := gradientPixels 4 4
  let img : PngImage := { width := 4, height := 4, pixels }
  let path := "testdata/ffi_roundtrip.png"
  match ← FFI.encode img with
  | .error e =>
    IO.eprintln s!"  FAIL encode: {e}"
    return false
  | .ok pngBytes =>
    -- Write to file
    IO.FS.writeBinFile path pngBytes
    -- Decode from file
    match ← FFI.decodeFile path with
    | .error e =>
      IO.eprintln s!"  FAIL decodeFile: {e}"
      return false
    | .ok decoded =>
      if decoded.width != 4 || decoded.height != 4 then
        IO.eprintln s!"  FAIL dimensions: {decoded.width}x{decoded.height}"
        return false
      let ok ← assertBytesEq "pixels" pixels decoded.pixels
      -- Also test IHDR from file
      match ← FFI.readIHDRFile path with
      | .error e =>
        IO.eprintln s!"  FAIL readIHDRFile: {e}"
        return false
      | .ok ihdr =>
        if ihdr.width != 4 || ihdr.height != 4 then
          IO.eprintln s!"  FAIL IHDR dimensions: {ihdr.width}x{ihdr.height}"
          return false
        return ok

/-- Test: solid white image (all bytes 255). -/
def testSolidWhite : IO Bool := do
  IO.println "  testSolidWhite"
  let pixels := solidPixels 32 32 255 255 255 255
  let img : PngImage := { width := 32, height := 32, pixels }
  match ← FFI.encode img with
  | .error e =>
    IO.eprintln s!"  FAIL encode: {e}"
    return false
  | .ok pngBytes =>
    match ← FFI.decodeMemory pngBytes with
    | .error e =>
      IO.eprintln s!"  FAIL decode: {e}"
      return false
    | .ok decoded =>
      assertBytesEq "pixels" pixels decoded.pixels

/-- Test: solid black transparent image (all bytes 0). -/
def testSolidBlackTransparent : IO Bool := do
  IO.println "  testSolidBlackTransparent"
  let pixels := solidPixels 2 2 0 0 0 0
  let img : PngImage := { width := 2, height := 2, pixels }
  match ← FFI.encode img with
  | .error e =>
    IO.eprintln s!"  FAIL encode: {e}"
    return false
  | .ok pngBytes =>
    match ← FFI.decodeMemory pngBytes with
    | .error e =>
      IO.eprintln s!"  FAIL decode: {e}"
      return false
    | .ok decoded =>
      assertBytesEq "pixels" pixels decoded.pixels

def runFFITests : IO Bool := do
  IO.println "FFI Tests:"
  let mut allPassed := true
  for test in [test1x1Roundtrip, test16x16Roundtrip, testIHDRMemory,
               testFileRoundtrip, testSolidWhite, testSolidBlackTransparent] do
    let passed ← test
    if passed then
      IO.println "    PASS"
    else
      allPassed := false
  return allPassed
