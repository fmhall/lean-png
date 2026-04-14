import Png.Native.Encode
import Png.Native.Decode

/-!
# PNG Encode/Decode Roundtrip Tests

Tests that encoding then decoding recovers the original image,
covering different filter strategies, image sizes, and error cases.
-/

namespace PngTest.Roundtrip

open Png
open Png.Native.Encode
open Png.Native.Decode

/-- Helper: assert condition with message. -/
def check (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure ()
  else throw (.userError s!"FAIL: {msg}")

/-! ## Basic roundtrip tests -/

/-- 1x1 red pixel, filter None. -/
def test1x1Red : IO Unit := do
  let image : PngImage := {
    width := 1, height := 1
    pixels := ByteArray.mk #[255, 0, 0, 255]  -- RGBA red
  }
  let encoded := encodePng image .none
  check (encoded.size > 0) "encoded data is empty"
  match decodePng encoded with
  | .ok decoded =>
    check (decoded == image)
      s!"1x1 roundtrip failed: decoded pixels size={decoded.pixels.size}, expected={image.pixels.size}"
  | .error e => throw (.userError s!"1x1 decode failed: {e}")

/-- 2x2 solid white image, filter None. -/
def test2x2SolidWhite : IO Unit := do
  let pixel := #[255, 255, 255, 255]  -- white RGBA
  let image : PngImage := {
    width := 2, height := 2
    pixels := ByteArray.mk (pixel ++ pixel ++ pixel ++ pixel)
  }
  let encoded := encodePng image .none
  match decodePng encoded with
  | .ok decoded =>
    check (decoded == image) "2x2 white roundtrip failed"
  | .error e => throw (.userError s!"2x2 white decode failed: {e}")

/-- 4x2 gradient image, filter None. -/
def test4x2Gradient : IO Unit := do
  let mut pixels := ByteArray.empty
  for r in [:2] do
    for c in [:4] do
      let v := ((r * 4 + c) * 32).toUInt8
      pixels := pixels ++ ByteArray.mk #[v, v, v, 255]
  let image : PngImage := { width := 4, height := 2, pixels }
  let encoded := encodePng image .none
  match decodePng encoded with
  | .ok decoded =>
    check (decoded == image) "4x2 gradient roundtrip failed"
  | .error e => throw (.userError s!"4x2 gradient decode failed: {e}")

/-- 3x3 solid black, filter None. -/
def test3x3Black : IO Unit := do
  let pixels := ByteArray.mk (Array.replicate (3 * 3 * 4) 0)
  let image : PngImage := { width := 3, height := 3, pixels }
  let encoded := encodePng image .none
  match decodePng encoded with
  | .ok decoded =>
    check (decoded == image) "3x3 black roundtrip failed"
  | .error e => throw (.userError s!"3x3 black decode failed: {e}")

/-! ## Filter strategy tests -/

/-- 4x4 gradient with Sub filter. -/
def testFilterSub : IO Unit := do
  let mut pixels := ByteArray.empty
  for r in [:4] do
    for c in [:4] do
      let v := ((r * 4 + c) * 16).toUInt8
      pixels := pixels ++ ByteArray.mk #[v, 0, 0, 255]
  let image : PngImage := { width := 4, height := 4, pixels }
  let encoded := encodePng image .sub
  match decodePng encoded with
  | .ok decoded =>
    check (decoded == image) "Sub filter roundtrip failed"
  | .error e => throw (.userError s!"Sub filter decode failed: {e}")

/-- 4x4 gradient with Up filter. -/
def testFilterUp : IO Unit := do
  let mut pixels := ByteArray.empty
  for r in [:4] do
    for c in [:4] do
      let v := ((r * 4 + c) * 16).toUInt8
      pixels := pixels ++ ByteArray.mk #[v, v, v, 255]
  let image : PngImage := { width := 4, height := 4, pixels }
  let encoded := encodePng image .up
  match decodePng encoded with
  | .ok decoded =>
    check (decoded == image) "Up filter roundtrip failed"
  | .error e => throw (.userError s!"Up filter decode failed: {e}")

/-- Test with fixed Average filter. -/
def testFilterAverage : IO Unit := do
  let mut pixels := ByteArray.empty
  for r in [:4] do
    for c in [:4] do
      pixels := pixels ++ ByteArray.mk #[((r * 60) % 256).toUInt8,
        ((c * 60) % 256).toUInt8, 128, 255]
  let image : PngImage := { width := 4, height := 4, pixels }
  let encoded := encodePng image (.fixed .average)
  match decodePng encoded with
  | .ok decoded =>
    check (decoded == image) "Average filter roundtrip failed"
  | .error e => throw (.userError s!"Average filter decode failed: {e}")

/-- Test with fixed Paeth filter. -/
def testFilterPaeth : IO Unit := do
  let mut pixels := ByteArray.empty
  for r in [:4] do
    for c in [:4] do
      pixels := pixels ++ ByteArray.mk #[((r * 60 + c * 30) % 256).toUInt8,
        ((r * 30 + c * 60) % 256).toUInt8, 64, 255]
  let image : PngImage := { width := 4, height := 4, pixels }
  let encoded := encodePng image (.fixed .paeth)
  match decodePng encoded with
  | .ok decoded =>
    check (decoded == image) "Paeth filter roundtrip failed"
  | .error e => throw (.userError s!"Paeth filter decode failed: {e}")

/-! ## Larger image test -/

/-- 16x16 image with varied pixel data. -/
def testLarger16x16 : IO Unit := do
  let mut pixels := ByteArray.empty
  for r in [:16] do
    for c in [:16] do
      pixels := pixels ++ ByteArray.mk #[
        ((r * 17) % 256).toUInt8,
        ((c * 17) % 256).toUInt8,
        (((r + c) * 8) % 256).toUInt8,
        255]
  let image : PngImage := { width := 16, height := 16, pixels }
  let encoded := encodePng image .up
  match decodePng encoded with
  | .ok decoded =>
    check (decoded == image) "16x16 roundtrip failed"
  | .error e => throw (.userError s!"16x16 decode failed: {e}")

/-! ## Error case tests -/

/-- Reject data that is not a PNG (bad signature). -/
def testBadSignature : IO Unit := do
  match decodePng (ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]) with
  | .ok _ => throw (.userError "should reject bad signature")
  | .error _ => pure ()

/-- Reject empty data. -/
def testEmptyData : IO Unit := do
  match decodePng ByteArray.empty with
  | .ok _ => throw (.userError "should reject empty data")
  | .error _ => pure ()

/-- Reject truncated PNG (signature only). -/
def testTruncatedPng : IO Unit := do
  -- Valid PNG signature but nothing after
  match decodePng (ByteArray.mk #[137, 80, 78, 71, 13, 10, 26, 10]) with
  | .ok _ => throw (.userError "should reject truncated PNG")
  | .error _ => pure ()

/-! ## Test runner -/

def runAll : IO Unit := do
  let tests : Array (String × IO Unit) := #[
    ("1x1 red",             test1x1Red),
    ("2x2 solid white",     test2x2SolidWhite),
    ("4x2 gradient",        test4x2Gradient),
    ("3x3 black",           test3x3Black),
    ("filter Sub",          testFilterSub),
    ("filter Up",           testFilterUp),
    ("filter Average",      testFilterAverage),
    ("filter Paeth",        testFilterPaeth),
    ("16x16 larger",        testLarger16x16),
    ("bad signature",       testBadSignature),
    ("empty data",          testEmptyData),
    ("truncated PNG",       testTruncatedPng)
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
  IO.println s!"Roundtrip tests: {passed} passed, {failed} failed"
  if failed > 0 then
    throw (.userError s!"{failed} roundtrip test(s) failed")

end PngTest.Roundtrip
