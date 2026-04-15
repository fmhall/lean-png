import Png.Native.Interlace
import PngTest.Helpers

/-!
# Adam7 Interlace Tests

Tests for Adam7 pass dimension calculations, coordinate conversion
roundtrips, extract/scatter roundtrips, and edge cases.
-/

namespace PngTest.Interlace

open Png PngTest
open Png.Native.Interlace

/-! ## Pass dimension tests -/

def testPassDimensions_8x8 : IO Unit := do
  -- 8x8 image: every pass has exactly 1 column/row per stride
  let w := 8; let h := 8
  -- Pass 1: rows 0, cols 0 → 1x1
  check (passWidth ⟨0, by omega⟩ w == 1) "8x8 pass1 width"
  check (passHeight ⟨0, by omega⟩ h == 1) "8x8 pass1 height"
  -- Pass 2: rows 0, cols 4 → 1x1
  check (passWidth ⟨1, by omega⟩ w == 1) "8x8 pass2 width"
  check (passHeight ⟨1, by omega⟩ h == 1) "8x8 pass2 height"
  -- Pass 3: rows 4, cols 0,4 → 2x1
  check (passWidth ⟨2, by omega⟩ w == 2) "8x8 pass3 width"
  check (passHeight ⟨2, by omega⟩ h == 1) "8x8 pass3 height"
  -- Pass 4: rows 0,4, cols 2,6 → 2x2
  check (passWidth ⟨3, by omega⟩ w == 2) "8x8 pass4 width"
  check (passHeight ⟨3, by omega⟩ h == 2) "8x8 pass4 height"
  -- Pass 5: rows 2,6, cols 0,2,4,6 → 4x2
  check (passWidth ⟨4, by omega⟩ w == 4) "8x8 pass5 width"
  check (passHeight ⟨4, by omega⟩ h == 2) "8x8 pass5 height"
  -- Pass 6: rows 0,2,4,6, cols 1,3,5,7 → 4x4
  check (passWidth ⟨5, by omega⟩ w == 4) "8x8 pass6 width"
  check (passHeight ⟨5, by omega⟩ h == 4) "8x8 pass6 height"
  -- Pass 7: rows 1,3,5,7, cols 0..7 → 8x4
  check (passWidth ⟨6, by omega⟩ w == 8) "8x8 pass7 width"
  check (passHeight ⟨6, by omega⟩ h == 4) "8x8 pass7 height"

def testPassDimensions_16x16 : IO Unit := do
  let w := 16; let h := 16
  -- Pass 1: 2x2
  check (passWidth ⟨0, by omega⟩ w == 2) "16x16 pass1 width"
  check (passHeight ⟨0, by omega⟩ h == 2) "16x16 pass1 height"
  -- Pass 7: 16x8
  check (passWidth ⟨6, by omega⟩ w == 16) "16x16 pass7 width"
  check (passHeight ⟨6, by omega⟩ h == 8) "16x16 pass7 height"

def testPassDimensions_1x1 : IO Unit := do
  -- 1x1 image: only pass 1 has a pixel
  let w := 1; let h := 1
  check (passWidth ⟨0, by omega⟩ w == 1) "1x1 pass1 width"
  check (passHeight ⟨0, by omega⟩ h == 1) "1x1 pass1 height"
  -- All other passes produce 0 total pixels (width * height = 0)
  -- Some passes may have nonzero height but zero width (or vice versa)
  for pv in [1, 2, 3, 4, 5, 6] do
    if hp : pv < 7 then
      let pw := passWidth ⟨pv, hp⟩ w
      let ph := passHeight ⟨pv, hp⟩ h
      check (pw * ph == 0) s!"1x1 pass{pv + 1} should have 0 pixels, got {pw}x{ph}"

def testPassDimensions_7x7 : IO Unit := do
  let w := 7; let h := 7
  -- Pass 1: ceil((7-0)/8) = 1 for both
  check (passWidth ⟨0, by omega⟩ w == 1) "7x7 pass1 width"
  check (passHeight ⟨0, by omega⟩ h == 1) "7x7 pass1 height"
  -- Pass 7: ceil((7-0)/1) = 7 wide, ceil((7-1)/2) = 3 tall
  check (passWidth ⟨6, by omega⟩ w == 7) "7x7 pass7 width"
  check (passHeight ⟨6, by omega⟩ h == 3) "7x7 pass7 height"

def testPassDimensions_nonSquare : IO Unit := do
  -- 3x12 image
  let w := 3; let h := 12
  check (passWidth ⟨0, by omega⟩ w == 1) "3x12 pass1 width"
  check (passHeight ⟨0, by omega⟩ h == 2) "3x12 pass1 height"
  -- 12x3 image
  let w := 12; let h := 3
  check (passWidth ⟨0, by omega⟩ w == 2) "12x3 pass1 width"
  check (passHeight ⟨0, by omega⟩ h == 1) "12x3 pass1 height"

def testPassDimensions_zero : IO Unit := do
  -- 0-width or 0-height
  check (passWidth ⟨0, by omega⟩ 0 == 0) "0xN pass1 width"
  check (passHeight ⟨0, by omega⟩ 0 == 0) "Nx0 pass1 height"
  check (passWidth ⟨6, by omega⟩ 0 == 0) "0xN pass7 width"
  check (passHeight ⟨6, by omega⟩ 0 == 0) "Nx0 pass7 height"

/-! ## Total pixel count tests -/

def testTotalPixels_8x8 : IO Unit := do
  -- Sum of all pass dimensions should be 64
  let mut total := 0
  for p in List.range 7 do
    if h : p < 7 then
      let pw := passWidth ⟨p, h⟩ 8
      let ph := passHeight ⟨p, h⟩ 8
      total := total + pw * ph
  check (total == 64) s!"8x8 total pixels: {total} != 64"

def testTotalPixels_1x1 : IO Unit := do
  let mut total := 0
  for p in List.range 7 do
    if h : p < 7 then
      total := total + passWidth ⟨p, h⟩ 1 * passHeight ⟨p, h⟩ 1
  check (total == 1) s!"1x1 total pixels: {total} != 1"

def testTotalPixels_16x16 : IO Unit := do
  let mut total := 0
  for p in List.range 7 do
    if h : p < 7 then
      total := total + passWidth ⟨p, h⟩ 16 * passHeight ⟨p, h⟩ 16
  check (total == 256) s!"16x16 total pixels: {total} != 256"

def testTotalPixels_7x7 : IO Unit := do
  let mut total := 0
  for p in List.range 7 do
    if h : p < 7 then
      total := total + passWidth ⟨p, h⟩ 7 * passHeight ⟨p, h⟩ 7
  check (total == 49) s!"7x7 total pixels: {total} != 49"

/-! ## Coordinate roundtrip tests -/

def testCoordRoundtrip : IO Unit := do
  -- For each pass, test fromSub(toSub(x)) = x for coordinates belonging to that pass
  for pv in List.range 7 do
    if h : pv < 7 then
      let p : Fin 7 := ⟨pv, h⟩
      let rs := adam7RowStart p
      let cs := adam7ColStart p
      let rstr := adam7RowStride p
      let cstr := adam7ColStride p
      -- Test a few rows belonging to this pass
      for k in List.range 5 do
        let r := rs + k * rstr
        let c := cs + k * cstr
        let sr := toSubRow p r
        let sc := toSubCol p c
        let r' := fromSubRow p sr
        let c' := fromSubCol p sc
        check (r' == r) s!"pass {pv}: fromSubRow(toSubRow({r})) = {r'} != {r}"
        check (c' == c) s!"pass {pv}: fromSubCol(toSubCol({c})) = {c'} != {c}"

def testCoordFromTo : IO Unit := do
  -- For each pass, test toSub(fromSub(x)) = x
  for pv in List.range 7 do
    if h : pv < 7 then
      let p : Fin 7 := ⟨pv, h⟩
      for sr in List.range 5 do
        let r := fromSubRow p sr
        let c := fromSubCol p sr
        check (toSubRow p r == sr) s!"pass {pv}: toSubRow(fromSubRow({sr})) != {sr}"
        check (toSubCol p c == sr) s!"pass {pv}: toSubCol(fromSubCol({sr})) != {sr}"

/-! ## Extract / scatter roundtrip tests -/

/-- Create a small test PngImage with unique pixel values. -/
def mkTestImage (w h : Nat) : PngImage :=
  let pixels := go w h 0 ByteArray.empty
  { width := w.toUInt32, height := h.toUInt32, pixels := pixels }
where
  go (w h : Nat) (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ w * h then out
    else
      let r := (i % 256).toUInt8
      let g := ((i * 7 + 13) % 256).toUInt8
      let b := ((i * 31 + 5) % 256).toUInt8
      let a := 255
      go w h (i + 1) (out.push r |>.push g |>.push b |>.push a)
  termination_by w * h - i

/-- Compare two PngImages for equality. -/
def imagesEqual (a b : PngImage) : Bool :=
  a.width == b.width && a.height == b.height && a.pixels == b.pixels

def testExtractScatterRoundtrip_4x4 : IO Unit := do
  let img := mkTestImage 4 4
  let subs := adam7Extract img
  check (subs.size == 7) s!"extract produced {subs.size} sub-images, expected 7"
  let restored := adam7Scatter subs 4 4
  check (imagesEqual img restored) "4x4 extract/scatter roundtrip failed"

def testExtractScatterRoundtrip_8x8 : IO Unit := do
  let img := mkTestImage 8 8
  let subs := adam7Extract img
  check (subs.size == 7) s!"extract produced {subs.size} sub-images, expected 7"
  let restored := adam7Scatter subs 8 8
  check (imagesEqual img restored) "8x8 extract/scatter roundtrip failed"

def testExtractScatterRoundtrip_1x1 : IO Unit := do
  let img := mkTestImage 1 1
  let subs := adam7Extract img
  check (subs.size == 7) "1x1 extract size"
  -- Only pass 1 should have pixels (width * height > 0)
  check (subs[0]!.width == 1) "1x1 sub0 width"
  check (subs[0]!.height == 1) "1x1 sub0 height"
  -- Pass 2 has width 0 (col start 4 > width 1), so 0 total pixels
  check (subs[1]!.width.toNat * subs[1]!.height.toNat == 0) "1x1 sub1 should have 0 pixels"
  let restored := adam7Scatter subs 1 1
  check (imagesEqual img restored) "1x1 extract/scatter roundtrip failed"

def testExtractScatterRoundtrip_nonSquare : IO Unit := do
  let img := mkTestImage 5 3
  let subs := adam7Extract img
  let restored := adam7Scatter subs 5 3
  check (imagesEqual img restored) "5x3 extract/scatter roundtrip failed"

def testExtractScatterRoundtrip_16x16 : IO Unit := do
  let img := mkTestImage 16 16
  let subs := adam7Extract img
  let restored := adam7Scatter subs 16 16
  check (imagesEqual img restored) "16x16 extract/scatter roundtrip failed"

/-! ## Empty pass handling -/

def testEmptyPasses : IO Unit := do
  -- 1x1: passes 2-7 should have 0 pixels
  let img := mkTestImage 1 1
  let subs := adam7Extract img
  for pv in [1, 2, 3, 4, 5, 6] do
    let sub := subs[pv]!
    check (sub.pixels.size == 0)
      s!"1x1 pass {pv + 1}: expected 0 bytes, got {sub.pixels.size}"

def testEmptyImage : IO Unit := do
  -- 0x0 image
  let img : PngImage := { width := 0, height := 0, pixels := ByteArray.empty }
  let subs := adam7Extract img
  check (subs.size == 7) "0x0 extract size"
  for pv in List.range 7 do
    let sub := subs[pv]!
    check (sub.pixels.size == 0) s!"0x0 pass {pv + 1} should be empty"

/-! ## Sub-image dimension consistency -/

def testSubImageDimensions : IO Unit := do
  -- Check that extracted sub-image dimensions match passWidth/passHeight
  let img := mkTestImage 8 8
  let subs := adam7Extract img
  for pv in List.range 7 do
    if h : pv < 7 then
      let sub := subs[pv]!
      let expectedW := passWidth ⟨pv, h⟩ 8
      let expectedH := passHeight ⟨pv, h⟩ 8
      check (sub.width.toNat == expectedW)
        s!"pass {pv + 1}: sub width {sub.width.toNat} != expected {expectedW}"
      check (sub.height.toNat == expectedH)
        s!"pass {pv + 1}: sub height {sub.height.toNat} != expected {expectedH}"
      check (sub.pixels.size == expectedW * expectedH * 4)
        s!"pass {pv + 1}: pixel size {sub.pixels.size} != expected {expectedW * expectedH * 4}"

/-! ## Test runner -/

def runAll : IO Unit := do
  let tests : Array (String × IO Unit) := #[
    ("pass dims 8x8",             testPassDimensions_8x8),
    ("pass dims 16x16",           testPassDimensions_16x16),
    ("pass dims 1x1",             testPassDimensions_1x1),
    ("pass dims 7x7",             testPassDimensions_7x7),
    ("pass dims non-square",      testPassDimensions_nonSquare),
    ("pass dims zero",            testPassDimensions_zero),
    ("total pixels 8x8",          testTotalPixels_8x8),
    ("total pixels 1x1",          testTotalPixels_1x1),
    ("total pixels 16x16",        testTotalPixels_16x16),
    ("total pixels 7x7",          testTotalPixels_7x7),
    ("coord roundtrip",           testCoordRoundtrip),
    ("coord from/to",             testCoordFromTo),
    ("extract/scatter 4x4",       testExtractScatterRoundtrip_4x4),
    ("extract/scatter 8x8",       testExtractScatterRoundtrip_8x8),
    ("extract/scatter 1x1",       testExtractScatterRoundtrip_1x1),
    ("extract/scatter non-square", testExtractScatterRoundtrip_nonSquare),
    ("extract/scatter 16x16",     testExtractScatterRoundtrip_16x16),
    ("empty passes",              testEmptyPasses),
    ("empty image",               testEmptyImage),
    ("sub-image dimensions",      testSubImageDimensions)
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
  IO.println s!"Interlace tests: {passed} passed, {failed} failed"
  if failed > 0 then
    throw (.userError s!"{failed} interlace test(s) failed")

end PngTest.Interlace
