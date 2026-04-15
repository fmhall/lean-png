import Png.Native.ColorConvert
import PngTest.Helpers

/-!
# Color Conversion Tests

Tests for all PNG pixel format converters: sub-byte unpacking,
grayscale, RGB, gray+alpha, 16-bit variants, and palette expansion.
-/

namespace PngTest.ColorConvert

open Png PngTest
open Png.Native.ColorConvert

/-! ## grayscaleToRGBA -/

def testGrayscaleToRGBA_single : IO Unit := do
  let data := ByteArray.mk #[128]
  let result := grayscaleToRGBA data
  check (result.size == 4) s!"size {result.size} != 4"
  check (result == ByteArray.mk #[128, 128, 128, 255]) "pixel mismatch"

def testGrayscaleToRGBA_black_white : IO Unit := do
  let data := ByteArray.mk #[0, 255]
  let result := grayscaleToRGBA data
  check (result.size == 8) s!"size {result.size} != 8"
  check (result == ByteArray.mk #[0, 0, 0, 255, 255, 255, 255, 255]) "black/white mismatch"

def testGrayscaleToRGBA_empty : IO Unit := do
  let result := grayscaleToRGBA ByteArray.empty
  check (result.size == 0) "non-empty result from empty input"

/-! ## rgbToRGBA -/

def testRgbToRGBA_single : IO Unit := do
  let data := ByteArray.mk #[255, 0, 0]
  let result := rgbToRGBA data
  check (result.size == 4) s!"size {result.size} != 4"
  check (result == ByteArray.mk #[255, 0, 0, 255]) "red pixel mismatch"

def testRgbToRGBA_two_pixels : IO Unit := do
  let data := ByteArray.mk #[255, 0, 0, 0, 255, 0]
  let result := rgbToRGBA data
  check (result.size == 8) s!"size {result.size} != 8"
  check (result == ByteArray.mk #[255, 0, 0, 255, 0, 255, 0, 255]) "two-pixel mismatch"

def testRgbToRGBA_empty : IO Unit := do
  let result := rgbToRGBA ByteArray.empty
  check (result.size == 0) "non-empty result from empty input"

/-! ## grayAlphaToRGBA -/

def testGrayAlphaToRGBA_single : IO Unit := do
  let data := ByteArray.mk #[200, 128]
  let result := grayAlphaToRGBA data
  check (result.size == 4) s!"size {result.size} != 4"
  check (result == ByteArray.mk #[200, 200, 200, 128]) "gray+alpha mismatch"

def testGrayAlphaToRGBA_two : IO Unit := do
  let data := ByteArray.mk #[0, 255, 255, 0]
  let result := grayAlphaToRGBA data
  check (result.size == 8) s!"size {result.size} != 8"
  check (result == ByteArray.mk #[0, 0, 0, 255, 255, 255, 255, 0]) "two-pixel gray+alpha mismatch"

def testGrayAlphaToRGBA_empty : IO Unit := do
  let result := grayAlphaToRGBA ByteArray.empty
  check (result.size == 0) "non-empty result from empty input"

/-! ## 16-bit converters -/

def testGrayscale16ToRGBA : IO Unit := do
  -- 16-bit gray: high=128, low=64 → takes high byte
  let data := ByteArray.mk #[128, 64]
  let result := grayscale16ToRGBA data
  check (result.size == 4) s!"size {result.size} != 4"
  check (result == ByteArray.mk #[128, 128, 128, 255]) "16-bit gray mismatch"

def testRgb16ToRGBA : IO Unit := do
  -- R=200/0, G=100/0, B=50/0
  let data := ByteArray.mk #[200, 0, 100, 0, 50, 0]
  let result := rgb16ToRGBA data
  check (result.size == 4) s!"size {result.size} != 4"
  check (result == ByteArray.mk #[200, 100, 50, 255]) "16-bit RGB mismatch"

def testGrayAlpha16ToRGBA : IO Unit := do
  -- G=180/0, A=64/0
  let data := ByteArray.mk #[180, 0, 64, 0]
  let result := grayAlpha16ToRGBA data
  check (result.size == 4) s!"size {result.size} != 4"
  check (result == ByteArray.mk #[180, 180, 180, 64]) "16-bit gray+alpha mismatch"

def testRgba16ToRGBA : IO Unit := do
  -- R=10/0, G=20/0, B=30/0, A=40/0
  let data := ByteArray.mk #[10, 0, 20, 0, 30, 0, 40, 0]
  let result := rgba16ToRGBA data
  check (result.size == 4) s!"size {result.size} != 4"
  check (result == ByteArray.mk #[10, 20, 30, 40]) "16-bit RGBA mismatch"

/-! ## expandPalette -/

def testExpandPalette_basic : IO Unit := do
  let plte : PLTEInfo := { entries := #[
    { r := 255, g := 0, b := 0 },     -- 0: red
    { r := 0, g := 255, b := 0 },     -- 1: green
    { r := 0, g := 0, b := 255 }      -- 2: blue
  ]}
  let indices := ByteArray.mk #[0, 1, 2]
  let result := expandPalette indices plte
  check (result.size == 12) s!"size {result.size} != 12"
  check (result == ByteArray.mk #[255, 0, 0, 255, 0, 255, 0, 255, 0, 0, 255, 255])
    "palette expansion mismatch"

def testExpandPalette_with_trns : IO Unit := do
  let plte : PLTEInfo := { entries := #[
    { r := 255, g := 0, b := 0 },
    { r := 0, g := 255, b := 0 }
  ]}
  let trns := TRNSInfo.palette (ByteArray.mk #[128, 64])
  let indices := ByteArray.mk #[0, 1]
  let result := expandPalette indices plte (some trns)
  check (result.size == 8) s!"size {result.size} != 8"
  -- Index 0: alpha=128, Index 1: alpha=64
  check (result == ByteArray.mk #[255, 0, 0, 128, 0, 255, 0, 64])
    "palette+tRNS mismatch"

def testExpandPalette_partial_trns : IO Unit := do
  -- tRNS shorter than palette — remaining entries get alpha=255
  let plte : PLTEInfo := { entries := #[
    { r := 10, g := 20, b := 30 },
    { r := 40, g := 50, b := 60 }
  ]}
  let trns := TRNSInfo.palette (ByteArray.mk #[100])  -- only 1 alpha
  let indices := ByteArray.mk #[0, 1]
  let result := expandPalette indices plte (some trns)
  check (result == ByteArray.mk #[10, 20, 30, 100, 40, 50, 60, 255])
    "partial tRNS mismatch"

def testExpandPalette_empty : IO Unit := do
  let plte : PLTEInfo := { entries := #[{ r := 0, g := 0, b := 0 }] }
  let result := expandPalette ByteArray.empty plte
  check (result.size == 0) "non-empty from empty indices"

/-! ## unpackSubByte -/

def testUnpack1bit : IO Unit := do
  -- 1 bit/sample, 8 samples wide, 1 row
  -- byte 0b10110100 = 0xB4 = samples: 1,0,1,1,0,1,0,0
  let data := ByteArray.mk #[0xB4]
  let result := unpackSubByte data 8 1 1 (Or.inl rfl)
  check (result.size == 8) s!"1-bit size {result.size} != 8"
  check (result == ByteArray.mk #[1, 0, 1, 1, 0, 1, 0, 0]) "1-bit unpack mismatch"

def testUnpack2bit : IO Unit := do
  -- 2 bits/sample, 4 samples wide, 1 row
  -- byte 0b11_10_01_00 = 0xE4 = samples: 3,2,1,0
  let data := ByteArray.mk #[0xE4]
  let result := unpackSubByte data 4 1 2 (Or.inr (Or.inl rfl))
  check (result.size == 4) s!"2-bit size {result.size} != 4"
  check (result == ByteArray.mk #[3, 2, 1, 0]) "2-bit unpack mismatch"

def testUnpack4bit : IO Unit := do
  -- 4 bits/sample, 2 samples wide, 1 row
  -- byte 0xAB = samples: 0xA=10, 0xB=11
  let data := ByteArray.mk #[0xAB]
  let result := unpackSubByte data 2 1 4 (Or.inr (Or.inr rfl))
  check (result.size == 2) s!"4-bit size {result.size} != 2"
  check (result == ByteArray.mk #[10, 11]) "4-bit unpack mismatch"

def testUnpack1bit_multirow : IO Unit := do
  -- 1-bit, 4 samples wide, 2 rows
  -- Row 0: 0b1010_0000 = 0xA0 → 1,0,1,0
  -- Row 1: 0b0101_0000 = 0x50 → 0,1,0,1
  let data := ByteArray.mk #[0xA0, 0x50]
  let result := unpackSubByte data 4 2 1 (Or.inl rfl)
  check (result.size == 8) s!"1-bit multirow size {result.size} != 8"
  check (result == ByteArray.mk #[1, 0, 1, 0, 0, 1, 0, 1]) "1-bit multirow mismatch"

/-! ## Test runner -/

def runAll : IO Unit := do
  let tests : Array (String × IO Unit) := #[
    ("grayscale single",           testGrayscaleToRGBA_single),
    ("grayscale black/white",      testGrayscaleToRGBA_black_white),
    ("grayscale empty",            testGrayscaleToRGBA_empty),
    ("RGB single",                 testRgbToRGBA_single),
    ("RGB two pixels",             testRgbToRGBA_two_pixels),
    ("RGB empty",                  testRgbToRGBA_empty),
    ("gray+alpha single",          testGrayAlphaToRGBA_single),
    ("gray+alpha two",             testGrayAlphaToRGBA_two),
    ("gray+alpha empty",           testGrayAlphaToRGBA_empty),
    ("16-bit grayscale",           testGrayscale16ToRGBA),
    ("16-bit RGB",                 testRgb16ToRGBA),
    ("16-bit gray+alpha",          testGrayAlpha16ToRGBA),
    ("16-bit RGBA",                testRgba16ToRGBA),
    ("palette basic",              testExpandPalette_basic),
    ("palette with tRNS",          testExpandPalette_with_trns),
    ("palette partial tRNS",       testExpandPalette_partial_trns),
    ("palette empty",              testExpandPalette_empty),
    ("unpack 1-bit",               testUnpack1bit),
    ("unpack 2-bit",               testUnpack2bit),
    ("unpack 4-bit",               testUnpack4bit),
    ("unpack 1-bit multirow",      testUnpack1bit_multirow)
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
  IO.println s!"ColorConvert tests: {passed} passed, {failed} failed"
  if failed > 0 then
    throw (.userError s!"{failed} ColorConvert test(s) failed")

end PngTest.ColorConvert
