import PngTest.FFI
import PngTest.Chunk
import PngTest.Conformance
import PngTest.Idat
import PngTest.Roundtrip
import PngTest.Interlace
import PngTest.ColorConvert
import PngTest.NativeDecode
import PngTest.Fuzz

/-!
# PNG Test Suite

Test modules for lean-png. Register new test files here.
-/

def main : IO UInt32 := do
  IO.println "lean-png test suite"
  IO.println "==================="
  let mut failures := 0
  if !(← runFFITests) then failures := failures + 1
  IO.println ""
  IO.println "=== Chunk framing ==="
  try
    PngTest.Chunk.runAll
  catch e =>
    IO.eprintln s!"Chunk tests failed: {e}"
    failures := failures + 1
  IO.println ""
  IO.println "=== IDAT pipeline ==="
  try
    PngTest.Idat.runAll
  catch e =>
    IO.eprintln s!"IDAT tests failed: {e}"
    failures := failures + 1
  IO.println ""
  IO.println "=== Roundtrip encode/decode ==="
  try
    PngTest.Roundtrip.runAll
  catch e =>
    IO.eprintln s!"Roundtrip tests failed: {e}"
    failures := failures + 1
  IO.println ""
  IO.println "=== Interlace ==="
  try
    PngTest.Interlace.runAll
  catch e =>
    IO.eprintln s!"Interlace tests failed: {e}"
    failures := failures + 1
  IO.println ""
  IO.println "=== Color Conversion ==="
  try
    PngTest.ColorConvert.runAll
  catch e =>
    IO.eprintln s!"ColorConvert tests failed: {e}"
    failures := failures + 1
  IO.println ""
  IO.println "=== Native Decode (all color types) ==="
  try
    PngTest.NativeDecode.runAll
  catch e =>
    IO.eprintln s!"NativeDecode tests failed: {e}"
    failures := failures + 1
  IO.println ""
  if !(← PngTest.Conformance.runAll) then failures := failures + 1
  IO.println ""
  IO.println "=== Fuzz (quick) ==="
  try
    PngTest.Fuzz.runAll
  catch e =>
    IO.eprintln s!"Fuzz tests failed: {e}"
    failures := failures + 1
  IO.println "==================="
  if failures > 0 then
    IO.println s!"FAILED: {failures} test group(s)"
    return 1
  else
    IO.println "All tests passed."
    return 0
