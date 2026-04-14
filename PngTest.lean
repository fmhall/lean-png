import PngTest.FFI
import PngTest.Chunk
import PngTest.Conformance
import PngTest.Idat
import PngTest.Roundtrip
import PngTest.Interlace

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
  if !(← PngTest.Conformance.runAll) then failures := failures + 1
  IO.println "==================="
  if failures > 0 then
    IO.println s!"FAILED: {failures} test group(s)"
    return 1
  else
    IO.println "All tests passed."
    return 0
