import Png.Native.Encode
import Png.Native.Decode
import Png.FFI
import PngTest.Helpers

/-!
# PNG Fuzzing Harness

Generates random PNG byte streams and decodes via both native and FFI paths,
comparing results. If FFI succeeds, native must succeed with the same pixels.
-/

namespace PngTest.Fuzz

open Png PngTest
open Png.Native.Encode
open Png.Native.Decode

structure Rng where
  state : UInt64
  deriving Inhabited

def Rng.new (seed : UInt64) : Rng := { state := seed }

def Rng.next (rng : Rng) : Rng × UInt64 :=
  let s := rng.state ^^^ (rng.state <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  ({ state := s }, s)

def Rng.nextUInt32 (rng : Rng) : Rng × UInt32 :=
  let (rng', v) := rng.next
  (rng', v.toUInt32)

def Rng.nextUInt8 (rng : Rng) : Rng × UInt8 :=
  let (rng', v) := rng.next
  (rng', v.toUInt8)

def Rng.nextNat (rng : Rng) (bound : Nat) : Rng × Nat :=
  if bound == 0 then (rng, 0)
  else
    let (rng', v) := rng.next
    (rng', v.toNat % bound)

def Rng.nextBytes (rng : Rng) (n : Nat) : Rng × ByteArray := Id.run do
  let mut r := rng
  let mut ba := ByteArray.mkEmpty n
  for _ in [:n] do
    let (r', b) := r.nextUInt8
    r := r'
    ba := ba.push b
  (r, ba)

def randomFilterStrategy (rng : Rng) : Rng × FilterStrategy :=
  let (rng', idx) := rng.nextNat 5
  let ft := match idx with
    | 0 => FilterType.none
    | 1 => FilterType.sub
    | 2 => FilterType.up
    | 3 => FilterType.average
    | _ => FilterType.paeth
  (rng', .fixed ft)

structure FuzzImage where
  image : PngImage
  strategy : FilterStrategy
  interlaced : Bool

def randomFuzzImage (rng : Rng) : Rng × FuzzImage := Id.run do
  let mut r := rng
  let (r', wRaw) := r.nextNat 64
  r := r'
  let w := (wRaw + 1).toUInt32
  let (r', hRaw) := r.nextNat 64
  r := r'
  let h := (hRaw + 1).toUInt32
  let pixelCount := w.toNat * h.toNat * 4
  let (r', pixels) := r.nextBytes pixelCount
  r := r'
  let (r', strategy) := randomFilterStrategy r
  r := r'
  let (r', intFlag) := r.nextNat 4
  r := r'
  let interlaced := intFlag == 0
  (r, {
    image := { width := w, height := h, pixels }
    strategy
    interlaced
  })

inductive FuzzResult where
  | pass
  | divergence (msg : String)
  | nativeError (msg : String)

def fuzzOne (fi : FuzzImage) : IO FuzzResult := do
  let encoded :=
    if fi.interlaced then encodePngInterlaced fi.image fi.strategy
    else encodePng fi.image fi.strategy
  let nativeResult := decodePng encoded
  let ffiResult ← Png.FFI.decodeMemory encoded
  match ffiResult, nativeResult with
  | .ok ffiImg, .ok nativeImg =>
    if nativeImg.width != ffiImg.width || nativeImg.height != ffiImg.height then
      return .divergence s!"dimension mismatch: native={nativeImg.width}x{nativeImg.height} ffi={ffiImg.width}x{ffiImg.height}"
    if nativeImg.pixels != ffiImg.pixels then
      return .divergence s!"pixel mismatch: native_size={nativeImg.pixels.size} ffi_size={ffiImg.pixels.size}"
    return .pass
  | .ok _, .error nativeErr =>
    return .divergence s!"FFI succeeded but native failed: {nativeErr}"
  | .error _, .ok _ =>
    return .pass
  | .error _, .error _ =>
    return .pass

def fuzzMutated (rng : Rng) (fi : FuzzImage) : IO (Rng × FuzzResult) := do
  let encoded :=
    if fi.interlaced then encodePngInterlaced fi.image fi.strategy
    else encodePng fi.image fi.strategy
  let mut r := rng
  let (r', numMutations) := r.nextNat 5
  r := r'
  let numMutations := numMutations + 1
  let mut mutated := encoded
  for _ in [:numMutations] do
    if mutated.size == 0 then break
    let (r', pos) := r.nextNat mutated.size
    r := r'
    let (r', val) := r.nextUInt8
    r := r'
    mutated := mutated.set! pos val
  let nativeResult := decodePng mutated
  let ffiResult ← Png.FFI.decodeMemory mutated
  match ffiResult, nativeResult with
  | .ok ffiImg, .ok nativeImg =>
    if nativeImg.width != ffiImg.width || nativeImg.height != ffiImg.height then
      return (r, .divergence s!"[mutated] dimension mismatch")
    if nativeImg.pixels != ffiImg.pixels then
      return (r, .divergence s!"[mutated] pixel mismatch")
    return (r, .pass)
  | .ok _, .error nativeErr =>
    return (r, .divergence s!"[mutated] FFI succeeded but native failed: {nativeErr}")
  | .error _, _ =>
    return (r, .pass)

def runFuzzBatch (seed : UInt64) (count : Nat) (verbose : Bool := false) : IO (Nat × Nat) := do
  let mut rng := Rng.new seed
  let mut passed := 0
  let mut failed := 0
  for i in [:count] do
    let (rng', fi) := randomFuzzImage rng
    rng := rng'
    let result ← fuzzOne fi
    match result with
    | .pass =>
      passed := passed + 1
    | .divergence msg =>
      failed := failed + 1
      let dims := s!"{fi.image.width}x{fi.image.height}"
      let intStr := if fi.interlaced then " interlaced" else ""
      IO.eprintln s!"  DIVERGENCE #{i} ({dims}{intStr}): {msg}"
    | .nativeError msg =>
      failed := failed + 1
      IO.eprintln s!"  NATIVE_ERROR #{i}: {msg}"
    let (rng', mutResult) ← fuzzMutated rng fi
    rng := rng'
    match mutResult with
    | .pass =>
      passed := passed + 1
    | .divergence msg =>
      failed := failed + 1
      IO.eprintln s!"  DIVERGENCE #{i} (mutated): {msg}"
    | .nativeError msg =>
      failed := failed + 1
      IO.eprintln s!"  NATIVE_ERROR #{i} (mutated): {msg}"
    if verbose && (i + 1) % 10000 == 0 then
      IO.println s!"  ... {i + 1}/{count} inputs ({passed} passed, {failed} failed)"
  return (passed, failed)

def runAll : IO Unit := do
  IO.println "=== Fuzz: native vs FFI ==="
  let numInputs := 50000
  IO.println s!"  Running {numInputs * 2} fuzz inputs (valid + mutated)..."
  let (passed, failed) ← runFuzzBatch 42 numInputs (verbose := true)
  let total := passed + failed
  IO.println s!"  Fuzz complete: {passed}/{total} passed, {failed} failed"
  if failed > 0 then
    throw (.userError s!"{failed} fuzz input(s) showed native/FFI divergence")

end PngTest.Fuzz
