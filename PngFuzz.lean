import Png

/-!
# PNG Fuzzing Harness

Generates random PNG byte streams and decodes via both native and FFI,
comparing results. Key invariants:

* On well-formed inputs (generated via roundtrip), if FFI succeeds then
  native must also succeed with the same pixels.
* On any input where both succeed, the decoded pixels must match.

FFI-only successes on mutated or random inputs are allowed: libpng
deliberately ignores IEND/PLTE CRC errors (see `png_crc_finish` in
libpng's `pngrutil.c`), while the native decoder enforces every chunk
CRC. Being stricter than libpng on corrupted input is a feature.

Usage:
  lake exe fuzz [count]        — run `count` fuzz iterations (default: 100000)
  lake exe fuzz [count] [seed] — use a specific PRNG seed
-/

open Png

namespace PngFuzz

structure RNG where
  state : UInt64
  deriving Repr

def RNG.new (seed : UInt64 := 0xDEADBEEFCAFE1234) : RNG :=
  { state := if seed == 0 then 1 else seed }

def RNG.next (rng : RNG) : RNG × UInt64 :=
  let s := rng.state
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  ({ state := s }, s)

def RNG.nextUInt8 (rng : RNG) : RNG × UInt8 :=
  let (rng, v) := rng.next
  (rng, (v % 256).toUInt8)

def RNG.nextNat (rng : RNG) (bound : Nat) : RNG × Nat :=
  let (rng, v) := rng.next
  (rng, v.toNat % bound.max 1)

def RNG.nextBytes (rng : RNG) (n : Nat) : RNG × ByteArray := Id.run do
  let mut rng := rng
  let mut arr := ByteArray.empty
  for _ in [:n] do
    let (r, b) := rng.nextUInt8
    rng := r
    arr := arr.push b
  (rng, arr)

private def pickSize (idx : Nat) : Nat :=
  match idx % 4 with | 0 => 1 | 1 => 2 | 2 => 4 | _ => 8

structure FuzzStats where
  total           : Nat := 0
  bothOk          : Nat := 0
  bothErr         : Nat := 0
  nativeOnlyOk    : Nat := 0
  ffiOnlyOk       : Nat := 0
  pixelMismatch   : Nat := 0
  deriving Repr

instance : ToString FuzzStats where
  toString s :=
    s!"total={s.total} bothOk={s.bothOk} bothErr={s.bothErr} " ++
    s!"nativeOnlyOk={s.nativeOnlyOk} ffiOnlyOk={s.ffiOnlyOk} " ++
    s!"pixelMismatch={s.pixelMismatch}"

inductive FuzzStrategy where
  | validRoundtrip
  | mutatedPng
  | randomBytes
  deriving Repr

def selectStrategy (rng : RNG) : RNG × FuzzStrategy :=
  let (rng, v) := rng.nextNat 10
  if v < 5 then (rng, .validRoundtrip)
  else if v < 8 then (rng, .mutatedPng)
  else (rng, .randomBytes)

def randomPixels (rng : RNG) (w h : Nat) : RNG × ByteArray :=
  rng.nextBytes (w * h * 4)

def selectFilterStrategy (rng : RNG) : RNG × Native.Encode.FilterStrategy :=
  let (rng, v) := rng.nextNat 5
  match v with
  | 0 => (rng, .none)
  | 1 => (rng, .sub)
  | 2 => (rng, .up)
  | 3 => (rng, .fixed .average)
  | _ => (rng, .fixed .paeth)

def generateValidPng (rng : RNG) : RNG × ByteArray := Id.run do
  let (rng, wIdx) := rng.nextNat 4
  let (rng, hIdx) := rng.nextNat 4
  let w := pickSize wIdx
  let h := pickSize hIdx
  let (rng, pixels) := randomPixels rng w h
  let (rng, filterStrat) := selectFilterStrategy rng
  let (rng, useInterlace) := rng.nextNat 4
  let image : PngImage := { width := w.toUInt32, height := h.toUInt32, pixels }
  let encoded :=
    if useInterlace == 0 then
      Native.Encode.encodePngInterlaced image filterStrat
    else
      Native.Encode.encodePng image filterStrat
  (rng, encoded)

def mutatePng (rng : RNG) (data : ByteArray) : RNG × ByteArray := Id.run do
  let (rng, numMutations) := rng.nextNat 10
  let numMutations := numMutations + 1
  let mut rng := rng
  let mut result := data
  for _ in [:numMutations] do
    if result.size == 0 then break
    let (r, pos) := rng.nextNat result.size
    rng := r
    let (r, val) := rng.nextUInt8
    rng := r
    result := result.set! pos val
  (rng, result)

def generateMutatedPng (rng : RNG) : RNG × ByteArray :=
  let (rng, validPng) := generateValidPng rng
  mutatePng rng validPng

def generateRandomBytes (rng : RNG) : RNG × ByteArray :=
  let (rng, len) := rng.nextNat 256
  rng.nextBytes (len + 8)

def compareDecoders (data : ByteArray) : IO (Bool × Bool × Bool × Option String) := do
  let nativeResult := Native.Decode.decodePng data
  let ffiResult ← FFI.decodeMemory data
  match nativeResult, ffiResult with
  | .ok nImg, .ok fImg =>
    if nImg.pixels == fImg.pixels && nImg.width == fImg.width && nImg.height == fImg.height then
      return (true, true, true, none)
    else
      return (true, true, false, some s!"pixel mismatch: native {nImg.width}x{nImg.height} ({nImg.pixels.size}B) vs FFI {fImg.width}x{fImg.height} ({fImg.pixels.size}B)")
  | .ok _, .error _ =>
    return (true, false, false, none)
  | .error _, .ok _ =>
    return (false, true, false, none)
  | .error _, .error _ =>
    return (false, false, false, none)

def runOne (rng : RNG) (stats : FuzzStats) : IO (RNG × FuzzStats × Option String) := do
  let (rng, strategy) := selectStrategy rng
  let (rng, data) := match strategy with
    | .validRoundtrip => generateValidPng rng
    | .mutatedPng     => generateMutatedPng rng
    | .randomBytes    => generateRandomBytes rng
  let (nativeOk, ffiOk, pixelsMatch, errMsg) ← compareDecoders data
  let stats := { stats with total := stats.total + 1 }
  match nativeOk, ffiOk with
  | true, true =>
    if pixelsMatch then
      return (rng, { stats with bothOk := stats.bothOk + 1 }, none)
    else
      return (rng, { stats with pixelMismatch := stats.pixelMismatch + 1 }, errMsg)
  | false, false =>
    return (rng, { stats with bothErr := stats.bothErr + 1 }, none)
  | true, false =>
    return (rng, { stats with nativeOnlyOk := stats.nativeOnlyOk + 1 }, none)
  | false, true =>
    -- Native is stricter than libpng on some malformed inputs (e.g. libpng
    -- deliberately ignores IEND/PLTE CRC errors per pngrutil.c; native
    -- enforces them). Only treat FFI-only success as a divergence on
    -- well-formed inputs where native is required to match.
    let msg := match strategy with
      | .validRoundtrip =>
        some s!"DIVERGENCE on valid input: FFI succeeded but native failed on {data.size}B input"
      | _ => none
    return (rng, { stats with ffiOnlyOk := stats.ffiOnlyOk + 1 }, msg)

def runFuzz (count : Nat) (seed : UInt64) : IO Bool := do
  IO.println s!"PNG Fuzz: {count} iterations, seed={seed}"
  IO.println "Strategy mix: 50% valid roundtrip, 30% mutated PNG, 20% random bytes"
  IO.println "Invariant: on valid inputs, FFI success ⇒ native success with same pixels"
  IO.println "---"
  let mut rng := RNG.new seed
  let mut stats : FuzzStats := {}
  let mut divergences : Nat := 0
  let progressInterval := count / 10 |>.max 1
  for i in [:count] do
    let (r, s, err) ← runOne rng stats
    rng := r
    stats := s
    if let some msg := err then
      IO.eprintln s!"  [{i}] {msg}"
      divergences := divergences + 1
    if (i + 1) % progressInterval == 0 then
      IO.println s!"  progress: {i + 1}/{count} — {stats}"
  IO.println "---"
  IO.println s!"Final: {stats}"
  if divergences > 0 then
    IO.eprintln s!"FAILED: {divergences} divergence(s) found"
    return false
  else
    IO.println "PASSED: no divergences"
    return true

end PngFuzz

def main (args : List String) : IO UInt32 := do
  let count := match args with
    | s :: _ => s.toNat?.getD 100000
    | [] => 100000
  let seed := match args with
    | _ :: s :: _ => s.toNat?.getD 0xDEADBEEFCAFE1234 |>.toUInt64
    | _ => (0xDEADBEEFCAFE1234 : UInt64)
  let ok ← PngFuzz.runFuzz count seed
  return if ok then 0 else 1
