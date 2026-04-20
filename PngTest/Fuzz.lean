import Png
import PngTest.Helpers

/-!
# Quick Fuzz Test

Runs a small number of fuzz iterations (1000) as part of the test suite
to catch native/FFI divergences. For the full 100K+ run, use `lake exe fuzz`.
-/

open Png PngTest

namespace PngTest.Fuzz

private structure RNG where
  state : UInt64

private def RNG.new (seed : UInt64 := 42) : RNG :=
  { state := if seed == 0 then 1 else seed }

private def RNG.next (rng : RNG) : RNG × UInt64 :=
  let s := rng.state
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  ({ state := s }, s)

private def RNG.nextUInt8 (rng : RNG) : RNG × UInt8 :=
  let (rng, v) := rng.next
  (rng, (v % 256).toUInt8)

private def RNG.nextNat (rng : RNG) (bound : Nat) : RNG × Nat :=
  let (rng, v) := rng.next
  (rng, v.toNat % bound.max 1)

private def RNG.nextBytes (rng : RNG) (n : Nat) : RNG × ByteArray := Id.run do
  let mut rng := rng
  let mut arr := ByteArray.empty
  for _ in [:n] do
    let (r, b) := rng.nextUInt8
    rng := r
    arr := arr.push b
  (rng, arr)

private def pickSize (idx : Nat) : Nat :=
  match idx % 4 with | 0 => 1 | 1 => 2 | 2 => 4 | _ => 8

private def generateValidPng (rng : RNG) : RNG × ByteArray := Id.run do
  let (rng, wIdx) := rng.nextNat 4
  let (rng, hIdx) := rng.nextNat 4
  let w := pickSize wIdx
  let h := pickSize hIdx
  let (rng, pixels) := rng.nextBytes (w * h * 4)
  let (rng, filterIdx) := rng.nextNat 5
  let filterStrat : Native.Encode.FilterStrategy := match filterIdx with
    | 0 => .none | 1 => .sub | 2 => .up
    | 3 => .fixed .average | _ => .fixed .paeth
  let image : PngImage := { width := w.toUInt32, height := h.toUInt32, pixels }
  let (rng, useInterlace) := rng.nextNat 4
  let encoded :=
    if useInterlace == 0 then Native.Encode.encodePngInterlaced image filterStrat
    else Native.Encode.encodePng image filterStrat
  (rng, encoded)

private def mutatePng (rng : RNG) (data : ByteArray) : RNG × ByteArray := Id.run do
  let (rng, n) := rng.nextNat 10
  let mut rng := rng
  let mut result := data
  for _ in [:(n + 1)] do
    if result.size == 0 then break
    let (r, pos) := rng.nextNat result.size
    let (r2, val) := r.nextUInt8
    rng := r2
    result := result.set! pos val
  (rng, result)

def runAll : IO Unit := do
  let iterations := 1000
  IO.println s!"  Running {iterations} fuzz iterations (quick mode)..."
  let mut rng := RNG.new
  let mut bothOk := 0
  let mut bothErr := 0
  let mut nativeOnly := 0
  let mut ffiOnly := 0
  let mut pixelMismatch := 0
  for i in [:iterations] do
    let (r, strategy) := rng.nextNat 10
    rng := r
    let (r, data) :=
      if strategy < 5 then generateValidPng rng
      else if strategy < 8 then
        let (r, valid) := generateValidPng rng
        mutatePng r valid
      else rng.nextBytes (8 + strategy)
    rng := r
    let nativeResult := Native.Decode.decodePng data
    let ffiResult ← FFI.decodeMemory data
    match nativeResult, ffiResult with
    | .ok nImg, .ok fImg =>
      if nImg.pixels == fImg.pixels && nImg.width == fImg.width && nImg.height == fImg.height then
        bothOk := bothOk + 1
      else
        pixelMismatch := pixelMismatch + 1
        throw (.userError s!"[{i}] pixel mismatch: native {nImg.width}x{nImg.height} vs FFI {fImg.width}x{fImg.height}")
    | .error _, .ok _ =>
      ffiOnly := ffiOnly + 1
      throw (.userError s!"[{i}] DIVERGENCE: FFI succeeded but native failed on {data.size}B input")
    | .ok _, .error _ => nativeOnly := nativeOnly + 1
    | .error _, .error _ => bothErr := bothErr + 1
  IO.println s!"  bothOk={bothOk} bothErr={bothErr} nativeOnly={nativeOnly} ffiOnly={ffiOnly} mismatches={pixelMismatch}"
  check (ffiOnly == 0) "FFI-only successes found (native must match FFI)"
  check (pixelMismatch == 0) "pixel mismatches found"
  IO.println s!"  {iterations} fuzz iterations passed"

end PngTest.Fuzz
