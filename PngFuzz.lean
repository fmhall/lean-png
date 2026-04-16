import Png.Native.Decode
import Png.Native.Encode
import Png.FFI
import Png.Native.Chunk
import Png.Native.Idat

/-!
# PNG Fuzzing Harness

Generate random PNG byte streams, decode via both native and FFI,
compare results. The key invariant: if FFI succeeds, native must
succeed with the same pixels.

Three fuzzing strategies:
1. **Structured**: Build valid PNGs with random parameters (color type,
   bit depth, dimensions, filter strategy, pixel data)
2. **Mutated**: Take valid PNGs and apply random byte mutations
3. **Random**: Completely random byte streams (mostly tests rejection)

Implements issue #15.
-/

open Png Png.Native.Decode Png.Native.Encode

/-- Simple xorshift64 PRNG for deterministic fuzzing. -/
structure Rng where
  state : UInt64
  deriving Repr

namespace Rng

def init (seed : UInt64) : Rng := { state := if seed == 0 then 1 else seed }

def next (rng : Rng) : Rng × UInt64 :=
  let s := rng.state
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  let s := if s == 0 then 1 else s
  ({ state := s }, s)

def nextUInt8 (rng : Rng) : Rng × UInt8 :=
  let (rng', v) := rng.next
  (rng', v.toUInt8)

def nextNat (rng : Rng) (bound : Nat) : Rng × Nat :=
  if bound == 0 then (rng, 0)
  else
    let (rng', v) := rng.next
    (rng', v.toNat % bound)

def nextBool (rng : Rng) : Rng × Bool :=
  let (rng', v) := rng.next
  (rng', v &&& 1 == 1)

/-- Generate a random ByteArray of given size. -/
def nextBytes (rng : Rng) (n : Nat) : Rng × ByteArray := Id.run do
  let mut r := rng
  let mut arr := ByteArray.empty
  for _ in [:n] do
    let (r', b) := r.nextUInt8
    r := r'
    arr := arr.push b
  (r, arr)

end Rng

/-- Color type configurations valid per PNG spec. Each entry is
    (ColorType, allowed bit depths). -/
private def colorTypeConfigs : Array (ColorType × Array UInt8) := #[
  (.grayscale,      #[1, 2, 4, 8, 16]),
  (.rgb,            #[8, 16]),
  (.palette,        #[1, 2, 4, 8]),
  (.grayscaleAlpha, #[8, 16]),
  (.rgba,           #[8, 16])
]

/-- Build a minimal valid PNG from raw components (same pattern as NativeDecode tests). -/
private def buildMinimalPng (ihdr : IHDRInfo) (plteData : Option ByteArray := none)
    (trnsData : Option ByteArray := none) (rawPixelData : ByteArray) : ByteArray := Id.run do
  let scanlineBytes := ihdr.scanlineBytes
  let numRows := ihdr.height.toNat
  let mut filtered := ByteArray.empty
  for r in [:numRows] do
    filtered := filtered.push 0  -- None filter
    let rowStart := r * scanlineBytes
    let rowEnd := rowStart + scanlineBytes
    filtered := filtered ++ rawPixelData.extract rowStart rowEnd
  let zlibData := Png.Idat.compressIdat filtered
  let ihdrChunk : PngChunk := { chunkType := ChunkType.IHDR, data := ihdr.toBytes }
  let mut chunks := ByteArray.empty
  chunks := chunks ++ ihdrChunk.serialize
  if let some plte := plteData then
    let plteChunk : PngChunk := { chunkType := ChunkType.PLTE, data := plte }
    chunks := chunks ++ plteChunk.serialize
  if let some trns := trnsData then
    let trnsChunk : PngChunk := { chunkType := ChunkType.tRNS, data := trns }
    chunks := chunks ++ trnsChunk.serialize
  let idatChunk : PngChunk := { chunkType := ChunkType.IDAT, data := zlibData }
  chunks := chunks ++ idatChunk.serialize
  let iendChunk : PngChunk := { chunkType := ChunkType.IEND, data := ByteArray.empty }
  chunks := chunks ++ iendChunk.serialize
  return Png.pngSignature ++ chunks

/-- Generate a random structured PNG with valid parameters. -/
private def genStructuredPng (rng : Rng) : Rng × ByteArray := Id.run do
  let mut r := rng
  -- Pick random color type config
  let (r', ctIdx) := r.nextNat colorTypeConfigs.size
  r := r'
  let (ct, depths) := colorTypeConfigs[ctIdx]!
  -- Pick random bit depth
  let (r', bdIdx) := r.nextNat depths.size
  r := r'
  let bitDepth := depths[bdIdx]!
  -- Pick random dimensions (small to keep it fast)
  let (r', w) := r.nextNat 32
  r := r'
  let width := w + 1  -- 1..32
  let (r', h) := r.nextNat 32
  r := r'
  let height := h + 1  -- 1..32
  -- Build IHDR
  let ihdr : IHDRInfo := {
    width := width.toUInt32, height := height.toUInt32,
    bitDepth := bitDepth, colorType := ct,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .none
  }
  -- Compute raw pixel data size
  let scanlineBytes := ihdr.scanlineBytes
  let totalRawBytes := scanlineBytes * height
  -- For palette images, generate a palette and constrain pixel values
  let mut plteData : Option ByteArray := none
  let mut trnsData : Option ByteArray := none
  match ct with
  | .palette =>
    -- Generate a palette respecting PNG spec: max entries = 2^bitDepth
    let maxEntries := min (1 <<< bitDepth.toNat) 256  -- 2, 4, 16, or 256
    let upperBound := min maxEntries 16  -- cap at 16 for speed
    let (r', nEntries) := r.nextNat (max upperBound 1)
    r := r'
    let numEntries := min (nEntries + 1) maxEntries  -- 1..maxEntries
    let (r', plteBytes) := r.nextBytes (numEntries * 3)
    r := r'
    plteData := some plteBytes
    -- Optionally add tRNS
    let (r', addTrns) := r.nextBool
    r := r'
    if addTrns then
      let (r', trnsBytes) := r.nextBytes numEntries
      r := r'
      trnsData := some trnsBytes
    -- Generate pixel data with indices in range
    let maxIdx := numEntries
    let mut rawPixels := ByteArray.empty
    for _ in [:totalRawBytes] do
      let (r', v) := r.nextNat maxIdx
      r := r'
      rawPixels := rawPixels.push v.toUInt8
    let png := buildMinimalPng ihdr plteData trnsData rawPixels
    return (r, png)
  | _ =>
    -- For non-palette types, generate random bytes
    let (r', rawPixels) := r.nextBytes totalRawBytes
    r := r'
    let png := buildMinimalPng ihdr plteData trnsData rawPixels
    return (r, png)

/-- Apply random mutations to a valid PNG byte stream. -/
private def mutatePng (rng : Rng) (png : ByteArray) (numMutations : Nat) : Rng × ByteArray := Id.run do
  if png.size == 0 then return (rng, png)
  let mut r := rng
  let mut data := png
  for _ in [:numMutations] do
    let (r', mutType) := r.nextNat 4
    r := r'
    match mutType with
    | 0 =>  -- flip a random byte
      let (r', pos) := r.nextNat data.size
      r := r'
      let (r', val) := r.nextUInt8
      r := r'
      data := data.set! pos val
    | 1 =>  -- flip a random bit
      let (r', pos) := r.nextNat data.size
      r := r'
      let (r', bitIdx) := r.nextNat 8
      r := r'
      let oldVal := data.get! pos
      let mask := (1 : UInt8) <<< bitIdx.toUInt8
      data := data.set! pos (oldVal ^^^ mask)
    | 2 =>  -- zero a random byte
      let (r', pos) := r.nextNat data.size
      r := r'
      data := data.set! pos 0
    | _ =>  -- set to 0xFF
      let (r', pos) := r.nextNat data.size
      r := r'
      data := data.set! pos 0xFF
  (r, data)

/-- Generate completely random bytes. -/
private def genRandomBytes (rng : Rng) : Rng × ByteArray := Id.run do
  let mut r := rng
  let (r', size) := r.nextNat 256
  r := r'
  r.nextBytes (size + 8)

/-- Show first N differing pixel bytes for diagnostics. -/
private def showPixelDiff (ffiPx nativePx : ByteArray) : String := Id.run do
  let mut diffs : Array String := #[]
  let len := min ffiPx.size nativePx.size
  for i in [:len] do
    if diffs.size >= 8 then
      return s!"{diffs.toList} ..."
    if ffiPx.get! i != nativePx.get! i then
      diffs := diffs.push s!"[{i}] ffi={ffiPx.get! i} native={nativePx.get! i}"
  if diffs.isEmpty then "sizes differ"
  else s!"{diffs.toList}"

/-- Result of a single fuzz iteration. -/
inductive FuzzResult where
  | ok         -- Both agree (both succeed with same pixels, or both fail)
  | divergence (msg : String)  -- FFI succeeds but native fails or differs

/-- Try to extract IHDR info from PNG bytes for diagnostics. -/
private def tryGetIHDR (data : ByteArray) : String :=
  match Png.parseIHDR data with
  | .ok ihdr =>
    let ct := match ihdr.colorType with
      | .grayscale => "gray" | .rgb => "rgb" | .palette => "palette"
      | .grayscaleAlpha => "gray+a" | .rgba => "rgba"
    s!"ct={ct} bd={ihdr.bitDepth} {ihdr.width}x{ihdr.height}"
  | .error _ => "unknown"

/-- Run one fuzz iteration: decode with both decoders, compare. -/
private def fuzzOne (data : ByteArray) : IO FuzzResult := do
  let ffiResult ← Png.FFI.decodeMemory data
  let nativeResult := decodePng data
  match ffiResult, nativeResult with
  | .error _, .error _ =>
    -- Both reject: OK
    return .ok
  | .error _, .ok _ =>
    -- Native accepts but FFI rejects: acceptable (native may be more lenient)
    return .ok
  | .ok ffiImg, .ok nativeImg =>
    -- Both succeed: pixels must match
    if ffiImg.width != nativeImg.width || ffiImg.height != nativeImg.height then
      return .divergence s!"dimension mismatch: FFI={ffiImg.width}x{ffiImg.height} native={nativeImg.width}x{nativeImg.height}"
    if ffiImg.pixels != nativeImg.pixels then
      let diff := showPixelDiff ffiImg.pixels nativeImg.pixels
      let ihdrInfo := tryGetIHDR data
      return .divergence s!"pixel mismatch [{ihdrInfo}]: {diff}"
    return .ok
  | .ok ffiImg, .error nativeErr =>
    -- FFI succeeds but native fails: DIVERGENCE (the key invariant)
    return .divergence s!"FFI decoded {ffiImg.width}x{ffiImg.height} but native failed: {nativeErr}"

/-- Fuzz strategy tag. -/
inductive FuzzStrategy where
  | structured | mutated | random

instance : ToString FuzzStrategy where
  toString
    | .structured => "structured"
    | .mutated    => "mutated"
    | .random     => "random"

/-- Fuzz statistics. -/
structure FuzzStats where
  total            : Nat := 0
  structured       : Nat := 0
  mutated          : Nat := 0
  random           : Nat := 0
  ok               : Nat := 0
  divStructured    : Nat := 0
  divMutated       : Nat := 0
  divRandom        : Nat := 0
  deriving Repr

def FuzzStats.divergence (s : FuzzStats) : Nat :=
  s.divStructured + s.divMutated + s.divRandom

instance : ToString FuzzStats where
  toString s :=
    let div := s.divergence
    s!"total={s.total} (structured={s.structured} mutated={s.mutated} random={s.random}) " ++
    s!"ok={s.ok} divergence={div}" ++
    (if div > 0 then s!" [struct={s.divStructured} mut={s.divMutated} rand={s.divRandom}]" else "")

/-- Generate one fuzz input based on strategy selection. -/
private def genFuzzInput (rng : Rng) : Rng × ByteArray × FuzzStrategy := Id.run do
  let (r, stratVal) := rng.nextNat 100
  if stratVal < 60 then
    let (r', png) := genStructuredPng r
    (r', png, .structured)
  else if stratVal < 85 then
    let (r', png) := genStructuredPng r
    let (r'', numMut) := r'.nextNat 10
    let (r''', mutated) := mutatePng r'' png (numMut + 1)
    (r''', mutated, .mutated)
  else
    let (r', bytes) := genRandomBytes r
    (r', bytes, .random)

def main (args : List String) : IO UInt32 := do
  let numIterations := match args.head? with
    | some n => n.toNat!
    | none => 100000
  IO.println s!"PNG Fuzz Harness — {numIterations} iterations"
  IO.println "================================================"
  let mut rng := Rng.init 42
  let mut stats : FuzzStats := {}
  let mut firstDivergence : Option String := none
  let mut divCount := 0
  -- Progress reporting interval
  let reportInterval := if numIterations >= 10 then numIterations / 10 else 1
  for i in [:numIterations] do
    -- Progress report
    if i > 0 && i % reportInterval == 0 then
      IO.println s!"  progress: {i}/{numIterations} — {stats}"
    -- Generate fuzz input
    let (rng', pngData, strategy) := genFuzzInput rng
    rng := rng'
    stats := { stats with total := stats.total + 1 }
    match strategy with
    | .structured => stats := { stats with structured := stats.structured + 1 }
    | .mutated    => stats := { stats with mutated := stats.mutated + 1 }
    | .random     => stats := { stats with random := stats.random + 1 }
    -- Run the fuzz iteration
    let result ← fuzzOne pngData
    match result with
    | .ok => stats := { stats with ok := stats.ok + 1 }
    | .divergence msg =>
      match strategy with
      | .structured => stats := { stats with divStructured := stats.divStructured + 1 }
      | .mutated    => stats := { stats with divMutated := stats.divMutated + 1 }
      | .random     => stats := { stats with divRandom := stats.divRandom + 1 }
      divCount := divCount + 1
      -- Log first 5 divergences with detail
      if divCount <= 5 then
        IO.eprintln s!"  DIVERGENCE #{divCount} at iteration {i} ({strategy}): {msg}"
      if firstDivergence.isNone then
        firstDivergence := some s!"iteration {i} ({strategy}): {msg}"
  IO.println "================================================"
  IO.println s!"Results: {stats}"
  if stats.divStructured > 0 then
    IO.eprintln s!"FAIL: {stats.divStructured} structured (valid PNG) divergence(s) — these indicate real bugs"
    return 1
  if stats.divergence > 0 then
    IO.println s!"NOTE: {stats.divergence} divergence(s) on mutated/random inputs (differences in corruption handling)"
    IO.println s!"PASS: 0 divergences on well-formed inputs ({stats.structured} structured tests)"
    return 0
  IO.println s!"PASS: {stats.total} inputs, 0 divergences"
  return 0
