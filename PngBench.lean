import Png

/-!
# PNG Benchmark Suite

Compares native Lean PNG decode/encode against libpng FFI on the
PngSuite corpus and synthetic images. Reports throughput in pixels/ms.

Usage:
    lake build bench
    lake exe bench
-/

open Png

/-- Time an IO action, returning (result, elapsed_ms). -/
def timeMs (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let result ← action
  let stop ← IO.monoMsNow
  return (result, stop - start)

/-- Benchmark a single image: encode then decode via both native and FFI. -/
def benchImage (label : String) (image : PngImage) : IO Unit := do
  -- Native encode (force evaluation via size check)
  let (encoded, encMs) ← timeMs (do
    let r := Native.Encode.encodePng image
    let _ := r.size  -- force
    return r)
  -- Native decode (force evaluation via match)
  let (decoded, decMs) ← timeMs (do
    let r := Native.Decode.decodePng encoded
    match r with
    | .ok img => let _ := img.pixels.size; return r
    | .error _ => return r)
  let nativeOk := match decoded with
    | .ok img => img.pixels == image.pixels
    | .error _ => false
  -- FFI encode
  let (ffiEncodedExcept, ffiEncMs) ← timeMs (FFI.encode image)
  -- FFI decode
  let (ffiDecodedExcept, ffiDecMs) ← timeMs (do
    match ffiEncodedExcept with
    | .ok enc => FFI.decodeMemory enc
    | .error e => return .error e)
  let ffiOk := match ffiDecodedExcept with
    | .ok img => img.pixels == image.pixels
    | .error _ => false
  let pixels := image.width.toNat * image.height.toNat
  IO.println s!"  {label}: {pixels} px | native enc {encMs}ms dec {decMs}ms | ffi enc {ffiEncMs}ms dec {ffiDecMs}ms | match: native={nativeOk} ffi={ffiOk}"

/-- Generate a synthetic RGBA image with a gradient pattern. -/
def makeGradient (w h : UInt32) : PngImage :=
  let size := w.toNat * h.toNat * 4
  let pixels := ByteArray.mk (Array.ofFn (n := size) fun i =>
    let idx := i.val
    let channel := idx % 4
    match channel with
    | 0 => (idx / 4 % w.toNat * 255 / (w.toNat.max 1)).toUInt8
    | 1 => (idx / 4 / w.toNat * 255 / (h.toNat.max 1)).toUInt8
    | 2 => 128
    | _ => 255)
  { width := w, height := h, pixels }

/-- Benchmark decoding PngSuite images via FFI. -/
def benchPngSuite : IO Unit := do
  IO.println "PngSuite decode (FFI only — native only supports RGBA 8-bit):"
  let dir := "testdata/pngsuite"
  let entries ← System.FilePath.readDir dir
  let pngs := entries.filter (fun e => e.fileName.endsWith ".png" && !e.fileName.startsWith "x")
  let mut totalMs : Nat := 0
  let mut count : Nat := 0
  for entry in pngs do
    let (resultExcept, ms) ← timeMs (FFI.decodeFile entry.path.toString)
    match resultExcept with
    | .ok _ => totalMs := totalMs + ms; count := count + 1
    | .error _ => pure ()
  IO.println s!"  {count} images decoded in {totalMs}ms total"

def main : IO Unit := do
  IO.println "lean-png benchmark suite"
  IO.println "========================"
  IO.println ""
  IO.println "Synthetic images (native vs FFI):"
  benchImage "1x1" (makeGradient 1 1)
  benchImage "16x16" (makeGradient 16 16)
  benchImage "64x64" (makeGradient 64 64)
  benchImage "256x256" (makeGradient 256 256)
  benchImage "512x512" (makeGradient 512 512)
  benchImage "1024x1024" (makeGradient 1024 1024)
  IO.println ""
  benchPngSuite
  IO.println ""
  IO.println "Done."
