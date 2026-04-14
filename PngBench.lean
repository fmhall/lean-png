import Png

/-! Benchmark driver for hyperfine.

Usage:
  lake exe bench <operation> <width> <height>

Operations:
  encode         — native PNG encode
  encode-ffi     — libpng FFI encode
  decode         — native PNG decode
  decode-ffi     — libpng FFI decode
  filter         — native scanline filtering only
  unfilter       — native scanline unfiltering only
  roundtrip      — native encode then decode
  roundtrip-ffi  — FFI encode then decode

Images are synthetic RGBA gradients of the given dimensions.

Examples:
  hyperfine 'lake exe bench encode 256 256' 'lake exe bench encode-ffi 256 256'
  hyperfine --parameter-list size 64,256,512,1024 \
            '.lake/build/bin/bench encode {size} {size}' \
            '.lake/build/bin/bench encode-ffi {size} {size}'
-/

open Png

/-- Generate a synthetic RGBA gradient image. -/
def makeGradient (w h : Nat) : PngImage :=
  let size := w * h * 4
  let pixels := ByteArray.mk (Array.ofFn (n := size) fun i =>
    let idx := i.val
    let channel := idx % 4
    match channel with
    | 0 => (idx / 4 % w * 255 / w.max 1).toUInt8
    | 1 => (idx / 4 / w * 255 / h.max 1).toUInt8
    | 2 => 128
    | _ => 255)
  { width := w.toUInt32, height := h.toUInt32, pixels }

def main (args : List String) : IO Unit := do
  match args with
  | [op, wStr, hStr] =>
    let some w := wStr.toNat? | usage
    let some h := hStr.toNat? | usage
    let image := makeGradient w h
    run op image
  | _ => usage
where
  usage := throw (IO.userError
    "usage: bench <encode|encode-ffi|decode|decode-ffi|filter|unfilter|roundtrip|roundtrip-ffi> <width> <height>")
  run (op : String) (image : PngImage) : IO Unit := do
    match op with
    | "encode" =>
      let encoded := Native.Encode.encodePng image
      -- Force evaluation
      if encoded.size == 0 then throw (IO.userError "empty")
    | "encode-ffi" =>
      let result ← FFI.encode image
      match result with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "decode" =>
      let encoded := Native.Encode.encodePng image
      match Native.Decode.decodePng encoded with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "decode-ffi" =>
      let result ← FFI.encode image
      match result with
      | .ok enc =>
        let dec ← FFI.decodeMemory enc
        match dec with
        | .ok _ => pure ()
        | .error e => throw (IO.userError e)
      | .error e => throw (IO.userError e)
    | "filter" =>
      let filtered := Native.Encode.filterScanlines image.pixels image.width image.height .none
      if filtered.size == 0 then throw (IO.userError "empty")
    | "unfilter" =>
      let filtered := Native.Encode.filterScanlines image.pixels image.width image.height .none
      match Native.Decode.unfilterScanlines filtered image.width image.height 4 with
      | .ok _ => pure ()
      | .error e => throw (IO.userError e)
    | "roundtrip" =>
      let encoded := Native.Encode.encodePng image
      match Native.Decode.decodePng encoded with
      | .ok decoded =>
        if decoded.pixels != image.pixels then throw (IO.userError "pixel mismatch")
      | .error e => throw (IO.userError e)
    | "roundtrip-ffi" =>
      let encResult ← FFI.encode image
      match encResult with
      | .ok enc =>
        let decResult ← FFI.decodeMemory enc
        match decResult with
        | .ok decoded =>
          if decoded.pixels != image.pixels then throw (IO.userError "pixel mismatch")
        | .error e => throw (IO.userError e)
      | .error e => throw (IO.userError e)
    | other => throw (IO.userError s!"unknown operation: {other}")
