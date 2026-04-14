import Png.Types

/-!
# PNG FFI Bindings

Lean wrappers around libpng C FFI functions. These provide:
- Decode PNG from file or memory → `PngImage` (RGBA 8-bit)
- Encode `PngImage` → PNG bytes
- Extract IHDR metadata from file or memory

The C functions return packed ByteArrays that are unpacked here
into typed Lean structures. See `c/png_ffi.c` for the wire format.
-/

namespace Png.FFI

-- Raw C FFI declarations. These return packed ByteArrays.
-- Decode: [width:4LE][height:4LE][RGBA pixels...]
-- IHDR:   [width:4LE][height:4LE][bitDepth:1][colorType:1][compression:1][filter:1][interlace:1]

@[extern "lean_png_decode_file"]
private opaque pngDecodeFileFFI (path : @& String) : IO (Except String ByteArray)

@[extern "lean_png_decode_memory"]
private opaque pngDecodeMemoryFFI (data : @& ByteArray) : IO (Except String ByteArray)

@[extern "lean_png_encode_rgba"]
private opaque pngEncodeRGBAFFI (width : UInt32) (height : UInt32)
    (pixels : @& ByteArray) : IO (Except String ByteArray)

@[extern "lean_png_read_ihdr_file"]
private opaque pngReadIHDRFileFFI (path : @& String) : IO (Except String ByteArray)

@[extern "lean_png_read_ihdr_memory"]
private opaque pngReadIHDRMemoryFFI (data : @& ByteArray) : IO (Except String ByteArray)

/-- Read a little-endian UInt32 from a ByteArray at the given offset. -/
private def readLE32 (ba : ByteArray) (off : Nat) : UInt32 :=
  let b0 := ba.get! off |>.toUInt32
  let b1 := ba.get! (off + 1) |>.toUInt32
  let b2 := ba.get! (off + 2) |>.toUInt32
  let b3 := ba.get! (off + 3) |>.toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Unpack a decode result ByteArray into a PngImage. -/
private def unpackDecodeResult (raw : ByteArray) : Except String PngImage := do
  if raw.size < 8 then
    throw "decode result too short"
  let width := readLE32 raw 0
  let height := readLE32 raw 4
  let pixels := raw.extract 8 raw.size
  let expected := PngImage.expectedSize width height
  if pixels.size != expected then
    throw s!"pixel size mismatch: got {pixels.size}, expected {expected}"
  return { width, height, pixels }

/-- Unpack a 13-byte IHDR ByteArray into an IHDRInfo. -/
private def unpackIHDR (raw : ByteArray) : Except String IHDRInfo := do
  if raw.size != 13 then
    throw s!"IHDR size mismatch: got {raw.size}, expected 13"
  let width := readLE32 raw 0
  let height := readLE32 raw 4
  let bitDepth := raw.get! 8
  let colorTypeRaw := raw.get! 9
  let compression := raw.get! 10
  let filter := raw.get! 11
  let interlaceRaw := raw.get! 12
  let colorType ← match ColorType.ofUInt8 colorTypeRaw with
    | some ct => pure ct
    | none => throw s!"unknown color type: {colorTypeRaw}"
  let interlaceMethod ← match InterlaceMethod.ofUInt8 interlaceRaw with
    | some im => pure im
    | none => throw s!"unknown interlace method: {interlaceRaw}"
  return {
    width, height, bitDepth, colorType,
    compressionMethod := compression,
    filterMethod := filter,
    interlaceMethod
  }

/-- Decode a PNG file to RGBA 8-bit pixels. -/
def decodeFile (path : String) : IO (Except String PngImage) := do
  let result ← pngDecodeFileFFI path
  return result.bind unpackDecodeResult

/-- Decode PNG bytes from memory to RGBA 8-bit pixels. -/
def decodeMemory (data : ByteArray) : IO (Except String PngImage) := do
  let result ← pngDecodeMemoryFFI data
  return result.bind unpackDecodeResult

/-- Encode RGBA 8-bit pixels to PNG bytes. -/
def encode (img : PngImage) : IO (Except String ByteArray) :=
  pngEncodeRGBAFFI img.width img.height img.pixels

/-- Read IHDR metadata from a PNG file. -/
def readIHDRFile (path : String) : IO (Except String IHDRInfo) := do
  let result ← pngReadIHDRFileFFI path
  return result.bind unpackIHDR

/-- Read IHDR metadata from PNG bytes in memory. -/
def readIHDRMemory (data : ByteArray) : IO (Except String IHDRInfo) := do
  let result ← pngReadIHDRMemoryFFI data
  return result.bind unpackIHDR

end Png.FFI
