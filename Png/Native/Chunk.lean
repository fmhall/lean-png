import Png.Types
import Zip.Native.Crc32

/-!
# PNG Chunk Parser and Serializer

Pure Lean implementation of PNG chunk framing: the 8-byte PNG signature,
chunk structure (length + type + data + CRC32), IHDR parsing, and
critical/ancillary classification.

PNG uses network byte order (big-endian) throughout.

## References

- PNG Specification §5 (Datastream structure)
- PNG Specification §11.2.2 (IHDR)
-/

namespace Png

/-! ## Big-endian binary helpers -/

/-- Read a big-endian UInt32 from `data` at `offset`. Returns 0 if out of bounds. -/
def readUInt32BE (data : ByteArray) (offset : Nat) : UInt32 :=
  if h : offset + 4 ≤ data.size then
    let b0 := data[offset]
    let b1 := data[offset + 1]
    let b2 := data[offset + 2]
    let b3 := data[offset + 3]
    (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) |||
    (b2.toUInt32 <<< 8) ||| b3.toUInt32
  else 0

/-- Write a big-endian UInt32 as a 4-byte ByteArray. -/
def writeUInt32BE (val : UInt32) : ByteArray :=
  .mk #[(val >>> 24).toUInt8, (val >>> 16).toUInt8,
         (val >>> 8).toUInt8, val.toUInt8]

/-! ## PNG signature -/

/-- The 8-byte PNG file signature. -/
def pngSignature : ByteArray :=
  .mk #[137, 80, 78, 71, 13, 10, 26, 10]

/-- Validate the PNG signature at the start of a byte array. -/
def validateSignature (data : ByteArray) : Bool :=
  if h : data.size ≥ 8 then
    data[0] == 137 && data[1] == 80 && data[2] == 78 && data[3] == 71 &&
    data[4] == 13 && data[5] == 10 && data[6] == 26 && data[7] == 10
  else false

/-! ## Chunk types -/

/-- A 4-byte PNG chunk type code, stored as a UInt32 for easy comparison. -/
abbrev ChunkType := UInt32

namespace ChunkType

def IHDR : ChunkType := 0x49484452  -- "IHDR"
def PLTE : ChunkType := 0x504C5445  -- "PLTE"
def IDAT : ChunkType := 0x49444154  -- "IDAT"
def IEND : ChunkType := 0x49454E44  -- "IEND"
def tRNS : ChunkType := 0x74524E53  -- "tRNS"

/-- Convert chunk type to its 4-byte representation. -/
def toBytes (ct : ChunkType) : ByteArray := writeUInt32BE ct

/-- Read chunk type from 4 bytes. -/
def fromBytes (data : ByteArray) (offset : Nat) : ChunkType :=
  readUInt32BE data offset

/-- A chunk is critical if the first byte (most significant) is uppercase (bit 5 = 0). -/
def isCritical (ct : ChunkType) : Bool :=
  (ct >>> 24).toUInt8 &&& 0x20 == 0

/-- A chunk is ancillary if the first byte is lowercase (bit 5 = 1). -/
def isAncillary (ct : ChunkType) : Bool :=
  !isCritical ct

/-- Convert chunk type to a 4-character string for display. -/
def toString (ct : ChunkType) : String :=
  let b0 := Char.ofNat ((ct >>> 24).toUInt8.toNat)
  let b1 := Char.ofNat ((ct >>> 16).toUInt8.toNat)
  let b2 := Char.ofNat ((ct >>> 8).toUInt8.toNat)
  let b3 := Char.ofNat (ct.toUInt8.toNat)
  String.ofList [b0, b1, b2, b3]

end ChunkType

/-! ## IHDR serialization (using IHDRInfo from Png.Types) -/

namespace IHDRInfo

/-- Number of channels for the given color type. -/
def channels (ct : ColorType) : Nat :=
  match ct with
  | .grayscale      => 1
  | .rgb            => 3
  | .palette        => 1
  | .grayscaleAlpha => 2
  | .rgba           => 4

/-- Bytes per pixel (rounded up). For palette images this is 1. -/
def bytesPerPixel (ihdr : IHDRInfo) : Nat :=
  let ch := channels ihdr.colorType
  let bits := ch * ihdr.bitDepth.toNat
  (bits + 7) / 8

/-- Expected scanline width in bytes (without the filter type byte). -/
def scanlineBytes (ihdr : IHDRInfo) : Nat :=
  let bitsPerLine := channels ihdr.colorType * ihdr.bitDepth.toNat * ihdr.width.toNat
  (bitsPerLine + 7) / 8

/-- Expected total decompressed IDAT size for non-interlaced images:
    height * (1 + scanlineBytes). -/
def expectedIdatSize (ihdr : IHDRInfo) : Nat :=
  ihdr.height.toNat * (1 + ihdr.scanlineBytes)

/-- Serialize IHDR fields to the 13-byte chunk data. -/
def toBytes (ihdr : IHDRInfo) : ByteArray :=
  writeUInt32BE ihdr.width ++
  writeUInt32BE ihdr.height ++
  .mk #[ihdr.bitDepth, ihdr.colorType.toUInt8, ihdr.compressionMethod,
         ihdr.filterMethod, ihdr.interlaceMethod.toUInt8]

/-- Parse IHDR from 13 bytes of chunk data. -/
def fromBytes (data : ByteArray) : Except String IHDRInfo :=
  if h : data.size = 13 then do
    let width := readUInt32BE data 0
    let height := readUInt32BE data 4
    if width == 0 then throw "IHDR: width is 0"
    if height == 0 then throw "IHDR: height is 0"
    let bitDepth := data[8]
    let colorType ← match ColorType.ofUInt8 data[9] with
      | some ct => pure ct
      | none => throw s!"IHDR: invalid color type {data[9]}"
    let compressionMethod := data[10]
    if compressionMethod != 0 then
      throw s!"IHDR: invalid compression method {compressionMethod}"
    let filterMethod := data[11]
    if filterMethod != 0 then
      throw s!"IHDR: invalid filter method {filterMethod}"
    let interlaceMethod ← match InterlaceMethod.ofUInt8 data[12] with
      | some im => pure im
      | none => throw s!"IHDR: invalid interlace method {data[12]}"
    pure { width, height, bitDepth, colorType, compressionMethod,
           filterMethod, interlaceMethod }
  else
    .error s!"IHDR: expected 13 bytes, got {data.size}"

end IHDRInfo

/-! ## PLTE (palette) parsing and serialization -/

namespace PLTEInfo

/-- Parse PLTE chunk data: must be 3*N bytes where 1 ≤ N ≤ 256. -/
def fromBytes (data : ByteArray) : Except String PLTEInfo := do
  if data.size == 0 then
    throw "PLTE: empty palette"
  if hmod : data.size % 3 != 0 then
    throw s!"PLTE: data length {data.size} not divisible by 3"
  else
  let numEntries := data.size / 3
  if numEntries > 256 then
    throw s!"PLTE: {numEntries} entries exceeds maximum of 256"
  pure { entries := go data numEntries 0 #[] (by omega) }
where
  go (data : ByteArray) (n i : Nat) (acc : Array PaletteEntry)
      (hn : n * 3 ≤ data.size) : Array PaletteEntry :=
    if hi : i < n then
      let off := i * 3
      let entry : PaletteEntry := {
        r := data[off]'(by omega)
        g := data[off + 1]'(by omega)
        b := data[off + 2]'(by omega)
      }
      go data n (i + 1) (acc.push entry) hn
    else acc
  termination_by n - i

/-- Serialize PLTE entries back to chunk data (3 bytes per entry). -/
def toBytes (plte : PLTEInfo) : ByteArray :=
  go plte.entries 0 ByteArray.empty
where
  go (entries : Array PaletteEntry) (i : Nat) (acc : ByteArray) : ByteArray :=
    if h : i < entries.size then
      let e := entries[i]
      go entries (i + 1) (acc.push e.r |>.push e.g |>.push e.b)
    else acc
  termination_by entries.size - i

end PLTEInfo

/-! ## tRNS (transparency) parsing and serialization -/

namespace TRNSInfo

/-- Read a big-endian UInt16 from `data` at `offset`. -/
private def readUInt16BE (data : ByteArray) (offset : Nat) : UInt16 :=
  if h : offset + 2 ≤ data.size then
    let b0 := data[offset]
    let b1 := data[offset + 1]
    (b0.toUInt16 <<< 8) ||| b1.toUInt16
  else 0

/-- Write a big-endian UInt16 as a 2-byte ByteArray. -/
private def writeUInt16BE (val : UInt16) : ByteArray :=
  .mk #[(val >>> 8).toUInt8, val.toUInt8]

/-- Parse tRNS chunk data given the image's color type.
    - Grayscale (type 0): 2 bytes
    - RGB (type 2): 6 bytes
    - Palette (type 3): N bytes (N ≤ palette size, validated by caller) -/
def fromBytes (data : ByteArray) (colorType : ColorType) : Except String TRNSInfo := do
  match colorType with
  | .grayscale =>
    if data.size != 2 then
      throw s!"tRNS: grayscale expects 2 bytes, got {data.size}"
    pure (.grayscale (readUInt16BE data 0))
  | .rgb =>
    if data.size != 6 then
      throw s!"tRNS: RGB expects 6 bytes, got {data.size}"
    pure (.rgb (readUInt16BE data 0) (readUInt16BE data 2) (readUInt16BE data 4))
  | .palette =>
    if data.size == 0 then
      throw "tRNS: empty palette transparency"
    if data.size > 256 then
      throw s!"tRNS: {data.size} alpha entries exceeds maximum of 256"
    pure (.palette data)
  | .grayscaleAlpha =>
    throw "tRNS: not allowed for grayscale+alpha images"
  | .rgba =>
    throw "tRNS: not allowed for RGBA images"

/-- Serialize tRNS data back to chunk bytes. -/
def toBytes : TRNSInfo → ByteArray
  | .grayscale gray => writeUInt16BE gray
  | .rgb r g b => writeUInt16BE r ++ writeUInt16BE g ++ writeUInt16BE b
  | .palette alphas => alphas

end TRNSInfo

/-! ## PNG Chunk -/

/-- A parsed PNG chunk. -/
structure PngChunk where
  chunkType : ChunkType
  data      : ByteArray
  deriving BEq, Inhabited

namespace PngChunk

/-- Is this chunk the IHDR chunk? -/
def isIHDR (c : PngChunk) : Bool := c.chunkType == ChunkType.IHDR

/-- Is this chunk an IDAT chunk? -/
def isIDAT (c : PngChunk) : Bool := c.chunkType == ChunkType.IDAT

/-- Is this chunk the IEND chunk? -/
def isIEND (c : PngChunk) : Bool := c.chunkType == ChunkType.IEND

/-- Is this a critical chunk? -/
def isCritical (c : PngChunk) : Bool := ChunkType.isCritical c.chunkType

/-- Compute the CRC32 over the chunk type + data (the CRC input per PNG spec). -/
def computeCrc (c : PngChunk) : UInt32 :=
  Crc32.Native.crc32 0 (writeUInt32BE c.chunkType ++ c.data)

/-- Serialize a chunk to its on-wire format:
    4-byte length (BE) + 4-byte type + data + 4-byte CRC32. -/
def serialize (c : PngChunk) : ByteArray :=
  let len := writeUInt32BE c.data.size.toUInt32
  let typeBytes := writeUInt32BE c.chunkType
  let typeAndData := typeBytes ++ c.data
  let crc := Crc32.Native.crc32 0 typeAndData
  len ++ typeAndData ++ writeUInt32BE crc

end PngChunk

/-! ## Chunk parsing -/

/-- Result of parsing a single chunk: the chunk and the offset after it. -/
structure ChunkParseResult where
  chunk  : PngChunk
  offset : Nat

/-- Parse a single PNG chunk starting at `offset` in `data`.
    Returns the chunk and the offset of the next chunk. -/
def parseChunk (data : ByteArray) (offset : Nat) : Except String ChunkParseResult := do
  -- Need at least 12 bytes: 4 length + 4 type + 0 data + 4 CRC
  if offset + 12 > data.size then
    throw "chunk: unexpected end of data (need header)"
  let length := readUInt32BE data offset
  let chunkType := readUInt32BE data (offset + 4)
  let dataStart := offset + 8
  let dataEnd := dataStart + length.toNat
  let crcOffset := dataEnd
  if crcOffset + 4 > data.size then
    throw s!"chunk: data extends beyond input (need {dataEnd + 4}, have {data.size})"
  let chunkData := data.extract dataStart dataEnd
  let storedCrc := readUInt32BE data crcOffset
  -- Validate CRC over type + data
  let typeAndData := data.extract (offset + 4) dataEnd
  let computedCrc := Crc32.Native.crc32 0 typeAndData
  if storedCrc != computedCrc then
    throw s!"chunk {ChunkType.toString chunkType}: CRC mismatch (stored={storedCrc}, computed={computedCrc})"
  pure { chunk := { chunkType, data := chunkData }, offset := crcOffset + 4 }

/-- Parse all chunks from a PNG byte stream (after the 8-byte signature). -/
def parseChunks (data : ByteArray) : Except String (Array PngChunk) :=
  if !validateSignature data then
    .error "not a PNG file (invalid signature)"
  else
    go data 8 #[]
where
  go (data : ByteArray) (offset : Nat) (acc : Array PngChunk) : Except String (Array PngChunk) :=
    if offset ≥ data.size then .ok acc
    else
      match parseChunk data offset with
      | .error e => .error e
      | .ok result =>
        let acc' := acc.push result.chunk
        if result.chunk.isIEND then .ok acc'
        else if result.offset ≤ offset then .error "chunk: parser did not advance"
        else go data result.offset acc'
  termination_by data.size - offset

/-- Parse a PNG byte stream and extract the IHDR. -/
def parseIHDR (data : ByteArray) : Except String IHDRInfo := do
  let chunks ← parseChunks data
  match chunks[0]? with
  | some chunk =>
    if !chunk.isIHDR then
      throw "first chunk is not IHDR"
    IHDRInfo.fromBytes chunk.data
  | none => throw "no chunks found"

/-! ## Chunk sequence validity -/

/-- Check IDAT contiguity starting at index `i`.
    `afterIDAT` is true if we have already left an IDAT run (seen IDAT then non-IDAT).
    `inIdat` tracks whether we are currently inside an IDAT run. -/
def idatContiguous (chunks : Array PngChunk) (i : Nat) (inIdat afterIDAT : Bool) : Bool :=
  if h : i < chunks.size then
    let c := chunks[i]
    if c.isIDAT then
      if afterIDAT then false  -- IDAT after gap: not contiguous
      else idatContiguous chunks (i + 1) true afterIDAT
    else
      idatContiguous chunks (i + 1) false (afterIDAT || inIdat)
  else true
termination_by chunks.size - i

/-- A chunk sequence is valid if:
    1. The first chunk is IHDR
    2. The last chunk is IEND
    3. IDAT chunks are contiguous (no non-IDAT between two IDATs) -/
def validChunkSequence (chunks : Array PngChunk) : Bool :=
  if h : chunks.size = 0 then false
  else
    let firstIsIHDR := chunks[0].isIHDR
    let lastIsIEND := chunks[chunks.size - 1].isIEND
    firstIsIHDR && lastIsIEND && idatContiguous chunks 0 false false

end Png
