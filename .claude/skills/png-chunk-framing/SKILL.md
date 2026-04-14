---
name: png-chunk-framing
description: Use when implementing or proving properties about PNG chunk parsing, serialization, CRC32 validation, chunk sequence ordering, or IHDR/IEND structure.
allowed-tools: Read, Bash, Grep
---

# PNG Chunk Framing Patterns

## PNG File Structure

```
PNG signature (8 bytes): 137 80 78 71 13 10 26 10
Chunk 1 (IHDR — must be first)
Chunk 2..N-1 (IDAT, ancillary chunks)
Chunk N (IEND — must be last)
```

## Chunk Structure

Each chunk is:
```
Length:  4 bytes (big-endian, unsigned)
Type:   4 bytes (ASCII)
Data:   `Length` bytes
CRC:    4 bytes (CRC32 of Type + Data)
```

Total chunk size = 12 + Length.

## CRC32 Integration with lean-zip

PNG CRC32 covers the chunk type AND data (NOT the length field):
```lean
import Zip.Native.Crc32

def chunkCrc (chunkType : ByteArray) (data : ByteArray) : UInt32 :=
  Zip.Native.Crc32.crc32 (chunkType ++ data)
```

Use `Zip.Spec.Crc32.updateList_append` for the compositionality proof:
```lean
crc32 (type ++ data) = update (update init type) data
```

## Parse/Serialize Roundtrip Pattern

The chunk roundtrip decomposes into three independent sub-proofs:

1. **Length roundtrip**: big-endian U32 write/read
   (use `ZipCommon.Binary.readUInt32BE_bytes` from lean-zip-common)

2. **Data roundtrip**: identity (raw bytes copied through)

3. **CRC roundtrip**: CRC32 computed on serialization, validated on parse.
   The proof chains:
   - Serializer computes `crc32(type ++ data)` and appends it
   - Parser reads CRC, recomputes `crc32(type ++ data)`, compares
   - Equality follows from determinism of CRC32

```lean
theorem parseChunk_serializeChunk (chunk : PngChunk)
    (hlen : chunk.data.size < 2^31) :
    parseChunk (serializeChunk chunk) = .ok chunk := by
  unfold serializeChunk parseChunk
  -- 1. Length field roundtrip
  rw [readUInt32BE_writeUInt32BE]
  -- 2. Type field (4 bytes, identity)
  simp only [ByteArray.extract_append_left]
  -- 3. Data field (identity)
  simp only [ByteArray.extract_append_mid]
  -- 4. CRC validation
  rw [crc32_deterministic]
  -- 5. Close
  exact ⟨rfl, rfl, rfl⟩
```

## IHDR Structure

IHDR is always exactly 13 bytes:
```
Width:              4 bytes (big-endian)
Height:             4 bytes (big-endian)
Bit depth:          1 byte (1, 2, 4, 8, or 16)
Color type:         1 byte (0, 2, 3, 4, or 6)
Compression method: 1 byte (always 0 = DEFLATE)
Filter method:      1 byte (always 0 = adaptive)
Interlace method:   1 byte (0 = none, 1 = Adam7)
```

The IHDR parse/serialize roundtrip is straightforward big-endian
integer read/write, closed by `bv_decide` for the fixed-width fields.

## Chunk Sequence Validity

A valid PNG chunk sequence satisfies:
1. First chunk is IHDR
2. Last chunk is IEND
3. IDAT chunks are contiguous (no non-IDAT between first and last IDAT)
4. At most one IHDR, one IEND
5. Critical chunks (uppercase first letter) must be understood

Define as an inductive predicate:
```lean
inductive ValidChunkSequence : List PngChunk → Prop where
  | single : chunk.isIHDR → ValidChunkSequence [chunk, iend]
  | consIDAT : ...
```

Or as a decidable Bool function for runtime checking + `decide` proofs.
