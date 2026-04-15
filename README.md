# lean-png

A formally verified PNG encoder/decoder in Lean 4. Two capstone
theorems -- `decodePng(encodePng(image)) = image` for non-interlaced
and `decodePng(encodePngInterlaced(image)) = image` for Adam7 --
are machine-checked by Lean 4's kernel with zero `sorry`. If it
type-checks, encoding followed by decoding recovers your original image.

Built on [lean-zip](https://github.com/kim-em/lean-zip)'s verified
DEFLATE/CRC32/Adler32. 29 source files, ~10,200 lines of Lean,
333 proven theorems, **zero `sorry`**, 180 tests. All 176 PngSuite
images handled correctly: 162 valid images decode natively and match
libpng pixel-for-pixel; 14 corrupt images correctly rejected.

## Why verified PNG?

PNG is everywhere. It is the default lossless image format on the web,
in screenshots, in medical imaging pipelines, in document scanners. The
reference C implementation, libpng, has accumulated
[dozens of CVEs](https://www.cvedetails.com/vulnerability-list/vendor_id-7294/Libpng.html)
over its lifetime -- buffer overflows, heap corruptions, integer
overflows in chunk parsing, filter arithmetic, and interlace handling.
Every one of those bugs existed in code that passed its test suite.

Testing finds bugs. Verification eliminates entire *classes* of bugs.
When you prove that `unfilterRow(filterRow(row)) = row` for all
possible inputs, there is no edge case left to discover. The theorem
*is* the test suite, and it covers every input simultaneously.

### Who watches the watchers?

This project was motivated by
["Who Watches the Watchers?"](https://kirancodes.me/posts/log-who-watches-the-watchers.html),
a blog post that fuzzed lean-zip -- this project's sibling verified
compression library. The fuzzer ran **105 million executions** against
the verified Lean code and found **zero bugs** in it.

But it did find:

- A **heap buffer overflow** in the Lean 4 *runtime itself*
  (`lean_alloc_sarray`) -- the trusted computing base underneath the
  verified code.
- Bugs in the **unverified archive parser** -- the part that hadn't
  been formally specified.

The lesson: **verification is only as strong as the questions you think
to ask and the foundations you choose to trust.** lean-png extends the
verified perimeter from compression to the full PNG pipeline, reducing
the unverified surface area one layer at a time.

## What's verified

All theorems below are machine-checked by Lean 4's kernel. No `sorry`
in these statements -- they are fully proven.

### Filter roundtrip (all 5 PNG filter types)

PNG compresses better when each row of pixels is "filtered" first --
subtracting a predicted value from each byte so the differences are
small. The decoder must reverse this exactly to recover the original
pixels. We prove that reversing the filter always gives back the
original row, for all five filter types the PNG spec defines:

```lean
-- Png/Spec/FilterCorrect.lean

theorem unfilterRow_filterRow (ft : FilterType) (bpp : Nat)
    (row prior : ByteArray) (hbpp : bpp > 0) :
    unfilterRow ft bpp (filterRow ft bpp row prior) prior = row
```

This dispatches to per-type lemmas, each proven by induction on byte
position with a content-preservation invariant:

```lean
theorem unfilterSub_filterSub (bpp : Nat) (row : ByteArray) (hbpp : bpp > 0) :
    unfilterSub bpp (filterSub bpp row) = row

theorem unfilterUp_filterUp (row prior : ByteArray) :
    unfilterUp (filterUp row prior) prior = row

theorem unfilterAverage_filterAverage (bpp : Nat) (row prior : ByteArray)
    (hbpp : bpp > 0) :
    unfilterAverage bpp (filterAverage bpp row prior) prior = row

theorem unfilterPaeth_filterPaeth (bpp : Nat) (row prior : ByteArray)
    (hbpp : bpp > 0) :
    unfilterPaeth bpp (filterPaeth bpp row prior) prior = row
```

The core insight: all five filters reduce to `UInt8.sub_add_cancel`:
`(x - pred + pred) = x` in modular arithmetic. For output-dependent
filters (Sub, Average, Paeth), the proof maintains an invariant that
reconstructed bytes match originals, so the predictor reads the same
values on both sides.

### Chunk framing roundtrip

A PNG file is made up of "chunks" -- labeled packets of data with a
checksum for integrity. We prove that writing a chunk to bytes and
reading it back always recovers the original chunk, including
correct checksum validation:

```lean
-- Png/Spec/ChunkCorrect.lean

theorem parseChunk_serialize (c : PngChunk) (hlen : c.data.size < 2 ^ 31) :
    parseChunk c.serialize 0 = .ok ⟨c, c.serialize.size⟩
```

Supporting properties, also proven:

```lean
theorem serialize_crc_valid (c : PngChunk) :
    readUInt32BE c.serialize (8 + c.data.size) =
      Crc32.Native.crc32 0 (writeUInt32BE c.chunkType ++ c.data)

theorem ihdr_fromBytes_toBytes (ihdr : IHDRInfo)
    (hw : ihdr.width ≠ 0) (hh : ihdr.height ≠ 0)
    (hc : ihdr.compressionMethod = 0) (hf : ihdr.filterMethod = 0) :
    IHDRInfo.fromBytes ihdr.toBytes = .ok ihdr

theorem plte_fromBytes_toBytes (plte : PLTEInfo)
    (hne : plte.entries.size > 0) (hle : plte.entries.size ≤ 256) :
    PLTEInfo.fromBytes plte.toBytes = .ok plte
```

### IDAT compression roundtrip

The actual pixel data in a PNG is compressed using zlib (a variant of
the DEFLATE algorithm used in ZIP files). We prove that compressing
the data and decompressing it gives back exactly the original bytes,
by reusing lean-zip's verified compression library:

```lean
-- Png/Spec/IdatCorrect.lean

theorem decompressIdat_compressIdat (data : ByteArray) (level : UInt8)
    (hsize : data.size < 1024 * 1024 * 1024) :
    decompressIdat (compressIdat data level) = .ok data

theorem extractIdatData_splitIntoIdatChunks (zlibData : ByteArray)
    (chunkSize : Nat) (hcs : chunkSize > 0) :
    extractIdatData (splitIntoIdatChunks zlibData chunkSize) = zlibData
```

The full pipeline -- compress, split into chunks, extract, decompress --
is also proven end-to-end:

```lean
theorem extractAndDecompress_compressAndSplit (rawData : ByteArray)
    (level : UInt8) (chunkSize : Nat) (hcs : chunkSize > 0)
    (hsize : rawData.size < 1024 * 1024 * 1024) :
    extractAndDecompress (compressAndSplit rawData level chunkSize) = .ok rawData
```

### Adam7 interlacing

Interlaced PNGs display a low-resolution preview first, then
progressively refine to full resolution. This works by splitting
the image into 7 sub-images at different sampling rates. We prove
that this splitting covers every pixel exactly once and that the
coordinate math is correct:

**Coverage** -- every pixel belongs to exactly one pass:

```lean
-- Png/Spec/InterlaceCorrect.lean

theorem adam7_coverage (r c : Nat) :
    ∃ (p : Fin 7), r % adam7RowStride p = adam7RowStart p ∧
                    c % adam7ColStride p = adam7ColStart p

theorem adam7_uniqueness (r c : Nat) (p q : Fin 7)
    (hp : r % adam7RowStride p = adam7RowStart p ∧ ...) 
    (hq : r % adam7RowStride q = adam7RowStart q ∧ ...) :
    p = q
```

**Coordinate roundtrips** -- converting between sub-image and
full-image coordinates is invertible:

```lean
theorem toSubRow_fromSubRow (p : Fin 7) (sr : Nat) :
    toSubRow p (fromSubRow p sr) = sr

theorem fromSubRow_toSubRow (p : Fin 7) (r : Nat)
    (h : r % adam7RowStride p = adam7RowStart p) :
    fromSubRow p (toSubRow p r) = r
```

**Pixel conservation** -- the sum of sub-image pixels equals
the full image:

```lean
theorem adam7_total_pixels (width height : Nat) :
    totalPassPixels width height = width * height
```

### Capstones: encode/decode roundtrip (PROVEN)

The main results: encoding an image as PNG and decoding it back
gives exactly the original image — for both non-interlaced and
Adam7-interlaced encoding. Machine-checked with zero `sorry`:

```lean
-- Png/Spec/RoundtripCorrect.lean (non-interlaced)

theorem decodePng_encodePng (image : PngImage) (strategy : FilterStrategy)
    (hvalid : image.isValid = true)
    (hsize : (filterScanlines image.pixels image.width image.height strategy).size
              < 1024 * 1024 * 1024)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    decodePng (encodePng image strategy) = .ok image

-- Png/Spec/InterlacedRoundtripCorrect.lean (Adam7 interlaced)

theorem decodePng_encodePngInterlaced (image : PngImage) (strategy : FilterStrategy)
    (hvalid : image.isValid = true)
    (hsize : (filterAllPasses (adam7Extract image) strategy).size
              < 1024 * 1024 * 1024)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    decodePng (encodePngInterlaced image strategy) = .ok image
```

The non-interlaced proof composes all building blocks in a 70-line chain:
1. Chunk parsing recovers IHDR + IDAT chunks (`parseChunk_at_offset`)
2. IDAT extraction + decompression recovers filtered data (`extractAndDecompress_compressAndSplit`)
3. Unfiltering recovers original pixels (`unfilterScanlines_filterScanlines`)
4. Reconstructed image matches original (`PngImage.ext`)

## Architecture

The roundtrip decomposes into independently-proven building blocks:

```
                    BB4: Composition (RoundtripCorrect.lean)
                   /        |         \           \
          BB1: Chunks    BB2: IDAT    BB3: Filters   BB5: Interlace
          ChunkCorrect   IdatCorrect  FilterCorrect  InterlaceCorrect
               |              |
          CRC32 (lean-zip)   DEFLATE (lean-zip)
```

| Block | What it proves | Status |
|-------|---------------|--------|
| BB1: Chunk framing | `parseChunk(serialize(c)) = c`, PLTE roundtrip | **Proven** |
| BB2: IDAT pipeline | `decompress(compress(data)) = data` | **Proven** |
| BB3: Scanline filters | `unfilter(filter(row)) = row` (all 5 types) | **Proven** |
| BB4: Composition | `decode(encode(image)) = image` (non-interlaced) | **Proven** |
| BB5: Interlacing | Coverage, uniqueness, scatter/extract roundtrip | **Proven** |
| BB6: Interlaced roundtrip | `decode(encodeInterlaced(image)) = image` | **Proven** |
| BB7: Color convert | Palette expansion bounds (CVE elimination) | **Proven** |
| BB8: Completeness | `validPng data → ∃ img, decode data = .ok img` | **Proven** |

### Source layout

```
Png/
  Types.lean            — PngImage, IHDRInfo, ColorType, PLTEInfo, TRNSInfo
  FFI.lean              — libpng C FFI bindings
  Util/
    ByteArray.lean      — General ByteArray/Array lemmas (upstreamable)
  Native/
    Chunk.lean          — Pure Lean chunk parser/serializer (IHDR, PLTE, tRNS)
    ColorConvert.lean   — Pixel format converters (all color types + sub-byte)
    Idat.lean           — IDAT compress/decompress pipeline
    Filter.lean         — All 5 filter types (filter + unfilter)
    Interlace.lean      — Adam7 extract/scatter
    Encode.lean         — PNG encoder (non-interlaced + Adam7 interlaced)
    Decode.lean         — PNG decoder (all color types + Adam7)
  Spec/
    BoundsCorrect.lean  — Index bound proofs (7 theorems)
    ChunkCorrect.lean   — Chunk + PLTE roundtrip proofs (57 theorems)
    ColorConvertCorrect.lean — Palette expansion bounds proof (10 theorems)
    DecompBombSafe.lean — Decompression bomb mitigation (17 theorems)
    FilterCorrect.lean  — Filter roundtrip proofs, all 5 types (36 theorems)
    IdatCorrect.lean    — IDAT roundtrip proofs (19 theorems)
    InterlaceCorrect.lean — Interlace proofs (61 theorems)
    InterlacedRoundtripCorrect.lean — Interlaced capstone (33 theorems)
    OverflowSafe.lean   — Overflow safety for dimension arithmetic (15 theorems)
    PngValid.lean       — validPng predicate + completeness (5 theorems)
    RoundtripCorrect.lean — Non-interlaced capstone (53 theorems)
PngTest/                — 180 tests (native vs FFI + PngSuite + unit tests)
PngBench.lean           — Benchmark driver for hyperfine
c/png_ffi.c             — libpng FFI wrapper (~500 lines of C)
```

## What comes from lean-zip

lean-png does not re-prove compression correctness. It reuses:

- **CRC32** -- verified checksum, used directly for chunk validation
- **Adler32** -- verified checksum, used by zlib framing
- **DEFLATE inflate/deflate** -- full roundtrip theorem
- **Zlib framing** -- verified compress/decompress
- **ByteArray/Array/List lemmas** -- the ZipForStd utility library
  (`push_getElem!_lt`, `size_push`, `extract_append`, etc.)

The IDAT roundtrip proof is literally one line:

```lean
exact zlib_decompressSingle_compress data level hsize
```

## Project status

**29 source files. ~10,200 lines of Lean. 333 theorems. Zero `sorry`.
180 tests. Both capstones proven (non-interlaced + Adam7). All 176
PngSuite images handled (162 decoded, 14 corrupt rejected).**

### All spec files fully proven (0 sorry)

| File | Theorems | Key result |
|------|----------|-----------|
| `BoundsCorrect.lean` | 7 | `parseChunk_offset_bounded`, `scanlineBytes_bounded` |
| `ChunkCorrect.lean` | 57 | `parseChunk_serialize`, `plte_fromBytes_toBytes` |
| `ColorConvertCorrect.lean` | 10 | `expandPalette_bounded` (CVE-class elimination) |
| `DecompBombSafe.lean` | 17 | `extractDecompressValidate_size`, decompression bomb mitigation |
| `FilterCorrect.lean` | 36 | `unfilterRow_filterRow` (all 5 types) |
| `IdatCorrect.lean` | 19 | `decompressIdat_compressIdat` |
| `InterlaceCorrect.lean` | 61 | `adam7Scatter_extract`, `adam7_coverage`, `adam7_uniqueness` |
| `InterlacedRoundtripCorrect.lean` | 33 | **`decodePng_encodePngInterlaced`** (interlaced capstone) |
| `OverflowSafe.lean` | 15 | `expectedIdatSize_fits_nat64`, `maxImagePixels` budget |
| `PngValid.lean` | 5 | `decodePng_complete`, `encodePng_validPng` |
| `RoundtripCorrect.lean` | 53 | **`decodePng_encodePng`** (non-interlaced capstone) |

Every theorem in every spec file is fully machine-checked. Zero `sorry`
across the entire codebase.

## Benchmarks

Benchmark driver for [hyperfine](https://github.com/sharkdp/hyperfine):

```bash
lake build bench
hyperfine '.lake/build/bin/bench encode 512 512' \
          '.lake/build/bin/bench encode-ffi 512 512'
```

Current performance (1024x1024 RGBA, Apple Silicon):

| Operation | Native Lean | libpng FFI | Ratio |
|-----------|------------|------------|-------|
| Encode | 650ms | 50ms | 13x |
| Decode | 250ms | 19ms | 13x |
| Filter only | 30ms | — | — |

The bottleneck is lean-zip's native DEFLATE compression (95% of encode
time), not PNG-specific code. Filter/unfilter is already fast at 30ms
for 1MP. Optimization via generational refinement (Track D in PLAN.md)
would target the compression layer.

## Development methodology

lean-png was built using a **formalization-first cycle**:

1. **Type signatures** with `:= sorry` -- define the interface
2. **Specification theorems** with `:= by sorry` -- state what must be true
3. **Implementation** -- fill in the function bodies
4. **Conformance tests** -- verify native code matches libpng FFI
5. **Proofs** -- discharge the sorries

This pattern enables parallelism: multiple agent sessions can work
simultaneously on different building blocks because the sorry
placeholders define stable interfaces. Phases B1 (chunks), B2 (IDAT),
B3 (filters), and A3 (test infrastructure) were developed concurrently.

Key lessons from ~25 agent sessions (see `.claude/LEARNINGS.md` for the
full list):

- **Well-founded recursion only.** `for`/`while`/`Id.run do` loops
  generate opaque `partial` defs that cannot be unfolded in proofs.
  Every function that appears in a theorem must use explicit recursion
  with `termination_by`.
- **Three-theorem pattern for buffer loops.** Every `go` function that
  builds a ByteArray needs: (1) `_size`, (2) `_getElem!_lt`
  (prefix preservation), (3) `_getElem!_ge` (content characterization).
  Each feeds the next.
- **Compose, don't re-prove.** The IDAT proof reuses lean-zip's
  theorem in one line. CRC32 verification is inherited, not re-derived.

## Usage

### Requirements

- Lean 4 (toolchain: `leanprover/lean4:v4.29.0-rc4`)
- zlib development headers
- libpng development headers (for FFI conformance tests)
- `pkg-config`

On NixOS, `nix-shell` provides all C dependencies automatically.

### Build

```bash
lake build          # build library + test executable
lake exe test       # run all tests
```

### As a library dependency

In your `lakefile.lean`:

```lean
require leanPng from git "https://github.com/kim-em/lean-png"
```

### Encode/Decode (native, verified)

```lean
import Png.Native.Encode
import Png.Native.Decode

-- Encode a PngImage to PNG bytes
let pngBytes := Png.Native.Encode.encodePng image

-- Decode PNG bytes back to a PngImage
match Png.Native.Decode.decodePng pngBytes with
| .ok image => -- use image.width, image.height, image.pixels
| .error e  => -- handle error
```

### Encode/Decode (FFI, via libpng)

```lean
import Png.FFI

-- Decode from file
let image ← Png.FFI.decodeFile "/path/to/image.png"

-- Encode to PNG bytes
let pngBytes ← Png.FFI.encode image

-- Decode from memory
let image2 ← Png.FFI.decodeMemory pngBytes
```

### Proofs in scope

```lean
import Png.Spec.RoundtripCorrect  -- capstone: decode(encode(img)) = img
import Png.Spec.FilterCorrect     -- filter roundtrips (all 5 types)
import Png.Spec.IdatCorrect       -- IDAT compress/decompress roundtrip
```

## References

- [PNG Specification (Second Edition)](https://www.w3.org/TR/PNG/),
  W3C, 2003. ISO/IEC 15948:2003.
- [lean-zip](https://github.com/kim-em/lean-zip) -- verified DEFLATE,
  CRC32, Adler32 in Lean 4.
- [lean-zip-common](https://github.com/kim-em/lean-zip-common) --
  shared utilities (Binary, BitReader, ZipForStd).
- ["Who Watches the Watchers?"](https://kirancodes.me/posts/log-who-watches-the-watchers.html)
  -- fuzzing lean-zip: 105M executions, zero bugs in verified code,
  one heap overflow in the Lean runtime.
- [PngSuite](http://www.schaik.com/pngsuite/) -- the official PNG test
  images.

## License

MIT
