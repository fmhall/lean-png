# Plan for lean-png

A verified PNG decoder/encoder in Lean 4, with formal proofs of
correctness. Reuses lean-zip's verified DEFLATE and CRC32 as
building blocks; adds chunk framing, scanline filtering, and
interlacing with full roundtrip proofs.

## What Is Realistic to Prove

### Chunk Framing (CRC32 validation)

Very provable. PNG chunks have a simple structure: 4-byte length,
4-byte type, `length` bytes of data, 4-byte CRC32. CRC32 is already
verified in lean-zip. Tractable theorems:

- Chunk parse/serialize invertibility:
  `parseChunk (serializeChunk chunk) = .ok chunk`
- CRC32 validation: well-formed chunks always pass CRC check
- Chunk sequence: IHDR first, IEND last, IDAT contiguous

### IDAT Decompression

Trivially provable — this is just zlib decompression of concatenated
IDAT chunk data, which lean-zip already verifies. The new work is
proving that IDAT concatenation + zlib decompress produces the
expected byte count (`height * (1 + width * bytesPerPixel)` for
non-interlaced images).

### Scanline Filtering

The core new mathematical content. PNG defines 5 filter types:

- **None (0)**: identity, trivially invertible
- **Sub (1)**: `filtered[i] = raw[i] - raw[i - bpp]` (mod 256)
  Invertible because UInt8 arithmetic is invertible.
- **Up (2)**: `filtered[i] = raw[i] - prior[i]` (mod 256)
  Same argument.
- **Average (3)**: `filtered[i] = raw[i] - floor((a + b) / 2)` (mod 256)
  where `a = raw[i - bpp]`, `b = prior[i]`. Invertible: the predictor
  `floor((a + b) / 2)` is computable from already-reconstructed bytes.
- **Paeth (4)**: `filtered[i] = raw[i] - PaethPredictor(a, b, c)` (mod 256)
  where `a = raw[i - bpp]`, `b = prior[i]`, `c = prior[i - bpp]`.
  PaethPredictor is a pure function (min-distance selection among a, b, c).
  Invertible by the same argument.

All filters have the form `filtered = raw - predictor(context)` where
the context is computable from prior rows and earlier bytes in the
current row. The roundtrip theorem is:

```
∀ (row priorRow : ByteArray) (filterType : UInt8),
  unfilterRow filterType bpp (filterRow filterType bpp row priorRow) priorRow = row
```

Each filter type is a separate lemma; the top-level dispatches on `filterType`.

The key proof technique: induction on byte position `i`, with the
invariant that `unfiltered[0..i] = raw[0..i]`. At each step, the
filter subtracted `predictor(context)` and the unfilter adds it back:
`(raw[i] - pred + pred) mod 256 = raw[i]` by modular arithmetic.

### Adam7 Interlacing

Provable but tedious. Adam7 defines 7 sub-images, each sampling the
full image at different offsets/strides. The proof is purely index
arithmetic:

```
∀ (pass : Fin 7) (row col : Nat),
  adam7Row pass row < height ∧ adam7Col pass col < width
```

And the bijectivity theorem: every pixel (r, c) in the full image
appears in exactly one pass at a unique sub-image position.

### Full Roundtrip

```
∀ (image : PngImage) (filterStrategy : FilterStrategy),
  decodePng (encodePng image filterStrategy) = .ok image
```

This decomposes into:
1. Chunk framing roundtrip (serialize/parse chunks)
2. IDAT roundtrip (zlib compress/decompress via lean-zip)
3. Filter roundtrip (per-row filter/unfilter invertibility)
4. Interlace roundtrip (scatter/gather bijectivity)
5. Composition

## Development Cycle

Each native implementation follows a formalization-first cycle:

1. **Type signature** of the new function, implemented as `:= sorry`
2. **Specification theorems** stating the desired properties, with `:= by sorry` proofs
3. **Implementation** of the function body
4. **Conformance tests** verifying agreement with the FFI/library version
5. **Proofs** of the specification theorems

This same pattern applies to optimized versions: the specification theorems
are equivalence with the unoptimized version, and the roundtrip/correctness
proofs transfer automatically via the equivalence.

Writing specs before implementations ensures the work stays grounded in
what we can actually prove, and prevents implementations from getting ahead
of the formalization.

## Phased Plan

### Overview

The work is organized into four tracks: a bootstrapping **A-track**,
a linear **B-track** (PNG verification pipeline), and two tracks
**C** and **D** that can be worked on concurrently once their
dependencies are met.

**Dependency graph:**

```
A1 → A2 → A3
            ↓
     B1 → B2 → B3 → B4 → B5
           │              │
           ↓              ↓
           D              C
```

- **A1–A3** are sequential: project setup, FFI wrappers, test infrastructure.
- **B1–B5** are sequential: chunk framing through full roundtrip.
  B1 depends on A3 (needs FFI wrappers and test infrastructure).
- **C** (interlacing) depends on B4: basic filter roundtrip must exist
  before interlace adds a second dimension.
- **D** (benchmarking and optimization) depends on B2: native
  implementations must exist before they can be profiled.

### A1: Project Setup

Lake project scaffolding, toolchain configuration, and build system.

**Deliverables**:
- `lakefile.lean` with Lake build configuration
- `lean-toolchain` pinning the Lean version
- `shell.nix` providing zlib, libpng, and pkg-config for NixOS
- C FFI scaffolding: `pkg-config` detection for libpng link flags
- Dependencies on `lean-zip` and `lean-zip-common`
- `README.md` with build and usage instructions

### A2: FFI Wrappers

C FFI bindings to libpng. These provide the fast path and serve as
the reference implementation for conformance testing.

**Deliverables**:
- **libpng FFI**: read PNG from file/memory → decoded RGBA pixels
- **libpng FFI**: write RGBA pixels → PNG file/memory
- **Metadata extraction**: IHDR fields (width, height, bit depth,
  color type, interlace method)
- C implementation in `c/` with allocation failure checks
- Basic tests for each FFI function

### A3: Test Infrastructure

Conformance test harness and PNG corpus.

**Deliverables**:
- **Test corpus**: collect standard PNG test suites (PngSuite,
  hand-crafted edge cases)
- **Conformance test harness**: native decode + FFI decode = same pixels,
  FFI decode(native encode(image)) = image
- **Edge cases**: 1x1, grayscale, RGBA, 16-bit, interlaced, all
  filter types, ancillary chunks, multiple IDAT chunks

### B1: Chunk Framing

Pure Lean PNG chunk parser/serializer with CRC32 validation.
Reuses CRC32 from lean-zip.

**Deliverables**:
- PNG signature validation (8-byte magic)
- Chunk parser: length + type + data + CRC32
- Chunk serializer: inverse of parser
- IHDR parser/serializer (13-byte fixed structure)
- IEND detection
- Critical vs ancillary chunk classification
- **Spec**: `parseChunk (serializeChunk c) = .ok c`
- **Spec**: `validateCrc (serializeChunk c) = true`
- **Spec**: chunk sequence validity predicate
- Conformance tests against real PNG files

### B2: IDAT Decompression Pipeline

Concatenate IDAT chunks and decompress via lean-zip's verified inflate.

**Deliverables**:
- IDAT data concatenation from chunk stream
- Zlib decompression of concatenated IDAT data (via lean-zip native inflate)
- Output size validation: decompressed size = expected byte count
  from IHDR (height * (1 + width * bytesPerPixel))
- IDAT compression: raw pixels → zlib compress → split into IDAT chunks
- **Spec**: `decompressIDAT (compressIDAT pixels ihdr) = .ok pixels`
  (via lean-zip's roundtrip theorem)
- **Spec**: decompressed size matches IHDR dimensions
- Conformance tests: native decompress = FFI decompress for test corpus

### B3: Scanline Filters

Pure Lean filter/unfilter for all 5 PNG filter types, with roundtrip
proofs. This is the core new mathematical content.

**Deliverables**:
- `filterRow`: apply filter to a raw scanline given prior row
- `unfilterRow`: reverse filter given prior row
- Per-filter-type roundtrip lemmas:
  - `unfilterNone_filterNone`: trivial (identity)
  - `unfilterSub_filterSub`: UInt8 modular arithmetic
  - `unfilterUp_filterUp`: UInt8 modular arithmetic
  - `unfilterAverage_filterAverage`: average predictor invertibility
  - `unfilterPaeth_filterPaeth`: Paeth predictor invertibility
- Top-level per-row roundtrip:
  ```lean
  theorem unfilterRow_filterRow (ft : FilterType) (bpp : Nat)
      (row priorRow : ByteArray) :
      unfilterRow ft bpp (filterRow ft bpp row priorRow) priorRow = row
  ```
- Full-image filter roundtrip (induction on rows, threading prior row):
  ```lean
  theorem unfilterImage_filterImage (image : Array ByteArray)
      (bpp : Nat) (strategy : FilterStrategy) :
      unfilterImage bpp (filterImage bpp strategy image) = image
  ```
- **Characterizing properties**:
  - Each filter type preserves row length
  - Filter/unfilter are pure functions (no side effects)
  - PaethPredictor selects the byte closest to `a + b - c`
- Conformance tests: native filter/unfilter matches libpng

### B4: Non-Interlaced Roundtrip

Compose B1–B3 into a full encode/decode roundtrip for non-interlaced
PNG images.

**Deliverables**:
- `encodePng`: image → filter → compress → chunk → PNG bytes
- `decodePng`: PNG bytes → chunk parse → decompress → unfilter → image
- **Capstone theorem** (non-interlaced):
  ```lean
  theorem decodePng_encodePng (image : PngImage) (strategy : FilterStrategy)
      (hsize : image.dataSize < maxSize)
      (hInterlace : image.interlaceMethod = .none) :
      decodePng (encodePng image strategy) = .ok image
  ```
- Proof architecture:
  1. `encodePng` produces valid chunk sequence (B1)
  2. IDAT decompression recovers filtered scanlines (B2)
  3. Unfiltering recovers original pixel data (B3)
  4. Composition chains 1–3

### B5: Full Roundtrip with Interlacing (= Track C)

Adam7 interlacing support with bijectivity proofs.

**Deliverables**:
- Adam7 sub-image extraction (7 passes)
- Adam7 pixel placement (scatter into full image)
- **Spec**: Adam7 index bijectivity — every pixel (r, c) appears
  in exactly one pass
- **Spec**: scatter(extract(image)) = image
- Extended roundtrip theorem covering interlaced images:
  ```lean
  theorem decodePng_encodePng_interlaced (image : PngImage) (strategy : FilterStrategy)
      (hsize : image.dataSize < maxSize) :
      decodePng (encodePng image strategy) = .ok image
  ```

### D: Benchmarking and Optimization

**Depends on: B2**

Follow the same methodology as lean-zip:

1. **Benchmark** against libpng on representative images (small icons,
   photos, screenshots, pathological patterns)
2. **Profile** to identify bottlenecks (likely: filter arithmetic,
   ByteArray allocation patterns, row iteration)
3. **Optimize** using generational refinement — prove equivalence
   with unoptimized version, transfer roundtrip proof
4. **Repeat** until competitive with libpng

## Optimization Strategy

### Initial approach: clarity first

Start with naive, easy-to-reason-about Lean implementations. Simple
byte-by-byte loops for filters, straightforward chunk parsing, direct
index arithmetic for interlacing. Once proofs are established, optimize
using generational refinement from lean-zip:

1. Write the faster implementation (Gen N+1) as a new definition
2. Prove `genN_plus_1 = genN`
3. Transfer the roundtrip theorem across the equivalence

### When to stop

When the native Lean PNG decoder/encoder is competitive with libpng
on representative workloads.

## What We Get from lean-zip for Free

- **CRC32**: verified, used directly for chunk validation
- **Adler32**: verified, used by zlib framing
- **DEFLATE inflate/deflate**: full roundtrip theorem
- **Zlib framing**: verified compress/decompress roundtrip
- **ByteArray/List/Array lemmas**: ZipForStd utility library
- **BitReader**: for any bit-level parsing needed

## References

- **PNG Specification** (W3C, 2003), "Portable Network Graphics (PNG)
  Specification (Second Edition)". ISO/IEC 15948:2003.
  https://www.w3.org/TR/PNG/

- **RFC 2083** (Boutell, 1997), "PNG (Portable Network Graphics)
  Specification Version 1.0".

- **PngSuite** (Schaik), the official PNG test images.
  http://www.schaik.com/pngsuite/

- **RFC 1950** (zlib format), **RFC 1951** (DEFLATE) — handled by lean-zip.
