# lean-png

Verified PNG decoder/encoder in Lean 4, with formal proofs of correctness.

Builds on [lean-zip](https://github.com/kim-em/lean-zip)'s verified DEFLATE
compression and CRC32 checksums. Adds chunk framing, scanline filtering, and
Adam7 interlacing — all with roundtrip proofs.

## Status

Early development. See [PLAN.md](PLAN.md) for the phased roadmap and
[PROGRESS.md](PROGRESS.md) for current status.

## Requirements

- Lean 4 (see `lean-toolchain` for pinned version)
- zlib development headers
- libpng development headers (for FFI conformance testing)
- `pkg-config`

On NixOS:
```bash
nix-shell    # provides zlib, libpng, pkg-config
```

## Build

```bash
lake build          # build library + test executable
lake exe test       # run all tests
```

## Architecture

```
Png/              — Pure Lean PNG implementation
  Native/         — Native Lean implementations (no FFI)
  Spec/           — Formal specifications and correctness proofs
PngTest/          — Test suite
c/                — libpng FFI (reference implementation)
```

### Proof structure

The roundtrip theorem `decodePng(encodePng(image)) = image` decomposes into
independently-proven building blocks:

1. **Chunk framing**: serialize/parse invertibility + CRC32 validation
2. **IDAT pipeline**: zlib compress/decompress (via lean-zip's proven roundtrip)
3. **Scanline filters**: per-row filter/unfilter invertibility for all 5 types
4. **Adam7 interlacing**: scatter/gather bijectivity

### Dependencies

- [lean-zip](https://github.com/kim-em/lean-zip) — verified DEFLATE, CRC32, Adler32
- [lean-zip-common](https://github.com/kim-em/lean-zip-common) — shared utilities (Binary, BitReader, ZipForStd)

## License

MIT
