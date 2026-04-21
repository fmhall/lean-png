# Security

`lean-png` is a formally verified PNG decoder/encoder written in Lean 4.
Every theorem in the table below is machine-checked: the proofs have
been accepted by the Lean kernel, and the build gates on zero `sorry`.
Security researchers can cite these theorems as evidence that an entire
class of PNG decoder bugs cannot exist in `lean-png`.

## CVE-class elimination

The Lean-side theorems are collected in
[`Png/Spec/SecurityClaims.lean`](Png/Spec/SecurityClaims.lean) under the
`Png.Spec.SecurityClaims` namespace. Each theorem re-exports an
already-proven lemma under a name that advertises the CVE class it
rules out.

| CVE / class                               | Theorem                         | Why this class is impossible in lean-png                                                                                                                                                       |
| ----------------------------------------- | ------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **CVE-2026-33636** — palette expansion OOB | `palette_expansion_bounded`     | Under the precondition that every index byte is `< plte.entries.size`, `expandPalette` is proven to read only from the in-bounds palette entry — the black fallback branch is never taken, and no byte is read past the palette array. |
| **CVE-2025-65018** — interlace overflow   | `interlace_scatter_bounded`     | `adam7Scatter subImages w h` produces a pixel buffer of **exactly** `w * h * 4` bytes. The output length is a provable function of the declared dimensions, so downstream code cannot overrun a scatter buffer. |
| **CVE-2026-25646** — palette swap         | `palette_index_valid`           | `expandPalette` is a pure function of `(data, plte, trns)` and the RGB triple for input `k` is proven to be exactly `plte.entries[data[k]]`. There is no mutable palette, no TOCTOU gap, and the entry returned is the one the index selected. |
| Chunk parsing overflow (class)            | `parseChunk_bounded`            | A successful `parseChunk data offset` is proven to return `offset < result.offset ≤ data.size`. The parser never advances past the input (no buffer overrun) and never fails to advance (no infinite loop / hang). |
| Filter arithmetic (class)                 | `filterByte_deterministic`      | `filterByte` / `unfilterByte` are the total `UInt8` subtraction / addition operations and are proven invertible: `unfilterByte (filterByte raw pred) pred = raw`. Signedness and integer-overflow bugs — a common class in C filter implementations — cannot arise. |

All five theorems live in the same file so they can be audited
together. Each is a one-liner that delegates to an upstream lemma:

- `palette_expansion_bounded` — `Png.Spec.expandPalette_bounded`
  (in [`Png/Spec/ColorConvertCorrect.lean`](Png/Spec/ColorConvertCorrect.lean))
- `palette_index_valid` — same underlying lemma, restricted to RGB
- `interlace_scatter_bounded` — `Png.Spec.DecompBombSafe.adam7Scatter_pixels_size`
  (in [`Png/Spec/DecompBombSafe.lean`](Png/Spec/DecompBombSafe.lean))
- `parseChunk_bounded` — `Png.Spec.BoundsCorrect.parseChunk_offset_advances`
  and `Png.Spec.BoundsCorrect.parseChunk_offset_bounded`
  (in [`Png/Spec/BoundsCorrect.lean`](Png/Spec/BoundsCorrect.lean))
- `filterByte_deterministic` — from the `UInt8.sub_add_cancel` identity
  used throughout [`Png/Spec/FilterCorrect.lean`](Png/Spec/FilterCorrect.lean)

## Scope

Verification applies to the **native** (pure-Lean) decoder and encoder
paths — the ones proven against the specifications in `Png/Spec/`. The
optional `FFI` path (libpng) is still available as a reference /
performance oracle; it is not covered by these proofs.

The theorems above rule out the specific bug class named, for inputs
that exercise the verified path. They do **not** make claims about:

- libpng (used only via `Png.FFI`);
- memory safety of the underlying Lean runtime;
- correctness of CPU / compiler behaviour;
- timing side-channels.

## Reporting a vulnerability

If you believe you have found a vulnerability that is not ruled out by
the theorems above — for example, a valid PNG that `Png.Native.Decode`
crashes on, or a case where the native and FFI decoders disagree on
pixel output — please open a GitHub issue on
[`fmhall/lean-png`](https://github.com/fmhall/lean-png/issues) with a
minimal reproducer.

## Reproducing the proofs

```bash
lake build            # builds the library + runs the kernel over all proofs
lake exe test         # runs the conformance test suite (native vs FFI)
lake exe fuzz 100000  # runs the differential fuzzer for 100K iterations
```

A green `lake build` is sufficient evidence that every theorem in
`Png/Spec/SecurityClaims.lean` — and therefore every claim in the
table above — has been checked by the Lean kernel.
