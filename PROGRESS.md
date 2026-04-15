# lean-png Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 3 complete, phase 4 next
- **Toolchain**: leanprover/lean4:v4.29.0-rc4
- **Sorries**: 0
- **Theorems**: 301 (all proven)
- **Source files**: 27 (18 Png/ + 8 PngTest/ + PngBench.lean)
- **Lines of Lean**: ~9,600
- **Tests**: 180 passing (162 PngSuite native conformance)
- **Merged PRs**: 31

## Phase 1 — Complete

- Proven-bounds decode path: all `]!` replaced with `]` (PR #20)
- Index bound theorems in `BoundsCorrect.lean` (PR #21)
- Default build target includes spec proofs (PR #23)
- All spec proof warnings fixed (PR #24)

## Phase 2 — Complete

- PLTE chunk parsing + tRNS transparency + roundtrip proof (PR #22)
- Color type converters: grayscale, RGB, gray+alpha, palette, 16-bit, sub-byte unpacking (PR #25)
- Generalized decoder: all 15 color type/bit depth combinations, 127/127 PngSuite (PR #27)
- Palette expansion bounds proof — CVE-class elimination (PR #28)

## Phase 3 — Complete

- Adam7 interlaced decoding: 162/162 PngSuite native conformance (PR #29)
- validPng predicate + decoder completeness theorem (PR #30)
- Interlaced encoder + interlaced roundtrip theorem, fully proven (PR #31)

## Remaining

- Phase 4: Overflow safety proofs, decompression bomb mitigation (#12, #13)
- Phase 5: CI/CD with sorry-count enforcement, fuzzing harness (#14, #15)
- Phase 6: Nightly agent automation (#16)
- Phase 7: SECURITY.md with CVE-class elimination mapping (#17, #18)
