# lean-png Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phases 1-6 complete, phase 7 next
- **Toolchain**: leanprover/lean4:v4.29.0-rc4
- **Sorries**: 0
- **Theorems**: 332 (all proven)
- **Source files**: 29 (19 Png/ + 9 PngTest/ + PngBench.lean)
- **Lines of Lean**: ~10,200
- **Tests**: 180 passing (162 valid PngSuite + 14 corrupt rejected)
- **Merged PRs**: 34
- **Open issues**: 3 (#15 fuzzing, #17 SECURITY.md, #18 CVE proofs)

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

## Phase 4 — Complete

- Overflow safety: 15 theorems, maxImagePixels budget, fits-in-nat64 (PR #33)
- Decompression bomb mitigation: 17 theorems, IDAT size validation chain (PR #34)
- Corrupt PngSuite rejection: all 14 x* files correctly rejected (PR #34)

## Phase 5 — Closed (CI/CD skipped, fuzzing open)

- #14 CI/CD: closed (not needed now)
- #15 Fuzzing harness: open

## Phase 6 — Closed

- #16 Nightly automation: closed (not needed now)

## Remaining

- #15: Build fuzzing harness (native vs FFI comparison)
- #17: Create SECURITY.md with CVE-class elimination mapping
- #18: Prove CVE-class elimination theorems
