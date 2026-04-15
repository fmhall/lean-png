# lean-png Progress

Global milestones — updated only on phase transitions and major events.
Per-session details are in `progress/`.

## Current State

- **Phase**: Phase 2 in progress (color type support)
- **Toolchain**: leanprover/lean4:v4.29.0-rc4
- **Sorries**: 0
- **Theorems**: 253 (all proven)
- **Source files**: 23 (16 Png/ + 7 PngTest/)
- **Lines of Lean**: ~7,600
- **Tests**: 180 passing
- **Merged PRs**: 25

## Phase 1 — Complete

- Proven-bounds decode path: all `]!` replaced with `]` (PR #20)
- Index bound theorems in `BoundsCorrect.lean` (PR #21)
- Default build target includes spec proofs (PR #23)
- All spec proof warnings fixed (PR #24)

## Phase 2 — In Progress

- PLTE chunk parsing + tRNS transparency + roundtrip proof (PR #22)
- Color type converters: grayscale, RGB, gray+alpha, palette, 16-bit, sub-byte unpacking (PR #25)
- Remaining: generalize decodePng to all color types (#8), palette bounds proof (#7)
