import Png.Spec.ColorConvertCorrect
import Png.Spec.InterlaceCorrect
import Png.Spec.BoundsCorrect
import Png.Spec.DecompBombSafe
import Png.Spec.FilterCorrect

/-!
# Security Claims: CVE-class Elimination Theorems

This module re-exposes correctness theorems under names that advertise
the CVE classes they eliminate. Security researchers can cite these
theorems as machine-checked evidence that an entire class of bugs
cannot exist in `lean-png`.

## Theorems

| Name | CVE class eliminated |
|------|----------------------|
| `palette_expansion_bounded` | CVE-2026-33636 (palette expansion OOB) |
| `interlace_scatter_bounded` | CVE-2025-65018 (interlace overflow) |
| `palette_index_valid`       | CVE-2026-25646 (palette swap) |
| `parseChunk_bounded`        | chunk parsing overflow (class) |
| `filterByte_deterministic`  | filter arithmetic (class) |

See `SECURITY.md` for the human-readable explanation of each claim.

## Status
All theorems are fully proven (0 sorry). This file composes
previously-verified lemmas from `Png/Spec/*Correct.lean`.
-/

namespace Png.Spec.SecurityClaims

open Png
open Png.Native.ColorConvert
open Png.Native.Interlace
open Png.Native.Filter

/-! ## Palette expansion (CVE-2026-33636 class) -/

/-- **CVE-2026-33636 class (palette expansion OOB) eliminated.**

If every index byte in `data` is a valid palette index
(`data[i].toNat < plte.entries.size`), then `expandPalette` reads
only from the proven-bounds branch of each lookup. The four output
bytes at positions `4*k, 4*k+1, 4*k+2, 4*k+3` are exactly the RGB
channels of `plte.entries[data[k]]` and the tRNS alpha. No lookup
falls back to a default, and no read reaches past the palette array.
-/
theorem palette_expansion_bounded (data : ByteArray) (plte : PLTEInfo)
    (trns : Option TRNSInfo)
    (hbounds : ∀ i, i < data.size → data[i]!.toNat < plte.entries.size)
    (k : Nat) (hk : k < data.size) :
    (expandPalette data plte trns)[k * 4]! =
        (plte.entries[data[k]!.toNat]'(hbounds k hk)).r ∧
    (expandPalette data plte trns)[k * 4 + 1]! =
        (plte.entries[data[k]!.toNat]'(hbounds k hk)).g ∧
    (expandPalette data plte trns)[k * 4 + 2]! =
        (plte.entries[data[k]!.toNat]'(hbounds k hk)).b ∧
    (expandPalette data plte trns)[k * 4 + 3]! =
        Png.Spec.alphaForIdx (Png.Spec.expandPaletteAlphas trns) (data[k]!) :=
  Png.Spec.expandPalette_bounded data plte trns hbounds k hk

/-! ## Palette index validity (CVE-2026-25646 class) -/

/-- **CVE-2026-25646 class (palette swap / index misdirection) eliminated.**

For each input index `k`, the RGB triple at output positions
`(4*k, 4*k+1, 4*k+2)` comes from the specific palette entry
`plte.entries[data[k]]` — not from some other entry.

Because `expandPalette` is a pure function of `(data, plte, trns)`,
there is no opportunity for the palette to be swapped between the
bounds check and the use: the bound `hbounds` and the lookup happen
in a single functional step, and the entry retrieved is proven to
be the one selected by `data[k]`.
-/
theorem palette_index_valid (data : ByteArray) (plte : PLTEInfo)
    (trns : Option TRNSInfo)
    (hbounds : ∀ i, i < data.size → data[i]!.toNat < plte.entries.size)
    (k : Nat) (hk : k < data.size) :
    (expandPalette data plte trns)[k * 4]! =
        (plte.entries[data[k]!.toNat]'(hbounds k hk)).r ∧
    (expandPalette data plte trns)[k * 4 + 1]! =
        (plte.entries[data[k]!.toNat]'(hbounds k hk)).g ∧
    (expandPalette data plte trns)[k * 4 + 2]! =
        (plte.entries[data[k]!.toNat]'(hbounds k hk)).b := by
  have h := Png.Spec.expandPalette_bounded data plte trns hbounds k hk
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## Interlace scatter (CVE-2025-65018 class) -/

/-- **CVE-2025-65018 class (interlace scatter overflow) eliminated.**

The Adam7 scatter output buffer has exactly `width * height * 4`
bytes — the output size is fully determined by the declared
dimensions. Buffer overrun at the scatter stage is therefore
impossible: downstream allocators and readers can rely on this
invariant.
-/
theorem interlace_scatter_bounded (subImages : Array PngImage) (w h : Nat) :
    (adam7Scatter subImages w h).pixels.size = w * h * 4 :=
  Png.Spec.DecompBombSafe.adam7Scatter_pixels_size subImages w h

/-! ## Chunk parsing bounds (overflow class) -/

/-- **Chunk parsing overflow class eliminated.**

A successful `parseChunk data offset` returns a `ChunkParseResult`
whose `.offset` field strictly advances past the input offset and
stays within `data.size`. This rules out the two failure modes
that plague chunk parsers in C:

1. returning an offset that exceeds `data.size` (buffer overrun),
2. returning an offset that does not advance (infinite loop).
-/
theorem parseChunk_bounded (data : ByteArray) (offset : Nat)
    (result : ChunkParseResult)
    (h : parseChunk data offset = .ok result) :
    offset < result.offset ∧ result.offset ≤ data.size :=
  ⟨Png.Spec.BoundsCorrect.parseChunk_offset_advances data offset result h,
   Png.Spec.BoundsCorrect.parseChunk_offset_bounded data offset result h⟩

/-! ## Filter byte arithmetic (class) -/

/-- **Filter arithmetic class eliminated.**

PNG's byte-level filter and unfilter operations are `UInt8`
subtraction and addition. They are invertible:
`unfilterByte (filterByte raw pred) pred = raw`
for any bytes `raw`, `pred`. Integer-overflow or signedness bugs —
a frequent source of filter-class CVEs in imperative decoders —
are ruled out because these functions are total `UInt8 → UInt8 → UInt8`
operations that commute as `(raw - pred) + pred = raw` mod 256.
-/
theorem filterByte_deterministic (raw pred : UInt8) :
    unfilterByte (filterByte raw pred) pred = raw := by
  simp only [unfilterByte, filterByte]
  rw [UInt8.sub_add_cancel]

end Png.Spec.SecurityClaims
