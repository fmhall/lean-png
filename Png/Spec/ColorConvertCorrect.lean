import Png.Native.ColorConvert
import Png.Util.ByteArray

/-!
# Color Conversion Correctness Specifications

Formal proofs that `expandPalette` never reads beyond palette bounds.
Under the precondition that all index bytes are valid palette entries,
every lookup takes the proven-bounds branch (not the fallback), and
the output contains the correct RGBA bytes.

**Security impact**: Eliminates CVE-2026-33636 class (palette expansion OOB).

## Structure

Following the three-theorem pattern:
1. `expandPalette_go_size` — already proven in ColorConvert.lean
2. `expandPalette_go_getElem!_lt` — prefix preservation
3. `expandPalette_go_r/g/b/a` — content (byte-level)

The main theorem `expandPalette_bounded` states that for each input
index `k`, the four output bytes at positions `4*k, 4*k+1, 4*k+2, 4*k+3`
equal `entries[data[k]!.toNat].r`, `.g`, `.b`, and the alpha value.
-/

namespace Png.Spec

open Png.Native.ColorConvert

/-! ## Prefix preservation for expandPalette.go -/

/-- Prefix preservation: `expandPalette.go` does not modify earlier accumulator bytes. -/
theorem expandPalette_go_getElem!_lt (data : ByteArray) (entries : Array PaletteEntry)
    (alphas : ByteArray) (i : Nat) (acc : ByteArray) (j : Nat) (hj : j < acc.size) :
    (expandPalette.go data entries alphas i acc)[j]! = acc[j]! := by
  unfold expandPalette.go; split
  case isTrue hlt =>
    simp only []
    rw [expandPalette_go_getElem!_lt data entries alphas (i + 1) _ j
      (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    exact ByteArray.push_getElem!_lt _ _ _ hj
  case isFalse => rfl
termination_by data.size - i

/-! ## Content theorems for expandPalette.go -/

/-- Helper: the alpha value for a given index byte and alpha table.
    This mirrors the `if idx.toNat < alphas.size then alphas.get! idx.toNat else 255`
    computation in `expandPalette.go`. -/
def alphaForIdx (alphas : ByteArray) (idx : UInt8) : UInt8 :=
  if idx.toNat < alphas.size then alphas.get! idx.toNat else 255

/-- Content: red byte at position `acc.size + (k - i) * 4`. -/
theorem expandPalette_go_r (data : ByteArray) (entries : Array PaletteEntry)
    (alphas : ByteArray) (i : Nat) (acc : ByteArray) (k : Nat)
    (hki : i ≤ k) (hk : k < data.size)
    (hbounds : ∀ j, j < data.size → data[j]!.toNat < entries.size) :
    (expandPalette.go data entries alphas i acc)[acc.size + (k - i) * 4]! =
      (entries[data[k]!.toNat]'(hbounds k hk)).r := by
  unfold expandPalette.go; split
  case isFalse hi => exact absurd (Nat.lt_of_le_of_lt hki hk) hi
  case isTrue hi =>
    simp only []
    by_cases hik : i = k
    · subst hik
      simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      have hidx : data[i].toNat < entries.size := by
        rw [← ByteArray.getElem!_eq_getElem data i hi]; exact hbounds i hi
      rw [expandPalette_go_getElem!_lt _ _ _ _ _ _
        (by simp only [ByteArray.size_push]; omega)]
      rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
      rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
      rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
      rw [ByteArray.push_getElem!_eq]
      simp only [dif_pos hidx, ByteArray.getElem!_eq_getElem data i hi]
    · generalize hdef :
        ((((acc.push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).r).push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).g).push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).b).push
          (if ha : (data[i]).toNat < alphas.size then alphas[(data[i]).toNat] else 255))
        = acc'
      have haccsize : acc'.size = acc.size + 4 := by
        rw [← hdef]; simp only [ByteArray.size_push]
      rw [show acc.size + (k - i) * 4 = acc'.size + (k - (i + 1)) * 4 from by omega]
      exact expandPalette_go_r data entries alphas (i + 1) acc' k (by omega) hk hbounds
termination_by data.size - i

/-- Content: green byte at position `acc.size + (k - i) * 4 + 1`. -/
theorem expandPalette_go_g (data : ByteArray) (entries : Array PaletteEntry)
    (alphas : ByteArray) (i : Nat) (acc : ByteArray) (k : Nat)
    (hki : i ≤ k) (hk : k < data.size)
    (hbounds : ∀ j, j < data.size → data[j]!.toNat < entries.size) :
    (expandPalette.go data entries alphas i acc)[acc.size + (k - i) * 4 + 1]! =
      (entries[data[k]!.toNat]'(hbounds k hk)).g := by
  unfold expandPalette.go; split
  case isFalse hi => exact absurd (Nat.lt_of_le_of_lt hki hk) hi
  case isTrue hi =>
    simp only []
    by_cases hik : i = k
    · subst hik
      simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      have hidx : data[i].toNat < entries.size := by
        rw [← ByteArray.getElem!_eq_getElem data i hi]; exact hbounds i hi
      rw [expandPalette_go_getElem!_lt _ _ _ _ _ _
        (by simp only [ByteArray.size_push]; omega)]
      rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
      rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
      rw [show acc.size + 1 = (acc.push _).size from by simp only [ByteArray.size_push]]
      rw [ByteArray.push_getElem!_eq]
      simp only [dif_pos hidx, ByteArray.getElem!_eq_getElem data i hi]
    · generalize hdef :
        ((((acc.push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).r).push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).g).push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).b).push
          (if ha : (data[i]).toNat < alphas.size then alphas[(data[i]).toNat] else 255))
        = acc'
      have haccsize : acc'.size = acc.size + 4 := by
        rw [← hdef]; simp only [ByteArray.size_push]
      rw [show acc.size + (k - i) * 4 + 1 = acc'.size + (k - (i + 1)) * 4 + 1 from by omega]
      exact expandPalette_go_g data entries alphas (i + 1) acc' k (by omega) hk hbounds
termination_by data.size - i

/-- Content: blue byte at position `acc.size + (k - i) * 4 + 2`. -/
theorem expandPalette_go_b (data : ByteArray) (entries : Array PaletteEntry)
    (alphas : ByteArray) (i : Nat) (acc : ByteArray) (k : Nat)
    (hki : i ≤ k) (hk : k < data.size)
    (hbounds : ∀ j, j < data.size → data[j]!.toNat < entries.size) :
    (expandPalette.go data entries alphas i acc)[acc.size + (k - i) * 4 + 2]! =
      (entries[data[k]!.toNat]'(hbounds k hk)).b := by
  unfold expandPalette.go; split
  case isFalse hi => exact absurd (Nat.lt_of_le_of_lt hki hk) hi
  case isTrue hi =>
    simp only []
    by_cases hik : i = k
    · subst hik
      simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      have hidx : data[i].toNat < entries.size := by
        rw [← ByteArray.getElem!_eq_getElem data i hi]; exact hbounds i hi
      rw [expandPalette_go_getElem!_lt _ _ _ _ _ _
        (by simp only [ByteArray.size_push]; omega)]
      rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
      rw [show acc.size + 2 = ((acc.push _).push _).size from by
        simp only [ByteArray.size_push]]
      rw [ByteArray.push_getElem!_eq]
      simp only [dif_pos hidx, ByteArray.getElem!_eq_getElem data i hi]
    · generalize hdef :
        ((((acc.push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).r).push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).g).push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).b).push
          (if ha : (data[i]).toNat < alphas.size then alphas[(data[i]).toNat] else 255))
        = acc'
      have haccsize : acc'.size = acc.size + 4 := by
        rw [← hdef]; simp only [ByteArray.size_push]
      rw [show acc.size + (k - i) * 4 + 2 = acc'.size + (k - (i + 1)) * 4 + 2 from by omega]
      exact expandPalette_go_b data entries alphas (i + 1) acc' k (by omega) hk hbounds
termination_by data.size - i

/-- Content: alpha byte at position `acc.size + (k - i) * 4 + 3`. -/
theorem expandPalette_go_a (data : ByteArray) (entries : Array PaletteEntry)
    (alphas : ByteArray) (i : Nat) (acc : ByteArray) (k : Nat)
    (hki : i ≤ k) (hk : k < data.size) :
    (expandPalette.go data entries alphas i acc)[acc.size + (k - i) * 4 + 3]! =
      alphaForIdx alphas (data[k]!) := by
  unfold expandPalette.go; split
  case isFalse hi => exact absurd (Nat.lt_of_le_of_lt hki hk) hi
  case isTrue hi =>
    simp only []
    by_cases hik : i = k
    · subst hik
      simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      rw [expandPalette_go_getElem!_lt _ _ _ _ _ _
        (by simp only [ByteArray.size_push]; omega)]
      rw [show acc.size + 3 = (((acc.push _).push _).push _).size from by
        simp only [ByteArray.size_push]]
      rw [ByteArray.push_getElem!_eq]
      simp only [alphaForIdx]
      rw [ByteArray.getElem!_eq_getElem data i hi]
      split <;> rename_i ha
      · rw [ByteArray.get!_eq_getElem!, ByteArray.getElem!_eq_getElem alphas _ ha]
      · rfl
    · generalize hdef :
        ((((acc.push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).r).push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).g).push
          (if h : (data[i]).toNat < entries.size then entries[(data[i]).toNat]
            else { r := 0, g := 0, b := 0 }).b).push
          (if ha : (data[i]).toNat < alphas.size then alphas[(data[i]).toNat] else 255))
        = acc'
      have haccsize : acc'.size = acc.size + 4 := by
        rw [← hdef]; simp only [ByteArray.size_push]
      rw [show acc.size + (k - i) * 4 + 3 = acc'.size + (k - (i + 1)) * 4 + 3 from by omega]
      exact expandPalette_go_a data entries alphas (i + 1) acc' k (by omega) hk
termination_by data.size - i

/-! ## Top-level theorems -/

/-- The alpha extraction function for `expandPalette`. Matches the
    `let alphas := match trns with ...` in the implementation. -/
def expandPaletteAlphas (trns : Option TRNSInfo) : ByteArray :=
  match trns with
  | some (.palette a) => a
  | _ => ByteArray.empty

/-- Output byte at position `4*k` is `plte.entries[data[k]!.toNat].r`. -/
theorem expandPalette_bounded_r (data : ByteArray) (plte : PLTEInfo)
    (trns : Option TRNSInfo)
    (k : Nat) (hk : k < data.size)
    (hbounds : ∀ i, i < data.size → data[i]!.toNat < plte.entries.size) :
    (expandPalette data plte trns)[k * 4]! =
      (plte.entries[data[k]!.toNat]'(hbounds k hk)).r := by
  simp only [expandPalette]
  rw [show k * 4 = 0 + (k - 0) * 4 from by omega]
  exact expandPalette_go_r data plte.entries _ 0 ByteArray.empty k (by omega) hk hbounds

/-- Output byte at position `4*k + 1` is `plte.entries[data[k]!.toNat].g`. -/
theorem expandPalette_bounded_g (data : ByteArray) (plte : PLTEInfo)
    (trns : Option TRNSInfo)
    (k : Nat) (hk : k < data.size)
    (hbounds : ∀ i, i < data.size → data[i]!.toNat < plte.entries.size) :
    (expandPalette data plte trns)[k * 4 + 1]! =
      (plte.entries[data[k]!.toNat]'(hbounds k hk)).g := by
  simp only [expandPalette]
  rw [show k * 4 + 1 = 0 + (k - 0) * 4 + 1 from by omega]
  exact expandPalette_go_g data plte.entries _ 0 ByteArray.empty k (by omega) hk hbounds

/-- Output byte at position `4*k + 2` is `plte.entries[data[k]!.toNat].b`. -/
theorem expandPalette_bounded_b (data : ByteArray) (plte : PLTEInfo)
    (trns : Option TRNSInfo)
    (k : Nat) (hk : k < data.size)
    (hbounds : ∀ i, i < data.size → data[i]!.toNat < plte.entries.size) :
    (expandPalette data plte trns)[k * 4 + 2]! =
      (plte.entries[data[k]!.toNat]'(hbounds k hk)).b := by
  simp only [expandPalette]
  rw [show k * 4 + 2 = 0 + (k - 0) * 4 + 2 from by omega]
  exact expandPalette_go_b data plte.entries _ 0 ByteArray.empty k (by omega) hk hbounds

/-- Output byte at position `4*k + 3` is the alpha from tRNS (or 255). -/
theorem expandPalette_bounded_a (data : ByteArray) (plte : PLTEInfo)
    (trns : Option TRNSInfo)
    (k : Nat) (hk : k < data.size) :
    (expandPalette data plte trns)[k * 4 + 3]! =
      alphaForIdx (expandPaletteAlphas trns) (data[k]!) := by
  simp only [expandPalette, expandPaletteAlphas]
  rw [show k * 4 + 3 = 0 + (k - 0) * 4 + 3 from by omega]
  exact expandPalette_go_a data plte.entries _ 0 ByteArray.empty k (by omega) hk

/-- **Main theorem**: `expandPalette` never reads beyond palette bounds.
    Under the precondition that every index byte is within palette bounds,
    the output is exactly the RGBA expansion of each palette entry — every
    lookup takes the proven-bounds branch, never the black fallback.

    This is stated as byte-level content: for each input index `k`,
    the four output bytes match the palette entry's R, G, B components
    and the tRNS alpha (or 255 if absent). -/
theorem expandPalette_bounded (data : ByteArray) (plte : PLTEInfo)
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
      alphaForIdx (expandPaletteAlphas trns) (data[k]!) :=
  ⟨expandPalette_bounded_r data plte trns k hk hbounds,
   expandPalette_bounded_g data plte trns k hk hbounds,
   expandPalette_bounded_b data plte trns k hk hbounds,
   expandPalette_bounded_a data plte trns k hk⟩

end Png.Spec
