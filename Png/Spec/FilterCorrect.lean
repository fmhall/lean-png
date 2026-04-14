import Png.Native.Filter
import Png.Util.ByteArray

/-!
# PNG Filter Correctness Proofs

Formal proofs that PNG scanline filtering is invertible:
`unfilterRow ft bpp (filterRow ft bpp row prior) prior = row`
-/

namespace Png.Spec.FilterCorrect

open Png.Native.Filter

theorem getByteOr0_eq_getElem! (arr : ByteArray) (i : Nat) :
    getByteOr0 arr i = arr[i]! := by
  simp only [getByteOr0]; split
  case isTrue h => rw [getElem!_pos arr i h]; rfl
  case isFalse h => rw [getElem!_neg arr i h]; rfl

/-! ## None -/

theorem unfilterNone_filterNone (row : ByteArray) :
    unfilterNone (filterNone row) = row := rfl

/-! ## Up filter -/

theorem filterUp_go_size (row prior : ByteArray) (i : Nat) (out : ByteArray) :
    (filterUp.go row prior i out).size = out.size + (row.size - i) := by
  unfold filterUp.go; split; · omega
  · simp only []; rw [filterUp_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

theorem filterUp_go_getElem!_lt (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    j < out.size → (filterUp.go row prior i out)[j]! = out[j]! := by
  intro hj; unfold filterUp.go; split; · rfl
  · simp only []
    let out' := out.push (filterByte (getByteOr0 row i) (getByteOr0 prior i))
    have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
    have ih := filterUp_go_getElem!_lt row prior (i + 1) j out' hj'
    rw [ih]; exact ByteArray.push_getElem!_lt out _ j hj
  termination_by row.size - i

theorem filterUp_go_getElem!_ge (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    out.size = i → j ≥ i → j < row.size →
    (filterUp.go row prior i out)[j]! = filterByte (getByteOr0 row j) (getByteOr0 prior j) := by
  intro hout hji hjrow; unfold filterUp.go; split; · omega
  · simp only []
    by_cases heq : j = i
    · subst heq
      let out' := out.push (filterByte (getByteOr0 row j) (getByteOr0 prior j))
      have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
      have ih := filterUp_go_getElem!_lt row prior (j + 1) j out' hj'
      rw [ih]; subst hout; exact ByteArray.push_getElem!_eq out _
    · let out' := out.push (filterByte (getByteOr0 row i) (getByteOr0 prior i))
      exact filterUp_go_getElem!_ge row prior (i + 1) j out'
        (by simp only [out', ByteArray.size_push]; omega) (by omega) hjrow
  termination_by row.size - i

theorem unfilterUp_go_size (row prior : ByteArray) (i : Nat) (out : ByteArray) :
    (unfilterUp.go row prior i out).size = out.size + (row.size - i) := by
  unfold unfilterUp.go; split; · omega
  · simp only []; rw [unfilterUp_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

theorem unfilterUp_go_getElem!_lt (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    j < out.size → (unfilterUp.go row prior i out)[j]! = out[j]! := by
  intro hj; unfold unfilterUp.go; split; · rfl
  · simp only []
    let out' := out.push (unfilterByte (getByteOr0 row i) (getByteOr0 prior i))
    have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
    have ih := unfilterUp_go_getElem!_lt row prior (i + 1) j out' hj'
    rw [ih]; exact ByteArray.push_getElem!_lt out _ j hj
  termination_by row.size - i

theorem unfilterUp_go_getElem!_ge (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    out.size = i → j ≥ i → j < row.size →
    (unfilterUp.go row prior i out)[j]! = unfilterByte (getByteOr0 row j) (getByteOr0 prior j) := by
  intro hout hji hjrow; unfold unfilterUp.go; split; · omega
  · simp only []
    by_cases heq : j = i
    · subst heq
      let out' := out.push (unfilterByte (getByteOr0 row j) (getByteOr0 prior j))
      have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
      have ih := unfilterUp_go_getElem!_lt row prior (j + 1) j out' hj'
      rw [ih]; subst hout; exact ByteArray.push_getElem!_eq out _
    · let out' := out.push (unfilterByte (getByteOr0 row i) (getByteOr0 prior i))
      exact unfilterUp_go_getElem!_ge row prior (i + 1) j out'
        (by simp only [out', ByteArray.size_push]; omega) (by omega) hjrow
  termination_by row.size - i

theorem filterUp_size (row prior : ByteArray) : (filterUp row prior).size = row.size := by
  simp only [filterUp, filterUp_go_size, ByteArray.size_empty]; omega

theorem unfilterUp_filterUp (row prior : ByteArray) :
    unfilterUp (filterUp row prior) prior = row := by
  apply ByteArray.ext_getElem!
  · simp only [unfilterUp, unfilterUp_go_size, ByteArray.size_empty, filterUp, filterUp_go_size]; omega
  · intro j hj
    have hjrow : j < row.size := by
      simp only [unfilterUp, unfilterUp_go_size, ByteArray.size_empty, filterUp, filterUp_go_size] at hj; omega
    have h1 := unfilterUp_go_getElem!_ge (filterUp.go row prior 0 ByteArray.empty) prior 0 j ByteArray.empty
      (by simp only [ByteArray.size_empty]) (by omega) (by rw [filterUp_go_size, ByteArray.size_empty]; omega)
    have h2 := filterUp_go_getElem!_ge row prior 0 j ByteArray.empty
      (by simp only [ByteArray.size_empty]) (by omega) hjrow
    simp only [unfilterUp, filterUp] at h1 ⊢
    rw [h1, getByteOr0_eq_getElem!, h2]
    simp only [unfilterByte, filterByte]
    rw [UInt8.sub_add_cancel]; exact getByteOr0_eq_getElem! row j

/-! ## Sub filter -/

theorem filterSub_go_size (bpp : Nat) (row : ByteArray) (i : Nat) (out : ByteArray) :
    (filterSub.go bpp row i out).size = out.size + (row.size - i) := by
  unfold filterSub.go; split; · omega
  · simp only []; rw [filterSub_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

theorem filterSub_go_getElem!_lt (bpp : Nat) (row : ByteArray) (i j : Nat) (out : ByteArray) :
    j < out.size → (filterSub.go bpp row i out)[j]! = out[j]! := by
  intro hj; unfold filterSub.go; split; · rfl
  · simp only []
    let out' := out.push (filterByte (getByteOr0 row i) (if i ≥ bpp then getByteOr0 row (i - bpp) else 0))
    have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
    have ih := filterSub_go_getElem!_lt bpp row (i + 1) j out' hj'
    rw [ih]; exact ByteArray.push_getElem!_lt out _ j hj
  termination_by row.size - i

theorem filterSub_go_getElem!_ge (bpp : Nat) (row : ByteArray) (i j : Nat) (out : ByteArray) :
    out.size = i → j ≥ i → j < row.size →
    (filterSub.go bpp row i out)[j]! =
      filterByte (getByteOr0 row j) (if j ≥ bpp then getByteOr0 row (j - bpp) else 0) := by
  intro hout hji hjrow; unfold filterSub.go; split; · omega
  · simp only []
    by_cases heq : j = i
    · subst heq
      let out' := out.push (filterByte (getByteOr0 row j) (if j ≥ bpp then getByteOr0 row (j - bpp) else 0))
      have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
      have ih := filterSub_go_getElem!_lt bpp row (j + 1) j out' hj'
      rw [ih]; subst hout; exact ByteArray.push_getElem!_eq out _
    · let out' := out.push (filterByte (getByteOr0 row i) (if i ≥ bpp then getByteOr0 row (i - bpp) else 0))
      exact filterSub_go_getElem!_ge bpp row (i + 1) j out'
        (by simp only [out', ByteArray.size_push]; omega) (by omega) hjrow
  termination_by row.size - i

theorem unfilterSub_go_size (bpp : Nat) (row : ByteArray) (i : Nat) (out : ByteArray) :
    (unfilterSub.go bpp row i out).size = out.size + (row.size - i) := by
  unfold unfilterSub.go; split; · omega
  · simp only []; rw [unfilterSub_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

theorem unfilterSub_go_getElem!_lt (bpp : Nat) (row : ByteArray) (i j : Nat) (out : ByteArray) :
    j < out.size → (unfilterSub.go bpp row i out)[j]! = out[j]! := by
  intro hj; unfold unfilterSub.go; split; · rfl
  · simp only []
    let out' := out.push (unfilterByte (getByteOr0 row i) (if i ≥ bpp then getByteOr0 out (i - bpp) else 0))
    have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
    have ih := unfilterSub_go_getElem!_lt bpp row (i + 1) j out' hj'
    rw [ih]; exact ByteArray.push_getElem!_lt out _ j hj
  termination_by row.size - i

-- Sub roundtrip: output-dependent. The invariant is that out[k] = origRow[k] for k < i.
-- When unfilterSub reads "left" from out[i - bpp], by the invariant that equals origRow[i - bpp],
-- which is the same value filterSub used. So unfilterByte(filterByte(x, pred), pred) = x.
theorem unfilterSub_go_roundtrip (bpp : Nat) (filtered origRow : ByteArray)
    (i : Nat) (out : ByteArray)
    (hbpp : bpp > 0)
    (hfsize : filtered.size = origRow.size) (hout : out.size = i)
    (hfilt : ∀ k, k < filtered.size →
      filtered[k]! = filterByte (getByteOr0 origRow k) (if k ≥ bpp then getByteOr0 origRow (k - bpp) else 0))
    (hinv : ∀ k, k < i → out[k]! = origRow[k]!) :
    ∀ j, j < origRow.size → (unfilterSub.go bpp filtered i out)[j]! = origRow[j]! := by
  intro j hjrow
  by_cases hji : j < i
  · rw [unfilterSub_go_getElem!_lt bpp filtered i j out (by omega)]; exact hinv j hji
  · unfold unfilterSub.go; split
    · omega
    · rename_i h
      simp only []
      have hleft : (if i ≥ bpp then getByteOr0 out (i - bpp) else (0 : UInt8)) =
          (if i ≥ bpp then getByteOr0 origRow (i - bpp) else 0) := by
        by_cases hge : i ≥ bpp
        · simp only [hge, ↓reduceIte]
          rw [getByteOr0_eq_getElem!, getByteOr0_eq_getElem!]; exact hinv _ (by omega)
        · simp only [hge, ↓reduceIte]
      rw [hleft]
      exact unfilterSub_go_roundtrip bpp filtered origRow (i + 1)
        (out.push (unfilterByte (getByteOr0 filtered i)
          (if i ≥ bpp then getByteOr0 origRow (i - bpp) else 0)))
        hbpp hfsize
        (by simp only [ByteArray.size_push]; omega)
        hfilt
        (fun k hk => by
          by_cases hki : k < i
          · rw [ByteArray.push_getElem!_lt out _ k (by omega)]
            exact hinv k hki
          · have hki_eq : k = i := by omega
            rw [hki_eq, show i = out.size from hout.symm]
            rw [ByteArray.push_getElem!_eq out _]
            rw [show out.size = i from hout]
            rw [getByteOr0_eq_getElem!]
            rw [hfilt i (by omega)]
            simp only [unfilterByte, filterByte]
            rw [UInt8.sub_add_cancel]
            exact getByteOr0_eq_getElem! origRow i)
        j hjrow
  termination_by origRow.size - i

theorem filterSub_size (bpp : Nat) (row : ByteArray) : (filterSub bpp row).size = row.size := by
  simp only [filterSub, filterSub_go_size, ByteArray.size_empty]; omega

theorem unfilterSub_filterSub (bpp : Nat) (row : ByteArray) (hbpp : bpp > 0) :
    unfilterSub bpp (filterSub bpp row) = row := by
  apply ByteArray.ext_getElem!
  · simp only [unfilterSub, unfilterSub_go_size, ByteArray.size_empty, filterSub, filterSub_go_size]; omega
  · intro j hj
    have hfsize := filterSub_size bpp row
    have hjrow : j < row.size := by
      simp only [unfilterSub, unfilterSub_go_size, ByteArray.size_empty, filterSub, filterSub_go_size] at hj; omega
    simp only [unfilterSub, filterSub]
    exact unfilterSub_go_roundtrip bpp _ row 0 ByteArray.empty hbpp hfsize
      (by simp only [ByteArray.size_empty])
      (fun k hk => filterSub_go_getElem!_ge bpp row 0 k ByteArray.empty
        (by simp only [ByteArray.size_empty]) (by omega) (by rw [hfsize] at hk; exact hk))
      (fun _ hk => by omega) j hjrow

/-! ## Average filter -/

-- The predictor for Average uses left (from row or output) and above (from prior).
-- Filter reads left from the input row; unfilter reads from reconstructed output.
-- By the invariant, these are equal, so the predictor values match.

theorem filterAverage_go_size (bpp : Nat) (row prior : ByteArray) (i : Nat) (out : ByteArray) :
    (filterAverage.go bpp row prior i out).size = out.size + (row.size - i) := by
  unfold filterAverage.go; split; · omega
  · simp only []; rw [filterAverage_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

theorem filterAverage_go_getElem!_lt (bpp : Nat) (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    j < out.size → (filterAverage.go bpp row prior i out)[j]! = out[j]! := by
  intro hj; unfold filterAverage.go; split; · rfl
  · simp only []
    let left := if i ≥ bpp then getByteOr0 row (i - bpp) else 0
    let pred := ((left.toNat + (getByteOr0 prior i).toNat) / 2).toUInt8
    let out' := out.push (filterByte (getByteOr0 row i) pred)
    have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
    have ih := filterAverage_go_getElem!_lt bpp row prior (i + 1) j out' hj'
    rw [ih]; exact ByteArray.push_getElem!_lt out _ j hj
  termination_by row.size - i

theorem filterAverage_go_getElem!_ge (bpp : Nat) (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    out.size = i → j ≥ i → j < row.size →
    (filterAverage.go bpp row prior i out)[j]! =
      filterByte (getByteOr0 row j)
        (((if j ≥ bpp then getByteOr0 row (j - bpp) else (0 : UInt8)).toNat +
          (getByteOr0 prior j).toNat) / 2).toUInt8 := by
  intro hout hji hjrow; unfold filterAverage.go; split; · omega
  · simp only []
    by_cases heq : j = i
    · subst heq
      let pred := (((if j ≥ bpp then getByteOr0 row (j - bpp) else (0 : UInt8)).toNat +
        (getByteOr0 prior j).toNat) / 2).toUInt8
      let out' := out.push (filterByte (getByteOr0 row j) pred)
      have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
      have ih := filterAverage_go_getElem!_lt bpp row prior (j + 1) j out' hj'
      rw [ih]; subst hout; exact ByteArray.push_getElem!_eq out _
    · let left := if i ≥ bpp then getByteOr0 row (i - bpp) else 0
      let pred := ((left.toNat + (getByteOr0 prior i).toNat) / 2).toUInt8
      let out' := out.push (filterByte (getByteOr0 row i) pred)
      exact filterAverage_go_getElem!_ge bpp row prior (i + 1) j out'
        (by simp only [out', ByteArray.size_push]; omega) (by omega) hjrow
  termination_by row.size - i

theorem unfilterAverage_go_size (bpp : Nat) (row prior : ByteArray) (i : Nat) (out : ByteArray) :
    (unfilterAverage.go bpp row prior i out).size = out.size + (row.size - i) := by
  unfold unfilterAverage.go; split; · omega
  · simp only []; rw [unfilterAverage_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

theorem unfilterAverage_go_getElem!_lt (bpp : Nat) (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    j < out.size → (unfilterAverage.go bpp row prior i out)[j]! = out[j]! := by
  intro hj; unfold unfilterAverage.go; split; · rfl
  · simp only []
    let left := if i ≥ bpp then getByteOr0 out (i - bpp) else 0
    let pred := ((left.toNat + (getByteOr0 prior i).toNat) / 2).toUInt8
    let out' := out.push (unfilterByte (getByteOr0 row i) pred)
    have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
    have ih := unfilterAverage_go_getElem!_lt bpp row prior (i + 1) j out' hj'
    rw [ih]; exact ByteArray.push_getElem!_lt out _ j hj
  termination_by row.size - i

-- Average roundtrip with output-dependency invariant (same pattern as Sub)
theorem unfilterAverage_go_roundtrip (bpp : Nat) (filtered origRow prior : ByteArray)
    (i : Nat) (out : ByteArray)
    (hbpp : bpp > 0)
    (hfsize : filtered.size = origRow.size) (hout : out.size = i)
    (hfilt : ∀ k, k < filtered.size →
      filtered[k]! = filterByte (getByteOr0 origRow k)
        (((if k ≥ bpp then getByteOr0 origRow (k - bpp) else (0 : UInt8)).toNat +
          (getByteOr0 prior k).toNat) / 2).toUInt8)
    (hinv : ∀ k, k < i → out[k]! = origRow[k]!) :
    ∀ j, j < origRow.size → (unfilterAverage.go bpp filtered prior i out)[j]! = origRow[j]! := by
  intro j hjrow
  by_cases hji : j < i
  · rw [unfilterAverage_go_getElem!_lt bpp filtered prior i j out (by omega)]; exact hinv j hji
  · unfold unfilterAverage.go; split
    · omega
    · rename_i h
      simp only []
      have hleft : (if i ≥ bpp then getByteOr0 out (i - bpp) else (0 : UInt8)) =
          (if i ≥ bpp then getByteOr0 origRow (i - bpp) else 0) := by
        by_cases hge : i ≥ bpp
        · simp only [hge, ↓reduceIte]
          rw [getByteOr0_eq_getElem!, getByteOr0_eq_getElem!]; exact hinv _ (by omega)
        · simp only [hge, ↓reduceIte]
      rw [hleft]
      exact unfilterAverage_go_roundtrip bpp filtered origRow prior (i + 1)
        (out.push (unfilterByte (getByteOr0 filtered i)
          (((if i ≥ bpp then getByteOr0 origRow (i - bpp) else (0 : UInt8)).toNat +
            (getByteOr0 prior i).toNat) / 2).toUInt8))
        hbpp hfsize
        (by simp only [ByteArray.size_push]; omega)
        hfilt
        (fun k hk => by
          by_cases hki : k < i
          · rw [ByteArray.push_getElem!_lt out _ k (by omega)]
            exact hinv k hki
          · have hki_eq : k = i := by omega
            rw [hki_eq, show i = out.size from hout.symm]
            rw [ByteArray.push_getElem!_eq out _]
            rw [show out.size = i from hout]
            rw [getByteOr0_eq_getElem!]
            rw [hfilt i (by omega)]
            simp only [unfilterByte, filterByte]
            rw [UInt8.sub_add_cancel]
            exact getByteOr0_eq_getElem! origRow i)
        j hjrow
  termination_by origRow.size - i

theorem filterAverage_size (bpp : Nat) (row prior : ByteArray) :
    (filterAverage bpp row prior).size = row.size := by
  simp only [filterAverage, filterAverage_go_size, ByteArray.size_empty]; omega

theorem unfilterAverage_filterAverage (bpp : Nat) (row prior : ByteArray) (hbpp : bpp > 0) :
    unfilterAverage bpp (filterAverage bpp row prior) prior = row := by
  apply ByteArray.ext_getElem!
  · simp only [unfilterAverage, unfilterAverage_go_size, ByteArray.size_empty,
               filterAverage, filterAverage_go_size]; omega
  · intro j hj
    have hfsize := filterAverage_size bpp row prior
    have hjrow : j < row.size := by
      simp only [unfilterAverage, unfilterAverage_go_size, ByteArray.size_empty,
                 filterAverage, filterAverage_go_size] at hj; omega
    simp only [unfilterAverage, filterAverage]
    exact unfilterAverage_go_roundtrip bpp _ row prior 0 ByteArray.empty hbpp hfsize
      (by simp only [ByteArray.size_empty])
      (fun k hk => filterAverage_go_getElem!_ge bpp row prior 0 k ByteArray.empty
        (by simp only [ByteArray.size_empty]) (by omega) (by rw [hfsize] at hk; exact hk))
      (fun _ hk => by omega) j hjrow

/-! ## Paeth filter -/

-- Paeth follows exactly the same pattern as Sub/Average.
-- The predictor uses left (from row/output), above (from prior), and upperLeft (from prior).
-- Only "left" differs between filter and unfilter; by the invariant they're equal.

theorem filterPaeth_go_size (bpp : Nat) (row prior : ByteArray) (i : Nat) (out : ByteArray) :
    (filterPaeth.go bpp row prior i out).size = out.size + (row.size - i) := by
  unfold filterPaeth.go; split; · omega
  · simp only []; rw [filterPaeth_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

theorem filterPaeth_go_getElem!_lt (bpp : Nat) (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    j < out.size → (filterPaeth.go bpp row prior i out)[j]! = out[j]! := by
  intro hj; unfold filterPaeth.go; split; · rfl
  · simp only []
    let left := if i ≥ bpp then getByteOr0 row (i - bpp) else 0
    let above := getByteOr0 prior i
    let upperLeft := if i ≥ bpp then getByteOr0 prior (i - bpp) else 0
    let out' := out.push (filterByte (getByteOr0 row i) (paethPredictor left above upperLeft))
    have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
    have ih := filterPaeth_go_getElem!_lt bpp row prior (i + 1) j out' hj'
    rw [ih]; exact ByteArray.push_getElem!_lt out _ j hj
  termination_by row.size - i

theorem filterPaeth_go_getElem!_ge (bpp : Nat) (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    out.size = i → j ≥ i → j < row.size →
    (filterPaeth.go bpp row prior i out)[j]! =
      filterByte (getByteOr0 row j)
        (paethPredictor
          (if j ≥ bpp then getByteOr0 row (j - bpp) else 0)
          (getByteOr0 prior j)
          (if j ≥ bpp then getByteOr0 prior (j - bpp) else 0)) := by
  intro hout hji hjrow; unfold filterPaeth.go; split; · omega
  · simp only []
    by_cases heq : j = i
    · subst heq
      let left := if j ≥ bpp then getByteOr0 row (j - bpp) else 0
      let above := getByteOr0 prior j
      let upperLeft := if j ≥ bpp then getByteOr0 prior (j - bpp) else 0
      let out' := out.push (filterByte (getByteOr0 row j) (paethPredictor left above upperLeft))
      have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
      have ih := filterPaeth_go_getElem!_lt bpp row prior (j + 1) j out' hj'
      rw [ih]; subst hout; exact ByteArray.push_getElem!_eq out _
    · let left := if i ≥ bpp then getByteOr0 row (i - bpp) else 0
      let above := getByteOr0 prior i
      let upperLeft := if i ≥ bpp then getByteOr0 prior (i - bpp) else 0
      let out' := out.push (filterByte (getByteOr0 row i) (paethPredictor left above upperLeft))
      exact filterPaeth_go_getElem!_ge bpp row prior (i + 1) j out'
        (by simp only [out', ByteArray.size_push]; omega) (by omega) hjrow
  termination_by row.size - i

theorem unfilterPaeth_go_size (bpp : Nat) (row prior : ByteArray) (i : Nat) (out : ByteArray) :
    (unfilterPaeth.go bpp row prior i out).size = out.size + (row.size - i) := by
  unfold unfilterPaeth.go; split; · omega
  · simp only []; rw [unfilterPaeth_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

theorem unfilterPaeth_go_getElem!_lt (bpp : Nat) (row prior : ByteArray) (i j : Nat) (out : ByteArray) :
    j < out.size → (unfilterPaeth.go bpp row prior i out)[j]! = out[j]! := by
  intro hj; unfold unfilterPaeth.go; split; · rfl
  · simp only []
    let left := if i ≥ bpp then getByteOr0 out (i - bpp) else 0
    let above := getByteOr0 prior i
    let upperLeft := if i ≥ bpp then getByteOr0 prior (i - bpp) else 0
    let out' := out.push (unfilterByte (getByteOr0 row i) (paethPredictor left above upperLeft))
    have hj' : j < out'.size := by simp only [out', ByteArray.size_push]; omega
    have ih := unfilterPaeth_go_getElem!_lt bpp row prior (i + 1) j out' hj'
    rw [ih]; exact ByteArray.push_getElem!_lt out _ j hj
  termination_by row.size - i

-- Paeth roundtrip with output-dependency invariant
theorem unfilterPaeth_go_roundtrip (bpp : Nat) (filtered origRow prior : ByteArray)
    (i : Nat) (out : ByteArray)
    (hbpp : bpp > 0)
    (hfsize : filtered.size = origRow.size) (hout : out.size = i)
    (hfilt : ∀ k, k < filtered.size →
      filtered[k]! = filterByte (getByteOr0 origRow k)
        (paethPredictor
          (if k ≥ bpp then getByteOr0 origRow (k - bpp) else 0)
          (getByteOr0 prior k)
          (if k ≥ bpp then getByteOr0 prior (k - bpp) else 0)))
    (hinv : ∀ k, k < i → out[k]! = origRow[k]!) :
    ∀ j, j < origRow.size → (unfilterPaeth.go bpp filtered prior i out)[j]! = origRow[j]! := by
  intro j hjrow
  by_cases hji : j < i
  · rw [unfilterPaeth_go_getElem!_lt bpp filtered prior i j out (by omega)]; exact hinv j hji
  · unfold unfilterPaeth.go; split
    · omega
    · rename_i h
      simp only []
      have hleft : (if i ≥ bpp then getByteOr0 out (i - bpp) else (0 : UInt8)) =
          (if i ≥ bpp then getByteOr0 origRow (i - bpp) else 0) := by
        by_cases hge : i ≥ bpp
        · simp only [hge, ↓reduceIte]
          rw [getByteOr0_eq_getElem!, getByteOr0_eq_getElem!]; exact hinv _ (by omega)
        · simp only [hge, ↓reduceIte]
      rw [hleft]
      exact unfilterPaeth_go_roundtrip bpp filtered origRow prior (i + 1)
        (out.push (unfilterByte (getByteOr0 filtered i)
          (paethPredictor
            (if i ≥ bpp then getByteOr0 origRow (i - bpp) else 0)
            (getByteOr0 prior i)
            (if i ≥ bpp then getByteOr0 prior (i - bpp) else 0))))
        hbpp hfsize
        (by simp only [ByteArray.size_push]; omega)
        hfilt
        (fun k hk => by
          by_cases hki : k < i
          · rw [ByteArray.push_getElem!_lt out _ k (by omega)]
            exact hinv k hki
          · have hki_eq : k = i := by omega
            rw [hki_eq, show i = out.size from hout.symm]
            rw [ByteArray.push_getElem!_eq out _]
            rw [show out.size = i from hout]
            rw [getByteOr0_eq_getElem!]
            rw [hfilt i (by omega)]
            simp only [unfilterByte, filterByte]
            rw [UInt8.sub_add_cancel]
            exact getByteOr0_eq_getElem! origRow i)
        j hjrow
  termination_by origRow.size - i

theorem filterPaeth_size (bpp : Nat) (row prior : ByteArray) :
    (filterPaeth bpp row prior).size = row.size := by
  simp only [filterPaeth, filterPaeth_go_size, ByteArray.size_empty]; omega

theorem unfilterPaeth_filterPaeth (bpp : Nat) (row prior : ByteArray) (hbpp : bpp > 0) :
    unfilterPaeth bpp (filterPaeth bpp row prior) prior = row := by
  apply ByteArray.ext_getElem!
  · simp only [unfilterPaeth, unfilterPaeth_go_size, ByteArray.size_empty,
               filterPaeth, filterPaeth_go_size]; omega
  · intro j hj
    have hfsize := filterPaeth_size bpp row prior
    have hjrow : j < row.size := by
      simp only [unfilterPaeth, unfilterPaeth_go_size, ByteArray.size_empty,
                 filterPaeth, filterPaeth_go_size] at hj; omega
    simp only [unfilterPaeth, filterPaeth]
    exact unfilterPaeth_go_roundtrip bpp _ row prior 0 ByteArray.empty hbpp hfsize
      (by simp only [ByteArray.size_empty])
      (fun k hk => filterPaeth_go_getElem!_ge bpp row prior 0 k ByteArray.empty
        (by simp only [ByteArray.size_empty]) (by omega) (by rw [hfsize] at hk; exact hk))
      (fun _ hk => by omega) j hjrow

/-! ## Top-level roundtrip -/

theorem filterRow_size (ft : FilterType) (bpp : Nat) (row prior : ByteArray) :
    (filterRow ft bpp row prior).size = row.size := by
  cases ft <;> simp only [filterRow, filterNone, filterUp_size, filterSub_size,
    filterAverage_size, filterPaeth_size]

theorem unfilterRow_filterRow (ft : FilterType) (bpp : Nat) (row prior : ByteArray)
    (hbpp : bpp > 0) :
    unfilterRow ft bpp (filterRow ft bpp row prior) prior = row := by
  cases ft <;> simp only [filterRow, unfilterRow, unfilterNone_filterNone,
    unfilterSub_filterSub bpp row hbpp, unfilterUp_filterUp,
    unfilterAverage_filterAverage bpp row prior hbpp,
    unfilterPaeth_filterPaeth bpp row prior hbpp]

end Png.Spec.FilterCorrect
