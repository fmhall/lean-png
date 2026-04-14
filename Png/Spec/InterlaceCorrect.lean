import Png.Native.Interlace

/-!
# Adam7 Interlace Correctness Proofs

Specification theorems for Adam7 interlacing. These state the key
properties that ensure correctness:

1. **Coverage**: every pixel in the full image appears in exactly one pass
2. **Coordinate roundtrips**: `fromSubRow ∘ toSubRow = id` (and columns)
3. **Scatter/extract roundtrip**: `adam7Scatter (adam7Extract image) = image`
4. **Total pixel count**: sum of pass dimensions = full dimensions
5. **Dimension bounds**: sub-image dimensions ≤ full image dimensions

Proofs are sorry placeholders for now.
-/

namespace Png.Spec.InterlaceCorrect

open Png.Native.Interlace

/-! ## Dimension Properties -/

/-- Sub-image width for any pass is at most the full image width. -/
theorem passWidth_le (p : Fin 7) (width : Nat) : passWidth p width ≤ width := by
  unfold passWidth
  split
  · omega
  · have hcs := adam7ColStride_pos p
    have hcsl := adam7ColStart_lt_stride p
    match p with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
      simp only [adam7ColStart, adam7ColStride] at * <;> omega

/-- Sub-image height for any pass is at most the full image height. -/
theorem passHeight_le (p : Fin 7) (height : Nat) : passHeight p height ≤ height := by
  unfold passHeight
  split
  · omega
  · have hrs := adam7RowStride_pos p
    have hrsl := adam7RowStart_lt_stride p
    match p with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
      simp only [adam7RowStart, adam7RowStride] at * <;> omega

/-- Pass width is 0 when full image width is 0. -/
theorem passWidth_zero (p : Fin 7) : passWidth p 0 = 0 := by
  simp only [passWidth, adam7ColStart, Nat.zero_le, ↓reduceIte]

/-- Pass height is 0 when full image height is 0. -/
theorem passHeight_zero (p : Fin 7) : passHeight p 0 = 0 := by
  simp only [passHeight, adam7RowStart, Nat.zero_le, ↓reduceIte]

/-! ## Coordinate Roundtrips -/

/-- Converting a sub-image row back to a full-image row and then to a
    sub-image row yields the original sub-image row. -/
theorem toSubRow_fromSubRow (p : Fin 7) (sr : Nat) :
    toSubRow p (fromSubRow p sr) = sr := by
  simp only [toSubRow, fromSubRow]
  have hpos := adam7RowStride_pos p
  rw [Nat.add_sub_cancel, Nat.mul_div_cancel _ hpos]

/-- Converting a sub-image column back to a full-image column and then
    to a sub-image column yields the original sub-image column. -/
theorem toSubCol_fromSubCol (p : Fin 7) (sc : Nat) :
    toSubCol p (fromSubCol p sc) = sc := by
  simp only [toSubCol, fromSubCol]
  have hpos := adam7ColStride_pos p
  rw [Nat.add_sub_cancel, Nat.mul_div_cancel _ hpos]

/-- Converting a full-image row to a sub-image row and back yields the
    original row, provided the row belongs to this pass. -/
theorem fromSubRow_toSubRow (p : Fin 7) (r : Nat)
    (h : r % adam7RowStride p = adam7RowStart p) :
    fromSubRow p (toSubRow p r) = r := by
  simp only [fromSubRow, toSubRow]
  have hpos := adam7RowStride_pos p
  have hstart_le : adam7RowStart p ≤ r := h ▸ Nat.mod_le r (adam7RowStride p)
  -- r = stride * (r / stride) + r % stride = stride * (r / stride) + start
  -- r - start = stride * (r / stride), so (r - start) / stride * stride = r - start
  have hdvd : adam7RowStride p ∣ (r - adam7RowStart p) := by
    have hmod := Nat.div_add_mod r (adam7RowStride p)
    rw [h] at hmod
    -- hmod : adam7RowStride p * (r / adam7RowStride p) + adam7RowStart p = r
    exact ⟨r / adam7RowStride p, Nat.sub_eq_of_eq_add hmod.symm⟩
  rw [Nat.div_mul_cancel hdvd]
  omega

/-- Converting a full-image column to a sub-image column and back yields the
    original column, provided the column belongs to this pass. -/
theorem fromSubCol_toSubCol (p : Fin 7) (c : Nat)
    (h : c % adam7ColStride p = adam7ColStart p) :
    fromSubCol p (toSubCol p c) = c := by
  simp only [fromSubCol, toSubCol]
  have hpos := adam7ColStride_pos p
  have hstart_le : adam7ColStart p ≤ c := h ▸ Nat.mod_le c (adam7ColStride p)
  have hdvd : adam7ColStride p ∣ (c - adam7ColStart p) := by
    have hmod := Nat.div_add_mod c (adam7ColStride p)
    rw [h] at hmod
    exact ⟨c / adam7ColStride p, Nat.sub_eq_of_eq_add hmod.symm⟩
  rw [Nat.div_mul_cancel hdvd]
  omega

/-! ## Coverage: Every pixel appears in exactly one pass -/

/-- Determine which pass a pixel belongs to, based on its row and column
    modular residues within the 8x8 Adam7 tile. -/
def adam7PassOf (rmod8 : Fin 8) (cmod8 : Fin 8) : Option (Fin 7) :=
  match rmod8, cmod8 with
  | ⟨0, _⟩, ⟨0, _⟩ => some ⟨0, by omega⟩  -- pass 1
  | ⟨0, _⟩, ⟨4, _⟩ => some ⟨1, by omega⟩  -- pass 2
  | ⟨4, _⟩, ⟨0, _⟩ => some ⟨2, by omega⟩  -- pass 3
  | ⟨4, _⟩, ⟨4, _⟩ => some ⟨2, by omega⟩  -- pass 3
  | ⟨0, _⟩, ⟨2, _⟩ => some ⟨3, by omega⟩  -- pass 4
  | ⟨0, _⟩, ⟨6, _⟩ => some ⟨3, by omega⟩  -- pass 4
  | ⟨4, _⟩, ⟨2, _⟩ => some ⟨3, by omega⟩  -- pass 4
  | ⟨4, _⟩, ⟨6, _⟩ => some ⟨3, by omega⟩  -- pass 4
  | ⟨2, _⟩, ⟨0, _⟩ => some ⟨4, by omega⟩  -- pass 5
  | ⟨2, _⟩, ⟨2, _⟩ => some ⟨4, by omega⟩  -- pass 5
  | ⟨2, _⟩, ⟨4, _⟩ => some ⟨4, by omega⟩  -- pass 5
  | ⟨2, _⟩, ⟨6, _⟩ => some ⟨4, by omega⟩  -- pass 5
  | ⟨6, _⟩, ⟨0, _⟩ => some ⟨4, by omega⟩  -- pass 5
  | ⟨6, _⟩, ⟨2, _⟩ => some ⟨4, by omega⟩  -- pass 5
  | ⟨6, _⟩, ⟨4, _⟩ => some ⟨4, by omega⟩  -- pass 5
  | ⟨6, _⟩, ⟨6, _⟩ => some ⟨4, by omega⟩  -- pass 5
  | ⟨0, _⟩, ⟨1, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨0, _⟩, ⟨3, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨0, _⟩, ⟨5, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨0, _⟩, ⟨7, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨2, _⟩, ⟨1, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨2, _⟩, ⟨3, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨2, _⟩, ⟨5, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨2, _⟩, ⟨7, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨4, _⟩, ⟨1, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨4, _⟩, ⟨3, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨4, _⟩, ⟨5, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨4, _⟩, ⟨7, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨6, _⟩, ⟨1, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨6, _⟩, ⟨3, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨6, _⟩, ⟨5, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | ⟨6, _⟩, ⟨7, _⟩ => some ⟨5, by omega⟩  -- pass 6
  | _, _ => some ⟨6, by omega⟩              -- pass 7 (odd rows)

/-- Every pixel in the full image belongs to exactly one Adam7 pass.
    Given any pixel at (r, c), there exists a unique pass `p` such that
    `r % rowStride p = rowStart p` and `c % colStride p = colStart p`. -/
private theorem adam7_coverage_aux (rm cm : Fin 8) :
    ∃ (p : Fin 7), rm.val % adam7RowStride p = adam7RowStart p ∧
                    cm.val % adam7ColStride p = adam7ColStart p := by
  revert rm cm; decide

theorem adam7_coverage (r c : Nat) :
    ∃ (p : Fin 7), r % adam7RowStride p = adam7RowStart p ∧
                    c % adam7ColStride p = adam7ColStart p := by
  have ⟨p, hp⟩ := adam7_coverage_aux ⟨r % 8, Nat.mod_lt r (by omega)⟩
                                       ⟨c % 8, Nat.mod_lt c (by omega)⟩
  refine ⟨p, ?_, ?_⟩
  · match p with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ =>
      simp only [adam7RowStride, adam7RowStart] at hp ⊢; omega
    | ⟨3, _⟩ | ⟨4, _⟩ =>
      simp only [adam7RowStride, adam7RowStart] at hp ⊢; omega
    | ⟨5, _⟩ | ⟨6, _⟩ =>
      simp only [adam7RowStride, adam7RowStart] at hp ⊢; omega
  · match p with
    | ⟨0, _⟩ | ⟨1, _⟩ =>
      simp only [adam7ColStride, adam7ColStart] at hp ⊢; omega
    | ⟨2, _⟩ | ⟨3, _⟩ =>
      simp only [adam7ColStride, adam7ColStart] at hp ⊢; omega
    | ⟨4, _⟩ | ⟨5, _⟩ =>
      simp only [adam7ColStride, adam7ColStart] at hp ⊢; omega
    | ⟨6, _⟩ =>
      simp only [adam7ColStride, adam7ColStart] at hp ⊢; omega

/-- Different passes have disjoint pixel sets: if a pixel matches pass `p`,
    it does not match any other pass `q ≠ p`. -/
private theorem adam7_uniqueness_aux (rm cm : Fin 8) (p q : Fin 7)
    (hp : rm.val % adam7RowStride p = adam7RowStart p ∧ cm.val % adam7ColStride p = adam7ColStart p)
    (hq : rm.val % adam7RowStride q = adam7RowStart q ∧ cm.val % adam7ColStride q = adam7ColStart q) :
    p = q := by
  revert rm cm p q; decide

theorem adam7_uniqueness (r c : Nat) (p q : Fin 7)
    (hp : r % adam7RowStride p = adam7RowStart p ∧ c % adam7ColStride p = adam7ColStart p)
    (hq : r % adam7RowStride q = adam7RowStart q ∧ c % adam7ColStride q = adam7ColStart q) :
    p = q := by
  have hr8 := Nat.mod_lt r (by omega : 0 < 8)
  have hc8 := Nat.mod_lt c (by omega : 0 < 8)
  apply adam7_uniqueness_aux ⟨r % 8, hr8⟩ ⟨c % 8, hc8⟩
  · constructor
    · match p with
      | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ =>
        simp only [adam7RowStride, adam7RowStart] at hp ⊢; omega
      | ⟨3, _⟩ | ⟨4, _⟩ =>
        simp only [adam7RowStride, adam7RowStart] at hp ⊢; omega
      | ⟨5, _⟩ | ⟨6, _⟩ =>
        simp only [adam7RowStride, adam7RowStart] at hp ⊢; omega
    · match p with
      | ⟨0, _⟩ | ⟨1, _⟩ =>
        simp only [adam7ColStride, adam7ColStart] at hp ⊢; omega
      | ⟨2, _⟩ | ⟨3, _⟩ =>
        simp only [adam7ColStride, adam7ColStart] at hp ⊢; omega
      | ⟨4, _⟩ | ⟨5, _⟩ =>
        simp only [adam7ColStride, adam7ColStart] at hp ⊢; omega
      | ⟨6, _⟩ =>
        simp only [adam7ColStride, adam7ColStart] at hp ⊢; omega
  · constructor
    · match q with
      | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ =>
        simp only [adam7RowStride, adam7RowStart] at hq ⊢; omega
      | ⟨3, _⟩ | ⟨4, _⟩ =>
        simp only [adam7RowStride, adam7RowStart] at hq ⊢; omega
      | ⟨5, _⟩ | ⟨6, _⟩ =>
        simp only [adam7RowStride, adam7RowStart] at hq ⊢; omega
    · match q with
      | ⟨0, _⟩ | ⟨1, _⟩ =>
        simp only [adam7ColStride, adam7ColStart] at hq ⊢; omega
      | ⟨2, _⟩ | ⟨3, _⟩ =>
        simp only [adam7ColStride, adam7ColStart] at hq ⊢; omega
      | ⟨4, _⟩ | ⟨5, _⟩ =>
        simp only [adam7ColStride, adam7ColStart] at hq ⊢; omega
      | ⟨6, _⟩ =>
        simp only [adam7ColStride, adam7ColStart] at hq ⊢; omega

/-! ## Scatter/Extract Roundtrip -/

/-- Scattering the extracted sub-images back into a full image
    recovers the original image. -/
-- This theorem requires characterizing the byte-level behavior of
-- extractPass.go and scatterPass.go composed together. The proof
-- needs auxiliary size and content lemmas for both recursive functions.
-- Leaving as sorry — it is the composition theorem requiring substantial
-- proof engineering comparable to the filter roundtrip proofs.
theorem adam7Scatter_extract (image : PngImage)
    (hvalid : image.isValid = true) :
    adam7Scatter (adam7Extract image) image.width.toNat image.height.toNat = image := by
  sorry

/-! ## Total Pixel Count Conservation -/

/-- Helper: sum of pass dimensions over all 7 passes. -/
def totalPassPixels (width height : Nat) : Nat :=
  go 0 0
where
  go (p : Nat) (acc : Nat) : Nat :=
    if h : p < 7 then
      go (p + 1) (acc + passWidth ⟨p, h⟩ width * passHeight ⟨p, h⟩ height)
    else acc
  termination_by 7 - p

/-- The sum of pixels across all 7 Adam7 passes equals the total
    number of pixels in the full image. -/
-- Step lemma: passWidth p (w + colStride p) = passWidth p w + 1 when w > colStart p
-- passWidth step lemma
private theorem passWidth_add_stride (p : Fin 7) (w : Nat) (hw : w > adam7ColStart p) :
    passWidth p (w + adam7ColStride p) = passWidth p w + 1 := by
  have hcs := adam7ColStride_pos p
  simp only [passWidth]
  have : ¬(w + adam7ColStride p ≤ adam7ColStart p) := by omega
  have : ¬(w ≤ adam7ColStart p) := by omega
  simp only [*, ↓reduceIte]
  have key : w + adam7ColStride p - adam7ColStart p + adam7ColStride p - 1 =
             (w - adam7ColStart p + adam7ColStride p - 1) + adam7ColStride p := by omega
  rw [key, Nat.add_div_right _ hcs]

-- passHeight step lemma
private theorem passHeight_add_stride (p : Fin 7) (h : Nat) (hh : h > adam7RowStart p) :
    passHeight p (h + adam7RowStride p) = passHeight p h + 1 := by
  have hrs := adam7RowStride_pos p
  simp only [passHeight]
  have : ¬(h + adam7RowStride p ≤ adam7RowStart p) := by omega
  have : ¬(h ≤ adam7RowStart p) := by omega
  simp only [*, ↓reduceIte]
  have key : h + adam7RowStride p - adam7RowStart p + adam7RowStride p - 1 =
             (h - adam7RowStart p + adam7RowStride p - 1) + adam7RowStride p := by omega
  rw [key, Nat.add_div_right _ hrs]

-- Prove for small dimensions by decide

-- Key lemma: passWidth expressed with Nat.div_add_mod
private theorem passWidth_formula (p : Fin 7) (w : Nat) :
    passWidth p w = if w ≤ adam7ColStart p then 0
    else (w - adam7ColStart p - 1) / adam7ColStride p + 1 := by
  simp only [passWidth]
  split
  · rfl
  · rename_i h
    have hcs := adam7ColStride_pos p
    have : w - adam7ColStart p + adam7ColStride p - 1 =
           (w - adam7ColStart p - 1) + adam7ColStride p := by omega
    rw [this, Nat.add_div_right _ hcs]

private theorem passHeight_formula (p : Fin 7) (h : Nat) :
    passHeight p h = if h ≤ adam7RowStart p then 0
    else (h - adam7RowStart p - 1) / adam7RowStride p + 1 := by
  simp only [passHeight]
  split
  · rfl
  · rename_i hh
    have hrs := adam7RowStride_pos p
    have : h - adam7RowStart p + adam7RowStride p - 1 =
           (h - adam7RowStart p - 1) + adam7RowStride p := by omega
    rw [this, Nat.add_div_right _ hrs]

-- Explicit computable version that avoids WF recursion
private def totalPassPixelsDirect (w h : Nat) : Nat :=
  passWidth ⟨0, by omega⟩ w * passHeight ⟨0, by omega⟩ h +
  passWidth ⟨1, by omega⟩ w * passHeight ⟨1, by omega⟩ h +
  passWidth ⟨2, by omega⟩ w * passHeight ⟨2, by omega⟩ h +
  passWidth ⟨3, by omega⟩ w * passHeight ⟨3, by omega⟩ h +
  passWidth ⟨4, by omega⟩ w * passHeight ⟨4, by omega⟩ h +
  passWidth ⟨5, by omega⟩ w * passHeight ⟨5, by omega⟩ h +
  passWidth ⟨6, by omega⟩ w * passHeight ⟨6, by omega⟩ h

-- Bridge: totalPassPixels = totalPassPixelsDirect
-- We prove this by observing both compute the same thing
private theorem totalPassPixels_eq_direct (w h : Nat) :
    totalPassPixels w h = totalPassPixelsDirect w h := by
  simp only [totalPassPixels, totalPassPixelsDirect]
  unfold totalPassPixels.go; simp only [show (0 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold totalPassPixels.go; simp only [show (1 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold totalPassPixels.go; simp only [show (2 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold totalPassPixels.go; simp only [show (3 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold totalPassPixels.go; simp only [show (4 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold totalPassPixels.go; simp only [show (5 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold totalPassPixels.go; simp only [show (6 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold totalPassPixels.go; simp only [show ¬(7 : Nat) < 7 from by omega, ↓reduceDIte]
  -- Both sides differ only in leading `0 +` — simp removes it
  simp only [Nat.zero_add]

-- Express passWidth/passHeight as linear functions for w = 8*q + r
private theorem passWidth_linear (p : Fin 7) (q : Nat) (rw : Fin 8) :
    passWidth p (8 * q + rw.val) = (8 / adam7ColStride p) * q + passWidth p rw.val := by
  match p with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
    simp only [passWidth, adam7ColStart, adam7ColStride]
    have hr := rw.isLt
    split <;> split <;> omega

private theorem passHeight_linear (p : Fin 7) (q : Nat) (rh : Fin 8) :
    passHeight p (8 * q + rh.val) = (8 / adam7RowStride p) * q + passHeight p rh.val := by
  match p with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
    simp only [passHeight, adam7RowStart, adam7RowStride]
    have hr := rh.isLt
    split <;> split <;> omega

-- Now prove for small residues using decide
private theorem totalPassPixelsDirect_small (rw rh : Fin 8) :
    totalPassPixelsDirect rw.val rh.val = rw.val * rh.val := by
  revert rw rh; decide

-- Helper: the linear identity for a specific residue pair
-- After passWidth_linear and passHeight_linear, the identity is polynomial in qw, qh
-- with concrete small coefficients
private theorem totalPassPixelsDirect_linear_aux (qw qh : Nat) (rw rh : Fin 8) :
    -- LHS after applying linearity:
    (1 * qw + passWidth ⟨0, by omega⟩ rw.val) * (1 * qh + passHeight ⟨0, by omega⟩ rh.val) +
    (1 * qw + passWidth ⟨1, by omega⟩ rw.val) * (1 * qh + passHeight ⟨1, by omega⟩ rh.val) +
    (2 * qw + passWidth ⟨2, by omega⟩ rw.val) * (1 * qh + passHeight ⟨2, by omega⟩ rh.val) +
    (2 * qw + passWidth ⟨3, by omega⟩ rw.val) * (2 * qh + passHeight ⟨3, by omega⟩ rh.val) +
    (4 * qw + passWidth ⟨4, by omega⟩ rw.val) * (2 * qh + passHeight ⟨4, by omega⟩ rh.val) +
    (4 * qw + passWidth ⟨5, by omega⟩ rw.val) * (4 * qh + passHeight ⟨5, by omega⟩ rh.val) +
    (8 * qw + passWidth ⟨6, by omega⟩ rw.val) * (4 * qh + passHeight ⟨6, by omega⟩ rh.val) =
    (8 * qw + rw.val) * (8 * qh + rh.val) := by
  -- The passWidth/passHeight values for Fin 8 inputs are concrete; decide will compute them
  -- Then grind handles the polynomial identity
  match rw, rh with
  | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩ | ⟨0, _⟩, ⟨3, _⟩ | ⟨0, _⟩, ⟨4, _⟩ | ⟨0, _⟩, ⟨5, _⟩ | ⟨0, _⟩, ⟨6, _⟩ | ⟨0, _⟩, ⟨7, _⟩
  | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨2, _⟩ | ⟨1, _⟩, ⟨3, _⟩ | ⟨1, _⟩, ⟨4, _⟩ | ⟨1, _⟩, ⟨5, _⟩ | ⟨1, _⟩, ⟨6, _⟩ | ⟨1, _⟩, ⟨7, _⟩
  | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨3, _⟩ | ⟨2, _⟩, ⟨4, _⟩ | ⟨2, _⟩, ⟨5, _⟩ | ⟨2, _⟩, ⟨6, _⟩ | ⟨2, _⟩, ⟨7, _⟩
  | ⟨3, _⟩, ⟨0, _⟩ | ⟨3, _⟩, ⟨1, _⟩ | ⟨3, _⟩, ⟨2, _⟩ | ⟨3, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨4, _⟩ | ⟨3, _⟩, ⟨5, _⟩ | ⟨3, _⟩, ⟨6, _⟩ | ⟨3, _⟩, ⟨7, _⟩
  | ⟨4, _⟩, ⟨0, _⟩ | ⟨4, _⟩, ⟨1, _⟩ | ⟨4, _⟩, ⟨2, _⟩ | ⟨4, _⟩, ⟨3, _⟩ | ⟨4, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨5, _⟩ | ⟨4, _⟩, ⟨6, _⟩ | ⟨4, _⟩, ⟨7, _⟩
  | ⟨5, _⟩, ⟨0, _⟩ | ⟨5, _⟩, ⟨1, _⟩ | ⟨5, _⟩, ⟨2, _⟩ | ⟨5, _⟩, ⟨3, _⟩ | ⟨5, _⟩, ⟨4, _⟩ | ⟨5, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨6, _⟩ | ⟨5, _⟩, ⟨7, _⟩
  | ⟨6, _⟩, ⟨0, _⟩ | ⟨6, _⟩, ⟨1, _⟩ | ⟨6, _⟩, ⟨2, _⟩ | ⟨6, _⟩, ⟨3, _⟩ | ⟨6, _⟩, ⟨4, _⟩ | ⟨6, _⟩, ⟨5, _⟩ | ⟨6, _⟩, ⟨6, _⟩ | ⟨6, _⟩, ⟨7, _⟩
  | ⟨7, _⟩, ⟨0, _⟩ | ⟨7, _⟩, ⟨1, _⟩ | ⟨7, _⟩, ⟨2, _⟩ | ⟨7, _⟩, ⟨3, _⟩ | ⟨7, _⟩, ⟨4, _⟩ | ⟨7, _⟩, ⟨5, _⟩ | ⟨7, _⟩, ⟨6, _⟩ | ⟨7, _⟩, ⟨7, _⟩ =>
    simp only [passWidth, passHeight, adam7ColStart, adam7ColStride, adam7RowStart, adam7RowStride] <;> grind

private theorem totalPassPixelsDirect_linear (qw qh : Nat) (rw rh : Fin 8) :
    totalPassPixelsDirect (8 * qw + rw.val) (8 * qh + rh.val) =
    (8 * qw + rw.val) * (8 * qh + rh.val) := by
  simp only [totalPassPixelsDirect, passWidth_linear, passHeight_linear]
  simp only [adam7ColStride, adam7RowStride]
  exact totalPassPixelsDirect_linear_aux qw qh rw rh

-- Prove the main theorem
theorem adam7_total_pixels (width height : Nat) :
    totalPassPixels width height = width * height := by
  rw [totalPassPixels_eq_direct]
  have hwmod := Nat.div_add_mod width 8
  have hhmod := Nat.div_add_mod height 8
  have hrw := Nat.mod_lt width (by omega : 0 < 8)
  have hrh := Nat.mod_lt height (by omega : 0 < 8)
  have h := totalPassPixelsDirect_linear (width / 8) (height / 8) ⟨width % 8, hrw⟩ ⟨height % 8, hrh⟩
  rwa [show 8 * (width / 8) + width % 8 = width from by omega,
       show 8 * (height / 8) + height % 8 = height from by omega] at h

/-! ## Extract produces correctly sized sub-images -/

/-- The array returned by `adam7Extract` always has exactly 7 elements. -/
theorem adam7Extract_size (image : PngImage) :
    (adam7Extract image).size = 7 := by
  simp only [adam7Extract]
  -- Unfold go 7 times
  unfold adam7Extract.go; simp only [show (0 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (1 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (2 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (3 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (4 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (5 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (6 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show ¬(7 : Nat) < 7 from by omega, ↓reduceDIte]
  simp only [Array.size_push, Array.size_empty]

end Png.Spec.InterlaceCorrect
