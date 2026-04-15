import Png.Native.Interlace
import Png.Util.ByteArray

/-!
# Adam7 Interlace Correctness Proofs

Specification theorems for Adam7 interlacing. These state the key
properties that ensure correctness:

1. **Coverage**: every pixel in the full image appears in exactly one pass
2. **Coordinate roundtrips**: `fromSubRow ∘ toSubRow = id` (and columns)
3. **Scatter/extract roundtrip**: `adam7Scatter (adam7Extract image) = image`
4. **Total pixel count**: sum of pass dimensions = full dimensions
5. **Dimension bounds**: sub-image dimensions ≤ full image dimensions

All properties fully proven, including `adam7Scatter_extract` (0 sorry).
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

/-- setPixelAt preserves buffer size. -/
private theorem setPixelAt_size (buf : ByteArray) (idx : Nat)
    (pixel : UInt8 × UInt8 × UInt8 × UInt8) :
    (setPixelAt buf idx pixel).size = buf.size := by
  simp only [setPixelAt]
  split
  · rw [ByteArray.size_set!, ByteArray.size_set!, ByteArray.size_set!, ByteArray.size_set!]
  · rfl

/-! ### Helper lemmas for scatter/extract roundtrip -/

-- Nat arithmetic helpers for div/mod with multiplication
private theorem mul_add_mod_eq (a b n : Nat) (h : b < n) : (a * n + b) % n = b := by
  rw [Nat.mul_comm a n, Nat.mul_add_mod, Nat.mod_eq_of_lt h]

private theorem mul_add_div_eq (a b n : Nat) (hn : n > 0) (h : b < n) :
    (a * n + b) / n = a := by
  rw [show a * n + b = b + n * a from by rw [Nat.mul_comm]; omega,
      Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt h, Nat.zero_add]

-- setPixelAt doesn't affect bytes outside [idx, idx+3]
private theorem setPixelAt_getElem!_ne (buf : ByteArray) (idx j : Nat)
    (pixel : UInt8 × UInt8 × UInt8 × UInt8) (hne : j < idx ∨ j > idx + 3) :
    (setPixelAt buf idx pixel)[j]! = buf[j]! := by
  by_cases h : idx + 3 < buf.size
  · unfold setPixelAt; simp only [show idx + 3 < buf.size from h, ↓reduceIte]
    rw [ByteArray.getElem!_set!_ne _ (idx + 3) j _ (by omega),
        ByteArray.getElem!_set!_ne _ (idx + 2) j _ (by omega),
        ByteArray.getElem!_set!_ne _ (idx + 1) j _ (by omega),
        ByteArray.getElem!_set!_ne _ idx j _ (by omega)]
  · unfold setPixelAt; simp only [show ¬(idx + 3 < buf.size) from h, ↓reduceIte]

-- scatterPass.go preserves byte j when no iteration writes to j's 4-byte group
private theorem scatterPass_go_preserve (buf : ByteArray) (fullWidth : Nat)
    (subPixels : ByteArray) (subW : Nat) (p : Fin 7) (i total : Nat) (j : Nat)
    (hj_ne : ∀ k, i ≤ k → k < total →
      j / 4 ≠ (fromSubRow p (k / subW) * fullWidth +
               fromSubCol p (if subW > 0 then k % subW else 0))) :
    (scatterPass.go buf fullWidth subPixels subW p i total)[j]! = buf[j]! := by
  unfold scatterPass.go; split; · rfl
  · rename_i hlt; have hi : i < total := by omega
    have : total - (i + 1) < total - i := by omega
    rw [scatterPass_go_preserve _ _ _ _ _ (i + 1) _ j
        (fun k hk_lo hk_hi => hj_ne k (by omega) hk_hi),
        setPixelAt_getElem!_ne _ _ _ _ (by have := hj_ne i (Nat.le_refl i) hi; omega)]
termination_by total - i

-- scatterPass.go preserves buffer size
private theorem scatterPass_go_size (buf : ByteArray) (fullWidth : Nat) (subPixels : ByteArray)
    (subW : Nat) (p : Fin 7) (i total : Nat) :
    (scatterPass.go buf fullWidth subPixels subW p i total).size = buf.size := by
  unfold scatterPass.go; split; · rfl
  · have : total - (i + 1) < total - i := by omega
    rw [scatterPass_go_size, setPixelAt_size]
termination_by total - i

private theorem scatterPass_size (buf : ByteArray) (fullWidth : Nat)
    (subImage : PngImage) (p : Fin 7) :
    (scatterPass buf fullWidth subImage p).size = buf.size := by
  simp only [scatterPass]; exact scatterPass_go_size _ _ _ _ _ _ _

-- adam7Scatter.go preserves buffer size
private theorem adam7Scatter_go_size (subImages : Array PngImage) (buf : ByteArray)
    (fullWidth : Nat) (p : Nat) :
    (adam7Scatter.go subImages buf fullWidth p).size = buf.size := by
  unfold adam7Scatter.go; split
  · rename_i h; split
    · have : 7 - (p + 1) < 7 - p := by omega
      rw [adam7Scatter_go_size, scatterPass_size]
    · have : 7 - (p + 1) < 7 - p := by omega
      exact adam7Scatter_go_size _ _ _ _
  · rfl
termination_by 7 - p

-- Coordinate mod lemmas: fromSubRow/Col produce pass-p coordinates
private theorem fromSubRow_mod (p : Fin 7) (sr : Nat) :
    (fromSubRow p sr) % adam7RowStride p = adam7RowStart p := by
  simp only [fromSubRow]
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (adam7RowStart_lt_stride p)]

private theorem fromSubCol_mod (p : Fin 7) (sc : Nat) :
    (fromSubCol p sc) % adam7ColStride p = adam7ColStart p := by
  simp only [fromSubCol]
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (adam7ColStart_lt_stride p)]

-- fromSubCol produces coordinates within bounds
private theorem fromSubCol_lt (p : Fin 7) (sc fullWidth : Nat)
    (hsc : sc < passWidth p fullWidth) :
    fromSubCol p sc < fullWidth := by
  simp only [fromSubCol, passWidth] at *; split at hsc; · omega
  · rw [Nat.lt_div_iff_mul_lt (adam7ColStride_pos p)] at hsc; omega

-- fromSubRow produces coordinates within bounds
private theorem fromSubRow_lt (p : Fin 7) (sr fullHeight : Nat)
    (hsr : sr < passHeight p fullHeight) :
    fromSubRow p sr < fullHeight := by
  simp only [fromSubRow, passHeight] at *; split at hsr; · omega
  · rw [Nat.lt_div_iff_mul_lt (adam7RowStride_pos p)] at hsr; omega

-- scatterPass preserves byte j when j's pixel doesn't belong to pass p
private theorem scatterPass_preserve_byte (buf : ByteArray) (fullWidth : Nat)
    (subImage : PngImage) (p : Fin 7) (j : Nat)
    (hnotpass : ¬(j / 4 / fullWidth % adam7RowStride p = adam7RowStart p ∧
                  j / 4 % fullWidth % adam7ColStride p = adam7ColStart p))
    (hfw_pos : fullWidth > 0)
    (hsw : subImage.width.toNat = passWidth p fullWidth) :
    (scatterPass buf fullWidth subImage p)[j]! = buf[j]! := by
  simp only [scatterPass]
  apply scatterPass_go_preserve
  intro k _ hk_total
  intro heq
  apply hnotpass
  have hsubW_pos : subImage.width.toNat > 0 := by
    have : subImage.width.toNat * subImage.height.toNat ≠ 0 := by omega
    exact Nat.pos_of_ne_zero (Nat.ne_zero_of_mul_ne_zero_left this)
  simp only [show subImage.width.toNat > 0 from hsubW_pos, ↓reduceIte] at heq
  have hsc_lt : fromSubCol p (k % subImage.width.toNat) < fullWidth :=
    fromSubCol_lt p _ fullWidth (by rw [← hsw]; exact Nat.mod_lt _ hsubW_pos)
  exact ⟨by rw [heq, mul_add_div_eq _ _ _ hfw_pos hsc_lt]; exact fromSubRow_mod p _,
         by rw [heq, mul_add_mod_eq _ _ _ hsc_lt]; exact fromSubCol_mod p _⟩

-- extractPass.go size characterization
private theorem extractPass_go_size (srcPixels : ByteArray) (srcWidth : Nat) (p : Fin 7)
    (subW i total : Nat) (out : ByteArray) (hle : i ≤ total) :
    (extractPass.go srcPixels srcWidth p subW i total out).size =
    out.size + 4 * (total - i) := by
  unfold extractPass.go; split; · omega
  · have : total - (i + 1) < total - i := by omega
    rw [extractPass_go_size _ _ _ _ _ _ _ (by omega)]
    simp only [ByteArray.size_push]; omega
termination_by total - i

-- extractPass.go preserves prefix bytes
private theorem extractPass_go_prefix (srcPixels : ByteArray) (srcWidth : Nat) (p : Fin 7)
    (subW i total : Nat) (out : ByteArray) (j : Nat) (hj : j < out.size) :
    (extractPass.go srcPixels srcWidth p subW i total out)[j]! = out[j]! := by
  unfold extractPass.go; split; · rfl
  · have : total - (i + 1) < total - i := by omega
    rw [extractPass_go_prefix _ _ _ _ _ _ _ _
        (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
        ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
        ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
        ByteArray.push_getElem!_lt _ _ _ hj]
termination_by total - i

-- Helper: reading at index buf.size + ch from 4 consecutive pushes
-- gives the ch-th pushed byte.
private theorem push4_getElem! (buf : ByteArray) (a b c d : UInt8) (ch : Fin 4) :
    ((((buf.push a).push b).push c).push d)[buf.size + ch.val]! =
    match ch with
    | ⟨0, _⟩ => a
    | ⟨1, _⟩ => b
    | ⟨2, _⟩ => c
    | ⟨3, _⟩ => d := by
  match ch with
  | ⟨0, _⟩ =>
    simp only [Nat.add_zero]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
        ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
        ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
        ByteArray.push_getElem!_eq]
  | ⟨1, _⟩ =>
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega),
        ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    have h1 : buf.size + 1 = (buf.push a).size := by simp only [ByteArray.size_push]
    rw [h1, ByteArray.push_getElem!_eq]
  | ⟨2, _⟩ =>
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    have h2 : buf.size + 2 = ((buf.push a).push b).size := by simp only [ByteArray.size_push]
    rw [h2, ByteArray.push_getElem!_eq]
  | ⟨3, _⟩ =>
    have h3 : buf.size + 3 = (((buf.push a).push b).push c).size := by
      simp only [ByteArray.size_push]
    conv => lhs; rw [h3]
    exact ByteArray.push_getElem!_eq _ _

-- extractPass.go content: byte at position out.size + 4*(k-i) + ch
-- equals the corresponding byte from the getPixel result
private theorem extractPass_go_content (srcPixels : ByteArray) (srcWidth : Nat) (p : Fin 7)
    (subW i total : Nat) (out : ByteArray)
    (k : Nat) (hk_lo : i ≤ k) (hk_hi : k < total)
    (ch : Fin 4)
    (hsubW_pos : subW > 0) :
    let sr := k / subW; let sc := k % subW
    let fullRow := fromSubRow p sr; let fullCol := fromSubCol p sc
    let idx := 4 * (fullRow * srcWidth + fullCol)
    (extractPass.go srcPixels srcWidth p subW i total out)[out.size + 4 * (k - i) + ch.val]! =
    if h : idx + 3 < srcPixels.size then
      srcPixels[idx + ch.val]'(by omega)
    else (0 : UInt8) := by
  simp only []
  unfold extractPass.go
  split
  · omega
  · rename_i hlt
    have hi : i < total := by omega
    by_cases hki : k = i
    · subst hki
      simp only [Nat.sub_self, Nat.mul_zero]
      rw [extractPass_go_prefix _ _ _ _ _ _ _ _
          (by simp only [ByteArray.size_push]; omega)]
      simp only [getPixel, Nat.add_zero]
      -- Match on ch FIRST to resolve Fin coercion, then split on bounds
      match ch with
      | ⟨0, _⟩ => split <;> (rw [push4_getElem!]; try rfl)
      | ⟨1, _⟩ => split <;> (rw [push4_getElem!]; try rfl)
      | ⟨2, _⟩ => split <;> (rw [push4_getElem!]; try rfl)
      | ⟨3, _⟩ => split <;> (rw [push4_getElem!]; try rfl)
    · -- k > i: byte is in the recursive call
      have hki' : i + 1 ≤ k := by omega
      have : total - (i + 1) < total - i := by omega
      rw [show out.size + 4 * (k - i) + ch.val =
           (out.push _ |>.push _ |>.push _ |>.push _).size + 4 * (k - (i + 1)) + ch.val
         from by simp only [ByteArray.size_push]; omega]
      exact extractPass_go_content _ _ _ _ _ _ _ _ hki' hk_hi ch hsubW_pos
termination_by total - i

-- Convenience: the if condition in scatterPass.go's pixel read
-- When subW > 0, the `if subW > 0` simplifies
private theorem dite_subW_pos {subW : Nat} (hpos : subW > 0) (k : Nat) :
    (if subW > 0 then k % subW else 0) = k % subW := by
  simp only [show subW > 0 from hpos, ↓reduceIte]

-- First, isValid gives buffer size
private theorem isValid_pixels_size (img : PngImage) (h : img.isValid = true) :
    img.pixels.size = img.width.toNat * img.height.toNat * 4 := by
  simp only [PngImage.isValid, PngImage.expectedSize, beq_iff_eq] at h; exact h

-- extractPass produces correctly sized sub-images
private theorem extractPass_pixels_size (image : PngImage) (p : Fin 7) :
    (extractPass image p).pixels.size =
    passWidth p image.width.toNat * passHeight p image.height.toNat * 4 := by
  simp only [extractPass]
  rw [extractPass_go_size _ _ _ _ _ _ _ (Nat.zero_le _)]
  show 0 + 4 * (passWidth p image.width.toNat * passHeight p image.height.toNat - 0) =
       passWidth p image.width.toNat * passHeight p image.height.toNat * 4
  omega

-- Nat.toUInt32.toNat roundtrip when value fits in UInt32
private theorem toUInt32_toNat (n : Nat) (h : n < 2 ^ 32) : n.toUInt32.toNat = n := by
  simp only [Nat.toUInt32, UInt32.toNat, UInt32.ofNat, BitVec.ofNat, BitVec.toNat]
  exact Nat.mod_eq_of_lt h

-- extractPass produces correct width/height fields
private theorem extractPass_width (image : PngImage) (p : Fin 7) :
    (extractPass image p).width.toNat = passWidth p image.width.toNat := by
  show (passWidth p image.width.toNat).toUInt32.toNat = passWidth p image.width.toNat
  have hw : image.width.toNat < 2 ^ 32 := image.width.toBitVec.isLt
  exact toUInt32_toNat _ (by have := passWidth_le p image.width.toNat; omega)

private theorem extractPass_height (image : PngImage) (p : Fin 7) :
    (extractPass image p).height.toNat = passHeight p image.height.toNat := by
  show (passHeight p image.height.toNat).toUInt32.toNat = passHeight p image.height.toNat
  have hh : image.height.toNat < 2 ^ 32 := image.height.toBitVec.isLt
  exact toUInt32_toNat _ (by have := passHeight_le p image.height.toNat; omega)

-- adam7Extract produces correctly sized sub-images
private theorem adam7Extract_getElem (image : PngImage) (p : Fin 7)
    (hs : (adam7Extract image).size = 7) :
    (adam7Extract image)[p.val]'(by rw [hs]; exact p.isLt) = extractPass image p := by
  simp only [adam7Extract]
  unfold adam7Extract.go; simp only [show (0 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (1 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (2 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (3 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (4 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (5 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show (6 : Nat) < 7 from by omega, ↓reduceDIte]
  unfold adam7Extract.go; simp only [show ¬(7 : Nat) < 7 from by omega, ↓reduceDIte]
  match p with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl

/-- `UInt32.toNat` composed with `Nat.toUInt32` is the identity. -/
private theorem UInt32_toNat_toUInt32 (u : UInt32) : u.toNat.toUInt32 = u := by
  simp only [UInt32.toNat, Nat.toUInt32, UInt32.ofNat]
  congr 1; exact BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt u.toBitVec.isLt)

-- setPixelAt writes the correct channel byte at a pixel-owned position
private theorem setPixelAt_getElem!_eq (buf : ByteArray) (idx : Nat) (ch : Fin 4)
    (pixel : UInt8 × UInt8 × UInt8 × UInt8)
    (h : idx + 3 < buf.size) :
    (setPixelAt buf idx pixel)[idx + ch.val]! =
    match ch with
    | ⟨0, _⟩ => pixel.1
    | ⟨1, _⟩ => pixel.2.1
    | ⟨2, _⟩ => pixel.2.2.1
    | ⟨3, _⟩ => pixel.2.2.2 := by
  unfold setPixelAt; simp only [h, ↓reduceIte]
  match ch with
  | ⟨0, _⟩ =>
    simp only [Nat.add_zero]
    rw [ByteArray.getElem!_set!_ne _ (idx + 3) idx _ (by omega),
        ByteArray.getElem!_set!_ne _ (idx + 2) idx _ (by omega),
        ByteArray.getElem!_set!_ne _ (idx + 1) idx _ (by omega),
        ByteArray.getElem!_set!_self _ idx _ (by omega)]
  | ⟨1, _⟩ =>
    rw [ByteArray.getElem!_set!_ne _ (idx + 3) (idx + 1) _ (by omega),
        ByteArray.getElem!_set!_ne _ (idx + 2) (idx + 1) _ (by omega),
        ByteArray.getElem!_set!_self _ (idx + 1) _ (by rw [ByteArray.size_set!]; omega)]
  | ⟨2, _⟩ =>
    rw [ByteArray.getElem!_set!_ne _ (idx + 3) (idx + 2) _ (by omega),
        ByteArray.getElem!_set!_self _ (idx + 2) _ (by rw [ByteArray.size_set!, ByteArray.size_set!]; omega)]
  | ⟨3, _⟩ =>
    rw [ByteArray.getElem!_set!_self _ (idx + 3) _ (by rw [ByteArray.size_set!, ByteArray.size_set!, ByteArray.size_set!]; omega)]

-- Injectivity of coordinate conversion functions
private theorem fromSubRow_inj (p : Fin 7) {a b : Nat}
    (h : fromSubRow p a = fromSubRow p b) : a = b := by
  simp only [fromSubRow] at h
  match p with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
    simp only [adam7RowStride, adam7RowStart] at h; omega

private theorem fromSubCol_inj (p : Fin 7) {a b : Nat}
    (h : fromSubCol p a = fromSubCol p b) : a = b := by
  simp only [fromSubCol] at h
  match p with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ =>
    simp only [adam7ColStride, adam7ColStart] at h; omega

-- Within a pass, different sub-image pixel indices map to different full-image positions
private theorem pass_pixel_pos_inj (p : Fin 7) (subW fullWidth : Nat)
    (k1 k2 : Nat) (_hsubW_pos : subW > 0)
    (hfc1 : fromSubCol p (k1 % subW) < fullWidth)
    (hfc2 : fromSubCol p (k2 % subW) < fullWidth)
    (heq : fromSubRow p (k1 / subW) * fullWidth + fromSubCol p (k1 % subW) =
           fromSubRow p (k2 / subW) * fullWidth + fromSubCol p (k2 % subW)) :
    k1 = k2 := by
  have hfw_pos : fullWidth > 0 := by omega
  have hr : fromSubRow p (k1 / subW) = fromSubRow p (k2 / subW) := by
    have h1 := mul_add_div_eq (fromSubRow p (k1 / subW)) (fromSubCol p (k1 % subW))
               fullWidth hfw_pos hfc1
    rw [heq] at h1
    have h2 := mul_add_div_eq (fromSubRow p (k2 / subW)) (fromSubCol p (k2 % subW))
               fullWidth hfw_pos hfc2
    omega
  have hc : fromSubCol p (k1 % subW) = fromSubCol p (k2 % subW) := by
    have heq' := heq; rw [hr] at heq'; omega
  have hd := fromSubRow_inj p hr
  have hm := fromSubCol_inj p hc
  have h1 := Nat.div_add_mod k1 subW
  have h2 := Nat.div_add_mod k2 subW
  rw [hd, hm] at h1; omega

-- toSubRow is bounded by passHeight for coordinates that belong to the pass
private theorem toSubRow_lt_passHeight (p : Fin 7) (r h : Nat)
    (hr_lt : r < h) (hr_mod : r % adam7RowStride p = adam7RowStart p) :
    toSubRow p r < passHeight p h := by
  simp only [toSubRow, passHeight]
  have hstride := adam7RowStride_pos p
  have hstart_le : adam7RowStart p ≤ r := hr_mod ▸ Nat.mod_le r _
  have h_not_le : ¬(h ≤ adam7RowStart p) := by omega
  simp only [h_not_le, ↓reduceIte]
  have hmod := Nat.div_add_mod r (adam7RowStride p)
  rw [hr_mod] at hmod
  -- r = stride * (r / stride) + start, so r - start = stride * (r / stride)
  have hdvd : adam7RowStride p * ((r - adam7RowStart p) / adam7RowStride p) =
              r - adam7RowStart p := by
    have hsub : r - adam7RowStart p = adam7RowStride p * (r / adam7RowStride p) := by omega
    rw [hsub, Nat.mul_div_cancel_left _ hstride]
  suffices hsuff : (r - adam7RowStart p) / adam7RowStride p + 1 ≤
      (h - adam7RowStart p + adam7RowStride p - 1) / adam7RowStride p by omega
  rw [Nat.le_div_iff_mul_le hstride, Nat.add_mul, Nat.one_mul]
  have hprod : ((r - adam7RowStart p) / adam7RowStride p) * adam7RowStride p =
               r - adam7RowStart p := by rw [Nat.mul_comm]; exact hdvd
  omega

-- toSubCol is bounded by passWidth for coordinates that belong to the pass
private theorem toSubCol_lt_passWidth (p : Fin 7) (c w : Nat)
    (hc_lt : c < w) (hc_mod : c % adam7ColStride p = adam7ColStart p) :
    toSubCol p c < passWidth p w := by
  simp only [toSubCol, passWidth]
  have hstride := adam7ColStride_pos p
  have hstart_le : adam7ColStart p ≤ c := hc_mod ▸ Nat.mod_le c _
  have h_not_le : ¬(w ≤ adam7ColStart p) := by omega
  simp only [h_not_le, ↓reduceIte]
  have hmod := Nat.div_add_mod c (adam7ColStride p)
  rw [hc_mod] at hmod
  have hdvd : adam7ColStride p * ((c - adam7ColStart p) / adam7ColStride p) =
              c - adam7ColStart p := by
    have hsub : c - adam7ColStart p = adam7ColStride p * (c / adam7ColStride p) := by omega
    rw [hsub, Nat.mul_div_cancel_left _ hstride]
  suffices hsuff : (c - adam7ColStart p) / adam7ColStride p + 1 ≤
      (w - adam7ColStart p + adam7ColStride p - 1) / adam7ColStride p by omega
  rw [Nat.le_div_iff_mul_le hstride, Nat.add_mul, Nat.one_mul]
  have hprod : ((c - adam7ColStart p) / adam7ColStride p) * adam7ColStride p =
               c - adam7ColStart p := by rw [Nat.mul_comm]; exact hdvd
  omega

-- passWidth > 0 when some column belongs to the pass
private theorem passWidth_pos_of_col (p : Fin 7) (c w : Nat)
    (hc_lt : c < w) (hc_mod : c % adam7ColStride p = adam7ColStart p) :
    passWidth p w > 0 := by
  have := toSubCol_lt_passWidth p c w hc_lt hc_mod; omega

-- Key write lemma: scatterPass.go writes the correct byte at the owning iteration's position
private theorem scatterPass_go_write_byte
    (buf : ByteArray) (fullWidth : Nat) (subPixels : ByteArray)
    (subW : Nat) (p : Fin 7) (i total : Nat) (k : Nat) (ch : Fin 4)
    (hk_lo : i ≤ k) (hk_hi : k < total)
    (hsubW_pos : subW > 0)
    (hfc_lt : ∀ m, m < total → fromSubCol p (m % subW) < fullWidth)
    (hbuf_all : ∀ m, i ≤ m → m < total →
      4 * (fromSubRow p (m / subW) * fullWidth + fromSubCol p (m % subW)) + 3 < buf.size)
    (hsrc : ∀ m, m < total → 4 * m + 3 < subPixels.size) :
    (scatterPass.go buf fullWidth subPixels subW p i total)[4 * (fromSubRow p (k / subW) * fullWidth + fromSubCol p (k % subW)) + ch.val]! =
    subPixels[4 * k + ch.val]! := by
  unfold scatterPass.go
  split
  · omega
  · rename_i hlt
    simp only []
    by_cases hki : k = i
    · -- This iteration writes our byte; remaining iterations preserve it
      rw [show k / subW = i / subW by rw [hki],
          show k % subW = i % subW by rw [hki]]
      rw [scatterPass_go_preserve _ _ _ _ _ (i + 1) _ _
          (fun k' hk'_lo hk'_hi => by
            simp only [show subW > 0 from hsubW_pos, ↓reduceIte]
            intro heq
            have h4div : (4 * (fromSubRow p (i / subW) * fullWidth +
                          fromSubCol p (i % subW)) + ch.val) / 4 =
                         fromSubRow p (i / subW) * fullWidth + fromSubCol p (i % subW) := by
              omega
            rw [h4div] at heq
            exact absurd (pass_pixel_pos_inj p subW fullWidth i k' hsubW_pos
                  (hfc_lt i (by omega)) (hfc_lt k' hk'_hi) heq)
                  (by omega))]
      -- setPixelAt writes the correct byte
      rw [setPixelAt_getElem!_eq _ _ ch _ (hbuf_all i (Nat.le_refl i) (by omega))]
      -- Change k to i in the getElem! RHS (no proof dependency issues)
      rw [hki]
      -- Simplify the pixel read from subPixels
      have hsrc_i := hsrc i (by omega)
      simp only [show 4 * i + 3 < subPixels.size from hsrc_i, ↓reduceDIte]
      -- Each channel: proven-bounds LHS vs getElem! RHS
      match ch with
      | ⟨0, _⟩ =>
        simp only [Nat.add_zero]
        exact (getElem!_pos subPixels _ (by omega)).symm
      | ⟨1, _⟩ => exact (getElem!_pos subPixels _ (by omega)).symm
      | ⟨2, _⟩ => exact (getElem!_pos subPixels _ (by omega)).symm
      | ⟨3, _⟩ => exact (getElem!_pos subPixels _ (by omega)).symm
    · -- k > i: use IH on the recursive call
      have hki' : i + 1 ≤ k := by omega
      have : total - (i + 1) < total - i := by omega
      exact scatterPass_go_write_byte _ fullWidth subPixels subW p (i + 1) total k ch
        hki' hk_hi hsubW_pos hfc_lt
        (fun m hm1 hm2 => by rw [setPixelAt_size]; exact hbuf_all m (by omega) hm2)
        hsrc
  termination_by total - i

-- After the owning pass, remaining passes preserve the byte (by uniqueness)
private theorem adam7Scatter_go_preserve_after (subImages : Array PngImage) (buf : ByteArray)
    (fullWidth : Nat) (startP : Nat) (j : Nat) (p : Fin 7)
    (hp_done : p.val < startP)
    (hp_own : j / 4 / fullWidth % adam7RowStride p = adam7RowStart p ∧
              j / 4 % fullWidth % adam7ColStride p = adam7ColStart p)
    (hfw_pos : fullWidth > 0)
    (hsize : subImages.size = 7)
    (hsw : ∀ q : Fin 7, (subImages[q.val]'(by rw [hsize]; exact q.isLt)).width.toNat =
           passWidth q fullWidth) :
    (adam7Scatter.go subImages buf fullWidth startP)[j]! = buf[j]! := by
  unfold adam7Scatter.go
  split
  · rename_i hlt
    split
    · rename_i hp_sub
      have : 7 - (startP + 1) < 7 - startP := by omega
      rw [adam7Scatter_go_preserve_after subImages _ fullWidth (startP + 1) j p (by omega)
          hp_own hfw_pos hsize hsw]
      exact scatterPass_preserve_byte buf fullWidth _ ⟨startP, hlt⟩ j
        (fun hq_own => by
          have := adam7_uniqueness (j / 4 / fullWidth) (j / 4 % fullWidth)
            ⟨startP, hlt⟩ p hq_own hp_own
          have := congrArg Fin.val this
          simp only [] at this; omega)
        hfw_pos (hsw ⟨startP, hlt⟩)
    · rename_i hp_nsub
      have : 7 - (startP + 1) < 7 - startP := by omega
      exact adam7Scatter_go_preserve_after subImages buf fullWidth (startP + 1) j p (by omega)
        hp_own hfw_pos hsize hsw
  · rfl
  termination_by 7 - startP

-- scatterPass writes the correct sub-image byte at a pass-owned position
private theorem scatterPass_at_byte
    (buf : ByteArray) (fullWidth fullHeight : Nat) (subImage : PngImage) (p : Fin 7) (j : Nat)
    (hr_mod : j / 4 / fullWidth % adam7RowStride p = adam7RowStart p)
    (hc_mod : j / 4 % fullWidth % adam7ColStride p = adam7ColStart p)
    (hfw_pos : fullWidth > 0)
    (hj_row : j / 4 / fullWidth < fullHeight)
    (hsw : subImage.width.toNat = passWidth p fullWidth)
    (hsh : subImage.height.toNat = passHeight p fullHeight)
    (hsp : subImage.pixels.size = passWidth p fullWidth * passHeight p fullHeight * 4)
    (hbuf_size : buf.size = fullWidth * fullHeight * 4) :
    (scatterPass buf fullWidth subImage p)[j]! =
    subImage.pixels[4 * (toSubRow p (j / 4 / fullWidth) * passWidth p fullWidth +
                         toSubCol p (j / 4 % fullWidth)) + j % 4]! := by
  -- Derived bounds
  have hc_lt : j / 4 % fullWidth < fullWidth := Nat.mod_lt _ hfw_pos
  have hsubW_pos : passWidth p fullWidth > 0 := passWidth_pos_of_col p _ _ hc_lt hc_mod
  have hsc_lt := toSubCol_lt_passWidth p _ _ hc_lt hc_mod
  have hsr_lt := toSubRow_lt_passHeight p _ _ hj_row hr_mod
  have hk_lt : toSubRow p (j / 4 / fullWidth) * passWidth p fullWidth +
               toSubCol p (j / 4 % fullWidth) <
               passWidth p fullWidth * passHeight p fullHeight := by
    have h1 : toSubRow p (j / 4 / fullWidth) * passWidth p fullWidth +
              toSubCol p (j / 4 % fullWidth) <
              (toSubRow p (j / 4 / fullWidth) + 1) * passWidth p fullWidth := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : (toSubRow p (j / 4 / fullWidth) + 1) * passWidth p fullWidth ≤
              passHeight p fullHeight * passWidth p fullWidth :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_comm (passWidth p fullWidth)]; omega
  have hk_div := mul_add_div_eq (toSubRow p (j / 4 / fullWidth))
    (toSubCol p (j / 4 % fullWidth)) (passWidth p fullWidth) hsubW_pos hsc_lt
  have hk_mod := mul_add_mod_eq (toSubRow p (j / 4 / fullWidth))
    (toSubCol p (j / 4 % fullWidth)) (passWidth p fullWidth) hsc_lt
  have hfr := fromSubRow_toSubRow p _ hr_mod
  have hfc := fromSubCol_toSubCol p _ hc_mod
  -- Index equation: scatter position for pixel k equals j
  have hj_eq : 4 * (fromSubRow p ((toSubRow p (j / 4 / fullWidth) * passWidth p fullWidth +
                 toSubCol p (j / 4 % fullWidth)) / passWidth p fullWidth) * fullWidth +
                 fromSubCol p ((toSubRow p (j / 4 / fullWidth) * passWidth p fullWidth +
                 toSubCol p (j / 4 % fullWidth)) % passWidth p fullWidth)) + j % 4 = j := by
    rw [hk_div, hk_mod, hfr, hfc,
        show j / 4 / fullWidth * fullWidth + j / 4 % fullWidth = j / 4
          from by rw [Nat.mul_comm]; exact Nat.div_add_mod _ fullWidth,
        show 4 * (j / 4) + j % 4 = j
          from Nat.div_add_mod j 4]
  -- Unfold scatterPass and apply scatterPass_go_write_byte
  simp only [scatterPass, hsw, hsh]
  -- Obtain the write byte result; then show it matches our goal at index j
  have hwrite := scatterPass_go_write_byte buf fullWidth subImage.pixels
    (passWidth p fullWidth) p 0
    (passWidth p fullWidth * passHeight p fullHeight)
    (toSubRow p (j / 4 / fullWidth) * passWidth p fullWidth +
     toSubCol p (j / 4 % fullWidth))
    ⟨j % 4, Nat.mod_lt j (by omega)⟩
    (Nat.zero_le _) hk_lt hsubW_pos
    (fun m _ => fromSubCol_lt p _ fullWidth (Nat.mod_lt _ hsubW_pos))
    (fun m _ hm => by
      rw [hbuf_size]
      have hmr := fromSubRow_lt p (m / passWidth p fullWidth) fullHeight
        (Nat.div_lt_of_lt_mul hm)
      have hmc := fromSubCol_lt p (m % passWidth p fullWidth) fullWidth
        (Nat.mod_lt _ hsubW_pos)
      have : fromSubRow p (m / passWidth p fullWidth) * fullWidth +
             fromSubCol p (m % passWidth p fullWidth) < fullHeight * fullWidth := by
        calc fromSubRow p (m / passWidth p fullWidth) * fullWidth +
             fromSubCol p (m % passWidth p fullWidth)
            < fromSubRow p (m / passWidth p fullWidth) * fullWidth + fullWidth := by omega
          _ = (fromSubRow p (m / passWidth p fullWidth) + 1) * fullWidth := by
              rw [Nat.add_mul, Nat.one_mul]
          _ ≤ fullHeight * fullWidth := Nat.mul_le_mul_right _ (by omega)
      rw [show fullWidth * fullHeight = fullHeight * fullWidth from Nat.mul_comm _ _]; omega)
    (fun m hm => by rw [hsp]; omega)
  -- hwrite : (...)[index_expr]! = subImage.pixels[4*k + j%4]!
  -- index_expr = j by hj_eq, so rw to convert
  rwa [show 4 * (fromSubRow p ((toSubRow p (j / 4 / fullWidth) * passWidth p fullWidth +
         toSubCol p (j / 4 % fullWidth)) / passWidth p fullWidth) * fullWidth +
         fromSubCol p ((toSubRow p (j / 4 / fullWidth) * passWidth p fullWidth +
         toSubCol p (j / 4 % fullWidth)) % passWidth p fullWidth)) +
         (⟨j % 4, Nat.mod_lt j (by omega)⟩ : Fin 4).val = j
       from hj_eq] at hwrite

-- Composition: adam7Scatter.go at byte j (owned by pass p) produces the sub-image pixel byte
private theorem adam7Scatter_go_byte_at_pass
    (subImages : Array PngImage) (buf : ByteArray)
    (fullWidth fullHeight : Nat) (startP : Nat) (j : Nat) (p : Fin 7)
    (hp_ge : startP ≤ p.val)
    (hr_mod : j / 4 / fullWidth % adam7RowStride p = adam7RowStart p)
    (hc_mod : j / 4 % fullWidth % adam7ColStride p = adam7ColStart p)
    (hfw_pos : fullWidth > 0)
    (hj_row : j / 4 / fullWidth < fullHeight)
    (hsize : subImages.size = 7)
    (hsw : ∀ q : Fin 7, (subImages[q.val]'(by rw [hsize]; exact q.isLt)).width.toNat =
           passWidth q fullWidth)
    (hsh : ∀ q : Fin 7, (subImages[q.val]'(by rw [hsize]; exact q.isLt)).height.toNat =
           passHeight q fullHeight)
    (hsp : ∀ q : Fin 7, (subImages[q.val]'(by rw [hsize]; exact q.isLt)).pixels.size =
           passWidth q fullWidth * passHeight q fullHeight * 4)
    (hbuf_size : buf.size = fullWidth * fullHeight * 4) :
    (adam7Scatter.go subImages buf fullWidth startP)[j]! =
    (subImages[p.val]'(by rw [hsize]; exact p.isLt)).pixels[
      4 * (toSubRow p (j / 4 / fullWidth) * passWidth p fullWidth +
           toSubCol p (j / 4 % fullWidth)) + j % 4]! := by
  unfold adam7Scatter.go
  split
  · rename_i hlt -- startP < 7
    split
    · rename_i hp_sub
      by_cases hpeq : startP = p.val
      · -- Base case: this is pass p
        have : 7 - (startP + 1) < 7 - startP := by omega
        -- Rewrite startP → p.val
        have hpeq' : startP = p.val := hpeq; subst hpeq'
        -- After scatterPass at pass p, remaining passes preserve byte j
        rw [adam7Scatter_go_preserve_after subImages _ fullWidth (p.val + 1) j p
            (by omega) ⟨hr_mod, hc_mod⟩ hfw_pos hsize hsw]
        -- Apply scatterPass_at_byte
        exact scatterPass_at_byte buf fullWidth fullHeight
          (subImages[p.val]'hp_sub) p j
          hr_mod hc_mod hfw_pos hj_row (hsw p) (hsh p) (hsp p) hbuf_size
      · -- IH case: startP < p.val
        have : 7 - (startP + 1) < 7 - startP := by omega
        exact adam7Scatter_go_byte_at_pass subImages _ fullWidth fullHeight (startP + 1)
          j p (by omega) hr_mod hc_mod hfw_pos hj_row hsize
          hsw hsh hsp (by rw [scatterPass_size]; exact hbuf_size)
    · rename_i hp_nsub; rw [hsize] at hp_nsub; omega
  · rename_i h_ge; omega
  termination_by 7 - startP

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

/-- Scattering the extracted sub-images back into a full image
    recovers the original image. -/
theorem adam7Scatter_extract (image : PngImage)
    (hvalid : image.isValid = true) :
    adam7Scatter (adam7Extract image) image.width.toNat image.height.toNat = image := by
  -- Unfold adam7Scatter to expose the structure fields
  simp only [adam7Scatter]
  -- Need { width := w.toUInt32, height := h.toUInt32, pixels := scatter_result } = image
  -- Decompose into cases on image
  cases image with
  | mk iw ih ipix =>
    simp only [] at hvalid ⊢
    -- Now goal is: { width := iw.toNat.toUInt32, height := ih.toNat.toUInt32, pixels := ... } = { width := iw, height := ih, pixels := ipix }
    congr 1
    · exact UInt32_toNat_toUInt32 iw
    · exact UInt32_toNat_toUInt32 ih
    · -- pixels equality: scatter(extract(image)).pixels = image.pixels
      -- Use ByteArray extensionality
      apply ByteArray.ext_getElem!
      · -- Same size
        rw [adam7Scatter_go_size]
        simp only [ByteArray.size, Array.size_replicate]
        have := isValid_pixels_size ⟨iw, ih, ipix⟩ hvalid
        simp only [ByteArray.size] at this
        omega
      · -- Same bytes at each index
        intro j hj
        -- j < scatter_result.size, which equals w * h * 4
        have hpix_sz := isValid_pixels_size ⟨iw, ih, ipix⟩ hvalid
        -- Handle w = 0 case (image is empty, no bytes to check)
        by_cases hw_pos : iw.toNat = 0
        · simp only [ByteArray.size] at hpix_sz; rw [hw_pos] at hpix_sz
          simp only [Nat.zero_mul] at hpix_sz
          rw [adam7Scatter_go_size, ByteArray.size, Array.size_replicate] at hj
          rw [hw_pos] at hj; simp only [Nat.zero_mul] at hj; omega
        · have hfw_pos : iw.toNat > 0 := Nat.pos_of_ne_zero hw_pos
          -- For each byte j, find the owning pass
          have ⟨p, hp⟩ := adam7_coverage (j / 4 / iw.toNat) (j / 4 % iw.toNat)
          -- Step 1: adam7Scatter.go gives the sub-image pixel byte
          have hextract_sz := adam7Extract_size ⟨iw, ih, ipix⟩
          have hsw : ∀ q : Fin 7,
              ((adam7Extract ⟨iw, ih, ipix⟩)[q.val]'(by rw [hextract_sz]; exact q.isLt)).width.toNat =
              passWidth q iw.toNat := by
            intro q; rw [adam7Extract_getElem _ q hextract_sz]; exact extractPass_width _ q
          have hsh : ∀ q : Fin 7,
              ((adam7Extract ⟨iw, ih, ipix⟩)[q.val]'(by rw [hextract_sz]; exact q.isLt)).height.toNat =
              passHeight q ih.toNat := by
            intro q; rw [adam7Extract_getElem _ q hextract_sz]; exact extractPass_height _ q
          have hsp : ∀ q : Fin 7,
              ((adam7Extract ⟨iw, ih, ipix⟩)[q.val]'(by rw [hextract_sz]; exact q.isLt)).pixels.size =
              passWidth q iw.toNat * passHeight q ih.toNat * 4 := by
            intro q; rw [adam7Extract_getElem _ q hextract_sz]; exact extractPass_pixels_size _ q
          have hbuf_size : (ByteArray.mk (Array.replicate (iw.toNat * ih.toNat * 4) 0)).size =
              iw.toNat * ih.toNat * 4 := by
            simp only [ByteArray.size, Array.size_replicate]
          -- Derive j / 4 / w < h from j < w * h * 4
          rw [adam7Scatter_go_size, ByteArray.size, Array.size_replicate] at hj
          have hj_row : j / 4 / iw.toNat < ih.toNat := by
            have hj4 : j / 4 < iw.toNat * ih.toNat := by omega
            exact Nat.div_lt_of_lt_mul hj4
          -- Apply the composition lemma
          rw [adam7Scatter_go_byte_at_pass (adam7Extract ⟨iw, ih, ipix⟩) _ iw.toNat ih.toNat
              0 j p (Nat.zero_le _) hp.1 hp.2 hfw_pos hj_row hextract_sz hsw hsh hsp hbuf_size]
          -- Step 2: Replace adam7Extract[p] with extractPass
          rw [adam7Extract_getElem _ p hextract_sz]
          -- Step 3: Use extractPass_go_content to get original pixels
          -- Goal: (extractPass ⟨iw, ih, ipix⟩ p).pixels[4*k + j%4]! = ipix[j]!
          simp only [extractPass]
          -- Derived bounds
          have hc_lt : j / 4 % iw.toNat < iw.toNat := Nat.mod_lt _ hfw_pos
          have hsubW_pos : passWidth p iw.toNat > 0 :=
            passWidth_pos_of_col p _ _ hc_lt hp.2
          have hsc_lt := toSubCol_lt_passWidth p _ _ hc_lt hp.2
          have hsr_lt := toSubRow_lt_passHeight p _ _ hj_row hp.1
          have hk_lt : toSubRow p (j / 4 / iw.toNat) * passWidth p iw.toNat +
                       toSubCol p (j / 4 % iw.toNat) <
                       passWidth p iw.toNat * passHeight p ih.toNat := by
            have h1 : toSubRow p (j / 4 / iw.toNat) * passWidth p iw.toNat +
                      toSubCol p (j / 4 % iw.toNat) <
                      (toSubRow p (j / 4 / iw.toNat) + 1) * passWidth p iw.toNat := by
              rw [Nat.add_mul, Nat.one_mul]; omega
            have h2 : (toSubRow p (j / 4 / iw.toNat) + 1) * passWidth p iw.toNat ≤
                      passHeight p ih.toNat * passWidth p iw.toNat :=
              Nat.mul_le_mul_right _ (by omega)
            rw [Nat.mul_comm (passWidth p iw.toNat)]; omega
          -- Apply extractPass_go_content
          have hcontent := extractPass_go_content ipix iw.toNat p (passWidth p iw.toNat)
            0 (passWidth p iw.toNat * passHeight p ih.toNat)
            ByteArray.empty
            (toSubRow p (j / 4 / iw.toNat) * passWidth p iw.toNat +
             toSubCol p (j / 4 % iw.toNat))
            (Nat.zero_le _) hk_lt
            ⟨j % 4, Nat.mod_lt j (by omega)⟩ hsubW_pos
          simp only [ByteArray.size_empty, Nat.zero_add, Nat.sub_zero] at hcontent
          -- hcontent: (...)[4*k + ch]! = if h : idx+3 < ipix.size then ipix[idx+ch] else 0
          -- Show the indices match and the dite resolves
          rw [hcontent]
          -- Compute div/mod of k
          have hk_div := mul_add_div_eq (toSubRow p (j / 4 / iw.toNat))
            (toSubCol p (j / 4 % iw.toNat)) (passWidth p iw.toNat) hsubW_pos hsc_lt
          have hk_mod := mul_add_mod_eq (toSubRow p (j / 4 / iw.toNat))
            (toSubCol p (j / 4 % iw.toNat)) (passWidth p iw.toNat) hsc_lt
          have hfr := fromSubRow_toSubRow p _ hp.1
          have hfc := fromSubCol_toSubCol p _ hp.2
          -- idx = 4 * (r * w + c) = 4 * (j / 4)
          simp only [hk_div, hk_mod, hfr, hfc]
          -- idx + ch = 4 * (j/4/w * w + j/4%w) + j%4 = 4*(j/4) + j%4 = j
          have hj_recon : 4 * (j / 4 / iw.toNat * iw.toNat + j / 4 % iw.toNat) + 3 < ipix.size := by
            rw [show j / 4 / iw.toNat * iw.toNat + j / 4 % iw.toNat = j / 4
                from by rw [Nat.mul_comm]; exact Nat.div_add_mod _ iw.toNat]
            -- Goal: 4 * (j / 4) + 3 < ipix.size
            -- hj : j < iw.toNat * ih.toNat * 4, hpix_sz : ipix.size = iw.toNat * ih.toNat * 4
            rw [hpix_sz]
            -- Goal: 4 * (j / 4) + 3 < iw.toNat * ih.toNat * 4
            -- Need j / 4 < iw.toNat * ih.toNat for omega
            have hj4 : j / 4 < iw.toNat * ih.toNat := by
              have : j < 4 * (iw.toNat * ih.toNat) := by omega
              exact Nat.div_lt_of_lt_mul this
            rw [show iw.toNat * ih.toNat * 4 = 4 * (iw.toNat * ih.toNat) from by
              rw [Nat.mul_comm]]
            omega
          simp only [hj_recon, ↓reduceDIte]
          -- Now: ipix[idx]'proof = ipix[j]! where idx = j
          -- Convert proven-bounds getElem to getElem!, then rewrite index
          have hidx_eq : 4 * (j / 4 / iw.toNat * iw.toNat + j / 4 % iw.toNat) + j % 4 = j := by
            rw [show j / 4 / iw.toNat * iw.toNat + j / 4 % iw.toNat = j / 4
                from by rw [Nat.mul_comm]; exact Nat.div_add_mod _ iw.toNat]
            exact Nat.div_add_mod j 4
          rw [← getElem!_pos ipix _ (by rw [hidx_eq]; simp only [ByteArray.size] at hpix_sz; omega), hidx_eq]

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

end Png.Spec.InterlaceCorrect
