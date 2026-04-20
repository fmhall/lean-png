import ZipForStd.ByteArray

/-!
# General ByteArray lemmas

Reusable lemmas about ByteArray, Array, and getElem! that are
independent of PNG. Candidates for upstreaming to ZipForStd or
Lean's standard library.
-/

/-! ## ByteArray extensionality via getElem! -/

/-- Two ByteArrays are equal if they have the same size and agree at every index. -/
theorem ByteArray.ext_getElem! (a b : ByteArray) (hs : a.size = b.size)
    (hg : ∀ i, i < a.size → a[i]! = b[i]!) : a = b := by
  apply ByteArray.ext
  exact Array.ext hs fun i h1 _ => by
    have hi : i < a.size := h1
    have hi2 : i < b.size := by omega
    have := hg i hi
    rw [getElem!_pos a i hi, getElem!_pos b i hi2] at this; exact this

/-! ## getElem! bridging -/

/-- `getElem!` equals `getElem` when the index is in bounds. -/
theorem ByteArray.getElem!_eq_getElem (ba : ByteArray) (i : Nat) (h : i < ba.size) :
    ba[i]! = ba[i] := by
  simp only [GetElem?.getElem!, decidableGetElem?, h, ↓reduceDIte]

/-- `ByteArray.get!` equals `getElem!`. -/
theorem ByteArray.get!_eq_getElem! (ba : ByteArray) (i : Nat) :
    ba.get! i = ba[i]! := by
  simp only [ByteArray.get!]
  by_cases h : i < ba.size
  · rw [getElem!_pos ba.data i h, getElem!_pos ba i h]; rfl
  · rw [getElem!_neg ba.data i h, getElem!_neg ba i h]

/-! ## Append indexing -/

/-- Reading from the left portion of a concatenation. -/
theorem ByteArray.append_getElem!_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by rw [ByteArray.size_append]; omega),
      getElem!_pos a i h]
  exact ByteArray.getElem_append_left h

/-- Reading past the split point gives the right array's byte. -/
theorem ByteArray.append_getElem!_right (a b : ByteArray) (j : Nat) (hj : j < b.size) :
    (a ++ b)[a.size + j]! = b[j]! := by
  have h1 : a.size + j < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (a ++ b) (a.size + j) h1, getElem!_pos b j hj,
      ByteArray.getElem_append_right (show a.size ≤ a.size + j from by omega)]
  congr 1; omega

/-! ## Array push indexing -/

/-- Push preserves earlier elements (getElem! version). -/
theorem Array.push_getElem!_lt [Inhabited α] (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  have h1 : i < (a.push x).size := by rw [Array.size_push]; omega
  change (if i < (a.push x).size then (a.push x)[i] else default) =
         (if i < a.size then a[i] else default)
  rw [if_pos h1, if_pos h, Array.getElem_push_lt h]
