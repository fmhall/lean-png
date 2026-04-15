import Png.Native.Chunk
import Png.Util.ByteArray

/-!
# Chunk Framing Correctness Specifications

Specification theorems for PNG chunk parsing and serialization.
These are characterizing properties — they state mathematical
invariants independent of the implementation:

1. **Roundtrip**: `parseChunk (serialize c)` recovers the original chunk
2. **CRC validity**: serialized chunks always pass CRC validation
3. **IHDR roundtrip**: `IHDRInfo.fromBytes (IHDRInfo.toBytes ihdr)` recovers the IHDR
4. **Chunk sequence**: validity predicate properties
-/

namespace Png.Spec

/-! ## Helper lemmas -/

theorem writeUInt32BE_size (v : UInt32) : (writeUInt32BE v).size = 4 := by
  simp only [writeUInt32BE, ByteArray.size, Array.size, List.length]

theorem readUInt32BE_writeUInt32BE_append (v : UInt32) (rest : ByteArray) :
    readUInt32BE (writeUInt32BE v ++ rest) 0 = v := by
  simp only [readUInt32BE, writeUInt32BE]
  have hsz : (ByteArray.mk #[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8] ++ rest).size
    = 4 + rest.size := by
    rw [ByteArray.size_append]; simp only [ByteArray.size, Array.size, List.length]
  have h4 : 0 + 4 ≤ (ByteArray.mk #[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8] ++ rest).size := by omega
  simp only [h4, ↓reduceDIte]
  have h0 : (0 : Nat) < (ByteArray.mk #[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]).size := by
    simp only [ByteArray.size, Array.size, List.length]; omega
  have h1 : (1 : Nat) < (ByteArray.mk #[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]).size := by
    simp only [ByteArray.size, Array.size, List.length]; omega
  have h2 : (2 : Nat) < (ByteArray.mk #[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]).size := by
    simp only [ByteArray.size, Array.size, List.length]; omega
  have h3 : (3 : Nat) < (ByteArray.mk #[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]).size := by
    simp only [ByteArray.size, Array.size, List.length]; omega
  rw [ByteArray.getElem_append_left h0, ByteArray.getElem_append_left h1,
      ByteArray.getElem_append_left h2, ByteArray.getElem_append_left h3]
  show (v >>> 24).toUInt8.toUInt32 <<< 24 ||| (v >>> 16).toUInt8.toUInt32 <<< 16 |||
    (v >>> 8).toUInt8.toUInt32 <<< 8 ||| v.toUInt8.toUInt32 = v
  bv_decide

set_option maxHeartbeats 800000 in
theorem readUInt32BE_append_at_size (a b : ByteArray) (hn : 4 ≤ b.size) :
    readUInt32BE (a ++ b) a.size = readUInt32BE b 0 := by
  simp only [readUInt32BE]
  rw [dif_pos (by rw [ByteArray.size_append]; omega : a.size + 4 ≤ (a ++ b).size),
      dif_pos (by omega : 0 + 4 ≤ b.size)]
  simp only [
    ByteArray.getElem_append_right (by omega : a.size ≤ a.size),
    ByteArray.getElem_append_right (by omega : a.size ≤ a.size + 1),
    ByteArray.getElem_append_right (by omega : a.size ≤ a.size + 2),
    ByteArray.getElem_append_right (by omega : a.size ≤ a.size + 3),
    Nat.sub_self, Nat.add_sub_cancel_left]
  rfl

/-! ## Serialize/parse roundtrip -/

/-- The CRC stored in a serialized chunk matches the computed CRC.
    This follows from the construction, but is a useful standalone property. -/
theorem serialize_crc_valid (c : PngChunk) :
    let s := c.serialize
    readUInt32BE s (8 + c.data.size) = Crc32.Native.crc32 0 (writeUInt32BE c.chunkType ++ c.data) := by
  simp only [PngChunk.serialize]
  have hprefix_size : (writeUInt32BE c.data.size.toUInt32 ++ (writeUInt32BE c.chunkType ++ c.data)).size = 8 + c.data.size := by
    rw [ByteArray.size_append, ByteArray.size_append, writeUInt32BE_size, writeUInt32BE_size]; omega
  rw [show 8 + c.data.size = (writeUInt32BE c.data.size.toUInt32 ++ (writeUInt32BE c.chunkType ++ c.data)).size from hprefix_size.symm]
  rw [readUInt32BE_append_at_size _ _ (by rw [writeUInt32BE_size]; omega)]
  rw [show writeUInt32BE (Crc32.Native.crc32 0 (writeUInt32BE c.chunkType ++ c.data)) =
    writeUInt32BE (Crc32.Native.crc32 0 (writeUInt32BE c.chunkType ++ c.data)) ++ ByteArray.empty from by
    simp only [ByteArray.append_empty]]
  exact readUInt32BE_writeUInt32BE_append _ _

/-- Serialized chunk length field matches data size. -/
theorem serialize_length_field (c : PngChunk) :
    readUInt32BE c.serialize 0 = c.data.size.toUInt32 := by
  simp only [PngChunk.serialize]
  rw [ByteArray.append_assoc]
  exact readUInt32BE_writeUInt32BE_append _ _

/-- Serialized chunk type field matches chunk type. -/
theorem serialize_type_field (c : PngChunk) :
    readUInt32BE c.serialize 4 = c.chunkType := by
  simp only [PngChunk.serialize]
  rw [ByteArray.append_assoc]
  rw [show (4 : Nat) = (writeUInt32BE c.data.size.toUInt32).size from (writeUInt32BE_size _).symm]
  rw [readUInt32BE_append_at_size _ _ (by
    rw [ByteArray.size_append, ByteArray.size_append, writeUInt32BE_size]; omega)]
  rw [ByteArray.append_assoc]
  exact readUInt32BE_writeUInt32BE_append _ _

/-- Serialized chunk size is exactly 12 + data length. -/
theorem serialize_size (c : PngChunk) :
    c.serialize.size = 12 + c.data.size := by
  simp only [PngChunk.serialize, writeUInt32BE]
  simp only [ByteArray.size_append]
  simp only [ByteArray.size, Array.size, List.length]
  omega

theorem serialize_extract_type_data (c : PngChunk) :
    c.serialize.extract 4 (8 + c.data.size) = writeUInt32BE c.chunkType ++ c.data := by
  simp only [PngChunk.serialize]
  rw [ByteArray.append_assoc]
  rw [ByteArray.extract_append_ge (writeUInt32BE c.data.size.toUInt32) _ 4 (8 + c.data.size)
    (by rw [writeUInt32BE_size]; omega)]
  simp only [writeUInt32BE_size, Nat.sub_self,
    show 8 + c.data.size - 4 = 4 + c.data.size from by omega]
  rw [show (4 + c.data.size) = (writeUInt32BE c.chunkType ++ c.data).size from by
    rw [ByteArray.size_append, writeUInt32BE_size]]
  exact ByteArray.extract_append_left _ _

theorem serialize_extract_data (c : PngChunk) :
    c.serialize.extract 8 (8 + c.data.size) = c.data := by
  simp only [PngChunk.serialize]
  rw [ByteArray.append_assoc]
  rw [ByteArray.extract_append_ge (writeUInt32BE c.data.size.toUInt32) _ 8 (8 + c.data.size)
    (by rw [writeUInt32BE_size]; omega)]
  simp only [writeUInt32BE_size,
    show 8 - 4 = 4 from by omega,
    show 8 + c.data.size - 4 = 4 + c.data.size from by omega]
  rw [ByteArray.append_assoc]
  rw [ByteArray.extract_append_ge (writeUInt32BE c.chunkType) _ 4 (4 + c.data.size)
    (by rw [writeUInt32BE_size]; omega)]
  simp only [writeUInt32BE_size, Nat.sub_self,
    show 4 + c.data.size - 4 = c.data.size from by omega]
  exact ByteArray.extract_append_left _ _

set_option maxHeartbeats 800000 in
/-- Parsing a serialized chunk recovers the original chunk.
    Requires that chunk data fits in the PNG length field (< 2^31 bytes per spec). -/
theorem parseChunk_serialize (c : PngChunk) (hlen : c.data.size < 2 ^ 31) :
    parseChunk c.serialize 0 = .ok ⟨c, c.serialize.size⟩ := by
  have hlen32 : c.data.size < 2 ^ 32 := by omega
  have hrt : c.data.size.toUInt32.toNat = c.data.size := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat', Nat.reducePow, Nat.mod_eq_of_lt hlen32]
  have hsize : c.serialize.size = 12 + c.data.size := serialize_size c
  simp only [Png.parseChunk,
    serialize_length_field c, serialize_type_field c, hrt,
    show ¬(0 + 12 > c.serialize.size) from by rw [hsize]; omega,
    show ¬(0 + 8 + c.data.size + 4 > c.serialize.size) from by rw [hsize]; omega,
    show (0 + 4 : Nat) = 4 from by omega,
    show (0 + 8 : Nat) = 8 from by omega,
    ↓reduceIte,
    bind, Except.bind, pure, Except.pure]
  -- Resolve CRC check
  rw [serialize_extract_type_data c,
    show (readUInt32BE c.serialize (8 + c.data.size) !=
      Crc32.Native.crc32 0 (writeUInt32BE c.chunkType ++ c.data)) = false from by
      rw [serialize_crc_valid c]; exact bne_self_eq_false _]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Resolve data extract and offset
  rw [serialize_extract_data c,
    show 8 + c.data.size + 4 = c.serialize.size from by rw [hsize]; omega]

/-! ## IHDR roundtrip helpers -/

-- ByteArray.getElem!_eq_getElem is now in Png.Util.ByteArray

private theorem ihdr_prefix_size (ihdr : IHDRInfo) :
    (writeUInt32BE ihdr.width ++ writeUInt32BE ihdr.height).size = 8 := by
  rw [ByteArray.size_append]; simp only [writeUInt32BE, ByteArray.size, Array.size, List.length]

private theorem ihdr_toBytes_tail (ihdr : IHDRInfo) (k : Nat) (hk : 8 ≤ k) (hk2 : k < 13) :
    ihdr.toBytes[k]! =
      (ByteArray.mk #[ihdr.bitDepth, ihdr.colorType.toUInt8, ihdr.compressionMethod,
        ihdr.filterMethod, ihdr.interlaceMethod.toUInt8])[k - 8]'(by
        simp only [ByteArray.size, Array.size, List.length]; omega) := by
  rw [ByteArray.getElem!_eq_getElem _ _ (by
    simp only [IHDRInfo.toBytes, writeUInt32BE]
    simp only [ByteArray.size_append]
    simp only [ByteArray.size, Array.size, List.length]; omega)]
  simp only [IHDRInfo.toBytes]
  rw [ByteArray.getElem_append_right (by rw [ihdr_prefix_size]; omega)]
  simp only [ihdr_prefix_size]

private theorem ihdr_read_width (ihdr : IHDRInfo) :
    readUInt32BE ihdr.toBytes 0 = ihdr.width := by
  simp only [IHDRInfo.toBytes, ByteArray.append_assoc]
  exact readUInt32BE_writeUInt32BE_append _ _

private theorem ihdr_read_height (ihdr : IHDRInfo) :
    readUInt32BE ihdr.toBytes 4 = ihdr.height := by
  simp only [IHDRInfo.toBytes, ByteArray.append_assoc]
  rw [show (4 : Nat) = (writeUInt32BE ihdr.width).size from (writeUInt32BE_size _).symm]
  rw [readUInt32BE_append_at_size _ _ (by
    rw [ByteArray.size_append, writeUInt32BE_size, ByteArray.size, Array.size, List.length]; omega)]
  exact readUInt32BE_writeUInt32BE_append _ _

/-! ## IHDR roundtrip -/

set_option maxHeartbeats 6400000 in
/-- Parsing serialized IHDR bytes recovers the original IHDR,
    provided the IHDR has valid field values. -/
theorem ihdr_fromBytes_toBytes (ihdr : IHDRInfo)
    (hw : ihdr.width ≠ 0) (hh : ihdr.height ≠ 0)
    (hc : ihdr.compressionMethod = 0) (hf : ihdr.filterMethod = 0) :
    IHDRInfo.fromBytes ihdr.toBytes = .ok ihdr := by
  unfold IHDRInfo.fromBytes
  -- Size check: toBytes.size = 13, so dite resolves via dif_pos
  have htsz : ihdr.toBytes.size = 13 := by
    simp only [IHDRInfo.toBytes, writeUInt32BE]; simp only [ByteArray.size_append];
    simp only [ByteArray.size, Array.size, List.length]
  rw [dif_pos htsz]
  -- Normalize getElem (proven bounds) back to getElem! for compatibility with sub-lemmas
  simp only [← getElem!_pos]
  -- Width check: readUInt32BE toBytes 0 = width ≠ 0
  simp only [ihdr_read_width, beq_iff_eq, hw, ↓reduceIte]
  -- Height check
  simp only [ihdr_read_height, hh, ↓reduceIte]
  -- ColorType roundtrip
  simp only [show ihdr.toBytes[9]! = ihdr.colorType.toUInt8 from by
    have := ihdr_toBytes_tail ihdr 9 (by omega) (by omega); simpa using this]
  simp only [show ColorType.ofUInt8 ihdr.colorType.toUInt8 = some ihdr.colorType from by
    cases ihdr.colorType <;> rfl]
  -- Compression method check: toBytes[10]! = compressionMethod = 0
  simp only [show ihdr.toBytes[10]! = ihdr.compressionMethod from by
    have := ihdr_toBytes_tail ihdr 10 (by omega) (by omega); simpa using this,
    hc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  -- Filter method check
  simp only [show ihdr.toBytes[11]! = ihdr.filterMethod from by
    have := ihdr_toBytes_tail ihdr 11 (by omega) (by omega); simpa using this,
    hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  -- Interlace method roundtrip
  simp only [show ihdr.toBytes[12]! = ihdr.interlaceMethod.toUInt8 from by
    have := ihdr_toBytes_tail ihdr 12 (by omega) (by omega); simpa using this]
  simp only [show InterlaceMethod.ofUInt8 ihdr.interlaceMethod.toUInt8 = some ihdr.interlaceMethod from by
    cases ihdr.interlaceMethod <;> rfl]
  -- Bit depth and final structure
  simp only [show ihdr.toBytes[8]! = ihdr.bitDepth from by
    have := ihdr_toBytes_tail ihdr 8 (by omega) (by omega); simpa using this]
  -- Now the do-notation with pure binds should reduce to .ok { ... }
  obtain ⟨w, h, bd, ct, cm, fm, im⟩ := ihdr
  subst hc; subst hf
  rfl

/-- IHDR serialization always produces exactly 13 bytes. -/
theorem ihdr_toBytes_size (ihdr : IHDRInfo) :
    ihdr.toBytes.size = 13 := by
  simp only [IHDRInfo.toBytes, writeUInt32BE]
  simp only [ByteArray.size_append]
  simp only [ByteArray.size, Array.size, List.length]

/-! ## Color type properties -/

/-- ColorType.ofUInt8 is a left inverse of ColorType.toUInt8. -/
theorem colorType_ofUInt8_toUInt8 (ct : ColorType) :
    ColorType.ofUInt8 ct.toUInt8 = some ct := by
  cases ct <;> rfl

/-- InterlaceMethod.ofUInt8 is a left inverse of InterlaceMethod.toUInt8. -/
theorem interlaceMethod_ofUInt8_toUInt8 (im : InterlaceMethod) :
    InterlaceMethod.ofUInt8 im.toUInt8 = some im := by
  cases im <;> rfl

/-! ## Critical/ancillary classification -/

/-- IHDR is a critical chunk. -/
theorem ihdr_isCritical : ChunkType.isCritical ChunkType.IHDR = true := by
  decide

/-- IDAT is a critical chunk. -/
theorem idat_isCritical : ChunkType.isCritical ChunkType.IDAT = true := by
  decide

/-- IEND is a critical chunk. -/
theorem iend_isCritical : ChunkType.isCritical ChunkType.IEND = true := by
  decide

/-- PLTE is a critical chunk. -/
theorem plte_isCritical : ChunkType.isCritical ChunkType.PLTE = true := by
  decide

/-! ## Chunk sequence validity -/

/-- `idatContiguous` past the end of the array always returns true. -/
theorem idatContiguous_ge (chunks : Array PngChunk) (i : Nat)
    (inIdat afterIDAT : Bool) (h : i ≥ chunks.size) :
    idatContiguous chunks i inIdat afterIDAT = true := by
  unfold idatContiguous
  rw [dif_neg (by omega)]

/-- Stepping through a non-IDAT chunk. -/
theorem idatContiguous_non_idat (chunks : Array PngChunk) (i : Nat)
    (inIdat afterIDAT : Bool) (hi : i < chunks.size)
    (hnotIDAT : chunks[i].isIDAT = false) :
    idatContiguous chunks i inIdat afterIDAT =
      idatContiguous chunks (i + 1) false (afterIDAT || inIdat) := by
  rw [idatContiguous.eq_1]
  simp only [hi, ↓reduceDIte, hnotIDAT, Bool.false_eq_true, ↓reduceIte]

/-- Stepping through an IDAT chunk with afterIDAT = false. -/
theorem idatContiguous_idat (chunks : Array PngChunk) (i : Nat)
    (inIdat : Bool) (hi : i < chunks.size)
    (hIDAT : chunks[i].isIDAT = true) :
    idatContiguous chunks i inIdat false =
      idatContiguous chunks (i + 1) true false := by
  rw [idatContiguous.eq_1]
  simp only [hi, ↓reduceDIte, hIDAT, Bool.false_eq_true, ↓reduceIte]

/-- Stepping through an IDAT chunk with afterIDAT = true returns false. -/
private theorem idatContiguous_idat_after (chunks : Array PngChunk) (i : Nat)
    (inIdat : Bool) (hi : i < chunks.size)
    (hIDAT : chunks[i].isIDAT = true) :
    idatContiguous chunks i inIdat true = false := by
  rw [idatContiguous.eq_1]
  simp only [hi, ↓reduceDIte, hIDAT, ↓reduceIte]

/-- If `isIHDR` is true then `isIDAT` is false. -/
theorem isIHDR_not_isIDAT (c : PngChunk) (h : c.isIHDR = true) :
    c.isIDAT = false := by
  simp only [PngChunk.isIHDR, PngChunk.isIDAT, beq_iff_eq] at h ⊢
  rw [h]; decide

/-- If `isIEND` is true then `isIDAT` is false. -/
theorem isIEND_not_isIDAT (c : PngChunk) (h : c.isIEND = true) :
    c.isIDAT = false := by
  simp only [PngChunk.isIEND, PngChunk.isIDAT, beq_iff_eq] at h ⊢
  rw [h]; decide

/-- Process a segment where no chunks are IDAT, preserving afterIDAT=false. -/
private theorem idatContiguous_noIdat_segment (chunks : Array PngChunk) (i n : Nat)
    (h : ∀ j, i ≤ j → j < i + n → (hj : j < chunks.size) → (chunks[j]'hj).isIDAT = false)
    (hn : i + n ≤ chunks.size) :
    idatContiguous chunks i false false = idatContiguous chunks (i + n) false false := by
  induction n generalizing i with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    have hi : i < chunks.size := by omega
    rw [idatContiguous_non_idat chunks i false false hi (h i (Nat.le_refl _) (by omega) hi)]
    simp only [Bool.false_or]
    have := ih (i + 1) (fun j hj1 hj2 hj3 => h j (by omega) (by omega) hj3) (by omega)
    rw [show i + 1 + k = i + (k + 1) from by omega] at this
    exact this

/-- Continue through IDAT chunks when already in IDAT mode. -/
theorem idatContiguous_idat_run (chunks : Array PngChunk) (i n : Nat)
    (h : ∀ j, i ≤ j → j < i + n → (hj : j < chunks.size) → (chunks[j]'hj).isIDAT = true)
    (hn : i + n ≤ chunks.size) :
    idatContiguous chunks i true false = idatContiguous chunks (i + n) true false := by
  induction n generalizing i with
  | zero => simp only [Nat.add_zero]
  | succ k ih =>
    have hi : i < chunks.size := by omega
    rw [idatContiguous_idat chunks i true hi (h i (Nat.le_refl _) (by omega) hi)]
    have := ih (i + 1) (fun j hj1 hj2 hj3 => h j (by omega) (by omega) hj3) (by omega)
    rw [show i + 1 + k = i + (k + 1) from by omega] at this
    exact this

/-- Process a segment where all chunks are IDAT starting from non-IDAT mode. -/
theorem idatContiguous_allIdat_segment (chunks : Array PngChunk) (i n : Nat)
    (h : ∀ j, i ≤ j → j < i + n → (hj : j < chunks.size) → (chunks[j]'hj).isIDAT = true)
    (hn : i + n ≤ chunks.size)
    (hpos : n > 0) :
    idatContiguous chunks i false false = idatContiguous chunks (i + n) true false := by
  have hi : i < chunks.size := by omega
  rw [idatContiguous_idat chunks i false hi (h i (Nat.le_refl _) (by omega) hi)]
  rw [idatContiguous_idat_run chunks (i + 1) (n - 1)
    (fun j hj1 hj2 hj3 => h j (by omega) (by omega) hj3) (by omega)]
  congr 1; omega

/-- A sequence with IHDR first, some IDATs, and IEND last is valid. -/
theorem validChunkSequence_basic
    (ihdr : PngChunk) (idats : Array PngChunk) (iend : PngChunk)
    (middle : Array PngChunk)
    (hIHDR : ihdr.isIHDR = true)
    (hIEND : iend.isIEND = true)
    (hIDATs : ∀ c ∈ idats.toList, c.isIDAT = true)
    (hMiddle : ∀ c ∈ middle.toList, c.isIDAT = false)
    (hNonemptyIDAT : idats.size > 0) :
    validChunkSequence (#[ihdr] ++ middle ++ idats ++ #[iend]) = true := by
  have hsz1 : (#[ihdr] : Array PngChunk).size = 1 := rfl
  have hsze : (#[iend] : Array PngChunk).size = 1 := rfl
  have hihdr_not_idat := isIHDR_not_isIDAT ihdr hIHDR
  have hiend_not_idat := isIEND_not_isIDAT iend hIEND
  have hnoIdat_prefix : ∀ j, 0 ≤ j → j < 1 + middle.size →
      (hj : j < (#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk).size) →
      ((#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk)[j]).isIDAT = false := by
    intro j _ hjm hjs
    rw [Array.getElem_append_left (by simp only [Array.size_append, hsz1]; omega : j < (#[ihdr] ++ middle ++ idats).size)]
    rw [Array.getElem_append_left (by simp only [Array.size_append, hsz1]; omega : j < (#[ihdr] ++ middle).size)]
    by_cases hj0 : j = 0
    · subst hj0; rw [Array.getElem_append_left (by simp only [hsz1]; omega : (0 : Nat) < (#[ihdr] : Array PngChunk).size)]
      exact hihdr_not_idat
    · rw [Array.getElem_append_right (by simp only [hsz1]; omega : (#[ihdr] : Array PngChunk).size ≤ j)]
      simp only [hsz1]
      exact hMiddle _ (Array.getElem_mem_toList ..)
  have hisIdat_range : ∀ j, 1 + middle.size ≤ j → j < 1 + middle.size + idats.size →
      (hj : j < (#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk).size) →
      ((#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk)[j]).isIDAT = true := by
    intro j hj1 hjm hjs
    rw [Array.getElem_append_left (by simp only [Array.size_append, hsz1]; omega : j < (#[ihdr] ++ middle ++ idats).size)]
    rw [Array.getElem_append_right (by simp only [Array.size_append, hsz1]; omega : (#[ihdr] ++ middle).size ≤ j)]
    simp only [Array.size_append, hsz1, show j - (1 + middle.size) = j - 1 - middle.size from by omega]
    exact hIDATs _ (Array.getElem_mem_toList ..)
  have hnoIdat_suffix : ∀ j, 1 + middle.size + idats.size ≤ j →
      (hj : j < (#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk).size) →
      ((#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk)[j]).isIDAT = false := by
    intro j hj1 hjs
    have hj_eq : j = 1 + middle.size + idats.size := by
      simp only [Array.size_append, hsz1, hsze] at hjs; omega
    subst hj_eq
    rw [Array.getElem_append_right (by simp only [Array.size_append, hsz1]; omega : (#[ihdr] ++ middle ++ idats).size ≤ 1 + middle.size + idats.size)]
    simp only [Array.size_append, hsz1,
      show 1 + middle.size + idats.size - (1 + middle.size + idats.size) = 0 from by omega]
    exact hiend_not_idat
  have hphase1 := idatContiguous_noIdat_segment (#[ihdr] ++ middle ++ idats ++ #[iend]) 0 (1 + middle.size)
      (fun j hj1 hj2 hjs => hnoIdat_prefix j (by omega) (by omega) hjs) (by simp only [Array.size_append, hsz1, hsze]; omega)
  have hphase2 := idatContiguous_allIdat_segment (#[ihdr] ++ middle ++ idats ++ #[iend]) (1 + middle.size) idats.size
      (fun j hj1 hj2 hjs => hisIdat_range j hj1 (by omega) hjs) (by simp only [Array.size_append, hsz1, hsze]; omega) hNonemptyIDAT
  have hphase3 := idatContiguous_non_idat (#[ihdr] ++ middle ++ idats ++ #[iend]) (1 + middle.size + idats.size) true false
      (by simp only [Array.size_append, hsz1, hsze]; omega) (hnoIdat_suffix _ (by omega) (by simp only [Array.size_append, hsz1, hsze]; omega))
  have hphase4 := idatContiguous_ge (#[ihdr] ++ middle ++ idats ++ #[iend]) (1 + middle.size + idats.size + 1) false true
      (by simp only [Array.size_append, hsz1, hsze]; omega)
  have hfirst : (#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk)[0]!.isIHDR = true := by
    rw [getElem!_pos _ _ (by simp only [Array.size_append, hsz1, hsze]; omega)]
    rw [Array.getElem_append_left (by simp only [Array.size_append, hsz1]; omega : (0 : Nat) < (#[ihdr] ++ middle ++ idats).size)]
    rw [Array.getElem_append_left (by simp only [Array.size_append, hsz1]; omega : (0 : Nat) < (#[ihdr] ++ middle).size)]
    rw [Array.getElem_append_left (by simp only [hsz1]; omega : (0 : Nat) < (#[ihdr] : Array PngChunk).size)]
    exact hIHDR
  have hlast : (#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk)[(#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk).size - 1]!.isIEND = true := by
    have hsz : (#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk).size =
        1 + middle.size + idats.size + 1 := by
      simp only [Array.size_append, hsz1, hsze]
    rw [hsz]
    show (#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk)[1 + middle.size + idats.size + 1 - 1]!.isIEND = true
    rw [show 1 + middle.size + idats.size + 1 - 1 = 1 + middle.size + idats.size from by omega]
    rw [getElem!_pos _ _ (by rw [hsz]; omega)]
    rw [Array.getElem_append_right (by simp only [Array.size_append, hsz1]; omega : (#[ihdr] ++ middle ++ idats).size ≤ 1 + middle.size + idats.size)]
    simp only [Array.size_append, hsz1,
      show 1 + middle.size + idats.size - (1 + middle.size + idats.size) = 0 from by omega]
    exact hIEND
  simp only [Nat.zero_add] at hphase1
  have hphase3' : idatContiguous (#[ihdr] ++ middle ++ idats ++ #[iend])
      (1 + middle.size + idats.size) true false =
      idatContiguous (#[ihdr] ++ middle ++ idats ++ #[iend])
      (1 + middle.size + idats.size + 1) false true := by
    rw [hphase3]; rfl
  unfold validChunkSequence
  have hszne : (#[ihdr] ++ middle ++ idats ++ #[iend] : Array PngChunk).size ≠ 0 := by
    simp only [Array.size_append, hsz1, hsze]; omega
  rw [dif_neg hszne]
  -- Normalize getElem (proven bounds) back to getElem! for compatibility with hfirst/hlast
  simp only [← getElem!_pos]
  rw [hfirst, hlast, Bool.true_and, Bool.true_and, hphase1, hphase2, hphase3', hphase4]

/-- An empty chunk sequence is invalid. -/
theorem validChunkSequence_empty : validChunkSequence #[] = false := by
  rfl

/-! ## Big-endian roundtrip -/

/-- Reading back a written big-endian UInt32 recovers the original value. -/
theorem readUInt32BE_writeUInt32BE (v : UInt32) :
    readUInt32BE (writeUInt32BE v) 0 = v := by
  simp only [readUInt32BE, writeUInt32BE]
  simp only [ByteArray.size, Array.size, List.length]
  have h4 : 0 + 4 ≤ 0 + 1 + 1 + 1 + 1 := by omega
  simp only [h4, ↓reduceDIte]
  show (v >>> 24).toUInt8.toUInt32 <<< 24 ||| (v >>> 16).toUInt8.toUInt32 <<< 16 |||
    (v >>> 8).toUInt8.toUInt32 <<< 8 ||| v.toUInt8.toUInt32 = v
  bv_decide

/-! ## Offset-shifting helpers for parseChunk_at_offset -/

set_option maxHeartbeats 1600000 in
/-- Reading a UInt32 from the left portion of a concatenation,
    when the 4-byte window is entirely within the left portion. -/
theorem readUInt32BE_append_right (a b : ByteArray) (offset : Nat) (h : offset + 4 ≤ a.size) :
    readUInt32BE (a ++ b) offset = readUInt32BE a offset := by
  have hab : offset + 4 ≤ (a ++ b).size := by rw [ByteArray.size_append]; omega
  simp only [readUInt32BE, hab, h, ↓reduceDIte]
  simp only [ByteArray.getElem_append_left (show offset < a.size from by omega),
    ByteArray.getElem_append_left (show offset + 1 < a.size from by omega),
    ByteArray.getElem_append_left (show offset + 2 < a.size from by omega),
    ByteArray.getElem_append_left (show offset + 3 < a.size from by omega)]
  rfl

/-- Extracting a range entirely within the left portion of a concatenation. -/
theorem extract_append_within_left (a b : ByteArray) (i j : Nat) (hj : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append,
    ByteArray.size_data,
    show j - a.size = 0 from by omega,
    Array.extract_zero, Array.append_empty]

set_option maxHeartbeats 1600000 in
/-- Reading a UInt32 from the right portion of a concatenation at offset `a.size + k`. -/
theorem readUInt32BE_append_at_offset (a b : ByteArray) (k : Nat) (hk : k + 4 ≤ b.size) :
    readUInt32BE (a ++ b) (a.size + k) = readUInt32BE b k := by
  have hab : (a.size + k) + 4 ≤ (a ++ b).size := by rw [ByteArray.size_append]; omega
  simp only [readUInt32BE, hab, hk, ↓reduceDIte]
  simp only [
    ByteArray.getElem_append_right (show a.size ≤ a.size + k from by omega),
    ByteArray.getElem_append_right (show a.size ≤ a.size + k + 1 from by omega),
    ByteArray.getElem_append_right (show a.size ≤ a.size + k + 2 from by omega),
    ByteArray.getElem_append_right (show a.size ≤ a.size + k + 3 from by omega),
    show a.size + k - a.size = k from by omega,
    show a.size + k + 1 - a.size = k + 1 from by omega,
    show a.size + k + 2 - a.size = k + 2 from by omega,
    show a.size + k + 3 - a.size = k + 3 from by omega]
  rfl

/-- Extracting a range from the right portion of a concatenation. -/
theorem extract_append_at_offset (a b : ByteArray) (i j : Nat) :
    (a ++ b).extract (a.size + i) (a.size + j) = b.extract i j := by
  rw [ByteArray.extract_append_ge _ _ _ _ (by omega : a.size + i ≥ a.size)]
  congr 1 <;> omega

/-- Reading the length field of a serialized chunk with an appended suffix. -/
theorem serialize_length_field_append (c : PngChunk) (suffix : ByteArray) :
    readUInt32BE (c.serialize ++ suffix) 0 = c.data.size.toUInt32 := by
  rw [readUInt32BE_append_right _ _ _ (by rw [serialize_size]; omega)]
  exact serialize_length_field c

/-- Reading the type field of a serialized chunk with an appended suffix. -/
theorem serialize_type_field_append (c : PngChunk) (suffix : ByteArray) :
    readUInt32BE (c.serialize ++ suffix) 4 = c.chunkType := by
  rw [readUInt32BE_append_right _ _ _ (by rw [serialize_size]; omega)]
  exact serialize_type_field c

/-- Extracting type+data from a serialized chunk with an appended suffix. -/
theorem serialize_extract_type_data_append (c : PngChunk) (suffix : ByteArray) :
    (c.serialize ++ suffix).extract 4 (8 + c.data.size) = writeUInt32BE c.chunkType ++ c.data := by
  rw [extract_append_within_left _ _ _ _ (by rw [serialize_size]; omega)]
  exact serialize_extract_type_data c

/-- Extracting data from a serialized chunk with an appended suffix. -/
theorem serialize_extract_data_append (c : PngChunk) (suffix : ByteArray) :
    (c.serialize ++ suffix).extract 8 (8 + c.data.size) = c.data := by
  rw [extract_append_within_left _ _ _ _ (by rw [serialize_size]; omega)]
  exact serialize_extract_data c

/-- Reading the CRC field of a serialized chunk with an appended suffix. -/
theorem serialize_crc_valid_append (c : PngChunk) (suffix : ByteArray) :
    readUInt32BE (c.serialize ++ suffix) (8 + c.data.size) =
      Crc32.Native.crc32 0 (writeUInt32BE c.chunkType ++ c.data) := by
  rw [readUInt32BE_append_right _ _ _ (by rw [serialize_size]; omega)]
  exact serialize_crc_valid c

/-! ## PLTE roundtrip -/

/-- Size of `toBytes.go`: accumulator grows by `(entries.size - i) * 3`. -/
theorem plte_toBytes_go_size (entries : Array PaletteEntry) (i : Nat) (acc : ByteArray) :
    (PLTEInfo.toBytes.go entries i acc).size = acc.size + (entries.size - i) * 3 := by
  unfold PLTEInfo.toBytes.go
  split
  case isTrue h =>
    rw [plte_toBytes_go_size]
    simp only [ByteArray.size_push]
    omega
  case isFalse h =>
    omega
termination_by entries.size - i

/-- Top-level size: `plte.toBytes.size = plte.entries.size * 3`. -/
theorem plte_toBytes_size (plte : PLTEInfo) :
    plte.toBytes.size = plte.entries.size * 3 := by
  simp only [PLTEInfo.toBytes]
  rw [plte_toBytes_go_size]
  have : (ByteArray.empty).size = 0 := rfl
  omega

/-- Prefix preservation: `toBytes.go` does not modify earlier accumulator bytes. -/
theorem plte_toBytes_go_prefix (entries : Array PaletteEntry) (i : Nat) (acc : ByteArray)
    (j : Nat) (hj : j < acc.size) :
    (PLTEInfo.toBytes.go entries i acc)[j]! = acc[j]! := by
  unfold PLTEInfo.toBytes.go
  split
  case isTrue h =>
    have hj3 : j < (acc.push entries[i].r |>.push entries[i].g |>.push entries[i].b).size := by
      simp only [ByteArray.size_push]; omega
    rw [plte_toBytes_go_prefix _ _ _ _ hj3]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    exact ByteArray.push_getElem!_lt _ _ _ hj
  case isFalse => rfl
termination_by entries.size - i

/-- Content: the red byte of entry `k` is at position `acc.size + (k - i) * 3`. -/
theorem plte_toBytes_go_r (entries : Array PaletteEntry) (i : Nat) (acc : ByteArray)
    (k : Nat) (hki : i ≤ k) (hk : k < entries.size) :
    (PLTEInfo.toBytes.go entries i acc)[acc.size + (k - i) * 3]! = entries[k].r := by
  unfold PLTEInfo.toBytes.go
  have hi : i < entries.size := by omega
  rw [dif_pos hi]
  simp only []  -- inline the `have e := entries[i]`
  by_cases hik : i = k
  · subst hik
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    have hacc3 : acc.size < (acc.push entries[i].r |>.push entries[i].g |>.push entries[i].b).size := by
      simp only [ByteArray.size_push]; omega
    rw [plte_toBytes_go_prefix _ _ _ _ hacc3]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    exact ByteArray.push_getElem!_eq _ _
  · have acc3_size : (acc.push entries[i].r |>.push entries[i].g |>.push entries[i].b).size = acc.size + 3 := by
      simp only [ByteArray.size_push]
    rw [show acc.size + (k - i) * 3 = (acc.size + 3) + (k - (i + 1)) * 3 from by omega,
        ← acc3_size]
    exact plte_toBytes_go_r entries (i + 1) _ k (by omega) hk
termination_by entries.size - i

/-- Content: the green byte of entry `k` is at position `acc.size + (k - i) * 3 + 1`. -/
theorem plte_toBytes_go_g (entries : Array PaletteEntry) (i : Nat) (acc : ByteArray)
    (k : Nat) (hki : i ≤ k) (hk : k < entries.size) :
    (PLTEInfo.toBytes.go entries i acc)[acc.size + (k - i) * 3 + 1]! = entries[k].g := by
  unfold PLTEInfo.toBytes.go
  have hi : i < entries.size := by omega
  rw [dif_pos hi]
  simp only []
  by_cases hik : i = k
  · subst hik
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    have hacc3 : acc.size + 1 < (acc.push entries[i].r |>.push entries[i].g |>.push entries[i].b).size := by
      simp only [ByteArray.size_push]; omega
    rw [plte_toBytes_go_prefix _ _ _ _ hacc3]
    rw [ByteArray.push_getElem!_lt _ _ _ (by simp only [ByteArray.size_push]; omega)]
    rw [show acc.size + 1 = (acc.push entries[i].r).size from by simp only [ByteArray.size_push]]
    exact ByteArray.push_getElem!_eq _ _
  · have acc3_size : (acc.push entries[i].r |>.push entries[i].g |>.push entries[i].b).size = acc.size + 3 := by
      simp only [ByteArray.size_push]
    rw [show acc.size + (k - i) * 3 + 1 = (acc.size + 3) + (k - (i + 1)) * 3 + 1 from by omega,
        ← acc3_size]
    exact plte_toBytes_go_g entries (i + 1) _ k (by omega) hk
termination_by entries.size - i

/-- Content: the blue byte of entry `k` is at position `acc.size + (k - i) * 3 + 2`. -/
theorem plte_toBytes_go_b (entries : Array PaletteEntry) (i : Nat) (acc : ByteArray)
    (k : Nat) (hki : i ≤ k) (hk : k < entries.size) :
    (PLTEInfo.toBytes.go entries i acc)[acc.size + (k - i) * 3 + 2]! = entries[k].b := by
  unfold PLTEInfo.toBytes.go
  have hi : i < entries.size := by omega
  rw [dif_pos hi]
  simp only []
  by_cases hik : i = k
  · subst hik
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    have hacc3 : acc.size + 2 < (acc.push entries[i].r |>.push entries[i].g |>.push entries[i].b).size := by
      simp only [ByteArray.size_push]; omega
    rw [plte_toBytes_go_prefix _ _ _ _ hacc3]
    rw [show acc.size + 2 = (acc.push entries[i].r |>.push entries[i].g).size from by
      simp only [ByteArray.size_push]]
    exact ByteArray.push_getElem!_eq _ _
  · have acc3_size : (acc.push entries[i].r |>.push entries[i].g |>.push entries[i].b).size = acc.size + 3 := by
      simp only [ByteArray.size_push]
    rw [show acc.size + (k - i) * 3 + 2 = (acc.size + 3) + (k - (i + 1)) * 3 + 2 from by omega,
        ← acc3_size]
    exact plte_toBytes_go_b entries (i + 1) _ k (by omega) hk
termination_by entries.size - i

/-- Top-level: byte at position `k * 3` in `toBytes` is `entries[k].r`. -/
theorem plte_toBytes_r (plte : PLTEInfo) (k : Nat) (hk : k < plte.entries.size) :
    plte.toBytes[k * 3]! = plte.entries[k].r := by
  simp only [PLTEInfo.toBytes]
  rw [show k * 3 = 0 + (k - 0) * 3 from by omega]
  exact plte_toBytes_go_r plte.entries 0 ByteArray.empty k (by omega) hk

/-- Top-level: byte at position `k * 3 + 1` in `toBytes` is `entries[k].g`. -/
theorem plte_toBytes_g (plte : PLTEInfo) (k : Nat) (hk : k < plte.entries.size) :
    plte.toBytes[k * 3 + 1]! = plte.entries[k].g := by
  simp only [PLTEInfo.toBytes]
  rw [show k * 3 + 1 = 0 + (k - 0) * 3 + 1 from by omega]
  exact plte_toBytes_go_g plte.entries 0 ByteArray.empty k (by omega) hk

/-- Top-level: byte at position `k * 3 + 2` in `toBytes` is `entries[k].b`. -/
theorem plte_toBytes_b (plte : PLTEInfo) (k : Nat) (hk : k < plte.entries.size) :
    plte.toBytes[k * 3 + 2]! = plte.entries[k].b := by
  simp only [PLTEInfo.toBytes]
  rw [show k * 3 + 2 = 0 + (k - 0) * 3 + 2 from by omega]
  exact plte_toBytes_go_b plte.entries 0 ByteArray.empty k (by omega) hk

/-- Size of the result of `fromBytes.go`. -/
private theorem plte_fromBytes_go_size (data : ByteArray) (n i : Nat) (acc : Array PaletteEntry)
    (hi : i ≤ n) :
    (PLTEInfo.fromBytes.go data n i acc).size = acc.size + (n - i) := by
  unfold PLTEInfo.fromBytes.go
  split
  case isTrue h =>
    rw [plte_fromBytes_go_size _ _ _ _ (by omega)]
    simp only [Array.size_push]; omega
  case isFalse h => omega
termination_by n - i

/-- Element access in the result of `fromBytes.go`: accumulated prefix is preserved. -/
private theorem plte_fromBytes_go_prefix (data : ByteArray) (n i : Nat) (acc : Array PaletteEntry)
    (_hi : i ≤ n) (j : Nat) (hj : j < acc.size) :
    (PLTEInfo.fromBytes.go data n i acc)[j]! = acc[j]! := by
  unfold PLTEInfo.fromBytes.go
  split
  case isTrue h =>
    rw [plte_fromBytes_go_prefix _ _ _ _ (by omega) j (by simp only [Array.size_push]; omega)]
    exact Array.push_getElem!_lt acc _ j hj
  case isFalse => rfl
termination_by n - i

/-- `fromBytes.go` on `toBytes plte` recovers each original entry at position `k`. -/
theorem plte_fromBytes_go_entry (plte : PLTEInfo) (i : Nat) (hi : i ≤ plte.entries.size)
    (acc : Array PaletteEntry) (k : Nat) (hki : i ≤ k) (hk : k < plte.entries.size) :
    (PLTEInfo.fromBytes.go plte.toBytes plte.entries.size i acc)[acc.size + (k - i)]! =
      plte.entries[k] := by
  unfold PLTEInfo.fromBytes.go
  rw [if_pos (by omega : i < plte.entries.size)]
  -- The byte reads recover the original entry
  have hr : plte.toBytes.get! (i * 3) = plte.entries[i].r := by
    rw [ByteArray.get!_eq_getElem!]; exact plte_toBytes_r plte i (by omega)
  have hg : plte.toBytes.get! (i * 3 + 1) = plte.entries[i].g := by
    rw [ByteArray.get!_eq_getElem!]; exact plte_toBytes_g plte i (by omega)
  have hb : plte.toBytes.get! (i * 3 + 2) = plte.entries[i].b := by
    rw [ByteArray.get!_eq_getElem!]; exact plte_toBytes_b plte i (by omega)
  simp only [hr, hg, hb]
  have hentry : ({ r := plte.entries[i].r, g := plte.entries[i].g, b := plte.entries[i].b } : PaletteEntry) = plte.entries[i] := by
    obtain ⟨r, g, b⟩ := plte.entries[i]; rfl
  rw [hentry]
  by_cases hik : i = k
  · subst hik
    simp only [Nat.sub_self]
    -- Need: (go ... (i+1) (acc.push entries[i]))[acc.size + 0]! = entries[i]
    rw [show acc.size + 0 = acc.size from by omega]
    rw [show acc.size = (acc.push plte.entries[i]).size - 1 from by simp only [Array.size_push]; omega]
    rw [plte_fromBytes_go_prefix _ _ _ _ (by omega) _ (by simp only [Array.size_push]; omega)]
    simp only [Array.size_push]
    rw [show acc.size + 1 - 1 = acc.size from by omega]
    rw [getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    exact Array.getElem_push_eq
  · rw [show acc.size + (k - i) = (acc.push plte.entries[i]).size + (k - (i + 1)) from by
      simp only [Array.size_push]; omega]
    exact plte_fromBytes_go_entry plte (i + 1) (by omega) _ k (by omega) hk
termination_by plte.entries.size - i

/-- `fromBytes.go` starting from 0 with empty accumulator produces the original entries. -/
theorem plte_fromBytes_go_eq (plte : PLTEInfo) :
    PLTEInfo.fromBytes.go plte.toBytes plte.entries.size 0 #[] = plte.entries := by
  apply Array.ext
  · rw [plte_fromBytes_go_size _ _ _ _ (by omega)]
    simp only [Array.size_empty]; omega
  · intro i hi1 hi2
    have hi1' : i < plte.entries.size := hi2
    have heq := plte_fromBytes_go_entry plte 0 (by omega) #[] i (by omega) hi1'
    simp only [Array.size_empty, Nat.zero_add, Nat.sub_zero] at heq
    rw [← getElem!_pos (PLTEInfo.fromBytes.go plte.toBytes plte.entries.size 0 #[]) i hi1, heq]

/-- **PLTE roundtrip**: parsing serialized PLTE bytes recovers the original palette. -/
theorem plte_fromBytes_toBytes (plte : PLTEInfo)
    (hpos : plte.entries.size > 0) (hmax : plte.entries.size ≤ 256) :
    PLTEInfo.fromBytes plte.toBytes = .ok plte := by
  have hsize : plte.toBytes.size = plte.entries.size * 3 := plte_toBytes_size plte
  have hnum : plte.toBytes.size / 3 = plte.entries.size := by
    rw [hsize]; exact Nat.mul_div_cancel plte.entries.size (by omega)
  unfold PLTEInfo.fromBytes
  -- Prove the Bool guards evaluate to false
  have hg1 : (plte.toBytes.size == 0) = false := by
    cases h : plte.toBytes.size == 0
    · rfl
    · simp only [beq_iff_eq] at h; omega
  have hg2 : (plte.toBytes.size % 3 != 0) = false := by
    cases h : plte.toBytes.size % 3 != 0
    · rfl
    · simp only [bne_iff_ne, ne_eq] at h
      rw [hsize, Nat.mul_comm] at h
      exact absurd (Nat.mul_mod_right 3 plte.entries.size) h
  -- Eliminate the first two guards (Bool = true → False)
  simp only [hg1, hg2, Bool.false_eq_true, ↓reduceIte]
  -- Eliminate the third guard (Prop: numEntries > 256)
  simp only [hnum, show ¬ plte.entries.size > 256 from by omega, ↓reduceIte]
  -- The go function produces the original entries
  simp only [pure, Except.pure, bind, Except.bind]
  rw [plte_fromBytes_go_eq plte]

end Png.Spec
