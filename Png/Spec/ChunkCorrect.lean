import Png.Native.Chunk

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

private theorem writeUInt32BE_size (v : UInt32) : (writeUInt32BE v).size = 4 := by
  simp only [writeUInt32BE, ByteArray.size, Array.size, List.length]

private theorem readUInt32BE_writeUInt32BE_append (v : UInt32) (rest : ByteArray) :
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
private theorem readUInt32BE_append_at_size (a b : ByteArray) (hn : 4 ≤ b.size) :
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

/-- Parsing a serialized chunk recovers the original chunk.
    We parse at offset 0 in the serialized output. -/
theorem parseChunk_serialize (c : PngChunk) :
    parseChunk c.serialize 0 = .ok ⟨c, c.serialize.size⟩ := by
  sorry

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

/-! ## IHDR roundtrip -/

/-- Parsing serialized IHDR bytes recovers the original IHDR,
    provided the IHDR has valid field values. -/
theorem ihdr_fromBytes_toBytes (ihdr : IHDRInfo)
    (hw : ihdr.width ≠ 0) (hh : ihdr.height ≠ 0)
    (hc : ihdr.compressionMethod = 0) (hf : ihdr.filterMethod = 0) :
    IHDRInfo.fromBytes ihdr.toBytes = .ok ihdr := by
  sorry

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
  sorry

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

end Png.Spec
