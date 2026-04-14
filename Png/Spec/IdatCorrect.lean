import Png.Native.Idat
import Png.Util.ByteArray
import Zip.Spec.ZlibCorrect

/-!
# IDAT Decompression Correctness Specifications

Specification theorems for the IDAT pipeline. These are characterizing
properties stating that:

1. IDAT data extraction correctly concatenates chunk payloads
2. Compression/decompression roundtrips via lean-zip's verified zlib
3. Decompressed size matches IHDR expectations

The roundtrip theorem (`decompressIdat_compressIdat`) delegates to
lean-zip's `zlib_decompressSingle_compress` — we do NOT re-prove
compression correctness.
-/

namespace Png.Spec.Idat

open Png.Idat Zip.Native

/-! ## extractIdatData.go lemmas -/

/-- The accumulator can be factored out of `extractIdatData.go`. -/
private theorem extractIdatData_go_acc (chunks : Array PngChunk) (i : Nat)
    (acc : ByteArray) :
    extractIdatData.go chunks i acc =
    acc ++ extractIdatData.go chunks i ByteArray.empty := by
  suffices ∀ (n : Nat), chunks.size - i = n →
    extractIdatData.go chunks i acc =
    acc ++ extractIdatData.go chunks i ByteArray.empty from this _ rfl
  intro n
  induction n generalizing i acc with
  | zero =>
    intro hn
    rw [extractIdatData.go, extractIdatData.go]
    simp only [show ¬ i < chunks.size from by omega, ↓reduceDIte, ByteArray.append_empty]
  | succ n ih =>
    intro hn
    rw [extractIdatData.go, extractIdatData.go]
    by_cases h : i < chunks.size
    · simp only [h, ↓reduceDIte]
      split
      · rw [ih (i + 1) (acc ++ chunks[i].data) (by omega),
            ih (i + 1) (ByteArray.empty ++ chunks[i].data) (by omega)]
        simp only [ByteArray.append_assoc, ByteArray.empty_append]
      · exact ih (i + 1) acc (by omega)
    · simp only [h, ↓reduceDIte, ByteArray.append_empty]

/-- `extractIdatData.go` on `push` with a non-IDAT chunk skips it. -/
private theorem extractIdatData_go_push_nonIdat (chunks : Array PngChunk)
    (c : PngChunk) (hc : c.isIDAT = false) (i : Nat) (acc : ByteArray)
    (hi : i ≤ chunks.size) :
    extractIdatData.go (chunks.push c) i acc =
    extractIdatData.go chunks i acc := by
  suffices ∀ (n : Nat), chunks.size + 1 - i = n →
    extractIdatData.go (chunks.push c) i acc =
    extractIdatData.go chunks i acc from this _ rfl
  intro n
  induction n generalizing i acc with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn
    by_cases hlt : i < chunks.size
    · rw [extractIdatData.go, extractIdatData.go]
      simp only [Array.size_push, show i < chunks.size + 1 from by omega, hlt, ↓reduceDIte,
        Array.getElem_push_lt hlt]
      split
      · exact ih (i + 1) _ (by omega) (by omega)
      · exact ih (i + 1) acc (by omega) (by omega)
    · have hi_eq : i = chunks.size := by omega
      subst hi_eq
      rw [extractIdatData.go]
      simp only [Array.size_push, show chunks.size < chunks.size + 1 from by omega,
        ↓reduceDIte, Array.getElem_push_eq, hc, Bool.false_eq_true, ↓reduceIte]
      rw [extractIdatData.go]
      simp only [Array.size_push,
        show ¬ chunks.size + 1 < chunks.size + 1 from by omega, ↓reduceDIte]
      rw [extractIdatData.go]
      simp only [show ¬ chunks.size < chunks.size from by omega, ↓reduceDIte]

/-- `extractIdatData.go` on `push` with an IDAT chunk appends its data. -/
private theorem extractIdatData_go_push_idat (chunks : Array PngChunk)
    (data : ByteArray) (i : Nat) (acc : ByteArray)
    (hi : i ≤ chunks.size) :
    extractIdatData.go
      (chunks.push { chunkType := ChunkType.IDAT, data }) i acc =
    extractIdatData.go chunks i acc ++ data := by
  suffices ∀ (n : Nat), chunks.size + 1 - i = n →
    extractIdatData.go
      (chunks.push { chunkType := ChunkType.IDAT, data }) i acc =
    extractIdatData.go chunks i acc ++ data from this _ rfl
  intro n
  induction n generalizing i acc with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn
    by_cases hlt : i < chunks.size
    · rw [extractIdatData.go, extractIdatData.go]
      simp only [Array.size_push, show i < chunks.size + 1 from by omega, hlt, ↓reduceDIte,
        Array.getElem_push_lt hlt]
      split
      · exact ih (i + 1) _ (by omega) (by omega)
      · exact ih (i + 1) acc (by omega) (by omega)
    · have hi_eq : i = chunks.size := by omega
      subst hi_eq
      have hrhs : extractIdatData.go chunks chunks.size acc = acc := by
        rw [extractIdatData.go]
        simp only [show ¬ chunks.size < chunks.size from by omega, ↓reduceDIte]
      rw [hrhs]
      rw [extractIdatData.go]
      simp only [Array.size_push, show chunks.size < chunks.size + 1 from by omega,
        ↓reduceDIte, Array.getElem_push_eq, PngChunk.isIDAT, ChunkType.IDAT,
        BEq.rfl, ↓reduceIte]
      rw [extractIdatData.go]
      simp only [Array.size_push,
        show ¬ chunks.size + 1 < chunks.size + 1 from by omega, ↓reduceDIte]

/-- `extractIdatData` on `push` with an IDAT chunk appends its data. -/
private theorem extractIdatData_push_idat (arr : Array PngChunk) (data : ByteArray) :
    extractIdatData (arr.push { chunkType := ChunkType.IDAT, data }) =
    extractIdatData arr ++ data := by
  unfold extractIdatData
  exact extractIdatData_go_push_idat arr data 0 ByteArray.empty (by omega)

/-- Helper: a ByteArray with size 0 is empty. -/
-- ByteArray.eq_empty_of_size is now in Png.Util.ByteArray

/-! ## Extraction correctness -/

/-- Extracting IDAT data from a single IDAT chunk returns that chunk's data. -/
theorem extractIdatData_singleton (data : ByteArray) :
    extractIdatData #[{ chunkType := ChunkType.IDAT, data }] = data := by
  unfold extractIdatData
  rw [extractIdatData.go]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.lt_add_one, ↓reduceDIte, List.getElem_toArray, List.getElem_cons_zero,
    ByteArray.empty_append, PngChunk.isIDAT, ChunkType.IDAT, BEq.rfl, ↓reduceIte]
  rw [extractIdatData.go]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.lt_irrefl, ↓reduceDIte]

set_option maxHeartbeats 400000 in
/-- Extracting IDAT data from two consecutive IDAT chunks concatenates their data. -/
theorem extractIdatData_pair (d1 d2 : ByteArray) :
    extractIdatData #[{ chunkType := ChunkType.IDAT, data := d1 },
                      { chunkType := ChunkType.IDAT, data := d2 }] = d1 ++ d2 := by
  unfold extractIdatData
  simp only [extractIdatData.go, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, show (0 : Nat) < 2 from by omega, show (1 : Nat) < 2 from by omega,
    show ¬(2 : Nat) < 2 from by omega,
    ↓reduceDIte, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    ByteArray.empty_append, PngChunk.isIDAT, ChunkType.IDAT, BEq.rfl, ↓reduceIte]

/-- Non-IDAT chunks are skipped during extraction. -/
theorem extractIdatData_skips_nonIdat (chunks : Array PngChunk)
    (c : PngChunk) (hc : c.isIDAT = false) :
    extractIdatData (chunks.push c) = extractIdatData chunks := by
  unfold extractIdatData
  exact extractIdatData_go_push_nonIdat chunks c hc 0 ByteArray.empty (by omega)

/-- Extraction from an empty chunk array is empty. -/
theorem extractIdatData_empty :
    extractIdatData #[] = ByteArray.empty := by
  unfold extractIdatData extractIdatData.go
  simp only [Array.size_empty, Nat.not_lt_zero, ↓reduceDIte]

/-! ## Compression/decompression roundtrip -/

/-- Zlib decompression of zlib-compressed data recovers the original.
    This is a direct consequence of lean-zip's roundtrip theorem.
    The size bound ensures the data fits within inflate's budget. -/
theorem decompressIdat_compressIdat (data : ByteArray) (level : UInt8)
    (hsize : data.size < 1024 * 1024 * 1024) :
    decompressIdat (compressIdat data level) = .ok data := by
  unfold decompressIdat compressIdat
  exact zlib_decompressSingle_compress data level hsize

/-! ## Size validation -/

/-- For a valid non-interlaced image, the decompressed IDAT size is
    `height * (1 + scanlineBytes)`. -/
theorem validateIdatSize_correct (ihdr : IHDRInfo)
    (rawData : ByteArray)
    (hsize : rawData.size = ihdr.expectedIdatSize) :
    validateIdatSize ihdr rawData = true := by
  unfold validateIdatSize
  simp only [hsize, beq_self_eq_true]

/-- The expected IDAT size is 0 for a 0-height image (which PNG forbids,
    but this documents the arithmetic). -/
theorem expectedIdatSize_zero_height :
    IHDRInfo.expectedIdatSize
      { width := 10, height := 0, bitDepth := 8, colorType := .rgba,
        compressionMethod := 0, filterMethod := 0, interlaceMethod := .none } = 0 := by
  unfold IHDRInfo.expectedIdatSize IHDRInfo.scanlineBytes IHDRInfo.channels; rfl

/-! ## Splitting correctness -/

/-- All chunks produced by `splitIntoIdatChunks.go` are IDAT. -/
private theorem splitIntoIdatChunks_go_allIdat (zlibData : ByteArray)
    (chunkSize : Nat) (hcs : chunkSize > 0) (offset : Nat)
    (acc : Array PngChunk)
    (hacc : ∀ c ∈ acc.toList, c.isIDAT = true) :
    ∀ c ∈ (splitIntoIdatChunks.go zlibData chunkSize hcs offset acc).toList,
      c.isIDAT = true := by
  rw [splitIntoIdatChunks.go]
  split
  case isTrue h =>
    apply splitIntoIdatChunks_go_allIdat
    intro c hc
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hc
    cases hc with
    | inl h => exact hacc c h
    | inr h => rw [h]; rfl
  case isFalse => exact hacc
termination_by zlibData.size - offset

/-- Every chunk produced by splitIntoIdatChunks is an IDAT chunk. -/
theorem splitIntoIdatChunks_allIdat (zlibData : ByteArray) (chunkSize : Nat) :
    ∀ c ∈ (splitIntoIdatChunks zlibData chunkSize).toList, c.isIDAT = true := by
  unfold splitIntoIdatChunks
  split
  case isTrue h =>
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rw [hc]; rfl
  case isFalse h =>
    split
    case isTrue hcs0 =>
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rw [hc]; rfl
    case isFalse hcs0 =>
      apply splitIntoIdatChunks_go_allIdat
      intro c hc; simp only [List.not_mem_nil] at hc

/-- Invariant for `splitIntoIdatChunks.go`: extraction recovers accumulated
    data plus the remaining range of `zlibData`. -/
private theorem split_go_extract_inv (zlibData : ByteArray) (chunkSize : Nat)
    (hcs : chunkSize > 0) (offset : Nat) (acc : Array PngChunk) :
    extractIdatData (splitIntoIdatChunks.go zlibData chunkSize hcs offset acc) =
    extractIdatData acc ++ zlibData.extract offset zlibData.size := by
  rw [splitIntoIdatChunks.go]
  split
  case isTrue h =>
    rw [split_go_extract_inv, extractIdatData_push_idat]
    rw [ByteArray.append_assoc]
    congr 1
    rw [ByteArray.extract_append_extract]
    congr 1 <;> omega
  case isFalse h =>
    have : zlibData.extract offset zlibData.size = ByteArray.empty := by
      simp only [ByteArray.extract_eq_empty_iff]; omega
    rw [this, ByteArray.append_empty]
termination_by zlibData.size - offset

/-- Extracting and concatenating data from split IDAT chunks
    recovers the original zlib data. -/
theorem extractIdatData_splitIntoIdatChunks (zlibData : ByteArray)
    (chunkSize : Nat) (hcs : chunkSize > 0) :
    extractIdatData (splitIntoIdatChunks zlibData chunkSize) = zlibData := by
  unfold splitIntoIdatChunks
  split
  case isTrue h =>
    simp only [extractIdatData_singleton]
    have hsz : zlibData.size = 0 := by
      revert h; simp only [beq_iff_eq]; exact id
    exact (ByteArray.eq_empty_of_size zlibData hsz).symm
  case isFalse h =>
    split
    case isTrue hcs0 => exact absurd hcs0 (by omega)
    case isFalse hcs0 =>
      rw [split_go_extract_inv]
      simp only [extractIdatData_empty, ByteArray.empty_append]
      simp only [ByteArray.extract_zero_size]

/-! ## Full pipeline roundtrip -/

/-- Compressed data is always non-empty (zlib header is at least 6 bytes). -/
private theorem compressIdat_size_pos (data : ByteArray) (level : UInt8) :
    (compressIdat data level).size > 0 := by
  unfold compressIdat; rw [ZlibEncode.compress_size]; omega

set_option maxRecDepth 2048 in
/-- The full roundtrip: compress raw data, split into IDAT chunks,
    extract, decompress = original data. -/
theorem extractAndDecompress_compressAndSplit (rawData : ByteArray)
    (level : UInt8) (chunkSize : Nat)
    (hcs : chunkSize > 0)
    (hsize : rawData.size < 1024 * 1024 * 1024) :
    extractAndDecompress (compressAndSplit rawData level chunkSize) = .ok rawData := by
  unfold extractAndDecompress compressAndSplit
  simp only [extractIdatData_splitIntoIdatChunks _ _ hcs]
  have hpos := compressIdat_size_pos rawData level
  split
  · rename_i h
    exfalso
    have : (compressIdat rawData level).size = 0 := by
      revert h; simp only [beq_iff_eq]; exact id
    omega
  · unfold decompressIdat compressIdat
    exact zlib_decompressSingle_compress rawData level hsize

end Png.Spec.Idat
