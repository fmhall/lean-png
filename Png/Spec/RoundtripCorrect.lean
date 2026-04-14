import Png.Native.Encode
import Png.Native.Decode
import Png.Spec.ChunkCorrect
import Png.Spec.IdatCorrect
import Png.Spec.FilterCorrect

/-!
# PNG Encode/Decode Roundtrip Correctness

Capstone theorem: decoding a non-interlaced PNG encoded from a valid image
recovers the original image.

This composes:
1. Chunk parse/serialize roundtrip (from ChunkCorrect)
2. IDAT decompress/compress roundtrip (from IdatCorrect, via lean-zip)
3. Filter unfilter/filter roundtrip (from FilterCorrect — proven!)

## Proven theorems
- `encodePng_ihdr_matches` — the IHDR chunk matches original dimensions
- `filterUnfilter_scanline_roundtrip` — single-row filter roundtrip
- `idat_roundtrip_in_pipeline` — IDAT compress/decompress roundtrip

## Helper lemmas (proven)
- `filterScanlines_size` — the filtered output has the expected size
- `filterScanlines_go_prefix` — the go function preserves prefix bytes
- `filterScanlines_go_get_ft_byte` — the go function writes the filter type byte

## Remaining sorries
- `encodePng_valid_chunks` — requires `parseChunks` WF refactoring
- `decodePng_chunks_roundtrip` — requires `parseChunks` WF refactoring
- `unfilterScanlines_filterScanlines` — requires byte-content characterization of filterScanlines
- `decodePng_encodePng` — capstone, requires all of the above
-/

namespace Png.Spec.RoundtripCorrect

open Png
open Png.Native.Encode
open Png.Native.Decode
open Png.Native.Filter

/-! ## Intermediate stepping-stone theorems -/

/-- The IHDR chunk in an encoded PNG matches the original image dimensions.
    Requires nonzero width/height since IHDRInfo.fromBytes rejects zero dimensions. -/
theorem encodePng_ihdr_matches (image : PngImage) (strategy : FilterStrategy)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    let ihdr := mkIHDRChunk image.width image.height
    ihdr.chunkType = ChunkType.IHDR ∧
    IHDRInfo.fromBytes ihdr.data = .ok {
      width := image.width
      height := image.height
      bitDepth := 8
      colorType := .rgba
      compressionMethod := 0
      filterMethod := 0
      interlaceMethod := .none
    } := by
  constructor
  · rfl
  · exact Png.Spec.ihdr_fromBytes_toBytes
      { width := image.width, height := image.height, bitDepth := 8, colorType := .rgba,
        compressionMethod := 0, filterMethod := 0, interlaceMethod := .none }
      hw hh rfl rfl

/-- Helper: getElem! on a pngSignature prefix. -/
private theorem pngSig_getElem!_append (rest : ByteArray) (i : Nat) (hi : i < 8) :
    (pngSignature ++ rest)[i]! = pngSignature[i]! := by
  rw [getElem!_pos _ _ (by rw [ByteArray.size_append]; simp only [pngSignature, ByteArray.size, Array.size, List.length]; omega)]
  rw [getElem!_pos _ _ (by simp only [pngSignature, ByteArray.size, Array.size, List.length]; omega)]
  exact ByteArray.getElem_append_left (by simp only [pngSignature, ByteArray.size, Array.size, List.length]; omega)

/-- validateSignature succeeds on data starting with pngSignature. -/
private theorem validateSignature_prefix (rest : ByteArray) :
    validateSignature (pngSignature ++ rest) = true := by
  simp only [validateSignature]
  have hsz : (pngSignature ++ rest).size ≥ 8 := by
    rw [ByteArray.size_append]; simp only [pngSignature, ByteArray.size, Array.size, List.length]; omega
  simp only [hsz, decide_true, Bool.true_and]
  simp only [pngSig_getElem!_append rest 0 (by omega), pngSig_getElem!_append rest 1 (by omega),
    pngSig_getElem!_append rest 2 (by omega), pngSig_getElem!_append rest 3 (by omega),
    pngSig_getElem!_append rest 4 (by omega), pngSig_getElem!_append rest 5 (by omega),
    pngSig_getElem!_append rest 6 (by omega), pngSig_getElem!_append rest 7 (by omega)]
  decide

set_option maxHeartbeats 3200000 in
/-- Parsing a serialized chunk at an arbitrary offset in a byte stream.
    If `data = pfx ++ c.serialize ++ sfx`, then
    `parseChunk data pfx.size = .ok ⟨c, pfx.size + c.serialize.size⟩`.
    Requires: chunk data fits in PNG length field (< 2^31). -/
private theorem parseChunk_at_offset (pfx sfx : ByteArray) (c : PngChunk)
    (hlen : c.data.size < 2 ^ 31) :
    parseChunk (pfx ++ c.serialize ++ sfx) pfx.size
      = .ok ⟨c, pfx.size + c.serialize.size⟩ := by
  -- Reassociate so we have pfx ++ (c.serialize ++ sfx)
  rw [ByteArray.append_assoc]
  -- Key facts
  have hlen32 : c.data.size < 2 ^ 32 := by omega
  have hrt : c.data.size.toUInt32.toNat = c.data.size := by
    simp only [Nat.toUInt32, UInt32.toNat_ofNat', Nat.reducePow, Nat.mod_eq_of_lt hlen32]
  have hsize : c.serialize.size = 12 + c.data.size := Png.Spec.serialize_size c
  have hcsz : (c.serialize ++ sfx).size = 12 + c.data.size + sfx.size := by
    rw [ByteArray.size_append, hsize]
  -- Length field: readUInt32BE at pfx.size
  have hlen_read : readUInt32BE (pfx ++ (c.serialize ++ sfx)) pfx.size = c.data.size.toUInt32 := by
    rw [Png.Spec.readUInt32BE_append_at_size pfx _ (by rw [hcsz]; omega)]
    exact Png.Spec.serialize_length_field_append c sfx
  -- Type field: readUInt32BE at pfx.size + 4
  have htype_read : readUInt32BE (pfx ++ (c.serialize ++ sfx)) (pfx.size + 4) = c.chunkType := by
    rw [Png.Spec.readUInt32BE_append_at_offset pfx _ 4 (by rw [hcsz]; omega)]
    exact Png.Spec.serialize_type_field_append c sfx
  -- Size guards
  have hguard1 : ¬(pfx.size + 12 > (pfx ++ (c.serialize ++ sfx)).size) := by
    rw [ByteArray.size_append, hcsz]; omega
  have hguard2 : ¬(pfx.size + 8 + c.data.size + 4 > (pfx ++ (c.serialize ++ sfx)).size) := by
    rw [ByteArray.size_append, hcsz]; omega
  -- Unfold parseChunk
  -- Unfold parseChunk, resolve length/type/guards
  simp only [Png.parseChunk, hlen_read, htype_read, hrt, hguard1, hguard2,
    ↓reduceIte, bind, Except.bind, pure, Except.pure]
  -- Normalize pfx.size + 8 + c.data.size → pfx.size + (8 + c.data.size) for offset matching
  rw [show pfx.size + 8 + c.data.size = pfx.size + (8 + c.data.size) from by omega]
  -- Extract type+data for CRC check
  rw [Png.Spec.extract_append_at_offset pfx (c.serialize ++ sfx) 4 (8 + c.data.size)]
  rw [Png.Spec.serialize_extract_type_data_append c sfx]
  -- CRC check: stored CRC matches computed CRC
  rw [Png.Spec.readUInt32BE_append_at_offset pfx (c.serialize ++ sfx) (8 + c.data.size)
      (by rw [hcsz]; omega)]
  rw [Png.Spec.serialize_crc_valid_append c sfx]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  -- Extract data
  rw [Png.Spec.extract_append_at_offset pfx (c.serialize ++ sfx) 8 (8 + c.data.size)]
  rw [Png.Spec.serialize_extract_data_append c sfx]
  -- Final offset computation
  rw [show pfx.size + (8 + c.data.size) + 4 = pfx.size + c.serialize.size from by
    rw [hsize]; omega]

/-- The IHDR chunk produced by mkIHDRChunk has data size 13. -/
private theorem mkIHDRChunk_data_size (w h : UInt32) :
    (mkIHDRChunk w h).data.size = 13 := by
  simp only [mkIHDRChunk, Png.Spec.ihdr_toBytes_size]

/-- The IEND chunk has empty data. -/
private theorem mkIENDChunk_data_size : mkIENDChunk.data.size = 0 := by
  rfl

/-- mkIHDRChunk produces a chunk with IHDR type. -/
private theorem mkIHDRChunk_isIHDR (w h : UInt32) :
    (mkIHDRChunk w h).isIHDR = true := by
  rfl

/-- mkIENDChunk produces a chunk with IEND type. -/
private theorem mkIENDChunk_isIEND : mkIENDChunk.isIEND = true := by
  rfl

/-- mkIHDRChunk is not IEND. -/
private theorem mkIHDRChunk_not_isIEND (w h : UInt32) :
    (mkIHDRChunk w h).isIEND = false := by
  simp only [mkIHDRChunk, PngChunk.isIEND, ChunkType.IHDR, ChunkType.IEND]; decide

/-- mkIENDChunk has data size < 2^31. -/
private theorem mkIENDChunk_data_small : mkIENDChunk.data.size < 2 ^ 31 := by
  decide

/-- mkIHDRChunk has data size < 2^31. -/
private theorem mkIHDRChunk_data_small (w h : UInt32) :
    (mkIHDRChunk w h).data.size < 2 ^ 31 := by
  rw [mkIHDRChunk_data_size]; omega

/-- The encoded data starts with pngSignature, so parseChunks passes the signature check
    and calls go at offset 8. -/
private theorem parseChunks_encodePng_unfold (image : PngImage) (strategy : FilterStrategy) :
    parseChunks (encodePng image strategy) =
      parseChunks.go (encodePng image strategy) 8 #[] := by
  unfold parseChunks
  have hvalid : validateSignature (encodePng image strategy) = true := by
    simp only [encodePng, ByteArray.append_assoc]
    exact validateSignature_prefix _
  rw [hvalid]; rfl

/-- parseChunks.go step: parsing a non-IEND chunk advances to the next offset. -/
private theorem parseChunks_go_step (data : ByteArray) (off : Nat) (acc : Array PngChunk)
    (c : PngChunk) (off' : Nat)
    (hparse : parseChunk data off = .ok ⟨c, off'⟩)
    (hnotIEND : c.isIEND = false)
    (hadv : off' > off)
    (hlt : off < data.size) :
    parseChunks.go data off acc = parseChunks.go data off' (acc.push c) := by
  rw [parseChunks.go.eq_1]
  simp only [show ¬(off ≥ data.size) from by omega, ↓reduceIte, hparse, hnotIEND,
    Bool.false_eq_true, show ¬(off' ≤ off) from by omega]

/-- parseChunks.go IEND step: parsing an IEND chunk terminates with success. -/
private theorem parseChunks_go_iend (data : ByteArray) (off : Nat) (acc : Array PngChunk)
    (c : PngChunk) (off' : Nat)
    (hparse : parseChunk data off = .ok ⟨c, off'⟩)
    (hIEND : c.isIEND = true)
    (hlt : off < data.size) :
    parseChunks.go data off acc = .ok (acc.push c) := by
  rw [parseChunks.go.eq_1]
  simp only [show ¬(off ≥ data.size) from by omega, ↓reduceIte, hparse, hIEND]

/-- parseChunk advances the offset by exactly serialize.size bytes. -/
private theorem parseChunk_offset_advance (pfx sfx : ByteArray) (c : PngChunk)
    (hlen : c.data.size < 2 ^ 31) :
    c.serialize.size > 0 := by
  rw [Png.Spec.serialize_size]; omega

/-- serializeChunks.go accumulates: it's an append with the result starting from empty. -/
private theorem serializeChunks_go_acc (chunks : Array PngChunk) (i : Nat) (acc : ByteArray) :
    serializeChunks.go chunks i acc = acc ++ serializeChunks.go chunks i ByteArray.empty := by
  unfold serializeChunks.go
  split
  case isTrue h =>
    rw [serializeChunks_go_acc chunks (i + 1) (acc ++ chunks[i].serialize)]
    rw [serializeChunks_go_acc chunks (i + 1) (ByteArray.empty ++ chunks[i].serialize)]
    rw [ByteArray.empty_append, ByteArray.append_assoc]
  case isFalse h =>
    simp only [ByteArray.append_empty]
termination_by chunks.size - i

/-- serializeChunks.go step: first chunk serialized ++ rest. -/
private theorem serializeChunks_go_step (chunks : Array PngChunk) (i : Nat) (h : i < chunks.size) :
    serializeChunks.go chunks i ByteArray.empty =
      chunks[i].serialize ++ serializeChunks.go chunks (i + 1) ByteArray.empty := by
  rw [serializeChunks.go.eq_1]
  simp only [h, ↓reduceDIte]
  rw [serializeChunks_go_acc]
  rw [ByteArray.empty_append]

/-- serializeChunks.go past the end is empty. -/
private theorem serializeChunks_go_past (chunks : Array PngChunk) (i : Nat) (h : ¬(i < chunks.size)) :
    serializeChunks.go chunks i ByteArray.empty = ByteArray.empty := by
  rw [serializeChunks.go.eq_1]
  simp only [h, ↓reduceDIte]

/-- serializeChunks = serializeChunks.go 0 empty. -/
private theorem serializeChunks_unfold (chunks : Array PngChunk) :
    serializeChunks chunks = serializeChunks.go chunks 0 ByteArray.empty := by
  unfold serializeChunks; rfl

/-- Array.push preserves getElem! at earlier indices. -/
private theorem Array_push_getElem!_lt [Inhabited α] (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  have h1 : i < (a.push x).size := by rw [Array.size_push]; omega
  -- a[i]! unfolds to if i < a.size then a[i] else default
  -- (a.push x)[i]! unfolds to if i < (a.push x).size then (a.push x)[i] else default
  -- Both conditions are true, so both reduce to the indexed values
  -- (a.push x)[i] = a[i] when i < a.size by Array.getElem_push_lt
  change (if i < (a.push x).size then (a.push x)[i] else default) =
         (if i < a.size then a[i] else default)
  rw [if_pos h1, if_pos h, Array.getElem_push_lt h]

set_option maxHeartbeats 6400000 in
/-- Key induction lemma: parseChunks.go on pfx ++ (serialized non-IEND chunks) ++ iend.serialize ++ sfx
    starting at pfx.size terminates successfully with the last chunk being iend.
    Also preserves all acc elements at their original positions. -/
private theorem parseChunks_go_serialized
    (pfx : ByteArray) (chunks : Array PngChunk) (j : Nat)
    (iendChunk : PngChunk) (sfx : ByteArray) (acc : Array PngChunk)
    (hIEND : iendChunk.isIEND = true)
    (hnotIEND : ∀ k, j ≤ k → (hk : k < chunks.size) → (chunks[k]'hk).isIEND = false)
    (hsmall : ∀ k, j ≤ k → (hk : k < chunks.size) → (chunks[k]'hk).data.size < 2 ^ 31)
    (hsmallIEND : iendChunk.data.size < 2 ^ 31)
    (hj : j ≤ chunks.size) :
    ∃ result : Array PngChunk,
      parseChunks.go
        (pfx ++ serializeChunks.go chunks j ByteArray.empty ++ iendChunk.serialize ++ sfx)
        pfx.size acc = .ok result ∧
      result.size ≥ acc.size + 1 ∧
      result[result.size - 1]! = iendChunk ∧
      (∀ i, i < acc.size → result[i]! = acc[i]!) := by
  by_cases hj_lt : j < chunks.size
  case pos =>
    -- Decompose and reassociate ByteArray
    have hreassoc :
      pfx ++ serializeChunks.go chunks j ByteArray.empty ++ iendChunk.serialize ++ sfx =
      pfx ++ (chunks[j]'hj_lt).serialize ++
        (serializeChunks.go chunks (j + 1) ByteArray.empty ++ iendChunk.serialize ++ sfx) := by
      rw [serializeChunks_go_step chunks j hj_lt]
      simp only [ByteArray.append_assoc]
    rw [hreassoc]
    -- Parse chunks[j] via parseChunk_at_offset
    have hparse := parseChunk_at_offset pfx
        (serializeChunks.go chunks (j + 1) ByteArray.empty ++ iendChunk.serialize ++ sfx)
        ((chunks[j]'hj_lt)) (hsmall j (Nat.le_refl _) hj_lt)
    -- Step parseChunks.go forward
    rw [parseChunks.go.eq_1]
    simp only [show ¬(pfx.size ≥ (pfx ++ (chunks[j]'hj_lt).serialize ++
        (serializeChunks.go chunks (j + 1) ByteArray.empty ++ iendChunk.serialize ++ sfx)).size) from by
      rw [ByteArray.size_append, ByteArray.size_append, Png.Spec.serialize_size]; omega,
      ↓reduceIte, hparse,
      hnotIEND j (Nat.le_refl _) hj_lt, Bool.false_eq_true,
      show ¬(pfx.size + (chunks[j]'hj_lt).serialize.size ≤ pfx.size) from by
        have := Png.Spec.serialize_size ((chunks[j]'hj_lt)); omega]
    -- Apply inductive hypothesis with extended prefix (pfx ++ chunks[j].serialize)
    have hdata_eq :
      pfx ++ (chunks[j]'hj_lt).serialize ++
        (serializeChunks.go chunks (j + 1) ByteArray.empty ++ iendChunk.serialize ++ sfx) =
      (pfx ++ (chunks[j]'hj_lt).serialize) ++
        serializeChunks.go chunks (j + 1) ByteArray.empty ++ iendChunk.serialize ++ sfx := by
      simp only [ByteArray.append_assoc]
    rw [hdata_eq]
    have ih := parseChunks_go_serialized (pfx ++ (chunks[j]'hj_lt).serialize) chunks (j + 1)
        iendChunk sfx (acc.push (chunks[j]'hj_lt))
        hIEND
        (fun k hk hk2 => hnotIEND k (by omega) hk2)
        (fun k hk hk2 => hsmall k (by omega) hk2)
        hsmallIEND
        (by omega)
    rw [ByteArray.size_append] at ih
    obtain ⟨result, hresult, hsize, hlast, hprefix⟩ := ih
    refine ⟨result, hresult, by rw [Array.size_push] at hsize; omega, hlast, ?_⟩
    intro i hi_acc
    have hi_push : i < (acc.push (chunks[j]'hj_lt)).size := by
      rw [Array.size_push]; omega
    rw [hprefix i hi_push, Array_push_getElem!_lt acc _ i hi_acc]
  case neg =>
    -- Base case: no more chunks, just parse iendChunk
    have hreassoc :
      pfx ++ serializeChunks.go chunks j ByteArray.empty ++ iendChunk.serialize ++ sfx =
      pfx ++ iendChunk.serialize ++ sfx := by
      rw [serializeChunks_go_past chunks j hj_lt]
      simp only [ByteArray.append_empty]
    rw [hreassoc]
    have hparse := parseChunk_at_offset pfx sfx iendChunk hsmallIEND
    rw [parseChunks.go.eq_1]
    simp only [show ¬(pfx.size ≥ (pfx ++ iendChunk.serialize ++ sfx).size) from by
      rw [ByteArray.size_append, ByteArray.size_append, Png.Spec.serialize_size]; omega,
      ↓reduceIte, hparse, hIEND]
    refine ⟨acc.push iendChunk, rfl, by rw [Array.size_push]; omega, ?_, ?_⟩
    · rw [Array.size_push, show acc.size + 1 - 1 = acc.size from by omega]
      rw [getElem!_pos _ _ (by rw [Array.size_push]; omega)]
      exact Array.getElem_push_eq
    · intro i hi
      exact Array_push_getElem!_lt acc iendChunk i hi
termination_by chunks.size - j

/-- encodePng produces a valid chunk sequence (IHDR first, IEND last, IDAT contiguous).

    The proof requires `parseChunk_at_offset` to show each chunk is correctly
    parsed from the concatenated stream. With `parseChunks` now using WF recursion,
    each step can be justified by unfolding `parseChunks.go`.

    TODO: The proof of `parseChunks_go_serialized` requires induction on
    chunks.size - j, stepping through each chunk using parseChunk_at_offset. -/
theorem encodePng_valid_chunks (image : PngImage) (strategy : FilterStrategy) :
    ∃ chunks : Array PngChunk,
      parseChunks (encodePng image strategy) = .ok chunks ∧
      validChunkSequence chunks = true := by
  -- Step 1: parseChunks validates signature and calls go at offset 8
  rw [parseChunks_encodePng_unfold]
  -- Step 2: go unfolds to parse the IHDR chunk at offset 8, then IDAT chunks, then IEND
  -- Each step requires parseChunk_at_offset to show the chunk is correctly parsed
  -- from the encoded byte stream: pngSignature (8) ++ ihdr.serialize (25) ++ ...
  sorry

/-- IDAT chunks from compressAndSplit are not IEND. -/
private theorem compressAndSplit_not_iend (data : ByteArray) :
    ∀ k, (hk : k < (Idat.compressAndSplit data).size) →
      ((Idat.compressAndSplit data)[k]'hk).isIEND = false := by
  intro k hk
  have h := Png.Spec.Idat.splitIntoIdatChunks_allIdat (Idat.compressIdat data 1) Idat.defaultChunkSize
  have hk' : (Idat.compressAndSplit data)[k]'hk ∈ (Idat.compressAndSplit data).toList := by
    exact Array.getElem_mem_toList ..
  have hidat := h _ hk'
  simp only [PngChunk.isIDAT, PngChunk.isIEND, beq_iff_eq] at hidat ⊢
  rw [hidat]; decide

/-- Each chunk produced by splitIntoIdatChunks.go has data.size ≤ chunkSize. -/
private theorem splitIntoIdatChunks_go_data_small (zlibData : ByteArray)
    (chunkSize : Nat) (hcs : chunkSize > 0) (offset : Nat)
    (acc : Array PngChunk)
    (hacc : ∀ j, (hj : j < acc.size) → (acc[j]'hj).data.size ≤ chunkSize) :
    ∀ j, (hj : j < (Idat.splitIntoIdatChunks.go zlibData chunkSize hcs offset acc).size) →
      ((Idat.splitIntoIdatChunks.go zlibData chunkSize hcs offset acc)[j]'hj).data.size ≤ chunkSize := by
  rw [Idat.splitIntoIdatChunks.go]
  split
  case isTrue h =>
    apply splitIntoIdatChunks_go_data_small
    intro j hj
    rw [Array.size_push] at hj
    by_cases hjlt : j < acc.size
    · rw [Array.getElem_push_lt hjlt]; exact hacc j hjlt
    · have hjeq : j = acc.size := by omega
      subst hjeq
      rw [Array.getElem_push_eq]
      simp only [ByteArray.size_extract]
      omega
  case isFalse => exact hacc
termination_by zlibData.size - offset

/-- Each chunk produced by splitIntoIdatChunks has data.size ≤ chunkSize. -/
private theorem splitIntoIdatChunks_data_small (zlibData : ByteArray)
    (chunkSize : Nat) (hcs : chunkSize > 0) :
    ∀ j, (hj : j < (Idat.splitIntoIdatChunks zlibData chunkSize).size) →
      ((Idat.splitIntoIdatChunks zlibData chunkSize)[j]'hj).data.size ≤ chunkSize := by
  unfold Idat.splitIntoIdatChunks
  split
  case isTrue h =>
    intro j hj
    have hsz : (#[{ chunkType := ChunkType.IDAT, data := ByteArray.empty : PngChunk }] : Array PngChunk).size = 1 := by rfl
    have hj0 : j = 0 := by rw [hsz] at hj; omega
    subst hj0; show ByteArray.empty.size ≤ chunkSize; rw [ByteArray.size_empty]; omega
  case isFalse h =>
    split
    case isTrue hcs0 => exact absurd hcs0 (by omega)
    case isFalse hcs0 =>
      apply splitIntoIdatChunks_go_data_small
      intro j hj; exact absurd hj (by rw [Array.size_empty]; omega)

/-- IDAT chunks from compressAndSplit have data.size < 2^31.
    Each chunk has at most defaultChunkSize = 65536 bytes. -/
private theorem compressAndSplit_data_small (data : ByteArray) :
    ∀ k, (hk : k < (Idat.compressAndSplit data).size) →
      ((Idat.compressAndSplit data)[k]'hk).data.size < 2 ^ 31 := by
  simp only [Idat.compressAndSplit, Idat.defaultChunkSize]
  intro k hk
  have h := splitIntoIdatChunks_data_small (Idat.compressIdat data 1) 65536 (by omega) k hk
  omega

/-- Parsing chunks from encodePng recovers the original IHDR and IDAT data. -/
theorem decodePng_chunks_roundtrip (image : PngImage) (strategy : FilterStrategy)
    (hvalid : image.isValid = true) :
    ∃ chunks : Array PngChunk,
      parseChunks (encodePng image strategy) = .ok chunks ∧
      chunks[0]!.isIHDR = true ∧
      chunks[chunks.size - 1]!.isIEND = true := by
  -- Step 1: Unfold past signature check
  rw [parseChunks_encodePng_unfold]
  -- Abbreviations
  let data := encodePng image strategy
  let ihdr := mkIHDRChunk image.width image.height
  let idats := Idat.compressAndSplit (filterScanlines image.pixels image.width image.height strategy)
  let iend := mkIENDChunk
  -- Show data structure
  have hdata : data = pngSignature ++ ihdr.serialize ++ serializeChunks idats ++ iend.serialize := rfl
  -- Show the goal's encodePng matches our local `data`
  show ∃ chunks, parseChunks.go data 8 #[] = .ok chunks ∧
    chunks[0]!.isIHDR = true ∧ chunks[chunks.size - 1]!.isIEND = true
  -- Parse IHDR chunk at offset 8
  have hihdr_parse : parseChunk data 8 = .ok ⟨ihdr, 8 + ihdr.serialize.size⟩ := by
    rw [hdata, show pngSignature ++ ihdr.serialize ++ serializeChunks idats ++ iend.serialize =
      pngSignature ++ ihdr.serialize ++ (serializeChunks idats ++ iend.serialize) from by
      simp only [ByteArray.append_assoc]]
    exact parseChunk_at_offset pngSignature (serializeChunks idats ++ iend.serialize) ihdr
      (mkIHDRChunk_data_small image.width image.height)
  -- IHDR is not IEND
  have hihdr_not_iend := mkIHDRChunk_not_isIEND image.width image.height
  -- Step forward past IHDR
  have hihdr_sz : ihdr.serialize.size = 25 := by
    rw [Png.Spec.serialize_size, mkIHDRChunk_data_size]
  have hadv : 8 + ihdr.serialize.size > 8 := by rw [hihdr_sz]; omega
  have hlt : 8 < data.size := by
    rw [hdata, ByteArray.size_append, ByteArray.size_append, ByteArray.size_append]
    rw [Png.Spec.serialize_size, Png.Spec.serialize_size, mkIHDRChunk_data_size, mkIENDChunk_data_size]
    omega
  have hstep := parseChunks_go_step data 8 #[] ihdr (8 + ihdr.serialize.size)
    hihdr_parse hihdr_not_iend hadv hlt
  rw [hstep]
  -- Now we have parseChunks.go data (8 + ihdr.serialize.size) #[ihdr]
  -- Rewrite data as (pngSig ++ ihdr.serialize) ++ serializeChunks.go idats 0 empty ++ iend.serialize ++ empty
  have hoff : 8 + ihdr.serialize.size = (pngSignature ++ ihdr.serialize).size := by
    rw [ByteArray.size_append]
    simp only [pngSignature, ByteArray.size, Array.size, List.length]
  rw [hoff]
  have hdata2 : data =
    (pngSignature ++ ihdr.serialize) ++ serializeChunks.go idats 0 ByteArray.empty ++ iend.serialize ++ ByteArray.empty := by
    rw [hdata, ByteArray.append_empty]
    simp only [serializeChunks, serializeChunks_unfold, ByteArray.append_assoc]
  rw [hdata2]
  -- Apply parseChunks_go_serialized
  have hresult := parseChunks_go_serialized
    (pngSignature ++ ihdr.serialize) idats 0 iend ByteArray.empty #[ihdr]
    mkIENDChunk_isIEND
    (fun k hk hk2 => compressAndSplit_not_iend _ k hk2)
    (fun k hk hk2 => compressAndSplit_data_small _ k hk2)
    mkIENDChunk_data_small
    (by omega)
  obtain ⟨result, hgo, hsize, hlast, hprefix⟩ := hresult
  refine ⟨result, hgo, ?_, ?_⟩
  · -- First chunk is IHDR: result[0]! = #[ihdr][0]! = ihdr
    rw [hprefix 0 (by show 0 < (#[ihdr] : Array PngChunk).size; simp only [Array.size, List.length]; omega)]
    exact mkIHDRChunk_isIHDR image.width image.height
  · -- Last chunk is IEND
    rw [show result[result.size - 1]! = iend from hlast]
    exact mkIENDChunk_isIEND

/-- Filtering then unfiltering a single scanline recovers the original row.
    This is a direct consequence of FilterCorrect.unfilterRow_filterRow. -/
theorem filterUnfilter_scanline_roundtrip (ft : FilterType) (row prior : ByteArray)
    (hbpp : 4 > 0 := by omega) :
    unfilterRow ft 4 (filterRow ft 4 row prior) prior = row :=
  Png.Spec.FilterCorrect.unfilterRow_filterRow ft 4 row prior hbpp

/-! ## filterScanlines helper lemmas -/

/-- The size of each filtered row equals the size of the raw row. -/
private theorem filterRow_size' (ft : FilterType) (row prior : ByteArray) :
    (filterRow ft 4 row prior).size = row.size :=
  Png.Spec.FilterCorrect.filterRow_size ft 4 row prior

/-- extractRow produces a ByteArray of size `width.toNat * 4`. -/
private theorem extractRow_size (pixels : ByteArray) (width : UInt32) (r : Nat)
    {height_nat : Nat}
    (hvalid : pixels.size = width.toNat * height_nat * 4)
    (hr : r < height_nat) :
    (extractRow pixels width r).size = width.toNat * 4 := by
  unfold extractRow
  simp only [ByteArray.size_extract]
  have hle : r * (width.toNat * 4) + width.toNat * 4 ≤ pixels.size := by
    rw [hvalid]
    have h1 : r + 1 ≤ height_nat := hr
    have h2 : (r + 1) * (width.toNat * 4) ≤ height_nat * (width.toNat * 4) :=
      Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul] at h2; simp only [Nat.one_mul] at h2
    rw [show width.toNat * height_nat * 4 = height_nat * (width.toNat * 4) from by
      rw [Nat.mul_comm width.toNat height_nat, Nat.mul_assoc]]
    exact h2
  omega

/-- FilterType.ofUInt8 (FilterType.toUInt8 ft) = ft for all filter types. -/
private theorem filterType_ofUInt8_toUInt8 (ft : FilterType) :
    FilterType.ofUInt8 ft.toUInt8 = ft := by
  cases ft <;> rfl

/-! ## filterScanlines.go size and content lemmas -/

private theorem filterScanlines_go_size (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy) (r : Nat)
    (result priorRow : ByteArray)
    (hr_le : r ≤ height.toNat)
    (hresult : result.size = r * (1 + width.toNat * 4))
    (hvalid : pixels.size = width.toNat * height.toNat * 4) :
    (filterScanlines.go pixels width height strategy 4 r result priorRow).size =
      height.toNat * (1 + width.toNat * 4) := by
  unfold filterScanlines.go
  split
  case isTrue hr =>
    have hfr := filterRow_size' (strategy.getFilterType r) (extractRow pixels width r) priorRow
    have hex := extractRow_size pixels width r hvalid hr
    apply filterScanlines_go_size
    · omega
    · rw [ByteArray.size_append, ByteArray.size_push, hfr, hex, hresult]
      rw [show (r + 1) * (1 + width.toNat * 4) = r * (1 + width.toNat * 4) + (1 + width.toNat * 4) from
        Nat.succ_mul r (1 + width.toNat * 4)]
      omega
    · exact hvalid
  case isFalse hr =>
    have heq : r = height.toNat := by omega
    rw [heq] at hresult; exact hresult
termination_by height.toNat - r

/-- The complete filterScanlines output has size height * (1 + width * 4). -/
theorem filterScanlines_size (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy)
    (hvalid : pixels.size = width.toNat * height.toNat * 4) :
    (filterScanlines pixels width height strategy).size =
      height.toNat * (1 + width.toNat * 4) := by
  unfold filterScanlines
  apply filterScanlines_go_size
  · omega
  · simp only [ByteArray.size_empty, Nat.zero_mul]
  · exact hvalid

/-- Append getElem! left: reading before the split point gives the left array's byte. -/
private theorem ByteArray_append_getElem!_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos (a ++ b) i (by rw [ByteArray.size_append]; omega),
      getElem!_pos a i h]
  exact ByteArray.getElem_append_left h

/-- The go function preserves the prefix: bytes before `result.size` are unchanged. -/
private theorem filterScanlines_go_prefix (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy) (r : Nat) (result priorRow : ByteArray)
    (j : Nat) (hj : j < result.size)
    (hr_le : r ≤ height.toNat)
    (hresult : result.size = r * (1 + width.toNat * 4))
    (hvalid : pixels.size = width.toNat * height.toNat * 4) :
    (filterScanlines.go pixels width height strategy 4 r result priorRow)[j]! = result[j]! := by
  unfold filterScanlines.go
  split
  case isTrue hr =>
    have hfr := filterRow_size' (strategy.getFilterType r) (extractRow pixels width r) priorRow
    have hex := extractRow_size pixels width r hvalid hr
    have hresult' : (result.push (strategy.getFilterType r).toUInt8 ++
        filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow).size
        = (r + 1) * (1 + width.toNat * 4) := by
      rw [ByteArray.size_append, ByteArray.size_push, hfr, hex, hresult]
      rw [Nat.succ_mul]; omega
    have hj' : j < (result.push (strategy.getFilterType r).toUInt8 ++
        filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow).size := by
      rw [hresult']; rw [hresult] at hj; rw [Nat.succ_mul]; omega
    rw [filterScanlines_go_prefix pixels width height strategy (r + 1) _ _ j hj'
        (by omega) hresult' hvalid]
    rw [ByteArray_append_getElem!_left _ _ _ (by rw [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_lt _ _ _ hj]
  case isFalse => rfl
termination_by height.toNat - r

/-- At position `result.size` (= r * rowStride), the go function writes the filter type byte. -/
private theorem filterScanlines_go_get_ft_byte (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy) (r : Nat) (result priorRow : ByteArray)
    (hr : r < height.toNat)
    (_hr_le : r ≤ height.toNat)
    (hresult : result.size = r * (1 + width.toNat * 4))
    (hvalid : pixels.size = width.toNat * height.toNat * 4) :
    (filterScanlines.go pixels width height strategy 4 r result priorRow)[result.size]! =
      (strategy.getFilterType r).toUInt8 := by
  unfold filterScanlines.go
  simp only [hr, ↓reduceIte]
  have hfr := filterRow_size' (strategy.getFilterType r) (extractRow pixels width r) priorRow
  have hex := extractRow_size pixels width r hvalid hr
  have hresult' : (result.push (strategy.getFilterType r).toUInt8 ++
      filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow).size
      = (r + 1) * (1 + width.toNat * 4) := by
    rw [ByteArray.size_append, ByteArray.size_push, hfr, hex, hresult]
    rw [Nat.succ_mul]; omega
  have hpos : result.size < (result.push (strategy.getFilterType r).toUInt8 ++
      filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow).size := by
    rw [hresult']; rw [hresult]; rw [Nat.succ_mul]; omega
  rw [filterScanlines_go_prefix pixels width height strategy (r + 1) _ _ result.size hpos
      (by omega) hresult' hvalid]
  rw [ByteArray_append_getElem!_left _ _ _ (by rw [ByteArray.size_push]; omega)]
  exact ByteArray.push_getElem!_eq result _

/-! ## Unfilter/filter scanlines roundtrip -/

/-- Append getElem! right at offset: reading past the split point gives the right array's byte. -/
private theorem ByteArray_append_getElem!_right (a b : ByteArray) (j : Nat) (hj : j < b.size) :
    (a ++ b)[a.size + j]! = b[j]! := by
  have h1 : a.size + j < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (a ++ b) (a.size + j) h1, getElem!_pos b j hj,
      ByteArray.getElem_append_right (show a.size ≤ a.size + j from by omega)]
  congr 1; omega

/-- Bridge ByteArray.get! and getElem! (they operate on the same data). -/
private theorem ByteArray_get!_eq_getElem! (ba : ByteArray) (i : Nat) :
    ba.get! i = ba[i]! := by
  simp only [ByteArray.get!]
  by_cases h : i < ba.size
  · rw [getElem!_pos ba.data i h, getElem!_pos ba i h]; rfl
  · rw [getElem!_neg ba.data i h, getElem!_neg ba i h]

/-- Helper for nonlinear arithmetic: row data region fits within total size. -/
private theorem row_data_end_le_total (r : Nat) (height : UInt32) (w4 : Nat)
    (hr : r < height.toNat) :
    r * (1 + w4) + 1 + w4 ≤ height.toNat * (1 + w4) := by
  have h1 : (r + 1) * (1 + w4) ≤ height.toNat * (1 + w4) := Nat.mul_le_mul_right _ hr
  rw [Nat.add_mul] at h1; simp only [Nat.one_mul] at h1; omega

/-- Content characterization: byte j of the filtered row data at row r. -/
private theorem filterScanlines_go_get_filtered_byte (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy) (r : Nat) (result priorRow : ByteArray)
    (j : Nat) (hr : r < height.toNat)
    (hresult : result.size = r * (1 + width.toNat * 4))
    (hvalid : pixels.size = width.toNat * height.toNat * 4)
    (hj : j < width.toNat * 4) :
    (filterScanlines.go pixels width height strategy 4 r result priorRow)[result.size + 1 + j]! =
      (filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow)[j]! := by
  unfold filterScanlines.go
  simp only [hr, ↓reduceIte]
  have hfr := filterRow_size' (strategy.getFilterType r) (extractRow pixels width r) priorRow
  have hex := extractRow_size pixels width r hvalid hr
  have hresult' : (result.push (strategy.getFilterType r).toUInt8 ++
      filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow).size
      = (r + 1) * (1 + width.toNat * 4) := by
    rw [ByteArray.size_append, ByteArray.size_push, hfr, hex, hresult, Nat.succ_mul]; omega
  rw [filterScanlines_go_prefix pixels width height strategy (r + 1) _ _ (result.size + 1 + j)
      (by rw [hresult']; rw [hresult]; rw [Nat.succ_mul]; omega)
      (by omega) hresult' hvalid]
  rw [show result.size + 1 + j = (result.push (strategy.getFilterType r).toUInt8).size + j from by
    rw [ByteArray.size_push]]
  exact ByteArray_append_getElem!_right _ _ j (by rw [hfr, hex]; exact hj)

/-- Extract characterization: the extract at row r of the filtered output
    equals the filterRow result. -/
private theorem filterScanlines_go_extract_row (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy) (r : Nat) (result priorRow : ByteArray)
    (hr : r < height.toNat)
    (hresult : result.size = r * (1 + width.toNat * 4))
    (hvalid : pixels.size = width.toNat * height.toNat * 4) :
    (filterScanlines.go pixels width height strategy 4 r result priorRow).extract
      (r * (1 + width.toNat * 4) + 1) (r * (1 + width.toNat * 4) + 1 + width.toNat * 4) =
      filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow := by
  have hfr := filterRow_size' (strategy.getFilterType r) (extractRow pixels width r) priorRow
  have hex := extractRow_size pixels width r hvalid hr
  have hfsz := filterScanlines_go_size pixels width height strategy r result priorRow
    (by omega) hresult hvalid
  have hbound := row_data_end_le_total r height (width.toNat * 4) hr
  apply Png.Spec.FilterCorrect.ByteArray.ext_getElem!
  · rw [ByteArray.size_extract, hfr, hex, Nat.min_eq_left (by rw [hfsz]; exact hbound)]; omega
  · intro i hi
    rw [ByteArray.size_extract, Nat.min_eq_left (by rw [hfsz]; exact hbound)] at hi
    have hi_bound : i < width.toNat * 4 := by omega
    rw [getElem!_pos _ i (by rw [ByteArray.size_extract, Nat.min_eq_left (by rw [hfsz]; exact hbound)]; omega)]
    rw [ByteArray.getElem_extract]
    rw [← getElem!_pos _ _ (by rw [hfsz]; have := row_data_end_le_total r height (width.toNat * 4) hr; omega)]
    rw [show r * (1 + width.toNat * 4) + 1 + i = result.size + 1 + i from by rw [hresult]]
    exact filterScanlines_go_get_filtered_byte pixels width height strategy r result priorRow i
      hr hresult hvalid hi_bound

/-- Step equation: unfolding filterScanlines.go one step at row r (when r < height). -/
private theorem filterScanlines_go_step (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy) (r : Nat) (result priorRow : ByteArray)
    (hr : r < height.toNat) :
    filterScanlines.go pixels width height strategy 4 r result priorRow =
      filterScanlines.go pixels width height strategy 4 (r + 1)
        (result.push (strategy.getFilterType r).toUInt8 ++
         filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow)
        (extractRow pixels width r) := by
  rw [filterScanlines.go.eq_1]
  simp only [hr, ↓reduceIte]

/-- The core go-level roundtrip: unfilterScanlines.go applied to the output of
    filterScanlines.go recovers the original pixels.

    The proof works by induction on `height - r`. At each row:
    1. The ft byte is read correctly (by `filterScanlines_go_get_ft_byte`)
    2. The filtered row is extracted correctly (by `filterScanlines_go_extract_row`)
    3. `unfilterRow_filterRow` recovers the raw row
    4. The filtered buffer is the same object at step r+1 (by `filterScanlines_go_step`)
    5. The unfilteredResult accumulates pixels row by row -/
private theorem unfilter_filter_go (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy) (r : Nat)
    (filtered : ByteArray)
    (filterResult unfiltResult priorRow : ByteArray)
    (hr_le : r ≤ height.toNat)
    (hfr_size : filterResult.size = r * (1 + width.toNat * 4))
    (hfiltered : filtered = filterScanlines.go pixels width height strategy 4 r filterResult priorRow)
    (hur : unfiltResult = pixels.extract 0 (r * (width.toNat * 4)))
    (hvalid : pixels.size = width.toNat * height.toNat * 4) :
    unfilterScanlines.go filtered width height 4 (width.toNat * 4)
      (1 + width.toNat * 4) r unfiltResult priorRow = pixels := by
  unfold unfilterScanlines.go
  split
  case isTrue hr =>
    -- Show the ft byte read matches the strategy's filter type
    have hft_get : filtered.get! (r * (1 + width.toNat * 4)) =
        (strategy.getFilterType r).toUInt8 := by
      rw [ByteArray_get!_eq_getElem!,
          show r * (1 + width.toNat * 4) = filterResult.size from by rw [hfr_size],
          hfiltered]
      exact filterScanlines_go_get_ft_byte pixels width height strategy r filterResult priorRow
        hr (by omega) hfr_size hvalid
    -- Show the extract gives the filtered row
    have hext : filtered.extract (r * (1 + width.toNat * 4) + 1)
        (r * (1 + width.toNat * 4) + 1 + width.toNat * 4) =
        filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow := by
      rw [hfiltered]
      exact filterScanlines_go_extract_row pixels width height strategy r filterResult priorRow
        hr hfr_size hvalid
    -- Rewrite through the have-bindings: ft byte, extract, and unfilterRow_filterRow
    simp only [hft_get, filterType_ofUInt8_toUInt8, hext,
      Png.Spec.FilterCorrect.unfilterRow_filterRow _ 4 _ priorRow (by omega)]
    -- Apply inductive hypothesis at row r+1
    exact unfilter_filter_go pixels width height strategy (r + 1) filtered
      (filterResult.push (strategy.getFilterType r).toUInt8 ++
       filterRow (strategy.getFilterType r) 4 (extractRow pixels width r) priorRow)
      (unfiltResult ++ extractRow pixels width r) (extractRow pixels width r)
      (by omega)
      (by rw [ByteArray.size_append, ByteArray.size_push,
              filterRow_size' _ _ _, extractRow_size pixels width r hvalid hr,
              hfr_size, Nat.succ_mul]; omega)
      (by rw [hfiltered, filterScanlines_go_step _ _ _ _ r _ _ hr])
      (by rw [hur]; unfold extractRow
          rw [ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
              Nat.max_eq_right (by omega),
              show r * (width.toNat * 4) + width.toNat * 4 = (r + 1) * (width.toNat * 4) from
                by rw [Nat.succ_mul]])
      hvalid
  case isFalse hr =>
    -- Base case: r ≥ height, both go functions return their accumulators
    have heq : r = height.toNat := by omega
    subst heq; rw [hur]
    rw [show height.toNat * (width.toNat * 4) = pixels.size from by
      rw [hvalid, ← Nat.mul_assoc, Nat.mul_comm height.toNat width.toNat, Nat.mul_assoc]]
    exact ByteArray.extract_zero_size
  termination_by height.toNat - r

/-- Unfiltering the filtered scanlines recovers the original pixel data.

    This composes the go-level roundtrip theorem with the top-level
    size check resolution. -/
theorem unfilterScanlines_filterScanlines (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy)
    (hvalid : pixels.size = width.toNat * height.toNat * 4) :
    unfilterScanlines (filterScanlines pixels width height strategy) width height 4
      = .ok pixels := by
  have hfsz := filterScanlines_size pixels width height strategy hvalid
  unfold unfilterScanlines
  simp only [hfsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  -- Goal: .ok (unfilterScanlines.go F ... 0 empty zeroPrior) = .ok pixels
  congr 1
  -- Apply the go-level roundtrip
  have hext0 : ByteArray.empty = pixels.extract 0 (0 * (width.toNat * 4)) := by
    simp only [Nat.zero_mul]
    apply Eq.symm; apply ByteArray.ext
    rw [ByteArray.data_extract, Array.extract_zero]; rfl
  exact unfilter_filter_go pixels width height strategy 0
    (filterScanlines pixels width height strategy)
    ByteArray.empty ByteArray.empty
    (ByteArray.mk (Array.replicate (width.toNat * 4) 0))
    (by omega)
    (by simp only [ByteArray.size_empty, Nat.zero_mul])
    (by unfold filterScanlines; rfl)
    hext0
    hvalid

/-- The IDAT roundtrip: compressing then decompressing filtered scanlines
    recovers the original filtered data. -/
theorem idat_roundtrip_in_pipeline (filteredData : ByteArray)
    (hsize : filteredData.size < 1024 * 1024 * 1024) :
    Png.Idat.extractAndDecompress (Png.Idat.compressAndSplit filteredData) = .ok filteredData := by
  exact Png.Spec.Idat.extractAndDecompress_compressAndSplit filteredData 1 Png.Idat.defaultChunkSize
    (by unfold Png.Idat.defaultChunkSize; omega) hsize

/-! ## Exact chunk array characterization -/

/-- parseChunks on encodePng returns exactly #[ihdr] ++ idats ++ #[iend]. -/
private theorem parseChunks_encodePng_result (image : PngImage) (strategy : FilterStrategy) :
    let ihdr := mkIHDRChunk image.width image.height
    let idats := Idat.compressAndSplit (filterScanlines image.pixels image.width image.height strategy)
    let iend := mkIENDChunk
    ∃ result : Array PngChunk,
      parseChunks (encodePng image strategy) = .ok result ∧
      result.size > 0 ∧
      result[0]! = ihdr ∧
      Idat.extractIdatData result = Idat.extractIdatData idats := by
  rw [parseChunks_encodePng_unfold]
  let data := encodePng image strategy
  let ihdr := mkIHDRChunk image.width image.height
  let idats := Idat.compressAndSplit (filterScanlines image.pixels image.width image.height strategy)
  let iend := mkIENDChunk
  show ∃ result : Array PngChunk,
    parseChunks.go data 8 #[] = .ok result ∧
    result.size > 0 ∧
    result[0]! = ihdr ∧
    Idat.extractIdatData result = Idat.extractIdatData idats
  have hdata : data = pngSignature ++ ihdr.serialize ++ serializeChunks idats ++ iend.serialize := rfl
  -- Parse IHDR at offset 8
  have hihdr_parse : parseChunk data 8 = .ok ⟨ihdr, 8 + ihdr.serialize.size⟩ := by
    rw [hdata, show pngSignature ++ ihdr.serialize ++ serializeChunks idats ++ iend.serialize =
      pngSignature ++ ihdr.serialize ++ (serializeChunks idats ++ iend.serialize) from by
      simp only [ByteArray.append_assoc]]
    exact parseChunk_at_offset pngSignature (serializeChunks idats ++ iend.serialize) ihdr
      (mkIHDRChunk_data_small image.width image.height)
  have hihdr_not_iend := mkIHDRChunk_not_isIEND image.width image.height
  have hadv : 8 + ihdr.serialize.size > 8 := by
    rw [Png.Spec.serialize_size, mkIHDRChunk_data_size]; omega
  have hlt : 8 < data.size := by
    rw [hdata, ByteArray.size_append, ByteArray.size_append, ByteArray.size_append]
    rw [Png.Spec.serialize_size, Png.Spec.serialize_size, mkIHDRChunk_data_size, mkIENDChunk_data_size]
    omega
  rw [parseChunks_go_step data 8 #[] ihdr (8 + ihdr.serialize.size)
    hihdr_parse hihdr_not_iend hadv hlt]
  -- Offset rewrite
  have hoff : 8 + ihdr.serialize.size = (pngSignature ++ ihdr.serialize).size := by
    rw [ByteArray.size_append]; simp only [pngSignature, ByteArray.size, Array.size, List.length]
  rw [hoff]
  have hdata2 : data =
    (pngSignature ++ ihdr.serialize) ++ serializeChunks.go idats 0 ByteArray.empty ++ iend.serialize ++ ByteArray.empty := by
    rw [hdata, ByteArray.append_empty]; simp only [serializeChunks, ByteArray.append_assoc]
  rw [hdata2]
  -- Apply parseChunks_go_serialized for the IDAT+IEND part
  have hresult := parseChunks_go_serialized
    (pngSignature ++ ihdr.serialize) idats 0 iend ByteArray.empty #[ihdr]
    mkIENDChunk_isIEND
    (fun k hk hk2 => compressAndSplit_not_iend _ k hk2)
    (fun k hk hk2 => compressAndSplit_data_small _ k hk2)
    mkIENDChunk_data_small
    (by omega)
  obtain ⟨result, hgo, hsize, hlast, hprefix⟩ := hresult
  refine ⟨result, hgo, by omega, hprefix 0 (by simp only [Array.size, List.length]; omega), ?_⟩
  -- extractIdatData result = extractIdatData idats
  -- result was built by pushing idats onto #[ihdr] and then pushing iend
  -- IHDR is not IDAT (skipped), each IDAT is preserved, IEND is not IDAT (skipped)
  sorry

/-! ## Capstone theorem -/

/-- Decoding an encoded PNG recovers the original image (non-interlaced, RGBA 8-bit).

    This is the composition of:
    1. Chunk serialization/parsing roundtrip
    2. IDAT compression/decompression roundtrip (via lean-zip)
    3. Filter/unfilter roundtrip (proven in FilterCorrect)

    The size bound ensures the data fits within zlib's decompression budget.
    The bpp > 0 condition is needed for filter roundtrip (trivially true for RGBA). -/
set_option maxHeartbeats 12800000 in
/- Note: Added hw and hh hypotheses because IHDRInfo.fromBytes rejects zero
   width/height, making the original statement unprovable for degenerate images. -/
theorem decodePng_encodePng (image : PngImage) (strategy : FilterStrategy)
    (hvalid : image.isValid = true)
    (hsize : image.pixels.size < 1024 * 1024 * 1024)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    decodePng (encodePng image strategy) = .ok image := by
  -- Get detailed chunk parse result
  obtain ⟨result, hparse, hsize_pos, hfirst, _hextract⟩ :=
    parseChunks_encodePng_result image strategy
  -- Unfold decodePng
  simp only [decodePng, bind, Except.bind]
  rw [hparse]
  -- chunks.size > 0
  have hne : (result.size == 0) = false := by
    simp only [beq_iff_eq]; omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  -- First chunk is IHDR
  have hisIHDR : result[0]!.isIHDR = true := by rw [hfirst]; rfl
  simp only [hisIHDR, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  -- IHDRInfo.fromBytes recovers the original IHDR info
  have hihdr_data : result[0]!.data = (mkIHDRChunk image.width image.height).data := by
    rw [hfirst]
  -- Need to derive width/height from isValid
  have hpixels_sz : image.pixels.size = image.width.toNat * image.height.toNat * 4 := by
    simp only [PngImage.isValid, PngImage.expectedSize, beq_iff_eq] at hvalid; exact hvalid
  -- IHDRInfo.fromBytes: need nonzero width/height
  -- If width = 0 or height = 0, then pixels.size = 0 (from hpixels_sz)
  -- That's fine, the image is valid with 0 pixels
  -- But IHDRInfo.fromBytes rejects width=0 or height=0
  -- We need w ≠ 0 and h ≠ 0 as hypotheses
  -- Actually from the encoding, the IHDR always has the image's width/height
  -- If they're 0, the proof needs them nonzero for IHDRInfo.fromBytes
  -- Let's case split
  sorry

end Png.Spec.RoundtripCorrect
