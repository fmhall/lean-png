import Png.Native.Encode
import Png.Native.Decode
import Png.Spec.ChunkCorrect
import Png.Spec.IdatCorrect
import Png.Spec.FilterCorrect
import Png.Spec.InterlaceCorrect
import Png.Spec.RoundtripCorrect
import Png.Util.ByteArray

/-!
# Interlaced PNG Encode/Decode Roundtrip Correctness

Capstone theorem: decoding an Adam7-interlaced PNG encoded from a valid image
recovers the original image.

This composes:
1. Chunk parse/serialize roundtrip (reuses ChunkCorrect infrastructure)
2. IDAT decompress/compress roundtrip (via lean-zip)
3. Per-pass filter/unfilter roundtrip (7 applications of FilterCorrect)
4. Adam7 scatter/extract roundtrip (from InterlaceCorrect)

## Status
- Chunk framing: fully proven (reuses existing infrastructure)
- IHDR parsing: fully proven
- IDAT roundtrip: fully proven (reuses existing infrastructure)
- Per-pass filter roundtrip: proven for non-empty passes via
  unfilterScanlines_filterScanlines; empty passes trivial
- Composition of decodeInterlaced with filterAllPasses: sorry
  (the hard middle — showing the concatenated data splits correctly
  at pass boundaries and each pass decodes to the corresponding sub-image)
- Adam7 scatter/extract: fully proven (in InterlaceCorrect)
-/

namespace Png.Spec.InterlacedRoundtripCorrect

open Png
open Png.Native.Encode
open Png.Native.Decode
open Png.Native.Filter
open Png.Native.Interlace

/-! ## IHDR for interlaced images -/

/-- The interlaced IHDR chunk has data size 13 (same as non-interlaced). -/
private theorem mkIHDRChunkInterlaced_data_size (w h : UInt32) :
    (mkIHDRChunkInterlaced w h).data.size = 13 := by
  simp only [mkIHDRChunkInterlaced, Png.Spec.ihdr_toBytes_size]

/-- mkIHDRChunkInterlaced produces a chunk with IHDR type. -/
private theorem mkIHDRChunkInterlaced_isIHDR (w h : UInt32) :
    (mkIHDRChunkInterlaced w h).isIHDR = true := by
  rfl

/-- mkIHDRChunkInterlaced is not IEND. -/
private theorem mkIHDRChunkInterlaced_not_isIEND (w h : UInt32) :
    (mkIHDRChunkInterlaced w h).isIEND = false := by
  simp only [mkIHDRChunkInterlaced, PngChunk.isIEND, ChunkType.IHDR, ChunkType.IEND]; decide

/-- mkIHDRChunkInterlaced has data size < 2^31. -/
private theorem mkIHDRChunkInterlaced_data_small (w h : UInt32) :
    (mkIHDRChunkInterlaced w h).data.size < 2 ^ 31 := by
  rw [mkIHDRChunkInterlaced_data_size]; omega

/-- The IHDR from interlaced encoding matches expected IHDRInfo. -/
theorem encodePngInterlaced_ihdr_matches (image : PngImage)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    let ihdr := mkIHDRChunkInterlaced image.width image.height
    ihdr.chunkType = ChunkType.IHDR ∧
    IHDRInfo.fromBytes ihdr.data = .ok {
      width := image.width
      height := image.height
      bitDepth := 8
      colorType := .rgba
      compressionMethod := 0
      filterMethod := 0
      interlaceMethod := .adam7
    } := by
  constructor
  · rfl
  · exact Png.Spec.ihdr_fromBytes_toBytes
      { width := image.width, height := image.height, bitDepth := 8, colorType := .rgba,
        compressionMethod := 0, filterMethod := 0, interlaceMethod := .adam7 }
      hw hh rfl rfl

/-! ## Chunk framing for interlaced encoder -/

/-- The encoded interlaced data starts with pngSignature. -/
private theorem parseChunks_encodePngInterlaced_unfold (image : PngImage) (strategy : FilterStrategy) :
    parseChunks (encodePngInterlaced image strategy) =
      parseChunks.go (encodePngInterlaced image strategy) 8 #[] := by
  unfold parseChunks
  have hvalid : validateSignature (encodePngInterlaced image strategy) = true := by
    simp only [encodePngInterlaced, ByteArray.append_assoc]
    exact Png.Spec.RoundtripCorrect.validateSignature_prefix _
  rw [hvalid]; rfl

/-- Parsing chunks from encodePngInterlaced recovers the original IHDR and IDAT data. -/
theorem parseChunks_encodePngInterlaced_result (image : PngImage) (strategy : FilterStrategy) :
    let ihdr := mkIHDRChunkInterlaced image.width image.height
    let idats := Idat.compressAndSplit (filterAllPasses (adam7Extract image) strategy)
    ∃ result : Array PngChunk,
      parseChunks (encodePngInterlaced image strategy) = .ok result ∧
      result.size > 0 ∧
      result[0]! = ihdr ∧
      Idat.extractIdatData result = Idat.extractIdatData idats := by
  rw [parseChunks_encodePngInterlaced_unfold]
  let data := encodePngInterlaced image strategy
  let ihdr := mkIHDRChunkInterlaced image.width image.height
  let idats := Idat.compressAndSplit (filterAllPasses (adam7Extract image) strategy)
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
    exact Png.Spec.RoundtripCorrect.parseChunk_at_offset pngSignature
      (serializeChunks idats ++ iend.serialize) ihdr
      (mkIHDRChunkInterlaced_data_small image.width image.height)
  have hihdr_not_iend := mkIHDRChunkInterlaced_not_isIEND image.width image.height
  have hadv : 8 + ihdr.serialize.size > 8 := by
    rw [Png.Spec.serialize_size, mkIHDRChunkInterlaced_data_size]; omega
  have hlt : 8 < data.size := by
    rw [hdata, ByteArray.size_append, ByteArray.size_append, ByteArray.size_append]
    rw [Png.Spec.serialize_size, Png.Spec.serialize_size,
        mkIHDRChunkInterlaced_data_size, Png.Spec.RoundtripCorrect.mkIENDChunk_data_size]
    omega
  rw [Png.Spec.RoundtripCorrect.parseChunks_go_step data 8 #[] ihdr (8 + ihdr.serialize.size)
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
  have hresult := Png.Spec.RoundtripCorrect.parseChunks_go_serialized
    (pngSignature ++ ihdr.serialize) idats 0 iend ByteArray.empty #[ihdr]
    Png.Spec.RoundtripCorrect.mkIENDChunk_isIEND
    (fun k hk hk2 => Png.Spec.RoundtripCorrect.compressAndSplit_not_iend _ k hk2)
    (fun k hk hk2 => Png.Spec.RoundtripCorrect.compressAndSplit_data_small _ k hk2)
    Png.Spec.RoundtripCorrect.mkIENDChunk_data_small
    (by omega)
  obtain ⟨result, hgo, hsize, hlast, hprefix, hsz_eq, hmiddle⟩ := hresult
  refine ⟨result, hgo, by omega, hprefix 0 (by simp only [Array.size, List.length]; omega), ?_⟩
  -- extractIdatData result = extractIdatData idats via sandwich lemma
  have hresult_sz : result.size = 1 + idats.size + 1 := by
    rw [hsz_eq]; simp only [Array.size, List.length]; omega
  have hihdr_not_idat : (result[0]'(by omega)).isIDAT = false := by
    rw [show result[0]'(by omega) = ihdr from by
      have := hprefix 0 (by simp only [Array.size, List.length]; omega)
      rw [getElem!_pos result 0 (by omega), getElem!_pos (#[ihdr] : Array PngChunk) 0
        (by simp only [Array.size, List.length]; omega)] at this
      exact this]
    rfl
  have hiend_not_idat : (result[result.size - 1]'(by omega)).isIDAT = false := by
    rw [show result[result.size - 1]'(by omega) = iend from by
      have := hlast
      rw [getElem!_pos result (result.size - 1) (by omega)] at this
      exact this]
    rfl
  have hmiddle' : ∀ k, (hk : k < idats.size) → result[1 + k]! = idats[k]! := by
    intro k hk
    have h1 : result[(#[ihdr] : Array PngChunk).size + (k - 0)]! = (idats[k]'hk) :=
      hmiddle k (by omega) hk
    simp only [Array.size, List.length, show 1 + (k - 0) = 1 + k from by omega] at h1
    rw [h1, getElem!_pos idats k hk]
  exact Png.Spec.RoundtripCorrect.extractIdatData_sandwich result idats hresult_sz
    hihdr_not_idat hmiddle' hiend_not_idat

/-! ## Per-pass filter/unfilter roundtrip helper lemmas -/

/-- For RGBA 8-bit, passScanlineBytes pw = pw * 4. -/
private theorem passScanlineBytes_rgba8 (pw : Nat) :
    passScanlineBytes pw ColorType.rgba 8 = pw * 4 := by
  unfold passScanlineBytes IHDRInfo.channels
  show (pw * 4 * 8 + 7) / 8 = pw * 4
  omega

/-- For RGBA 8-bit, passDecompressedSize when non-empty. -/
private theorem nat_beq_false_of_pos (n : Nat) (h : n > 0) : (n == 0) = false := by
  cases n with
  | zero => omega
  | succ n => rfl

private theorem passDecompressedSize_rgba8 (pw ph : Nat) (hpw : pw > 0) (hph : ph > 0) :
    passDecompressedSize pw ph ColorType.rgba 8 = ph * (1 + pw * 4) := by
  unfold passDecompressedSize
  rw [nat_beq_false_of_pos pw hpw, nat_beq_false_of_pos ph hph]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, passScanlineBytes_rgba8]

/-! ## The core composition

The central challenge: showing `decodeInterlaced` on the output of
`filterAllPasses (adam7Extract image)` produces `.ok image`.

This requires:
1. The concatenated filtered data splits at the right offsets
2. Each pass's data unfilters to the sub-image pixels
3. The decoded sub-images match `adam7Extract image`
4. `adam7Scatter` on those sub-images gives `image`

Steps 2-4 are individually proven:
- Step 2: `unfilterScanlines_filterScanlines` (from RoundtripCorrect)
- Step 3: follows from step 2 + `convertToRGBA` identity for RGBA
- Step 4: `adam7Scatter_extract` (from InterlaceCorrect)

Step 1 (the splitting lemma) is the hard part: it requires an induction
over the 7 passes showing that `filterAllPasses.go` concatenates data
in exactly the sizes that `decodeInterlaced.go` expects. This is
structurally sound but requires ~200 lines of offset arithmetic.
-/

-- Helper: Unfiltering the filterScanlines output recovers original pixels.
-- This wraps the existing unfilterScanlines_filterScanlines for use in our context.
private theorem unfilter_filterScanlines_roundtrip (pixels : ByteArray)
    (width height : UInt32) (strategy : FilterStrategy)
    (hpix : pixels.size = width.toNat * height.toNat * 4) :
    unfilterScanlines (filterScanlines pixels width height strategy)
      width height 4 (width.toNat * 4) = .ok pixels :=
  Png.Spec.RoundtripCorrect.unfilterScanlines_filterScanlines pixels width height strategy hpix

-- Helper: decodePass on filterPass output for a non-empty valid sub-image.
private theorem decodePass_filterPass_ok (subImage : PngImage)
    (strategy : FilterStrategy)
    (hvalid : subImage.isValid = true)
    (hpw : subImage.width.toNat > 0) (hph : subImage.height.toNat > 0) :
    decodePass (filterPass subImage strategy)
      subImage.width.toNat subImage.height.toNat
      ColorType.rgba 8 4 none none = .ok subImage := by
  unfold decodePass
  rw [nat_beq_false_of_pos _ hpw, nat_beq_false_of_pos _ hph]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, passScanlineBytes_rgba8]
  -- Nat.toUInt32 roundtrip
  have hwU : subImage.width.toNat.toUInt32 = subImage.width :=
    Png.Spec.InterlaceCorrect.UInt32_toNat_toUInt32 subImage.width
  have hhU : subImage.height.toNat.toUInt32 = subImage.height :=
    Png.Spec.InterlaceCorrect.UInt32_toNat_toUInt32 subImage.height
  rw [hwU, hhU]
  -- filterPass for non-empty = filterScanlines
  have hfp : filterPass subImage strategy =
      filterScanlines subImage.pixels subImage.width subImage.height strategy := by
    unfold filterPass
    have hw_ne : subImage.width ≠ 0 := by
      intro h; rw [h] at hpw; contradiction
    have hh_ne : subImage.height ≠ 0 := by
      intro h; rw [h] at hph; contradiction
    rw [beq_false_of_ne hw_ne, beq_false_of_ne hh_ne]
    simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [hfp]
  -- Unfilter roundtrip
  have hpix : subImage.pixels.size = subImage.width.toNat * subImage.height.toNat * 4 := by
    simp only [PngImage.isValid, PngImage.expectedSize, beq_iff_eq] at hvalid; exact hvalid
  rw [unfilter_filterScanlines_roundtrip subImage.pixels subImage.width subImage.height
    strategy hpix]
  -- convertToRGBA for RGBA 8 is identity, PngImage eta
  simp only [bind, Except.bind, convertToRGBA, pure, Except.pure]

-- The full decodeInterlaced roundtrip on filterAllPasses output.
-- SORRY: The composition of all 7 passes through the offset splitting
-- is the hard middle. Each individual piece is proven above
-- (decodePass_filterPass_ok, unfilter_filterScanlines_roundtrip).
-- What remains is the inductive argument showing filterAllPasses.go
-- and decodeInterlaced.go are in lockstep: the concatenated data splits
-- at exactly the boundaries expected by the decoder. This is ~200 lines
-- of offset arithmetic that would compose the existing pieces.
-- The adam7Scatter_extract theorem from InterlaceCorrect provides the
-- final step: scatter(extract(image)) = image.
private theorem decodeInterlaced_filterAllPasses (image : PngImage)
    (strategy : FilterStrategy)
    (hvalid : image.isValid = true)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    let ihdr : IHDRInfo := {
      width := image.width, height := image.height,
      bitDepth := 8, colorType := .rgba,
      compressionMethod := 0, filterMethod := 0, interlaceMethod := .adam7
    }
    decodeInterlaced ihdr (filterAllPasses (adam7Extract image) strategy) none none
      = .ok image := by
  sorry

/-! ## Capstone theorem -/

/-- Decoding an interlaced-encoded PNG recovers the original image (RGBA 8-bit).

    This is the composition of:
    1. Chunk serialization/parsing roundtrip (same infrastructure as non-interlaced)
    2. IDAT compression/decompression roundtrip (via lean-zip)
    3. Per-pass filter/unfilter roundtrip (7 copies of FilterCorrect)
    4. Adam7 scatter/extract roundtrip (from InterlaceCorrect)

    Preconditions:
    - Image is valid (pixels.size = width * height * 4)
    - Filtered data fits in zlib budget (< 1 GiB)
    - Nonzero dimensions (IHDR rejects width=0 or height=0)
-/
theorem decodePng_encodePngInterlaced (image : PngImage) (strategy : FilterStrategy)
    (hvalid : image.isValid = true)
    (hsize : (filterAllPasses (adam7Extract image) strategy).size < 1024 * 1024 * 1024)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    decodePng (encodePngInterlaced image strategy) = .ok image := by
  -- Get detailed chunk parse result
  obtain ⟨result, hparse, hsize_pos, hfirst, hextract⟩ :=
    parseChunks_encodePngInterlaced_result image strategy
  -- The IHDR info that will be recovered
  let ihdrInfo : IHDRInfo := {
    width := image.width, height := image.height,
    bitDepth := 8, colorType := .rgba,
    compressionMethod := 0, filterMethod := 0, interlaceMethod := .adam7
  }
  -- IHDRInfo.fromBytes on the first chunk's data recovers ihdrInfo
  have hfromBytes : IHDRInfo.fromBytes result[0]!.data = .ok ihdrInfo := by
    rw [hfirst]
    exact Png.Spec.ihdr_fromBytes_toBytes ihdrInfo hw hh rfl rfl
  -- Unfold decodePng step by step
  simp only [decodePng, bind, Except.bind]
  rw [hparse]
  -- chunks.size > 0
  simp only [dif_neg (show ¬ result.size = 0 from by omega)]
  simp only [← getElem!_pos]
  -- First chunk is IHDR
  have hisIHDR : result[0]!.isIHDR = true := by rw [hfirst]; rfl
  simp only [hisIHDR, Bool.not_true]
  -- IHDRInfo.fromBytes succeeds
  rw [hfromBytes]
  -- interlaceMethod check: .adam7 ≠ .none → takes interlaced branch
  simp only [show (ihdrInfo.interlaceMethod != .none) = true from by rfl]
  -- Now in the interlaced branch: monadic steps with PLTE, tRNS, extractAndDecompress
  -- For RGBA 8-bit: plte match → pure none, trns match → pure none
  -- These bind steps simplify to Except.bind (.ok none) (fun _ => ...)
  -- extractAndDecompress roundtrip
  let filteredData := filterAllPasses (adam7Extract image) strategy
  have hfilt_size : filteredData.size < 1024 * 1024 * 1024 := hsize
  have hextract_decompress : Idat.extractAndDecompress result = .ok filteredData := by
    unfold Idat.extractAndDecompress
    rw [hextract]
    have h_roundtrip := Png.Spec.RoundtripCorrect.idat_roundtrip_in_pipeline filteredData hfilt_size
    unfold Idat.extractAndDecompress at h_roundtrip
    exact h_roundtrip
  -- decodeInterlaced roundtrip
  have hdecodeI := decodeInterlaced_filterAllPasses image strategy hvalid hw hh
  -- The remaining goal threads through the monadic binds
  simp only [ihdrInfo, pure, Except.pure, hextract_decompress]
  exact hdecodeI

end Png.Spec.InterlacedRoundtripCorrect
