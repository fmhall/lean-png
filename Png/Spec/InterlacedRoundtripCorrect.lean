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
- Composition of decodeInterlaced with filterAllPasses: fully proven
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

-- extractPass produces valid sub-images
private theorem extractPass_isValid (image : PngImage) (p : Fin 7) :
    (extractPass image p).isValid = true := by
  simp only [PngImage.isValid, PngImage.expectedSize, beq_iff_eq]
  rw [Png.Spec.InterlaceCorrect.extractPass_width,
      Png.Spec.InterlaceCorrect.extractPass_height,
      Png.Spec.InterlaceCorrect.extractPass_pixels_size]

-- filterPass size for non-empty pass: matches passDecompressedSize
private theorem filterPass_size_nonempty (subImage : PngImage)
    (strategy : FilterStrategy)
    (hvalid : subImage.isValid = true)
    (hpw : subImage.width.toNat > 0) (hph : subImage.height.toNat > 0) :
    (filterPass subImage strategy).size =
      passDecompressedSize subImage.width.toNat subImage.height.toNat ColorType.rgba 8 := by
  have hfp : filterPass subImage strategy =
      filterScanlines subImage.pixels subImage.width subImage.height strategy := by
    unfold filterPass
    have hw_ne : subImage.width ≠ 0 := by intro h; rw [h] at hpw; contradiction
    have hh_ne : subImage.height ≠ 0 := by intro h; rw [h] at hph; contradiction
    rw [beq_false_of_ne hw_ne, beq_false_of_ne hh_ne]
    simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [hfp]
  have hpix : subImage.pixels.size = subImage.width.toNat * subImage.height.toNat * 4 := by
    simp only [PngImage.isValid, PngImage.expectedSize, beq_iff_eq] at hvalid; exact hvalid
  rw [Png.Spec.RoundtripCorrect.filterScanlines_size _ _ _ strategy hpix,
      passDecompressedSize_rgba8 _ _ hpw hph]

-- passDecompressedSize for empty pass
private theorem passDecompressedSize_zero_left (ph : Nat) :
    passDecompressedSize 0 ph ColorType.rgba 8 = 0 := by
  unfold passDecompressedSize
  simp only [show ((0 : Nat) == 0) = true from rfl, Bool.true_or, ↓reduceIte]

private theorem passDecompressedSize_zero_right (pw : Nat) :
    passDecompressedSize pw 0 ColorType.rgba 8 = 0 := by
  unfold passDecompressedSize
  simp only [show ((0 : Nat) == 0) = true from rfl, Bool.or_true, ↓reduceIte]

-- decodePass for empty pass: produces empty image
private theorem decodePass_empty_left (passData : ByteArray)
    (ph : Nat) :
    decodePass passData 0 ph ColorType.rgba 8 4 none none =
      .ok { width := 0, height := 0, pixels := ByteArray.empty } := by
  unfold decodePass
  simp only [show ((0 : Nat) == 0) = true from rfl, Bool.true_or, ↓reduceIte, pure, Except.pure]

private theorem decodePass_empty_right (passData : ByteArray)
    (pw : Nat) :
    decodePass passData pw 0 ColorType.rgba 8 4 none none =
      .ok { width := 0, height := 0, pixels := ByteArray.empty } := by
  unfold decodePass
  simp only [show ((0 : Nat) == 0) = true from rfl, Bool.or_true, ↓reduceIte, pure, Except.pure]

-- Helper: UInt32.toNat = 0 implies UInt32 = 0
private theorem UInt32_eq_zero_of_toNat_zero (u : UInt32) (h : u.toNat = 0) : u = 0 := by
  cases u with | ofBitVec v =>
  simp only [UInt32.toNat, UInt32.zero_def] at *
  congr 1; exact BitVec.eq_of_toNat_eq h

-- filterPass for empty sub-image produces empty ByteArray
private theorem filterPass_empty_width (subImage : PngImage) (strategy : FilterStrategy)
    (hw : subImage.width = 0) :
    (filterPass subImage strategy) = ByteArray.empty := by
  unfold filterPass; rw [hw]
  simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte]

private theorem filterPass_empty_height (subImage : PngImage) (strategy : FilterStrategy)
    (hh : subImage.height = 0) :
    (filterPass subImage strategy) = ByteArray.empty := by
  unfold filterPass; rw [hh]
  simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte]

-- filterPass size always matches passDecompressedSize for valid sub-images
private theorem filterPass_size_eq (subImage : PngImage) (strategy : FilterStrategy)
    (hvalid : subImage.isValid = true) :
    (filterPass subImage strategy).size =
      passDecompressedSize subImage.width.toNat subImage.height.toNat ColorType.rgba 8 := by
  by_cases hpw : subImage.width.toNat > 0
  · by_cases hph : subImage.height.toNat > 0
    · exact filterPass_size_nonempty subImage strategy hvalid hpw hph
    · have hph0 : subImage.height.toNat = 0 := by omega
      have hh0 : subImage.height = 0 := UInt32_eq_zero_of_toNat_zero _ hph0
      rw [filterPass_empty_height subImage strategy hh0, ByteArray.size_empty, hph0,
          passDecompressedSize_zero_right]
  · have hpw0 : subImage.width.toNat = 0 := by omega
    have hw0 : subImage.width = 0 := UInt32_eq_zero_of_toNat_zero _ hpw0
    rw [filterPass_empty_width subImage strategy hw0, ByteArray.size_empty, hpw0,
        passDecompressedSize_zero_left]

-- filterAllPasses.go acc = acc ++ filterAllPasses.go subImages strategy p empty
private theorem filterAllPasses_go_append (subImages : Array PngImage)
    (strategy : FilterStrategy) (p : Nat) (acc : ByteArray) :
    filterAllPasses.go subImages strategy p acc =
      acc ++ filterAllPasses.go subImages strategy p ByteArray.empty := by
  if hp : p < 7 then
    unfold filterAllPasses.go
    rw [dif_pos hp, dif_pos hp]
    rw [filterAllPasses_go_append subImages strategy (p + 1)]
    rw [filterAllPasses_go_append subImages strategy (p + 1) (ByteArray.empty ++ _)]
    simp only [ByteArray.empty_append, ByteArray.append_assoc]
  else
    unfold filterAllPasses.go
    rw [dif_neg hp, dif_neg hp]
    simp only [ByteArray.append_empty]
termination_by 7 - p

-- filterAllPasses.go from pass p with empty acc = passData(p) ++ go(p+1, empty)
private theorem filterAllPasses_go_cons (subImages : Array PngImage)
    (strategy : FilterStrategy) (p : Nat) (hp : p < 7) (hps : p < subImages.size) :
    filterAllPasses.go subImages strategy p ByteArray.empty =
      filterPass subImages[p] strategy ++
        filterAllPasses.go subImages strategy (p + 1) ByteArray.empty := by
  rw [filterAllPasses.go.eq_1]
  simp only [dif_pos hp, dif_pos hps, ByteArray.empty_append]
  exact filterAllPasses_go_append subImages strategy (p + 1) _

-- filterAllPasses.go size
private theorem filterAllPasses_go_size_acc (subImages : Array PngImage)
    (strategy : FilterStrategy) (p : Nat) (acc : ByteArray) :
    (filterAllPasses.go subImages strategy p acc).size ≥ acc.size := by
  rw [filterAllPasses_go_append]
  rw [ByteArray.size_append]
  omega

-- bytesPerPixel for RGBA 8-bit IHDR is 4
private theorem bpp_rgba8_eq_4 (ihdr : IHDRInfo)
    (hct : ihdr.colorType = .rgba) (hbd : ihdr.bitDepth = 8) :
    IHDRInfo.bytesPerPixel ihdr = 4 := by
  unfold IHDRInfo.bytesPerPixel IHDRInfo.channels; rw [hct, hbd]; decide

-- scatterPass is no-op when subImage has width=0
private theorem scatterPass_width_zero (buf : ByteArray) (fullWidth : Nat)
    (subImage : PngImage) (p : Fin 7) (hw : subImage.width = 0) :
    scatterPass buf fullWidth subImage p = buf := by
  unfold scatterPass; rw [hw]
  show scatterPass.go buf fullWidth subImage.pixels 0 p 0 (0 * subImage.height.toNat) = buf
  simp only [Nat.zero_mul]; rw [scatterPass.go.eq_1]
  simp only [show (0 : Nat) ≥ 0 from Nat.le_refl 0, ↓reduceIte]

-- scatterPass is no-op when subImage has height=0
private theorem scatterPass_height_zero (buf : ByteArray) (fullWidth : Nat)
    (subImage : PngImage) (p : Fin 7) (hh : subImage.height = 0) :
    scatterPass buf fullWidth subImage p = buf := by
  unfold scatterPass; rw [hh]
  show scatterPass.go buf fullWidth subImage.pixels subImage.width.toNat p 0 (subImage.width.toNat * 0) = buf
  simp only [Nat.mul_zero]; rw [scatterPass.go.eq_1]
  simp only [show (0 : Nat) ≥ 0 from Nat.le_refl 0, ↓reduceIte]

-- adam7Scatter.go is invariant when sub-images either match or both scatter to no-op
set_option maxHeartbeats 800000 in
private theorem adam7Scatter_go_equiv (subs1 subs2 : Array PngImage) (buf : ByteArray) (fw : Nat)
    (p : Nat) (hs1 : subs1.size = 7) (hs2 : subs2.size = 7)
    (heq : ∀ q, p ≤ q → (hq : q < 7) →
      (subs1[q]'(by rw [hs1]; exact hq) = subs2[q]'(by rw [hs2]; exact hq)) ∨
      ((subs1[q]'(by rw [hs1]; exact hq)).width = 0 ∧ (subs2[q]'(by rw [hs2]; exact hq)).width = 0) ∨
      ((subs1[q]'(by rw [hs1]; exact hq)).height = 0 ∧ (subs2[q]'(by rw [hs2]; exact hq)).height = 0)) :
    adam7Scatter.go subs1 buf fw p = adam7Scatter.go subs2 buf fw p := by
  if hp : p < 7 then
    have hp1 : p < subs1.size := by rw [hs1]; exact hp
    have hp2 : p < subs2.size := by rw [hs2]; exact hp
    have hcase := heq p (Nat.le_refl p) hp
    have lhs_unfold : adam7Scatter.go subs1 buf fw p =
        adam7Scatter.go subs1 (scatterPass buf fw subs1[p] ⟨p, hp⟩) fw (p + 1) := by
      rw [adam7Scatter.go.eq_1]; simp only [dif_pos hp, dif_pos hp1]
    have rhs_unfold : adam7Scatter.go subs2 buf fw p =
        adam7Scatter.go subs2 (scatterPass buf fw subs2[p] ⟨p, hp⟩) fw (p + 1) := by
      rw [adam7Scatter.go.eq_1]; simp only [dif_pos hp, dif_pos hp2]
    rw [lhs_unfold, rhs_unfold]
    rcases hcase with h_eq | ⟨hw1, hw2⟩ | ⟨hh1, hh2⟩
    · rw [h_eq]; exact adam7Scatter_go_equiv subs1 subs2 _ fw (p + 1) hs1 hs2
        (fun q hq hq7 => heq q (by omega) hq7)
    · rw [scatterPass_width_zero _ _ _ _ hw1, scatterPass_width_zero _ _ _ _ hw2]
      exact adam7Scatter_go_equiv subs1 subs2 buf fw (p + 1) hs1 hs2
        (fun q hq hq7 => heq q (by omega) hq7)
    · rw [scatterPass_height_zero _ _ _ _ hh1, scatterPass_height_zero _ _ _ _ hh2]
      exact adam7Scatter_go_equiv subs1 subs2 buf fw (p + 1) hs1 hs2
        (fun q hq hq7 => heq q (by omega) hq7)
  else
    have h1 : adam7Scatter.go subs1 buf fw p = buf := by
      rw [adam7Scatter.go.eq_1]; simp only [dif_neg hp]
    have h2 : adam7Scatter.go subs2 buf fw p = buf := by
      rw [adam7Scatter.go.eq_1]; simp only [dif_neg hp]
    rw [h1, h2]
termination_by 7 - p

-- Local copy of the private adam7Extract_getElem
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
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl

-- The core inductive lemma with weakened invariant
set_option maxHeartbeats 3200000 in
private theorem decodeInterlaced_go_inv (image : PngImage)
    (strategy : FilterStrategy) (hvalid : image.isValid = true)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0)
    (ihdr : IHDRInfo) (hihdr_w : ihdr.width = image.width) (hihdr_h : ihdr.height = image.height)
    (hihdr_bd : ihdr.bitDepth = 8) (hihdr_ct : ihdr.colorType = .rgba)
    (p : Nat) (offset : Nat) (decoded : Array PngImage)
    (subs : Array PngImage) (hsubs : subs = adam7Extract image) (hsubs_size : subs.size = 7)
    (decompressed : ByteArray)
    (hdecomp : decompressed.size = offset +
        (filterAllPasses.go subs strategy p ByteArray.empty).size)
    (hextract : ∀ i, i < (filterAllPasses.go subs strategy p ByteArray.empty).size →
        decompressed[offset + i]! =
          (filterAllPasses.go subs strategy p ByteArray.empty)[i]!)
    (hdec_size : decoded.size = p)
    (hdecoded : ∀ i, (hi : i < decoded.size) → (his : i < subs.size) →
      (decoded[i] = subs[i]) ∨
      (decoded[i].width = 0 ∧ subs[i].width = 0) ∨
      (decoded[i].height = 0 ∧ subs[i].height = 0))
    (hp7 : p ≤ 7) :
    decodeInterlaced.go ihdr decompressed none none 4
      image.width.toNat image.height.toNat p offset decoded = .ok image := by
  subst hsubs
  if hp : p < 7 then
    rw [decodeInterlaced.go.eq_1]
    simp only [dif_pos hp, hihdr_ct, hihdr_bd]
    have hps : p < (adam7Extract image).size := by rw [hsubs_size]; exact hp
    -- sub[p] = extractPass image p
    have hsub_eq : (adam7Extract image)[p] = extractPass image ⟨p, hp⟩ :=
      adam7Extract_getElem image ⟨p, hp⟩ hsubs_size
    have hpw_eq : passWidth ⟨p, hp⟩ image.width.toNat = (adam7Extract image)[p].width.toNat := by
      rw [hsub_eq]; exact (Png.Spec.InterlaceCorrect.extractPass_width image ⟨p, hp⟩).symm
    have hph_eq : passHeight ⟨p, hp⟩ image.height.toNat = (adam7Extract image)[p].height.toNat := by
      rw [hsub_eq]; exact (Png.Spec.InterlaceCorrect.extractPass_height image ⟨p, hp⟩).symm
    have hfp_size_raw : (filterPass (adam7Extract image)[p] strategy).size =
        passDecompressedSize (adam7Extract image)[p].width.toNat (adam7Extract image)[p].height.toNat ColorType.rgba 8 := by
      exact filterPass_size_eq _ strategy (by rw [hsub_eq]; exact extractPass_isValid image ⟨p, hp⟩)
    have hfp_size : (filterPass (adam7Extract image)[p] strategy).size =
        passDecompressedSize (passWidth ⟨p, hp⟩ image.width.toNat)
          (passHeight ⟨p, hp⟩ image.height.toNat) ColorType.rgba 8 := by
      rw [hpw_eq, hph_eq]; exact hfp_size_raw
    have hgo_eq := filterAllPasses_go_cons (adam7Extract image) strategy p hp hps
    have hrem_size : (filterAllPasses.go (adam7Extract image) strategy p ByteArray.empty).size =
        (filterPass (adam7Extract image)[p] strategy).size +
          (filterAllPasses.go (adam7Extract image) strategy (p + 1) ByteArray.empty).size := by
      rw [hgo_eq, ByteArray.size_append]
    have hoff_ok : ¬(offset + passDecompressedSize (passWidth ⟨p, hp⟩ image.width.toNat)
        (passHeight ⟨p, hp⟩ image.height.toNat) ColorType.rgba 8 > decompressed.size) := by
      rw [hdecomp, hrem_size, hfp_size]; omega
    simp only [hoff_ok, ↓reduceIte]
    have hextract_eq : decompressed.extract offset
        (offset + passDecompressedSize (passWidth ⟨p, hp⟩ image.width.toNat)
          (passHeight ⟨p, hp⟩ image.height.toNat) ColorType.rgba 8) =
        filterPass (adam7Extract image)[p] strategy := by
      apply ByteArray.ext_getElem!
      · rw [ByteArray.size_extract, hfp_size]; omega
      · intro j hj
        rw [ByteArray.size_extract] at hj
        rw [ByteArray.getElem!_eq_getElem _ _ (by rw [ByteArray.size_extract]; omega)]
        rw [ByteArray.getElem_extract, ← ByteArray.getElem!_eq_getElem _ _ (by omega)]
        rw [hextract j (by rw [hrem_size, hfp_size]; omega)]
        rw [hgo_eq, ByteArray.append_getElem!_left _ _ _ (by rw [hfp_size]; omega)]
    rw [hextract_eq]
    have hextract_next : ∀ i,
        i < (filterAllPasses.go (adam7Extract image) strategy (p + 1) ByteArray.empty).size →
        decompressed[offset + passDecompressedSize (passWidth ⟨p, hp⟩ image.width.toNat)
          (passHeight ⟨p, hp⟩ image.height.toNat) ColorType.rgba 8 + i]! =
          (filterAllPasses.go (adam7Extract image) strategy (p + 1) ByteArray.empty)[i]! := by
      intro i hi
      rw [show offset + passDecompressedSize _ _ _ _ + i =
          offset + ((filterPass (adam7Extract image)[p] strategy).size + i) from by rw [hfp_size]; omega]
      rw [hextract _ (by rw [hrem_size]; omega), hgo_eq, ByteArray.append_getElem!_right _ _ _ hi]
    by_cases hpw : passWidth ⟨p, hp⟩ image.width.toNat = 0
    · -- Empty pass width=0
      rw [hpw, passDecompressedSize_zero_left, decodePass_empty_left]
      have hsub_w0 : (adam7Extract image)[p].width = 0 := UInt32_eq_zero_of_toNat_zero _ (by rw [← hpw_eq]; exact hpw)
      apply decodeInterlaced_go_inv image strategy hvalid hw hh ihdr
        hihdr_w hihdr_h hihdr_bd hihdr_ct (p + 1) (offset + 0)
        (decoded.push { width := 0, height := 0, pixels := ByteArray.empty })
        (adam7Extract image) rfl hsubs_size decompressed
      · rw [hdecomp, hrem_size, hfp_size, hpw, passDecompressedSize_zero_left]; omega
      · intro i hi
        rw [show offset + 0 + i = offset + ((filterPass (adam7Extract image)[p] strategy).size + i) from by
          rw [hfp_size, hpw, passDecompressedSize_zero_left]; omega]
        rw [hextract _ (by rw [hrem_size]; omega), hgo_eq, ByteArray.append_getElem!_right _ _ _ hi]
      · rw [Array.size_push, hdec_size]
      · intro i hi his
        rw [Array.size_push] at hi
        if hip : i < decoded.size then
          have his' : i < (adam7Extract image).size := by omega
          rw [Array.getElem_push_lt hip]; exact hdecoded i hip his'
        else
          -- i = p (from hdec_size and hip : ¬(i < decoded.size))
          -- Show the pushed array at i = the pushed value
          have hid : i = decoded.size := by omega
          have hpush : (decoded.push { width := 0, height := 0, pixels := ByteArray.empty })[i]'
              (by rw [Array.size_push]; omega) =
            { width := 0, height := 0, pixels := ByteArray.empty } := by
            subst hid; exact Array.getElem_push_eq
          -- Show (adam7Extract image)[i] = (adam7Extract image)[p]
          have hidx : (adam7Extract image)[i]'his = (adam7Extract image)[p]'hps := by
            congr 1; omega
          rw [hpush, hidx]
          exact Or.inr (Or.inl ⟨rfl, hsub_w0⟩)
      · omega
    · by_cases hph : passHeight ⟨p, hp⟩ image.height.toNat = 0
      · -- Empty pass height=0
        rw [hph, passDecompressedSize_zero_right, decodePass_empty_right]
        have hsub_h0 : (adam7Extract image)[p].height = 0 := UInt32_eq_zero_of_toNat_zero _ (by rw [← hph_eq]; exact hph)
        apply decodeInterlaced_go_inv image strategy hvalid hw hh ihdr
          hihdr_w hihdr_h hihdr_bd hihdr_ct (p + 1) (offset + 0)
          (decoded.push { width := 0, height := 0, pixels := ByteArray.empty })
          (adam7Extract image) rfl hsubs_size decompressed
        · rw [hdecomp, hrem_size, hfp_size, hph, passDecompressedSize_zero_right]; omega
        · intro i hi
          rw [show offset + 0 + i = offset + ((filterPass (adam7Extract image)[p] strategy).size + i) from by
            rw [hfp_size, hph, passDecompressedSize_zero_right]; omega]
          rw [hextract _ (by rw [hrem_size]; omega), hgo_eq, ByteArray.append_getElem!_right _ _ _ hi]
        · rw [Array.size_push, hdec_size]
        · intro i hi his
          rw [Array.size_push] at hi
          if hip : i < decoded.size then
            have his' : i < (adam7Extract image).size := by omega
            rw [Array.getElem_push_lt hip]; exact hdecoded i hip his'
          else
            have hid : i = decoded.size := by omega
            have hpush : (decoded.push { width := 0, height := 0, pixels := ByteArray.empty })[i]'
                (by rw [Array.size_push]; omega) =
              { width := 0, height := 0, pixels := ByteArray.empty } := by
              subst hid; exact Array.getElem_push_eq
            have hidx : (adam7Extract image)[i]'his = (adam7Extract image)[p]'hps := by
              congr 1; omega
            rw [hpush, hidx]
            exact Or.inr (Or.inr ⟨rfl, hsub_h0⟩)
        · omega
      · -- Non-empty pass
        have hpw_pos : passWidth ⟨p, hp⟩ image.width.toNat > 0 := by omega
        have hph_pos : passHeight ⟨p, hp⟩ image.height.toNat > 0 := by omega
        have hdec_ok := decodePass_filterPass_ok (adam7Extract image)[p] strategy
          (by rw [hsub_eq]; exact extractPass_isValid image ⟨p, hp⟩)
          (by rw [← hpw_eq]; exact hpw_pos) (by rw [← hph_eq]; exact hph_pos)
        rw [← hpw_eq, ← hph_eq] at hdec_ok; rw [hdec_ok]
        apply decodeInterlaced_go_inv image strategy hvalid hw hh ihdr
          hihdr_w hihdr_h hihdr_bd hihdr_ct (p + 1)
          (offset + passDecompressedSize (passWidth ⟨p, hp⟩ image.width.toNat)
            (passHeight ⟨p, hp⟩ image.height.toNat) ColorType.rgba 8)
          (decoded.push (adam7Extract image)[p]) (adam7Extract image) rfl hsubs_size decompressed
        · rw [hdecomp, hrem_size, hfp_size]; omega
        · exact hextract_next
        · rw [Array.size_push, hdec_size]
        · intro i hi his
          rw [Array.size_push] at hi
          if hip : i < decoded.size then
            have his' : i < (adam7Extract image).size := by omega
            rw [Array.getElem_push_lt hip]; exact hdecoded i hip his'
          else
            have hid : i = decoded.size := by omega
            have hpush : (decoded.push (adam7Extract image)[p])[i]'
                (by rw [Array.size_push]; omega) =
              (adam7Extract image)[p] := by
              subst hid; exact Array.getElem_push_eq
            have hidx : (adam7Extract image)[i]'his = (adam7Extract image)[p]'hps := by
              congr 1; omega
            rw [hpush, hidx]; exact Or.inl rfl
        · omega
  else
    have hp_eq : p = 7 := by omega
    rw [decodeInterlaced.go.eq_1]
    simp only [dif_neg hp]
    show Except.ok (adam7Scatter decoded image.width.toNat image.height.toNat) = Except.ok image
    congr 1
    have hscatter_eq : adam7Scatter decoded image.width.toNat image.height.toNat =
        adam7Scatter (adam7Extract image) image.width.toNat image.height.toNat := by
      simp only [adam7Scatter]
      let buf := ByteArray.mk (Array.replicate (image.width.toNat * image.height.toNat * 4) 0)
      have hgo := adam7Scatter_go_equiv decoded (adam7Extract image) buf image.width.toNat 0
        (by rw [hdec_size, hp_eq]) hsubs_size
        (fun q hq hq7 => hdecoded q (by rw [hdec_size, hp_eq]; exact hq7) (by rw [hsubs_size]; exact hq7))
      exact congrArg (fun buf => PngImage.mk _ _ buf) hgo
    rw [hscatter_eq]
    exact Png.Spec.InterlaceCorrect.adam7Scatter_extract image hvalid
termination_by 7 - p

-- The full decodeInterlaced roundtrip on filterAllPasses output.
private theorem decodeInterlaced_filterAllPasses (image : PngImage)
    (strategy : FilterStrategy) (hvalid : image.isValid = true)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    let ihdr : IHDRInfo := {
      width := image.width, height := image.height,
      bitDepth := 8, colorType := .rgba,
      compressionMethod := 0, filterMethod := 0, interlaceMethod := .adam7
    }
    decodeInterlaced ihdr (filterAllPasses (adam7Extract image) strategy) none none
      = .ok image := by
  intro ihdr
  unfold decodeInterlaced
  show decodeInterlaced.go ihdr (filterAllPasses (adam7Extract image) strategy) none none
    (IHDRInfo.bytesPerPixel ihdr) image.width.toNat image.height.toNat 0 0 #[] = .ok image
  rw [show IHDRInfo.bytesPerPixel ihdr = 4 from bpp_rgba8_eq_4 ihdr rfl rfl]
  apply decodeInterlaced_go_inv image strategy hvalid hw hh ihdr rfl rfl rfl rfl
    0 0 #[] (adam7Extract image) rfl (Png.Spec.InterlaceCorrect.adam7Extract_size image)
    (filterAllPasses (adam7Extract image) strategy)
  · simp only [filterAllPasses]; omega
  · intro i hi; unfold filterAllPasses; simp only [Nat.zero_add]
  · simp only [Array.size_empty]
  · intro i hi his; simp only [Array.size_empty] at hi; omega
  · omega

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
