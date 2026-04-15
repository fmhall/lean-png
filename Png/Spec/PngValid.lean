import Png.Native.Decode
import Png.Spec.RoundtripCorrect

/-!
# PNG Validity Predicate and Decode Completeness

Defines `validPng`, a predicate on `ByteArray` capturing all structural
and value constraints for a well-formed non-interlaced RGBA 8-bit PNG,
and proves `decodePng_complete`: for every valid PNG byte stream, the
decoder produces an image.

## Design

`validPng` is an existentially quantified conjunction: it asserts the
existence of intermediate values (chunks, IHDR, decompressed data) that
satisfy all the decoder's preconditions. The conditions are:

1. Valid PNG signature and chunk framing (parseChunks succeeds)
2. At least one chunk, first chunk is IHDR
3. IHDR fields: non-zero width/height, RGBA color type, 8-bit depth,
   non-interlaced
4. IDAT extraction, decompression, and size validation succeed
5. Decompressed size matches IHDR expectations

## Status: 0 sorry -- all theorems fully proven
-/

namespace Png.Spec.PngValid

open Png
open Png.Native.Encode
open Png.Native.Decode
open Png.Native.Filter
open Png.Idat

/-! ## Validity predicate -/

/-- A PNG byte stream is valid (non-interlaced RGBA 8-bit) if the decoder's
    preconditions are met at every step.

    The existential witnesses are the parsed chunks, IHDR info, and
    decompressed IDAT data -- the intermediate values the decoder computes.
    The conditions on these witnesses ensure every branch of `decodePng`
    succeeds. -/
def validPng (data : ByteArray) : Prop :=
  ∃ (chunks : Array PngChunk) (ihdr : IHDRInfo) (decompressed : ByteArray),
    -- Chunk parsing succeeds
    parseChunks data = .ok chunks ∧
    -- At least one chunk, first chunk is IHDR
    chunks.size > 0 ∧
    chunks[0]!.isIHDR = true ∧
    -- IHDR parsing succeeds
    IHDRInfo.fromBytes chunks[0]!.data = .ok ihdr ∧
    -- Non-interlaced
    ihdr.interlaceMethod = .none ∧
    -- RGBA 8-bit
    ihdr.colorType = .rgba ∧
    ihdr.bitDepth = 8 ∧
    -- Non-zero dimensions
    ihdr.width ≠ 0 ∧
    ihdr.height ≠ 0 ∧
    -- IDAT extraction, decompression, and validation succeed
    extractDecompressValidate ihdr chunks = .ok decompressed ∧
    -- Decompressed size matches expected (height * (1 + scanlineBytes))
    -- For RGBA 8-bit: scanlineBytes = width * 4
    decompressed.size = ihdr.height.toNat * (1 + ihdr.width.toNat * 4)

/-! ## Helper lemmas -/

/-- bytesPerPixel for RGBA 8-bit is 4. -/
private theorem bpp_rgba8 (ihdr : IHDRInfo)
    (hct : ihdr.colorType = .rgba) (hbd : ihdr.bitDepth = 8) :
    IHDRInfo.bytesPerPixel ihdr = 4 := by
  unfold IHDRInfo.bytesPerPixel IHDRInfo.channels
  rw [hct, hbd]; decide

/-- scanlineBytes for RGBA 8-bit is width * 4. -/
private theorem scanlineBytes_rgba8 (ihdr : IHDRInfo)
    (hct : ihdr.colorType = .rgba) (hbd : ihdr.bitDepth = 8) :
    IHDRInfo.scanlineBytes ihdr = ihdr.width.toNat * 4 := by
  unfold IHDRInfo.scanlineBytes IHDRInfo.channels
  rw [hct, hbd]
  simp only [show UInt8.toNat 8 = 8 from by decide]
  rw [show 4 * 8 * ihdr.width.toNat = 8 * (ihdr.width.toNat * 4) from by omega]
  rw [Nat.mul_add_div (by omega : (8 : Nat) > 0) (ihdr.width.toNat * 4) 7]
  omega

/-! ## Main theorem -/

/-- **Decode completeness**: every valid PNG byte stream can be decoded.

    For any byte stream satisfying `validPng`, the decoder `decodePng`
    produces a `PngImage`. This is the converse direction of the roundtrip
    theorem: roundtrip says "encode then decode = original"; completeness
    says "anything structurally valid can be decoded".

    Currently proven for non-interlaced RGBA 8-bit PNGs.
    TODO: extend to all color types and interlacing. -/
theorem decodePng_complete (data : ByteArray) (h : validPng data) :
    ∃ img, decodePng data = .ok img := by
  obtain ⟨chunks, ihdr, decompressed, hparse, hne, hihdr_first, hihdr_ok,
          hni, hct, hbd, _hw, _hh, hidat, hdsz⟩ := h
  -- The proof follows the same structure as decodePng_encodePng in RoundtripCorrect,
  -- threading each step through the monadic bind chain.
  -- We use the fact that decodePng succeeds to construct our witness.
  -- First, establish that decodePng actually produces .ok from our hypotheses
  -- by unfolding decodePng and rewriting each step.

  -- Compute bpp and scanlineBytes
  have hbpp := bpp_rgba8 ihdr hct hbd
  have hscan := scanlineBytes_rgba8 ihdr hct hbd

  -- unfilterScanlines succeeds
  have hunfilter : ∃ rawPixels, unfilterScanlines decompressed ihdr.width ihdr.height
      4 (ihdr.width.toNat * 4) = .ok rawPixels := by
    simp only [unfilterScanlines]
    rw [dif_pos (show decompressed.size = ihdr.height.toNat * (1 + ihdr.width.toNat * 4) from hdsz)]
    exact ⟨_, rfl⟩
  obtain ⟨rawPixels, hunfilter⟩ := hunfilter

  -- Now unfold decodePng and simplify
  -- The key: thread all intermediate results into a single simp call
  unfold decodePng
  simp only [bind, Except.bind, hparse,
    dif_neg (show ¬ chunks.size = 0 from by omega)]
  -- After dif_neg, the goal has chunks[0]'h for some h : ¬chunks.size = 0
  -- Convert to getElem! for hypothesis matching
  simp only [← getElem!_pos, hihdr_first, Bool.not_true, hihdr_ok,
    show (ihdr.interlaceMethod != InterlaceMethod.none) = false from by rw [hni]; rfl,
    hidat, hbpp, hscan, hunfilter, pure, Except.pure, hct, hbd, convertToRGBA]
  exact ⟨_, rfl⟩

/-! ## Bridge: encoded PNGs are valid -/

/-- Any PNG produced by `encodePng` satisfies `validPng`, provided
    the image has valid dimensions and the compressed data is within budget.

    This bridges the roundtrip theorem and the completeness theorem:
    `encodePng` produces valid data, and valid data always decodes. -/
theorem encodePng_validPng (image : PngImage) (strategy : FilterStrategy)
    (hvalid : image.isValid = true)
    (hsize : (filterScanlines image.pixels image.width image.height strategy).size
              < 1024 * 1024 * 1024)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    validPng (encodePng image strategy) := by
  -- Get chunk parse result
  obtain ⟨result, hparse, hsize_pos, hfirst, hextract⟩ :=
    Png.Spec.RoundtripCorrect.parseChunks_encodePng_result image strategy
  -- Derive pixel size
  have hpixels_sz : image.pixels.size = image.width.toNat * image.height.toNat * 4 := by
    simp only [PngImage.isValid, PngImage.expectedSize, beq_iff_eq] at hvalid; exact hvalid
  -- The IHDR info
  let ihdrInfo : IHDRInfo :=
    { width := image.width, height := image.height,
      bitDepth := 8, colorType := .rgba,
      compressionMethod := 0, filterMethod := 0, interlaceMethod := .none }
  -- IHDRInfo.fromBytes on the first chunk
  have hfromBytes : IHDRInfo.fromBytes result[0]!.data = .ok ihdrInfo := by
    rw [hfirst]
    exact Png.Spec.ihdr_fromBytes_toBytes ihdrInfo hw hh rfl rfl
  -- The first chunk is IHDR
  have hfirst_ihdr : result[0]!.isIHDR = true := by rw [hfirst]; rfl
  -- extractDecompressValidate succeeds on the filtered data
  let filteredData := filterScanlines image.pixels image.width image.height strategy
  have hextract_decompress : Idat.extractAndDecompress result = .ok filteredData := by
    unfold Idat.extractAndDecompress
    rw [hextract]
    have h_roundtrip := Png.Spec.RoundtripCorrect.idat_roundtrip_in_pipeline filteredData hsize
    unfold Idat.extractAndDecompress at h_roundtrip
    exact h_roundtrip
  have hscanline : IHDRInfo.scanlineBytes ihdrInfo = image.width.toNat * 4 :=
    scanlineBytes_rgba8 ihdrInfo rfl rfl
  have hvalid_size : Idat.validateIdatSize ihdrInfo filteredData = true := by
    have hexpected : IHDRInfo.expectedIdatSize ihdrInfo =
        image.height.toNat * (1 + image.width.toNat * 4) := by
      unfold IHDRInfo.expectedIdatSize; rw [hscanline]
    rw [Idat.validateIdatSize, hexpected,
        Png.Spec.RoundtripCorrect.filterScanlines_size image.pixels image.width image.height
          strategy hpixels_sz,
        beq_self_eq_true]
  have hextract_validate : Idat.extractDecompressValidate ihdrInfo result = .ok filteredData := by
    unfold Idat.extractDecompressValidate
    simp only [hextract_decompress, bind, Except.bind, hvalid_size, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  have hfsz : filteredData.size = image.height.toNat * (1 + image.width.toNat * 4) :=
    Png.Spec.RoundtripCorrect.filterScanlines_size image.pixels image.width image.height
      strategy hpixels_sz
  -- Construct the validPng witness
  exact ⟨result, ihdrInfo, filteredData, hparse, hsize_pos, hfirst_ihdr, hfromBytes,
         rfl, rfl, rfl, hw, hh, hextract_validate, hfsz⟩

/-! ## Corollary -/

/-- Corollary: decoding an encoded PNG always succeeds.
    This follows from `encodePng_validPng` + `decodePng_complete`,
    providing an alternative proof of decode success. -/
theorem decodePng_encodePng_succeeds (image : PngImage) (strategy : FilterStrategy)
    (hvalid : image.isValid = true)
    (hsize : (filterScanlines image.pixels image.width image.height strategy).size
              < 1024 * 1024 * 1024)
    (hw : image.width ≠ 0) (hh : image.height ≠ 0) :
    ∃ img, decodePng (encodePng image strategy) = .ok img :=
  decodePng_complete _ (encodePng_validPng image strategy hvalid hsize hw hh)

end Png.Spec.PngValid
