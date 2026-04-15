import Png.Native.Chunk
import Png.Native.Encode
import Png.Spec.BoundsCorrect
import Png.Spec.RoundtripCorrect

/-!
# Overflow Safety Proofs

Proves that all dimension arithmetic in the PNG decode/encode path stays
within safe bounds under stated size limits. Defines a configurable
`maxImagePixels` constant with proven downstream bounds.

## Key results

1. `channels_bounded` — channels(ct) ≤ 4 for all color types
2. `bytesPerPixel_bounded` — bytesPerPixel ≤ 8 under bitDepth ≤ 16
3. `scanlineBytes_bounded_by_width` — scanlineBytes < 2^34 under width < 2^31
4. `expectedIdatSize_bounded` — expectedIdatSize < 2^66 under dim < 2^31
5. `filterScanlines_size_bounded` — filterScanlines output bounded < 2^64
6. `maxImagePixels` — 2^30 pixel budget with proven downstream bounds
7. `totalPixelBytes_bounded` — width * height * 4 ≤ 2^32 under budget
8. `expectedIdatSize_fits_nat64` — expectedIdatSize < 2^63 under budget

## Status: 0 sorry — all theorems fully proven
-/

namespace Png.Spec.OverflowSafe

open Png
open Png.Native.Encode

/-! ## Channel count bounds -/

/-- The number of channels for any PNG color type is at most 4. -/
theorem channels_bounded (ct : ColorType) : IHDRInfo.channels ct ≤ 4 := by
  cases ct <;> simp only [IHDRInfo.channels] <;> omega

/-- The number of channels for any PNG color type is at least 1. -/
theorem channels_pos (ct : ColorType) : IHDRInfo.channels ct ≥ 1 := by
  cases ct <;> simp only [IHDRInfo.channels] <;> omega

/-! ## Bytes per pixel bounds -/

/-- Under the PNG spec constraint bitDepth ≤ 16, bytesPerPixel ≤ 8.
    (Max: 4 channels × 16 bits = 64 bits = 8 bytes.) -/
theorem bytesPerPixel_bounded (ihdr : IHDRInfo)
    (hbd : ihdr.bitDepth.toNat ≤ 16) :
    ihdr.bytesPerPixel ≤ 8 := by
  unfold IHDRInfo.bytesPerPixel
  simp only []
  have hch := channels_bounded ihdr.colorType
  have : IHDRInfo.channels ihdr.colorType * ihdr.bitDepth.toNat ≤ 64 :=
    Nat.le_trans (Nat.mul_le_mul hch hbd) (by omega)
  omega

/-- bytesPerPixel is always at least 1 when bitDepth ≥ 1. -/
theorem bytesPerPixel_pos (ihdr : IHDRInfo)
    (hbd : ihdr.bitDepth.toNat ≥ 1) :
    ihdr.bytesPerPixel ≥ 1 := by
  unfold IHDRInfo.bytesPerPixel
  simp only []
  have hch := channels_pos ihdr.colorType
  have : IHDRInfo.channels ihdr.colorType * ihdr.bitDepth.toNat ≥ 1 :=
    Nat.le_trans (by omega) (Nat.mul_le_mul hch hbd)
  omega

/-! ## Scanline bytes bounds -/

/-- Under width < 2^31 and valid PNG parameters (channels ≤ 4, bitDepth ≤ 16),
    scanlineBytes < 2^34.
    Derivation: bitsPerLine ≤ 4 * 16 * (2^31 - 1) < 2^37.
    scanlineBytes = (bitsPerLine + 7) / 8 < 2^34. -/
theorem scanlineBytes_bounded_by_width (ihdr : IHDRInfo)
    (hw : ihdr.width.toNat < 2 ^ 31)
    (hbd : ihdr.bitDepth.toNat ≤ 16) :
    ihdr.scanlineBytes < 2 ^ 34 := by
  unfold IHDRInfo.scanlineBytes
  simp only []
  have hch := channels_bounded ihdr.colorType
  have hprod : IHDRInfo.channels ihdr.colorType * ihdr.bitDepth.toNat ≤ 64 :=
    Nat.le_trans (Nat.mul_le_mul hch hbd) (by omega)
  have : IHDRInfo.channels ihdr.colorType * ihdr.bitDepth.toNat * ihdr.width.toNat
         ≤ 64 * ihdr.width.toNat :=
    Nat.mul_le_mul_right _ hprod
  omega

/-! ## Expected IDAT size bounds -/

/-- Under width < 2^31, height < 2^31, and valid PNG parameters,
    expectedIdatSize < 2^66. Uses factor-by-factor bounding to avoid
    nonlinear reasoning. -/
theorem expectedIdatSize_bounded (ihdr : IHDRInfo)
    (hw : ihdr.width.toNat < 2 ^ 31)
    (hh : ihdr.height.toNat < 2 ^ 31)
    (hbd : ihdr.bitDepth.toNat ≤ 16) :
    ihdr.expectedIdatSize < 2 ^ 66 := by
  unfold IHDRInfo.expectedIdatSize
  have hscan := scanlineBytes_bounded_by_width ihdr hw hbd
  -- Bound each factor: height ≤ 2^31-1, 1+scanlineBytes ≤ 2^34
  have h1 : 1 + ihdr.scanlineBytes ≤ 2 ^ 34 := by omega
  have h2 : ihdr.height.toNat * (1 + ihdr.scanlineBytes) ≤
            ihdr.height.toNat * 2 ^ 34 :=
    Nat.mul_le_mul_left _ h1
  have h3 : ihdr.height.toNat * 2 ^ 34 ≤ (2 ^ 31 - 1) * 2 ^ 34 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## Filter scanlines output bounds -/

/-- The filterScanlines output size is bounded under valid dimension constraints.
    Under width < 2^31, height < 2^31:
    size = height * (1 + width * 4) < 2^64. -/
theorem filterScanlines_size_bounded (pixels : ByteArray) (width height : UInt32)
    (strategy : FilterStrategy)
    (hvalid : pixels.size = width.toNat * height.toNat * 4)
    (hw : width.toNat < 2 ^ 31)
    (hh : height.toNat < 2 ^ 31) :
    (filterScanlines pixels width height strategy).size < 2 ^ 64 := by
  have hsz := Png.Spec.RoundtripCorrect.filterScanlines_size pixels width height strategy hvalid
  rw [hsz]
  -- Bound each factor separately using Nat.mul_le_mul
  have h1 : 1 + width.toNat * 4 ≤ 1 + (2 ^ 31 - 1) * 4 := by omega
  have h2 : height.toNat * (1 + width.toNat * 4) ≤
            height.toNat * (1 + (2 ^ 31 - 1) * 4) :=
    Nat.mul_le_mul_left _ h1
  have h3 : height.toNat * (1 + (2 ^ 31 - 1) * 4) ≤
            (2 ^ 31 - 1) * (1 + (2 ^ 31 - 1) * 4) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## Maximum image pixel budget -/

/-- Maximum number of pixels allowed for safe processing.
    Set to 2^30 = 1,073,741,824 (approximately 1 billion pixels).
    This ensures all downstream arithmetic stays within 64-bit bounds. -/
def maxImagePixels : Nat := 2 ^ 30

/-- maxImagePixels is positive. -/
theorem maxImagePixels_pos : maxImagePixels > 0 := by
  unfold maxImagePixels; omega

/-- maxImagePixels equals 1073741824. -/
theorem maxImagePixels_val : maxImagePixels = 1073741824 := by
  unfold maxImagePixels; omega

/-! ## Bounds under the maxImagePixels budget -/

/-- Under the pixel budget, the total RGBA pixel bytes fit in 32 bits.
    width * height * 4 ≤ 4 * maxImagePixels = 2^32. -/
theorem totalPixelBytes_bounded (w h : Nat)
    (hpix : w * h ≤ maxImagePixels) :
    w * h * 4 ≤ 2 ^ 32 := by
  unfold maxImagePixels at hpix
  omega

/-- Under the pixel budget, width * height fits in 31 bits. -/
theorem pixel_count_fits_nat32 (w h : Nat)
    (hpix : w * h ≤ maxImagePixels) :
    w * h < 2 ^ 31 := by
  unfold maxImagePixels at hpix
  omega

/-- Under the pixel budget with valid PNG parameters,
    expectedIdatSize < 2^63 (fits in signed 64-bit).

    Uses the `scanlineBytes_le` bound from BoundsCorrect, then rewrites
    the nonlinear product `height * scanlineBytes` into a form where omega
    can apply the pixel budget constraint. -/
theorem expectedIdatSize_fits_nat64 (ihdr : IHDRInfo)
    (hpix : ihdr.width.toNat * ihdr.height.toNat ≤ maxImagePixels)
    (hbd : ihdr.bitDepth.toNat ≤ 16)
    (hh_pos : ihdr.height.toNat ≥ 1) :
    ihdr.expectedIdatSize < 2 ^ 63 := by
  unfold IHDRInfo.expectedIdatSize
  have hscan_le := Png.Spec.BoundsCorrect.scanlineBytes_le ihdr
  have hch := channels_bounded ihdr.colorType
  have hcbw : IHDRInfo.channels ihdr.colorType * ihdr.bitDepth.toNat * ihdr.width.toNat
              ≤ 64 * ihdr.width.toNat :=
    Nat.mul_le_mul_right _
      (Nat.le_trans (Nat.mul_le_mul hch hbd) (by omega))
  have hscan64 : ihdr.scanlineBytes ≤ 64 * ihdr.width.toNat := by omega
  have hh32 : ihdr.height.toNat < 2 ^ 32 := ihdr.height.toBitVec.isLt
  -- Distribute: h * (1 + s) = h + h * s
  rw [Nat.mul_add ihdr.height.toNat 1 ihdr.scanlineBytes, Nat.mul_one]
  -- Bound h * s: first bound s ≤ 64 * w, then rewrite to get w * h form
  have step1 : ihdr.height.toNat * ihdr.scanlineBytes ≤
               ihdr.height.toNat * (64 * ihdr.width.toNat) :=
    Nat.mul_le_mul_left _ hscan64
  -- h * (64 * w) = 64 * w * h = 64 * (w * h) ≤ 64 * maxImagePixels
  have step2 : ihdr.height.toNat * (64 * ihdr.width.toNat) =
               64 * ihdr.width.toNat * ihdr.height.toNat := Nat.mul_comm _ _
  have step3 : 64 * ihdr.width.toNat * ihdr.height.toNat =
               64 * (ihdr.width.toNat * ihdr.height.toNat) := Nat.mul_assoc _ _ _
  have step4 : ihdr.height.toNat * ihdr.scanlineBytes ≤ 64 * 2 ^ 30 := by
    unfold maxImagePixels at hpix; omega
  omega

/-! ## Convenience: RGBA 8-bit specific bounds -/

/-- For RGBA 8-bit images, scanlineBytes = width * 4. -/
theorem rgba8_scanlineBytes (ihdr : IHDRInfo)
    (hct : ihdr.colorType = .rgba)
    (hbd : ihdr.bitDepth = 8) :
    ihdr.scanlineBytes = ihdr.width.toNat * 4 := by
  unfold IHDRInfo.scanlineBytes
  rw [hct]
  simp only [IHDRInfo.channels, UInt8.toNat]
  rw [hbd]
  have : (UInt8.toBitVec 8).toNat = 8 := by decide
  rw [this]
  omega

/-- For RGBA 8-bit images, expectedIdatSize = height * (1 + width * 4). -/
theorem rgba8_expectedIdatSize (ihdr : IHDRInfo)
    (hct : ihdr.colorType = .rgba)
    (hbd : ihdr.bitDepth = 8) :
    ihdr.expectedIdatSize = ihdr.height.toNat * (1 + ihdr.width.toNat * 4) := by
  unfold IHDRInfo.expectedIdatSize
  rw [rgba8_scanlineBytes ihdr hct hbd]

/-- For RGBA 8-bit images under the pixel budget, expectedIdatSize < 2^33.
    This is a much tighter bound than the general case. -/
theorem rgba8_expectedIdatSize_tight (ihdr : IHDRInfo)
    (hct : ihdr.colorType = .rgba)
    (hbd : ihdr.bitDepth = 8)
    (hpix : ihdr.width.toNat * ihdr.height.toNat ≤ maxImagePixels)
    (hh_pos : ihdr.height.toNat ≥ 1) :
    ihdr.expectedIdatSize < 2 ^ 33 := by
  unfold IHDRInfo.expectedIdatSize
  rw [rgba8_scanlineBytes ihdr hct hbd]
  -- Distribute: h * (1 + w * 4) = h + h * (w * 4)
  rw [Nat.mul_add ihdr.height.toNat 1 (ihdr.width.toNat * 4), Nat.mul_one]
  -- Rewrite h * (w * 4) = 4 * w * h = 4 * (w * h) to use pixel budget
  have step1 : ihdr.height.toNat * (ihdr.width.toNat * 4) =
               4 * ihdr.width.toNat * ihdr.height.toNat := by
    rw [Nat.mul_comm ihdr.height.toNat, Nat.mul_comm ihdr.width.toNat 4]
  have step2 : 4 * ihdr.width.toNat * ihdr.height.toNat =
               4 * (ihdr.width.toNat * ihdr.height.toNat) := Nat.mul_assoc _ _ _
  have step3 : ihdr.height.toNat * (ihdr.width.toNat * 4) ≤ 4 * 2 ^ 30 := by
    unfold maxImagePixels at hpix; omega
  have hh32 : ihdr.height.toNat < 2 ^ 32 := ihdr.height.toBitVec.isLt
  omega

end Png.Spec.OverflowSafe
