import Png.Native.Decode
import Png.Native.Idat
import Png.Spec.OverflowSafe
import Png.Spec.IdatCorrect

/-!
# Decompression Bomb Safety Proofs

Proves that the PNG decode pipeline cannot produce unbounded decompression
output. The defense composes three proven layers:

## Layer A: IDAT size validation (`extractDecompressValidate_size`)

`extractDecompressValidate` passes `maxOutputSize` (default 1 GiB) to
lean-zip's `decompressSingle`, then validates that the decompressed size
matches `ihdr.expectedIdatSize`. If it returns `.ok`, the output size is
exactly `expectedIdatSize`.

## Layer B: expectedIdatSize bounded (from OverflowSafe)

Under reasonable dimension constraints (width/height < 2^31 or under the
`maxImagePixels` budget), `expectedIdatSize` is bounded:
- `expectedIdatSize_bounded` — < 2^66 under width/height < 2^31
- `expectedIdatSize_fits_nat64` — < 2^63 under maxImagePixels budget

## Layer C: Pixel output size (`adam7Scatter_pixels_size`)

Interlace scatter produces exactly `w * h * 4` bytes, ensuring the final
pixel buffer has a deterministic, bounded size.

## Key theorems

- `extractDecompressValidate_size` — decompressed IDAT = expectedIdatSize
- `extractDecompressValidate_fits_nat64` — decompressed IDAT < 2^63
- `adam7Scatter_pixels_size` — interlace scatter output = w * h * 4
- `decodeInterlaced_pixels_size` — interlaced decode output = w * h * 4
- `unfilterRow_size` — each unfilter variant preserves row size
- `unfilterScanlines_ok_size` — unfiltered data = height * scanlineBytes

## Status: 0 sorry — all theorems fully proven
-/

namespace Png.Spec.DecompBombSafe

open Png
open Png.Idat
open Png.Native.Decode
open Png.Native.Filter
open Png.Native.ColorConvert
open Png.Native.Interlace

/-! ## Layer A: extractDecompressValidate guarantees output size -/

/-- If `extractDecompressValidate` succeeds, the output size equals
    `ihdr.expectedIdatSize`. This follows directly from the
    `validateIdatSize` check: if it returns `.ok`, the size matched. -/
theorem extractDecompressValidate_size (ihdr : IHDRInfo) (chunks : Array PngChunk)
    (result : ByteArray) (h : extractDecompressValidate ihdr chunks = .ok result) :
    result.size = ihdr.expectedIdatSize := by
  unfold extractDecompressValidate at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i raw _
    split at h
    · contradiction
    · rename_i hv
      simp only [pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
      have hval : validateIdatSize ihdr raw = true := by
        revert hv; cases validateIdatSize ihdr raw <;> simp
      unfold validateIdatSize at hval
      exact beq_iff_eq.mp hval

/-! ## Composition: expectedIdatSize is bounded under dimension constraints -/

/-- Under the maxImagePixels budget (2^30), the decompressed IDAT output
    from `extractDecompressValidate` fits in signed 64-bit (< 2^63).
    Composes Layer A (output = expectedIdatSize) with Layer B
    (expectedIdatSize < 2^63 from OverflowSafe). -/
theorem extractDecompressValidate_fits_nat64
    (ihdr : IHDRInfo) (chunks : Array PngChunk)
    (result : ByteArray) (h : extractDecompressValidate ihdr chunks = .ok result)
    (hpix : ihdr.width.toNat * ihdr.height.toNat ≤ Png.Spec.OverflowSafe.maxImagePixels)
    (hbd : ihdr.bitDepth.toNat ≤ 16)
    (hh_pos : ihdr.height.toNat ≥ 1) :
    result.size < 2 ^ 63 := by
  rw [extractDecompressValidate_size ihdr chunks result h]
  exact Png.Spec.OverflowSafe.expectedIdatSize_fits_nat64 ihdr hpix hbd hh_pos

/-- Under general dimension constraints (width/height < 2^31), the
    decompressed IDAT output fits in < 2^66. -/
theorem extractDecompressValidate_bounded_general
    (ihdr : IHDRInfo) (chunks : Array PngChunk)
    (result : ByteArray) (h : extractDecompressValidate ihdr chunks = .ok result)
    (hw : ihdr.width.toNat < 2 ^ 31)
    (hh : ihdr.height.toNat < 2 ^ 31)
    (hbd : ihdr.bitDepth.toNat ≤ 16) :
    result.size < 2 ^ 66 := by
  rw [extractDecompressValidate_size ihdr chunks result h]
  exact Png.Spec.OverflowSafe.expectedIdatSize_bounded ihdr hw hh hbd

/-! ## unfilterRow and unfilterScanlines output size -/

private theorem unfilterSub_go_size (bpp : Nat) (row : ByteArray) (i : Nat) (out : ByteArray) :
    (unfilterSub.go bpp row i out).size = out.size + (row.size - i) := by
  unfold unfilterSub.go; split
  case isTrue hge => omega
  case isFalse =>
    simp only []; rw [unfilterSub_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

private theorem unfilterUp_go_size (row prior : ByteArray) (i : Nat) (out : ByteArray) :
    (unfilterUp.go row prior i out).size = out.size + (row.size - i) := by
  unfold unfilterUp.go; split
  case isTrue hge => omega
  case isFalse =>
    simp only []; rw [unfilterUp_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

private theorem unfilterAverage_go_size (bpp : Nat) (row prior : ByteArray)
    (i : Nat) (out : ByteArray) :
    (unfilterAverage.go bpp row prior i out).size = out.size + (row.size - i) := by
  unfold unfilterAverage.go; split
  case isTrue hge => omega
  case isFalse =>
    simp only []; rw [unfilterAverage_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

private theorem unfilterPaeth_go_size (bpp : Nat) (row prior : ByteArray)
    (i : Nat) (out : ByteArray) :
    (unfilterPaeth.go bpp row prior i out).size = out.size + (row.size - i) := by
  unfold unfilterPaeth.go; split
  case isTrue hge => omega
  case isFalse =>
    simp only []; rw [unfilterPaeth_go_size]; simp only [ByteArray.size_push]; omega
  termination_by row.size - i

/-- All unfilter variants produce output of the same size as the input row. -/
theorem unfilterRow_size (ft : FilterType) (bpp : Nat) (row prior : ByteArray) :
    (unfilterRow ft bpp row prior).size = row.size := by
  unfold unfilterRow
  cases ft with
  | none => unfold unfilterNone; rfl
  | sub =>
    unfold unfilterSub
    rw [unfilterSub_go_size]; simp only [ByteArray.size_empty]; omega
  | up =>
    unfold unfilterUp
    rw [unfilterUp_go_size]; simp only [ByteArray.size_empty]; omega
  | average =>
    unfold unfilterAverage
    rw [unfilterAverage_go_size]; simp only [ByteArray.size_empty]; omega
  | paeth =>
    unfold unfilterPaeth
    rw [unfilterPaeth_go_size]; simp only [ByteArray.size_empty]; omega

private theorem unfilterScanlines_go_size (decompressed : ByteArray) (width height : UInt32)
    (bpp scanlineBytes : Nat) (r : Nat) (result priorRow : ByteArray)
    (hdsz : decompressed.size = height.toNat * (1 + scanlineBytes))
    (hrs : (1 + scanlineBytes) ≥ 1) :
    (unfilterScanlines.go decompressed width height bpp scanlineBytes (1 + scanlineBytes) r
      result priorRow hdsz hrs).size = result.size + (height.toNat - r) * scanlineBytes := by
  unfold unfilterScanlines.go
  split
  case isTrue hlt =>
    simp only []
    rw [unfilterScanlines_go_size _ _ _ _ _ _ _ _ hdsz hrs]
    simp only [ByteArray.size_append]
    rw [unfilterRow_size]
    -- The extract size is min (r * (1+sl) + 1 + sl) decompressed.size - (r * (1+sl) + 1)
    -- = scanlineBytes, since r < height implies the range is within bounds.
    have hle : r * (1 + scanlineBytes) + 1 + scanlineBytes ≤ decompressed.size := by
      rw [hdsz]
      have hrp1 : r * (1 + scanlineBytes) + 1 + scanlineBytes = (r + 1) * (1 + scanlineBytes) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      rw [hrp1]
      exact Nat.mul_le_mul_right _ (by omega)
    simp only [ByteArray.size_extract]
    rw [Nat.min_eq_left hle]
    -- The extract size simplifies: (r*(1+sl)+1+sl) - (r*(1+sl)+1) = sl
    have hext : r * (1 + scanlineBytes) + 1 + scanlineBytes - (r * (1 + scanlineBytes) + 1) = scanlineBytes := by omega
    rw [hext]
    -- Now: result.size + sl + (height-(r+1)) * sl = result.size + (height-r) * sl
    have hsub : (height.toNat - r) * scanlineBytes = scanlineBytes + (height.toNat - (r + 1)) * scanlineBytes := by
      have : height.toNat - r = 1 + (height.toNat - (r + 1)) := by omega
      rw [this, Nat.add_mul, Nat.one_mul]
    omega
  case isFalse hge =>
    have : height.toNat - r = 0 := by omega
    simp only [this, Nat.zero_mul, Nat.add_zero]
  termination_by height.toNat - r

/-- When `unfilterScanlines` succeeds, the output has size `height * scanlineBytes`. -/
theorem unfilterScanlines_ok_size
    (decompressed : ByteArray) (width height : UInt32) (bpp scanlineBytes : Nat)
    (result : ByteArray)
    (h : unfilterScanlines decompressed width height bpp scanlineBytes = .ok result) :
    result.size = height.toNat * scanlineBytes := by
  unfold unfilterScanlines at h
  simp only [] at h
  split at h
  · rename_i hdsz
    simp only [Except.ok.injEq] at h
    rw [← h]
    have := unfilterScanlines_go_size decompressed width height bpp scanlineBytes
      0 ByteArray.empty
      (ByteArray.mk (Array.replicate scanlineBytes 0)) hdsz (by omega)
    simp only [ByteArray.size_empty, Nat.zero_add, Nat.sub_zero] at this
    exact this
  · contradiction

/-! ## adam7Scatter pixel buffer size -/

private theorem setPixelAt_size (pixels : ByteArray) (idx : Nat)
    (pixel : UInt8 × UInt8 × UInt8 × UInt8) :
    (setPixelAt pixels idx pixel).size = pixels.size := by
  unfold setPixelAt; split <;> simp only [ByteArray.size_set!]

private theorem scatterPass_go_size (buf : ByteArray) (fullWidth : Nat)
    (subPixels : ByteArray) (subW : Nat) (p : Fin 7) (i total : Nat) :
    (scatterPass.go buf fullWidth subPixels subW p i total).size = buf.size := by
  unfold scatterPass.go; split
  · rfl
  · simp only []; rw [scatterPass_go_size, setPixelAt_size]
  termination_by total - i

private theorem scatterPass_size (buf : ByteArray) (fullWidth : Nat)
    (subImage : PngImage) (p : Fin 7) :
    (scatterPass buf fullWidth subImage p).size = buf.size := by
  unfold scatterPass
  exact scatterPass_go_size buf fullWidth subImage.pixels subImage.width.toNat p 0
    (subImage.width.toNat * subImage.height.toNat)

private theorem adam7Scatter_go_size (subImages : Array PngImage) (buf : ByteArray)
    (fullWidth : Nat) (p : Nat) :
    (adam7Scatter.go subImages buf fullWidth p).size = buf.size := by
  unfold adam7Scatter.go; split
  · split
    · rw [adam7Scatter_go_size, scatterPass_size]
    · rw [adam7Scatter_go_size]
  · rfl
  termination_by 7 - p

/-- `adam7Scatter` produces a pixel buffer of exactly `width * height * 4` bytes. -/
theorem adam7Scatter_pixels_size (subImages : Array PngImage) (w h : Nat) :
    (adam7Scatter subImages w h).pixels.size = w * h * 4 := by
  unfold adam7Scatter
  simp only []
  rw [adam7Scatter_go_size]
  simp only [ByteArray.size, Array.size_replicate]

/-! ## decodeInterlaced output size -/

private theorem interlaced_go_pixels_size (ihdr : IHDRInfo) (decompressed : ByteArray)
    (plte : Option PLTEInfo) (trns : Option TRNSInfo)
    (bpp w h p offset : Nat) (subImages : Array PngImage) (result : PngImage)
    (hw : w = ihdr.width.toNat) (hh : h = ihdr.height.toNat)
    (hgo : decodeInterlaced.go ihdr decompressed plte trns bpp w h p offset subImages = .ok result) :
    result.pixels.size = result.width.toNat * result.height.toNat * 4 := by
  unfold decodeInterlaced.go at hgo
  split at hgo
  case isTrue hp =>
    simp only [] at hgo
    split at hgo
    · contradiction
    · split at hgo
      · contradiction
      · exact interlaced_go_pixels_size ihdr decompressed plte trns bpp w h (p + 1)
          _ _ result hw hh hgo
  case isFalse =>
    simp only [Except.ok.injEq] at hgo; rw [← hgo]
    rw [adam7Scatter_pixels_size]
    unfold adam7Scatter
    simp only []
    have hw32 : w < 2 ^ 32 := by rw [hw]; exact ihdr.width.toBitVec.isLt
    have hh32 : h < 2 ^ 32 := by rw [hh]; exact ihdr.height.toBitVec.isLt
    have hwmod : w % 2 ^ 32 = w := Nat.mod_eq_of_lt hw32
    have hhmod : h % 2 ^ 32 = h := Nat.mod_eq_of_lt hh32
    unfold Nat.toUInt32 UInt32.toNat UInt32.ofNat
    simp only [BitVec.toNat_ofNat, hwmod, hhmod]
  termination_by 7 - p

/-- If `decodeInterlaced` succeeds, the pixel buffer is `w * h * 4`. -/
theorem decodeInterlaced_pixels_size (ihdr : IHDRInfo) (decompressed : ByteArray)
    (plte : Option PLTEInfo) (trns : Option TRNSInfo) (result : PngImage)
    (h : decodeInterlaced ihdr decompressed plte trns = .ok result) :
    result.pixels.size = result.width.toNat * result.height.toNat * 4 := by
  unfold decodeInterlaced at h
  exact interlaced_go_pixels_size ihdr decompressed plte trns
    ihdr.bytesPerPixel ihdr.width.toNat ihdr.height.toNat 0 0 #[] result rfl rfl h

end Png.Spec.DecompBombSafe
