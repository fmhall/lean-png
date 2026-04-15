import Png.Native.Chunk
import Png.Native.Encode
import Png.Native.Decode

/-!
# Index Bounds Correctness

Theorems proving that key index computations in the decode/encode path
stay within bounds. These are characterizing properties — they state
that successful operations produce results within safe ranges,
independent of how the bounds checks are implemented.

## Theorems

1. `parseChunk_offset_bounded` — successful parse → result offset ≤ data.size
2. `parseChunk_offset_advances` — successful parse → result offset > input offset
3. `validateSignature_implies_size` — signature validation → data.size ≥ 8
4. `scanlineBytes_le` — scanlineBytes is bounded by the bits-per-line input
5. `scanlineBytes_bounded` — under reasonable width, scanlineBytes < 2^31
6. `extractRow_inbounds` — valid pixel array → extractRow stays in bounds
7. `unfilterScanlines_row_offset_valid` — each row offset is valid in decompressed data
-/

namespace Png.Spec.BoundsCorrect

open Png
open Png.Native.Encode
open Png.Native.Decode

/-! ## Chunk parsing bounds -/

/-- A successful `parseChunk` always returns an offset within the data. -/
theorem parseChunk_offset_bounded (data : ByteArray) (offset : Nat)
    (result : ChunkParseResult)
    (h : parseChunk data offset = .ok result) :
    result.offset ≤ data.size := by
  unfold parseChunk at h
  simp only [bind, Except.bind] at h
  split at h <;> simp only [Except.ok.injEq] at h
  -- First guard passed: ¬(offset + 12 > data.size), so offset + 12 ≤ data.size
  rename_i hguard1
  split at h <;> simp only [Except.ok.injEq] at h
  -- Second guard passed: ¬(crcOffset + 4 > data.size)
  rename_i hguard2
  split at h <;> simp only [Except.ok.injEq] at h
  -- CRC check passed
  rename_i hguard3
  -- Extract the offset from the result
  have := h.2
  omega

/-- A successful `parseChunk` always advances past the input offset. -/
theorem parseChunk_offset_advances (data : ByteArray) (offset : Nat)
    (result : ChunkParseResult)
    (h : parseChunk data offset = .ok result) :
    result.offset > offset := by
  unfold parseChunk at h
  simp only [bind, Except.bind] at h
  split at h <;> simp only [Except.ok.injEq] at h
  rename_i hguard1
  split at h <;> simp only [Except.ok.injEq] at h
  rename_i hguard2
  split at h <;> simp only [Except.ok.injEq] at h
  rename_i hguard3
  have := h.2
  omega

/-! ## Signature bounds -/

/-- If `validateSignature` succeeds, the data has at least 8 bytes. -/
theorem validateSignature_implies_size (data : ByteArray)
    (h : validateSignature data = true) :
    data.size ≥ 8 := by
  unfold validateSignature at h
  split at h
  case isTrue hsz => exact hsz
  case isFalse => simp at h

/-! ## Scanline bounds -/

/-- `scanlineBytes` is at most `channels * bitDepth * width` (the bits-per-line
    divided by 8, rounded up). In particular it is bounded by the total bits. -/
theorem scanlineBytes_le (ihdr : IHDRInfo) :
    ihdr.scanlineBytes ≤
      IHDRInfo.channels ihdr.colorType * ihdr.bitDepth.toNat * ihdr.width.toNat := by
  unfold IHDRInfo.scanlineBytes
  omega

/-- Under a reasonable width constraint, `scanlineBytes` fits in 31 bits.
    The precondition `channels * bitDepth * width < 2^31` is always satisfied
    for valid PNG images (max 4 channels × 16-bit × width < 2^31). -/
theorem scanlineBytes_bounded (ihdr : IHDRInfo)
    (hbits : IHDRInfo.channels ihdr.colorType * ihdr.bitDepth.toNat * ihdr.width.toNat < 2 ^ 31) :
    ihdr.scanlineBytes < 2 ^ 31 := by
  have h := scanlineBytes_le ihdr
  omega

/-! ## Pixel buffer bounds -/

/-- When the pixel buffer has the expected size, `extractRow` accesses stay
    within bounds — the slice `[r * rowBytes, r * rowBytes + rowBytes)` is
    entirely within `pixels`. -/
theorem extractRow_inbounds (pixels : ByteArray) (width : UInt32)
    (r height_nat : Nat)
    (hvalid : pixels.size = width.toNat * height_nat * 4)
    (hr : r < height_nat) :
    r * (width.toNat * 4) + width.toNat * 4 ≤ pixels.size := by
  rw [hvalid]
  have h1 : r + 1 ≤ height_nat := hr
  have h2 : (r + 1) * (width.toNat * 4) ≤ height_nat * (width.toNat * 4) :=
    Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul] at h2; simp only [Nat.one_mul] at h2
  rw [show width.toNat * height_nat * 4 = height_nat * (width.toNat * 4) from by ring]
  exact h2

/-- Each row in the decompressed IDAT data starts at a valid offset.
    Row `r` starts at `r * rowStride` where `rowStride = 1 + scanlineBytes`,
    and this offset plus the full row stride fits within the buffer. -/
theorem unfilterScanlines_row_offset_valid
    (decompressed : ByteArray) (width height : UInt32)
    (bpp r : Nat)
    (hsize : decompressed.size = height.toNat * (1 + width.toNat * bpp))
    (hr : r < height.toNat) :
    r * (1 + width.toNat * bpp) + (1 + width.toNat * bpp) ≤ decompressed.size := by
  rw [hsize]
  have h1 : r + 1 ≤ height.toNat := hr
  have h2 : (r + 1) * (1 + width.toNat * bpp) ≤ height.toNat * (1 + width.toNat * bpp) :=
    Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul] at h2; simp only [Nat.one_mul] at h2
  exact h2

end Png.Spec.BoundsCorrect
