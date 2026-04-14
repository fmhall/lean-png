/-!
# PNG Scanline Filtering (Native Lean)

Pure Lean implementations of all 5 PNG filter types:
- None (0): identity
- Sub (1): difference from byte `bpp` positions left
- Up (2): difference from corresponding byte in prior row
- Average (3): difference from floor-average of left and above
- Paeth (4): difference from Paeth predictor of left, above, upper-left

Each filter has the form `filtered[i] = raw[i] - predictor(context)` (mod 256).
Unfiltering reverses this: `raw[i] = filtered[i] + predictor(context)` (mod 256).

See `Png/Spec/FilterCorrect.lean` for roundtrip proofs.
-/

namespace Png.Native.Filter

/-- PNG filter types as defined in the PNG specification. -/
inductive FilterType where
  | none    : FilterType  -- 0
  | sub     : FilterType  -- 1
  | up      : FilterType  -- 2
  | average : FilterType  -- 3
  | paeth   : FilterType  -- 4
  deriving Repr, BEq, DecidableEq

/-- Convert a byte to a filter type. Returns `none` for unknown values. -/
def FilterType.ofUInt8 (b : UInt8) : FilterType :=
  match b with
  | 0 => .none
  | 1 => .sub
  | 2 => .up
  | 3 => .average
  | 4 => .paeth
  | _ => .none

/-- Convert a filter type to its byte value. -/
def FilterType.toUInt8 : FilterType → UInt8
  | .none    => 0
  | .sub     => 1
  | .up      => 2
  | .average => 3
  | .paeth   => 4

/-! ## Helper functions -/

/-- Get byte at position `i` from a ByteArray, returning 0 if out of bounds.
    This matches PNG spec behavior where out-of-bounds references are treated as 0. -/
@[inline] def getByteOr0 (arr : ByteArray) (i : Nat) : UInt8 :=
  if h : i < arr.size then arr.get i h else 0

/-- The Paeth predictor as defined in the PNG specification.
    Given three neighboring bytes a (left), b (above), c (upper-left),
    returns the one closest to the linear prediction `a + b - c`. -/
def paethPredictor (a b c : UInt8) : UInt8 :=
  let p : Int := a.toNat + b.toNat - c.toNat
  let pa := (p - a.toNat).natAbs
  let pb := (p - b.toNat).natAbs
  let pc := (p - c.toNat).natAbs
  if pa ≤ pb ∧ pa ≤ pc then a
  else if pb ≤ pc then b
  else c

/-! ## Byte-level filter/unfilter

These operate on a single byte position given the predictor value.
The key identity: `(x - pred + pred) mod 256 = x` for UInt8 arithmetic. -/

/-- Filter one byte: subtract the predictor (mod 256). -/
@[inline] def filterByte (raw pred : UInt8) : UInt8 := raw - pred

/-- Unfilter one byte: add back the predictor (mod 256). -/
@[inline] def unfilterByte (filtered pred : UInt8) : UInt8 := filtered + pred

/-! ## Row-level filter operations

Each function takes:
- `bpp`: bytes per pixel (used by Sub, Average, Paeth for the "left" reference)
- `row`: the raw scanline bytes (for filter) or filtered bytes (for unfilter)
- `prior`: the previous row's reconstructed bytes (0s for the first row)

The implementations use well-founded recursion on byte position so that
proofs can use functional induction. -/

/-- Apply the None filter to a row (identity — copies bytes unchanged). -/
def filterNone (row : ByteArray) : ByteArray := row

/-- Reverse the None filter (identity). -/
def unfilterNone (row : ByteArray) : ByteArray := row

/-- Apply the Sub filter to a row.
    `filtered[i] = raw[i] - raw[i - bpp]` (mod 256). -/
def filterSub (bpp : Nat) (row : ByteArray) : ByteArray :=
  go 0 (ByteArray.empty)
where
  go (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ row.size then out
    else
      let raw_i := getByteOr0 row i
      let left := if i ≥ bpp then getByteOr0 row (i - bpp) else 0
      go (i + 1) (out.push (filterByte raw_i left))
  termination_by row.size - i

/-- Reverse the Sub filter.
    `raw[i] = filtered[i] + reconstructed[i - bpp]` (mod 256).
    Note: we read from the output (already-reconstructed bytes) for the left reference. -/
def unfilterSub (bpp : Nat) (row : ByteArray) : ByteArray :=
  go 0 (ByteArray.empty)
where
  go (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ row.size then out
    else
      let filt_i := getByteOr0 row i
      let left := if i ≥ bpp then getByteOr0 out (i - bpp) else 0
      go (i + 1) (out.push (unfilterByte filt_i left))
  termination_by row.size - i

/-- Apply the Up filter to a row.
    `filtered[i] = raw[i] - prior[i]` (mod 256). -/
def filterUp (row prior : ByteArray) : ByteArray :=
  go 0 (ByteArray.empty)
where
  go (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ row.size then out
    else
      let raw_i := getByteOr0 row i
      let above := getByteOr0 prior i
      go (i + 1) (out.push (filterByte raw_i above))
  termination_by row.size - i

/-- Reverse the Up filter.
    `raw[i] = filtered[i] + prior[i]` (mod 256). -/
def unfilterUp (row prior : ByteArray) : ByteArray :=
  go 0 (ByteArray.empty)
where
  go (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ row.size then out
    else
      let filt_i := getByteOr0 row i
      let above := getByteOr0 prior i
      go (i + 1) (out.push (unfilterByte filt_i above))
  termination_by row.size - i

/-- Apply the Average filter to a row.
    `filtered[i] = raw[i] - floor((left + above) / 2)` (mod 256). -/
def filterAverage (bpp : Nat) (row prior : ByteArray) : ByteArray :=
  go 0 (ByteArray.empty)
where
  go (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ row.size then out
    else
      let raw_i := getByteOr0 row i
      let left := if i ≥ bpp then getByteOr0 row (i - bpp) else 0
      let above := getByteOr0 prior i
      let pred := ((left.toNat + above.toNat) / 2).toUInt8
      go (i + 1) (out.push (filterByte raw_i pred))
  termination_by row.size - i

/-- Reverse the Average filter.
    `raw[i] = filtered[i] + floor((left + above) / 2)` (mod 256).
    Left is read from already-reconstructed output. -/
def unfilterAverage (bpp : Nat) (row prior : ByteArray) : ByteArray :=
  go 0 (ByteArray.empty)
where
  go (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ row.size then out
    else
      let filt_i := getByteOr0 row i
      let left := if i ≥ bpp then getByteOr0 out (i - bpp) else 0
      let above := getByteOr0 prior i
      let pred := ((left.toNat + above.toNat) / 2).toUInt8
      go (i + 1) (out.push (unfilterByte filt_i pred))
  termination_by row.size - i

/-- Apply the Paeth filter to a row.
    `filtered[i] = raw[i] - PaethPredictor(left, above, upperLeft)` (mod 256). -/
def filterPaeth (bpp : Nat) (row prior : ByteArray) : ByteArray :=
  go 0 (ByteArray.empty)
where
  go (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ row.size then out
    else
      let raw_i := getByteOr0 row i
      let left := if i ≥ bpp then getByteOr0 row (i - bpp) else 0
      let above := getByteOr0 prior i
      let upperLeft := if i ≥ bpp then getByteOr0 prior (i - bpp) else 0
      let pred := paethPredictor left above upperLeft
      go (i + 1) (out.push (filterByte raw_i pred))
  termination_by row.size - i

/-- Reverse the Paeth filter.
    `raw[i] = filtered[i] + PaethPredictor(left, above, upperLeft)` (mod 256).
    Left and upperLeft are read from already-reconstructed output and prior row. -/
def unfilterPaeth (bpp : Nat) (row prior : ByteArray) : ByteArray :=
  go 0 (ByteArray.empty)
where
  go (i : Nat) (out : ByteArray) : ByteArray :=
    if i ≥ row.size then out
    else
      let filt_i := getByteOr0 row i
      let left := if i ≥ bpp then getByteOr0 out (i - bpp) else 0
      let above := getByteOr0 prior i
      let upperLeft := if i ≥ bpp then getByteOr0 prior (i - bpp) else 0
      let pred := paethPredictor left above upperLeft
      go (i + 1) (out.push (unfilterByte filt_i pred))
  termination_by row.size - i

/-! ## Top-level dispatch -/

/-- Apply a filter to a raw scanline given the prior (reconstructed) row. -/
def filterRow (ft : FilterType) (bpp : Nat) (row prior : ByteArray) : ByteArray :=
  match ft with
  | .none    => filterNone row
  | .sub     => filterSub bpp row
  | .up      => filterUp row prior
  | .average => filterAverage bpp row prior
  | .paeth   => filterPaeth bpp row prior

/-- Reverse a filter on a filtered scanline given the prior (reconstructed) row. -/
def unfilterRow (ft : FilterType) (bpp : Nat) (row prior : ByteArray) : ByteArray :=
  match ft with
  | .none    => unfilterNone row
  | .sub     => unfilterSub bpp row
  | .up      => unfilterUp row prior
  | .average => unfilterAverage bpp row prior
  | .paeth   => unfilterPaeth bpp row prior

end Png.Native.Filter
