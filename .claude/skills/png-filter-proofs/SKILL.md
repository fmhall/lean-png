---
name: png-filter-proofs
description: Use when proving PNG scanline filter/unfilter roundtrip theorems, UInt8 modular arithmetic invertibility, Paeth predictor properties, or Average predictor floor-division patterns.
allowed-tools: Read, Bash, Grep
---

# PNG Scanline Filter Proof Patterns

## Filter Roundtrip Structure

All 5 PNG filter types follow the same pattern:

```
filtered[i] = raw[i] - predictor(context) (mod 256)
unfiltered[i] = filtered[i] + predictor(context) (mod 256)
```

The roundtrip proof for each byte reduces to:
```
(raw[i] - pred + pred) mod 256 = raw[i]
```

Since UInt8 arithmetic wraps at 256, this is `Nat.sub_add_cancel` in
the modular ring, or equivalently UInt8 cancellation.

## Per-Filter-Type Strategies

### None (type 0)

Trivial: `filterNone = id`, `unfilterNone = id`. Proof: `rfl`.

### Sub (type 1)

```lean
filtered[i] = raw[i] - raw[i - bpp]  -- UInt8 subtraction (wrapping)
unfiltered[i] = filtered[i] + reconstructed[i - bpp]
```

Induction on byte position `i`. The key insight: `reconstructed[i - bpp]`
in the unfilter step equals `raw[i - bpp]` by the induction hypothesis
(earlier bytes are already correctly reconstructed).

**Proof pattern:**
```lean
induction i generalizing ... with
| zero =>
  -- i < bpp: predictor is 0, filtered[i] = raw[i] - 0 = raw[i]
  simp [filterSub, unfilterSub, UInt8.sub_zero]
| succ k ih =>
  -- i >= bpp: use IH to show reconstructed[i-bpp] = raw[i-bpp]
  rw [unfilterSub, filterSub]
  -- Goal: (raw[i] - raw[i-bpp] + raw[i-bpp]) = raw[i]
  exact UInt8.sub_add_cancel ...
```

### Up (type 2)

```lean
filtered[i] = raw[i] - prior[i]
unfiltered[i] = filtered[i] + prior[i]
```

No induction needed — each byte is independent. Direct UInt8 cancellation.

### Average (type 3)

```lean
filtered[i] = raw[i] - floor((a + b) / 2)
-- where a = reconstructed[i-bpp] (or 0), b = prior[i]
```

The predictor `floor((a + b) / 2)` involves integer division. The key
lemma is that the predictor is deterministic given the context bytes,
which are available during both filtering and unfiltering.

**Caution**: The average is computed on Nat (not UInt8) before truncation:
`(a.toNat + b.toNat) / 2` then cast back to UInt8. Proofs must go
through Nat arithmetic, not UInt8 directly.

### Paeth (type 4)

```lean
filtered[i] = raw[i] - PaethPredictor(a, b, c)
-- where a = reconstructed[i-bpp], b = prior[i], c = prior[i-bpp]
```

PaethPredictor is a pure function:
```
p = a + b - c
pa = |p - a|
pb = |p - b|
pc = |p - c|
if pa <= pb && pa <= pc then a
else if pb <= pc then b
else c
```

The proof doesn't need to reason about *which* value Paeth selects —
only that it's deterministic and computable from context bytes. The
roundtrip is still just UInt8 cancellation after establishing that
both filter and unfilter compute the same predictor.

## Row-Level Proof Pattern

```lean
theorem unfilterRow_filterRow (ft : FilterType) (bpp : Nat)
    (row priorRow : ByteArray)
    (hlen : row.size > 0) :
    unfilterRow ft bpp (filterRow ft bpp row priorRow) priorRow = row := by
  cases ft with
  | none => exact unfilterNone_filterNone ...
  | sub => exact unfilterSub_filterSub ...
  | up => exact unfilterUp_filterUp ...
  | average => exact unfilterAverage_filterAverage ...
  | paeth => exact unfilterPaeth_filterPaeth ...
```

## Image-Level Proof Pattern

Induction on the list of rows, threading the prior row:

```lean
theorem unfilterImage_filterImage (rows : Array ByteArray) (bpp : Nat)
    (strategy : FilterStrategy) :
    unfilterImage bpp (filterImage bpp strategy rows) = rows := by
  -- Induction on row index, with invariant:
  -- after processing rows[0..k], unfiltered[0..k] = rows[0..k]
  -- The prior row for row k is rows[k-1] (or zeros for row 0)
```

## UInt8 Cancellation Lemmas

These are the core building blocks for all filter proofs:

```lean
-- Needed for Sub, Up, Average, Paeth roundtrips
theorem UInt8.sub_add_cancel (a b : UInt8) : a - b + b = a
theorem UInt8.add_sub_cancel (a b : UInt8) : a + b - b = a

-- For Average predictor
theorem Nat.div_deterministic (a b : Nat) : (a + b) / 2 = (a + b) / 2 := rfl
```

The UInt8 cancellation follows from `BitVec.sub_add_cancel` (since
UInt8 = BitVec 8). Use `bv_decide` if direct proof is awkward.
