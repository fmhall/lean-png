---
name: png-interlace-proofs
description: Use when implementing or proving properties about Adam7 interlacing, sub-image extraction, pixel scatter/gather, or interlace index bijectivity.
allowed-tools: Read, Bash, Grep
---

# Adam7 Interlace Proof Patterns

## Adam7 Pass Layout

Adam7 defines 7 passes over the image grid. Each pass samples pixels
at specific row/column offsets and strides:

| Pass | Row start | Row stride | Col start | Col stride |
|------|-----------|------------|-----------|------------|
| 1    | 0         | 8          | 0         | 8          |
| 2    | 0         | 8          | 4         | 8          |
| 3    | 4         | 8          | 0         | 4          |
| 4    | 0         | 4          | 2         | 4          |
| 5    | 2         | 4          | 0         | 2          |
| 6    | 0         | 2          | 1         | 2          |
| 7    | 1         | 2          | 0         | 1          |

These constants are fixed by the PNG spec. Define them as lookup
tables and verify properties by `decide`.

## Sub-Image Dimensions

For an image of size `width x height`, pass `p` produces a sub-image
of size:

```lean
def passWidth (p : Fin 7) (width : Nat) : Nat :=
  (width + colStride[p] - colStart[p] - 1) / colStride[p]

def passHeight (p : Fin 7) (height : Nat) : Nat :=
  (height + rowStride[p] - rowStart[p] - 1) / rowStride[p]
```

## Key Theorems

### 1. Coverage: Every pixel is in exactly one pass

```lean
theorem adam7_coverage (width height : Nat) (r : Fin height) (c : Fin width) :
    ∃! (p : Fin 7) (sr : Fin (passHeight p height)) (sc : Fin (passWidth p width)),
      adam7Row p sr = r ∧ adam7Col p sc = c
```

This is the bijectivity theorem. Proof approach:
- **Existence**: compute `r % rowStride` and `c % colStride` to determine
  which pass `(r, c)` belongs to. This is a finite case analysis on
  `(r % 8, c % 8)` — there are 64 cases, each mapping to exactly one pass.
  Closeable by `decide` on the 64-entry lookup table.
- **Uniqueness**: different passes have disjoint `(row_mod_8, col_mod_8)` 
  patterns. Also closeable by `decide`.

### 2. Scatter/Gather Roundtrip

```lean
theorem scatter_extract (image : PngImage) :
    adam7Scatter (adam7Extract image) = image
```

Where `adam7Extract` produces 7 sub-images and `adam7Scatter` places
their pixels back into the full image.

Proof: by coverage theorem, every pixel `(r, c)` is extracted into
exactly one sub-image at a unique position, and scattered back to `(r, c)`.

### 3. Total Pixel Count

```lean
theorem adam7_total_pixels (width height : Nat) :
    (Finset.range 7).sum (fun p => passWidth p width * passHeight p height)
    = width * height
```

This follows from the coverage bijectivity.

## Proof Techniques

### Finite case analysis on mod residues

The 8x8 Adam7 pattern tile is small enough for `decide`:

```lean
-- Which pass does pixel (r % 8, c % 8) belong to?
def adam7PassFor (rmod cmod : Fin 8) : Fin 7 := ...

-- Verify exhaustive coverage by decide
theorem adam7PassFor_covers : ∀ (rm cm : Fin 8),
    adam7Row (adam7PassFor rm cm) ... = rm ∧ ... := by decide
```

### Index arithmetic for sub-image coordinates

Converting between full-image coordinates and sub-image coordinates:

```lean
-- Full image → sub-image
def toSubRow (p : Fin 7) (r : Nat) : Nat := (r - rowStart[p]) / rowStride[p]
def toSubCol (p : Fin 7) (c : Nat) : Nat := (c - colStart[p]) / colStride[p]

-- Sub-image → full image
def fromSubRow (p : Fin 7) (sr : Nat) : Nat := sr * rowStride[p] + rowStart[p]
def fromSubCol (p : Fin 7) (sc : Nat) : Nat := sc * colStride[p] + colStart[p]
```

The roundtrip `toSubRow p (fromSubRow p sr) = sr` follows from:
```
((sr * stride + start) - start) / stride = sr
```
Which is `Nat.add_sub_cancel` + `Nat.mul_div_cancel`.

Use `omega` for the arithmetic goals.
