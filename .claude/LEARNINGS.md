# Agent Learnings

Hard-won lessons from ~30 agent sessions building lean-png. **Read this
before starting work.** It will save you hours.

## 1. Read the skills and dependencies FIRST

The single biggest time sink across all sessions was agents searching for
lemma names by trial-and-error (writing test files to /tmp, grepping
randomly) instead of reading what already exists.

**Before writing any proof**, run:
```bash
grep -rn 'push_getElem\|size_push\|append_getElem\|extract_append' \
  .lake/packages/zipCommon/ZipForStd/ByteArray.lean
```

Key lemmas that come up constantly:
- `ByteArray.push_getElem!_lt` — push preserves earlier elements
- `ByteArray.push_getElem!_eq` — pushed element is at index `size`
- `ByteArray.size_push` — `(ba.push b).size = ba.size + 1`
- `ByteArray.size_append` — `(a ++ b).size = a.size + b.size`
- `ByteArray.extract_append_left/right` — extract from concatenation

Also read the relevant `.claude/skills/` files. They contain exact proof
patterns distilled from lean-zip's 600+ PRs.

## 2. The three-theorem pattern for buffer loops

Every function that builds a ByteArray via a `go` loop needs three
theorems proved **in this order** (each feeds the next):

1. `_size`: `(go ... i out).size = out.size + (n - i)`
2. `_getElem!_lt`: `j < out.size → (go ... i out)[j]! = out[j]!` (preservation)
3. `_getElem!_ge`: `j ≥ out.size → (go ... i out)[j]! = expected` (content)

This pattern (from the `lean-content-preservation` skill) was the
breakthrough for all filter proofs. The B3 agent was stuck for an
entire session until it adopted this structure.

## 3. NO opaque loops — WF recursion only

`for`/`while`/`Id.run do` loops generate `Lean.Loop.forIn.loop` or
`Std.Legacy.Range.forIn'` — both are opaque `partial` defs that
**cannot be unfolded in proofs**. This bit us repeatedly:

- `extractIdatData` — had to refactor from `for chunk in chunks` to WF `go`
- `splitIntoIdatChunks` — had to refactor from `while` to WF `go`
- `filterScanlines` — had to refactor from `for r in [:height]` to WF `go`
- `unfilterScanlines` — same
- `encodePng` — same
- `validChunkSequence` — same
- `parseChunks` — refactored to WF `go` (was blocking capstone proof)

**Rule**: Never write `for`, `while`, `Id.run do`, or `mut` in any
function that will appear in a theorem statement. Use explicit recursion
with `termination_by` from the start. Refactoring later wastes an entire
agent session.

## 4. UInt8 cancellation is the core filter lemma

All 5 PNG filter roundtrips reduce to:
```lean
UInt8.sub_add_cancel : ∀ (a b : UInt8), a - b + b = a
```

This already exists in the standard library. The B3 agent spent a long
time trying `bv_decide`, `omega`, manual BitVec proofs — all unnecessary.
**Search the stdlib first**: `grep -rn 'sub_add_cancel' .lake/packages/`

For output-dependent filters (Sub, Average, Paeth), the proof also needs
an invariant: "after processing i bytes, `out[k] = origRow[k]` for all
`k < i`." The predictor reads from `out[i - bpp]` which equals
`origRow[i - bpp]` by the invariant. Then cancellation closes the goal.

## 5. Compose, don't re-prove

The IDAT roundtrip is one line:
```lean
exact zlib_decompressSingle_compress data level hsize
```

Multiple agents almost went down the path of re-proving compression
correctness. The whole point of depending on lean-zip is to reuse its
theorems. Similarly, `Crc32.Native.crc32` is already verified — just
use it.

## 6. Formalization-first cycle enables parallelism

The pattern `sorry stubs → parallel agents → fill proofs` worked
extremely well. We ran B1 (chunks), B2 (IDAT), B3 (filters), and
A3 (test corpus) simultaneously because the sorry placeholders defined
the interfaces.

But: **agents on the same file without git isolation will collide**.
The B2 proofs agent and refactoring agent both edited IdatCorrect.lean
concurrently. It happened to work because one finished first, but this
is fragile.

## 7. Theorem preconditions matter

- `parseChunk_serialize` needs `c.data.size < 2^31` (PNG spec limit)
- `unfilterRow_filterRow` needs `bpp > 0` (because at bpp=0, filter
  reads from `row[i]` but unfilter reads from shorter `out[i]`)
- `decompressIdat_compressIdat` needs `data.size < 1024 * 1024 * 1024`
  (lean-zip's inflate budget)

Agents that tried to prove theorems without these preconditions wasted
time. If a proof seems impossible, check if the theorem statement needs
a hypothesis added — it's often a real constraint from the spec.

## 8. What closes what

Quick reference for common proof patterns:

| Goal shape | Tactic |
|-----------|--------|
| Enum roundtrip (`ofUInt8 (toUInt8 x) = x`) | `cases x <;> rfl` |
| Concrete decidable prop | `decide` or `decide_cbv` |
| BitVec/UInt equality | `bv_decide` |
| Linear arithmetic | `omega` |
| Algebraic/case-splitting | `grind` |
| `¬(i ≥ n)` | `omega` (NOT `push_neg`, no Mathlib) |
| `Except.error = Except.ok` contradiction | `exact nomatch h` |
| ByteArray equality | `ByteArray.ext_getElem!` + element-wise |
| WF function case split | `unfold f; split` (NOT `simp only [f]` — loops!) |

## 9. What was hard (and how it was solved)

The capstone `decodePng_encodePng` is now **fully proven**. The hardest
sub-problems and their solutions:

**`unfilterScanlines_filterScanlines`**: Treat the filtered buffer as a
fixed object, prove by induction on rows that each unfilter step recovers
the original row. Key: both go-loops thread the same `priorRow`, so the
IH applies directly. (~200 lines)

**`parseChunk_at_offset`**: Parsing a chunk at arbitrary offset in a
concatenated stream. Solved by lifting each field-access lemma
(`readUInt32BE`, `extract`, CRC) to work at offset `pfx.size`. (~100 lines)

**`parseChunks_go_serialized`**: Stepping `parseChunks.go` through a
sequence of serialized chunks. Had to strengthen the IH to track middle
elements (not just prefix preservation). (~100 lines)

**`extractIdatData` tracking**: Showing that `extractIdatData` on the
parsed array equals `extractIdatData` on the original IDAT array. Solved
via a "sandwich lemma" showing extraction skips non-IDAT prefix/suffix.

## 10. Agent prompt quality matters enormously

Agents that got detailed prompts with:
- Exact file paths to read
- Specific lemma names to use
- What NOT to do (no bare simp, no Mathlib, no for loops)
- The proof pattern to follow
- Which theorems to prove first vs last

...finished in 2-5 minutes. Agents with vague prompts spent 20+ minutes
exploring and often got stuck. Brief the agent like a colleague who just
walked into the room.

## 11. Formalization-first is slower to start but faster to finish

PLAN.md prescribes: type signature (sorry) → spec theorems (sorry) →
implementation → proofs. We skipped this for `encodePng`/`decodePng`,
writing implementations first and trying to prove properties after.

**Consequences of implementation-first:**
- Agents wrote `for`/`while` loops (natural Lean) that had to be
  refactored to WF recursion later — an entire agent session wasted.
- `filterScanlines` builds a flat ByteArray by appending
  `[ft_byte] ++ filteredRow` per row. The capstone proof has to
  reverse-engineer that buffer structure from the implementation.
  Spec-first would have *designed* the function so composition is
  structurally obvious (e.g. `Array ByteArray` per row + flatten).
- `parseChunk_at_offset` was discovered as a blocker mid-proof.
  Spec-first would have surfaced it immediately as a design requirement.

**Why we did it anyway:** parallelism. Formalization-first is inherently
sequential (spec → impl → proof). Implementation-first let us run B1,
B2, B3 simultaneously on day one, producing a working tested library
in ~2 hours. The cost: ~3 extra hours of proof engineering fighting
code that wasn't designed for proofs.

**The tradeoff:** implementation-first optimizes for breadth (get
everything built fast). Formalization-first optimizes for depth (each
piece is proof-complete before moving on). For a team of parallel agents,
implementation-first with sorry stubs is a reasonable choice — but the
Encode/Decode layer should have used WF recursion and proof-friendly
data structures from the start, even without full specs.
