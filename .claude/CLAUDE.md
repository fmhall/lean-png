# lean-png

Verified PNG decoder/encoder in Lean 4, with formal proofs of correctness.
Reuses lean-zip's verified DEFLATE/CRC32. Toolchain: see `lean-toolchain`.
Build system: Lake.

**IMPORTANT**: Read `.claude/LEARNINGS.md` before starting any proof work.
It contains hard-won lessons from prior agent sessions that will save you
hours of wasted effort (opaque loop pitfalls, key lemma names, proof
patterns that work).

## Build and Test

    lake build          # build library + test executable
    lake exe test       # run all tests

Run from the project root. Tests require `testdata/` directory.

**Quality metric**: sorry count — `grep -rc sorry Png/ || true`

### NixOS / nix-shell

On NixOS, the project's `shell.nix` provides zlib/libpng/pkg-config.
If direnv is set up, the environment activates automatically on `cd`.
Otherwise, prefix commands with `nix-shell --run`:

    nix-shell --run "lake build && lake exe test"

**Important:** Lake caches `run_io` results (like `moreLinkArgs`) in
`.lake/`. If you switch between nix-shell and bare shell, or the nix
environment changes, you may need `rm -rf .lake` before building — a
plain `lake clean` is not sufficient to clear the cached link flags.

## Code Organization

### Source layout

Survey `Png/` and `PngTest/` directly. Every source file has a
module-level `/-! ... -/` docstring describing its purpose. Run `ls Png/**/*.lean`
to orient. Key directories:
- `Png/` — FFI wrappers and pure-Lean implementations
- `Png/Native/` — Native Lean implementations (no FFI)
- `Png/Spec/` — Formal specifications and correctness proofs
- `PngTest/` — Per-module tests
- Shared utilities (Binary, Handle, BitReader, ZipForStd) from
  [lean-zip-common](https://github.com/kim-em/lean-zip-common)
- DEFLATE/CRC32/Adler32 from [lean-zip](https://github.com/kim-em/lean-zip)

### Key documents
    PLAN.md              — Phased roadmap and development cycle (do not modify)
    PROGRESS.md          — Global milestones (updated by summarize agents)
    progress/            — Per-session progress entries (one file per session)
    plans/               — Per-session plan files (one file per active session)
    .claude/skills/      — Project-local skill files (proof patterns)

## Quality Standards

### Development cycle (from PLAN.md)
1. Type signature with `:= sorry`
2. Specification theorems with `:= by sorry`
3. Implementation
4. Auto-solve pass: run `try?` on each `sorry`. If `try?` succeeds, it
   generates info messages with replacement tactics — prefer the suggested
   replacement, but if it looks brittle (e.g. depends on nonlocal simp
   lemmas), use a simpler alternative and note why. Never leave `try?` in
   committed code. Use `bv_decide` when the goal involves `BitVec`.
5. Conformance tests (native vs FFI)
6. Manual proofs for goals that resist automation

### Native implementations
- Place in `Png/Native/` (e.g. `Png/Native/Filter.lean`)
- Formal specs in `Png/Spec/` (e.g. `Png/Spec/FilterCorrect.lean`)
- Keep FFI implementations intact as the fast path
- Start simple, optimize later with equivalence proofs

### Specifications

There are three levels of specification quality. Know which you're
writing and be honest about it:

1. **Tautological**: restates the implementation (`f x = fImpl x`).
   Proves nothing useful. Avoid.
2. **Characterizing properties**: mathematical properties independent
   of how the function is computed — algebraic identities, structural
   invariants, or invertibility theorems (e.g. `unfilter (filter x) = x`).
   This is the gold standard.
3. **Algorithmic correspondence**: two implementations of the same
   algorithm agree (e.g. native decoder = reference decoder). Useful
   when the algorithm IS the spec (e.g. PNG spec pseudocode), but be
   explicit that this is translation validation.

When a function's "specification" is an algorithm (PNG spec pseudocode),
transcribing it into proof-friendly style and proving correspondence
IS the right approach. But characterize the mathematical building
blocks independently where possible.

- For optimized versions, specs are equivalence with the simple version.
- Do NOT modify theorem statements just to make proofs easier. If a spec
  is genuinely wrong or too strong, it can be changed — but document the
  rationale in PLAN.md

### Proofs
- Do NOT remove a working proof — refactoring a proof (same statement,
  better proof) is fine and encouraged; deleting a theorem is not
- Do NOT write multi-line tactic blocks without checking intermediate state
- Do NOT try the same approach more than 3 times — each retry must be
  fundamentally different (different tactic family, decomposition, or lemma)
- Do NOT use `native_decide` — it is forbidden in this codebase. When
  tempted to use it (e.g. for decidable propositions over large finite
  types), try `decide_cbv` instead, which uses kernel-level evaluation
  without native code generation
- Prefer `omega`, `decide`, `simp`, `grind` over manual arithmetic
- After getting a proof to work, refactor it immediately:
  combine steps, find minimal proof, extract reusable lemmas
- Think about generally useful constructions that could be upstreamed
- **Opaque loop functions**: Both `Lean.Loop.forIn` (from `while`) and
  `Std.Legacy.Range.forIn'` (from `for ... in [:n]`) use auto-generated
  `loop✝` functions that CANNOT be unfolded in proofs. If you need to
  prove invariants through these loops, refactor the implementation to
  use well-founded recursion with `termination_by` instead.
- **No bare simp**: Always use `simp only [...]` with explicit lemma lists.
  Use `simp?` to discover the minimal lemma set. Bare `simp` (without
  `only`) is fragile and depends on the global simp database.

### Tests
- Every new feature needs tests in `PngTest/`
- Register new test modules in `PngTest.lean`
- Include edge cases: 1x1 images, grayscale, RGBA, 16-bit, interlaced
- Conformance: native decode + FFI decode = same pixels (and vice versa)

### Commits
- Conventional prefixes: `feat:`, `fix:`, `refactor:`, `test:`, `doc:`, `chore:`
- Each commit must compile and pass tests
- One logical change per commit
- `sorry` policy: intermediate commits with `sorry` are acceptable during
  multi-session development. Mark such commits clearly (e.g.
  `feat: add filter spec (proofs WIP)`). Track remaining `sorry`s in
  `PLAN.md` for the next session.

### C FFI changes
- Match style in existing `c/*.c` files
- Check allocation failures, use overflow guards

### Reusing lean-zip

This project depends on lean-zip for DEFLATE and CRC32. Key imports:
- `Zip.Native.Inflate` / `Zip.Native.Deflate` — verified compression
- `Zip.Native.Crc32` — verified CRC32
- `Zip.Spec.DeflateRoundtrip` — roundtrip theorem
- `Zip.Spec.Crc32` — CRC32 specification
- `ZipCommon.Binary` — little-endian/big-endian read/write
- `ZipForStd.*` — general ByteArray/Array/List lemmas

When proving PNG roundtrip theorems, compose with lean-zip theorems
rather than re-proving compression correctness.
