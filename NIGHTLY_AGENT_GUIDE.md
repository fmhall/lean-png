# Nightly Agent Guide

How an autonomous agent should make progress on lean-png every night.

## Schedule

Run at 2:00 AM local time. Total runtime budget: ~2 hours.

## Session Sequence

### 1. Planner (10 min)

**Read first:**
- `.claude/LEARNINGS.md` — proof patterns and pitfalls
- `PROGRESS.md` — current phase and milestones
- Latest 3 entries in `progress/` — what was done recently

**Assess state:**
```bash
grep -rc 'sorry' Png/                          # sorry count (target: 0)
lake exe test 2>&1 | grep TOTAL                # test count (must not decrease)
grep -c 'theorem ' Png/Spec/*.lean | awk -F: '{sum+=$2} END {print sum}'  # theorem count
find Png PngTest -name '*.lean' | wc -l        # file count
```

**Create work items:**
- Check the master plan (`.claude/plans/elegant-watching-ember.md`) for the current phase
- Create 3-5 GitHub issues from the phase's deliverables
- Label each: `proof`, `feature`, `test`, `refactor`, or `optimize`
- Priority order: (a) sorry elimination, (b) proven bounds, (c) color type expansion, (d) tests, (e) optimization

**Issue template:**
```markdown
## Task
[One sentence description]

## Context
[Which phase, which deliverable, why this matters]

## Files to modify
- [exact paths]

## Approach
[Proof strategy, key lemmas to use, patterns from LEARNINGS.md]

## Success criteria
- [ ] Compiles: `lake build`
- [ ] Tests pass: `lake exe test`
- [ ] Sorry count: unchanged or decreased
- [ ] [Specific theorem proven / test added / etc.]
```

### 2. Workers (3 parallel, 30 min each)

**Before starting:**
1. Read `.claude/LEARNINGS.md` — EVERY TIME
2. Read the issue body completely
3. Read all files mentioned in the issue
4. Check what lemmas exist: `grep -rn 'theorem' Png/Spec/<relevant>.lean`

**Workflow:**
```bash
git checkout -b agent/<issue-number>
# ... do work ...
lake build                    # must succeed
lake exe test 2>&1 | tail -3  # must pass
grep -rc 'sorry' Png/         # must not increase
git add -A && git commit -m "feat: <description>"
git push -u origin agent/<issue-number>
gh pr create --title "<description>" --body "Closes #<N>"
```

**Rules:**
- NO bare `simp` — always `simp only [...]`
- NO `for`/`while`/`Id.run do` — WF recursion with `termination_by`
- NO `native_decide` — use `decide` or `decide_cbv`
- NO modifying `PLAN.md`, `.claude/CLAUDE.md`, or `lakefile.lean`
- Commit after every compiling change (checkpoints)
- If stuck after 3 fundamentally different approaches, leave sorry and document why

**Auto-merge criteria (reviewer can approve without human):**
- `lake build` succeeds
- `lake exe test` passes (all tests)
- Sorry count ≤ previous count
- No new `]!` in decode path (after Phase 1)
- Only touches files listed in the issue
- Diff < 500 lines

### 3. Reviewer (15 min)

**Check each open PR:**
```bash
gh pr list --state open
# For each PR:
gh pr diff <N>
# Verify:
# - No new sorry (grep the diff)
# - No new ]! in decode path
# - No bare simp
# - No for/while loops in functions that need proofs
# - Commit messages use conventional prefixes
```

**Approve** if auto-merge criteria met. **Request changes** with specific feedback otherwise. **Close** PRs older than 7 days with no activity.

### 4. Summarizer (5 min)

**Write progress entry:**
```bash
cat > progress/$(date -u +%Y%m%d_%H%M)_nightly.md << 'EOF'
# Nightly Session — $(date -u +%Y-%m-%d)

## Metrics
- Sorry count: X (delta: ±N)
- Theorem count: X (delta: +N)
- Test count: X (delta: +N)
- Files: X

## Issues created: #A, #B, #C
## Issues claimed: #D, #E
## PRs merged: #F, #G
## Blockers: [description]

## Phase: [current phase from master plan]
## Next priority: [what tomorrow's planner should focus on]
EOF
```

## What to Read Before Each Task Type

| Task type | Must read |
|-----------|----------|
| **Proof work** | LEARNINGS.md (all), relevant skill in `.claude/skills/`, the spec file being modified, the implementation file being proven |
| **New feature** | LEARNINGS.md (#3 NO opaque loops, #7 preconditions), Types.lean, existing similar code |
| **Test work** | PngTest/ for patterns, FFI.lean for reference decoder, testdata/ for corpus |
| **Refactoring** | LEARNINGS.md (#2 three-theorem pattern), the file being refactored + its spec file |
| **Optimization** | PngBench.lean, LEARNINGS.md (#5 compose don't re-prove, #12 consult lean-zip) |

## How to Add a Feature (Step by Step)

1. **Type signature with `:= sorry`** — define the function, implement as sorry
2. **Spec theorems with `:= by sorry`** — state what must be true
3. **Build** — verify it compiles with sorries
4. **Implementation** — fill in the function body
5. **Build + test** — verify implementation works
6. **Auto-solve** — run `try?` on each sorry, use suggestions
7. **Manual proofs** — for goals that resist automation
8. **Refactor proofs** — combine steps, extract reusable lemmas
9. **Commit** — one logical change per commit

## When NOT to Merge Automatically

- Changes to `lakefile.lean` (build system)
- Changes to `Png/Types.lean` (type definitions affect everything)
- Adding new dependencies
- Removing theorems (even `private` ones)
- Any change that increases sorry count
- Diffs > 500 lines
- Changes touching 5+ files

These require human review.

## Error Recovery

| Problem | Action |
|---------|--------|
| Build fails after edit | Revert last edit, try different approach |
| 3 consecutive build failures | Skip issue with reason, move to next |
| Sorry count increased | Do NOT commit — fix or revert |
| Test regression | Check if test expectation changed, fix or revert |
| Rate limit hit | Stop cleanly, commit what compiles, document progress in issue comment |
| Merge conflict | Rebase on main, resolve conflicts, re-run tests |

## Phase-Specific Focus

| Phase | Agent focus | Key patterns |
|-------|------------|-------------|
| 1: Hardening | `]!` → `]` conversions, adam7 sorry | `lean-content-preservation` skill, `getElem!_eq_getElem` bridging |
| 2: Color types | PLTE parsing, color converters | Three-theorem pattern for new go-loops, `bpp > 0` from IHDR |
| 3: Interlace + completeness | Wire adam7, validity predicate | Compose existing theorems, monadic stepping |
| 4: Overflow | Size bound proofs | `omega` for arithmetic, explicit overflow lemmas |
| 5: CI/Fuzz | Infrastructure, no proofs | Shell scripts, YAML workflows |
| 6: Automation | Pod config, commands | Copy lean-zip patterns |
| 7: CVE proofs | Security claims | Name theorems after CVE classes |
