# `native_decide` audit — 2026-10-14 (evening)

**Rule:** Pablo's MASTER DIRECTIVE forbids `native_decide` corpus-wide
(introduces `Lean.ofReduceBool` + `Lean.trustCompiler` axioms, violating
the project axiom budget).

## Result

**ZERO `native_decide` tactic usages found** in `PF_Lean4_Code/PF/**/*.lean`.

## Method

1. Count of textual mentions: **265 occurrences across 253 files.**
2. All 265 occurrences are in **documentation comments** stating the ban
   (patterns like "No sorry, native_decide, axiom", "no `native_decide`",
   "r317 removed native_decide", etc.) or in **doc-strings describing
   external context**.
3. Precise tactic-form search
   `(^\s*native_decide\s*$|:= by native_decide|<;> native_decide|exact\s+by\s+native_decide|·\s*native_decide)`
   returned **0 matches**.
4. Spot-check of `BSDFrobeniusTraceAttempt.lean`,
   `CollatzConjectureFrameworkAttack.lean`,
   `OddPerfectNumberFrameworkAttack.lean`,
   `BrocardProblemFrameworkAttack.lean` — all use `decide` (kernel) in
   actual tactic form; `native_decide` only in prose.
5. Historical note from `CollatzConjectureFrameworkAttack.lean` l.33:
   *"Each via `decide` (kernel-native; r317 removed `native_decide`)."*
   The r317 cleanup (2026-08-24) migrated remaining usage.

## One stale reference flagged (not a violation, but documentation drift)

`PF/Referee/FrameworkUniversalReach.lean` lines 23–28 state:

> TWENTY-THREE PROBLEM ATTACKS — all axiom-free at kernel level
> ([propext, Classical.choice, Quot.sound] for the structural-linkage
> core; the non-Clay capstones that use `decide` / `native_decide` for
> their small-case witnesses additionally rely on the kernel facilities
> [Lean.ofReduceBool, Lean.trustCompiler] — standard Lean kernel
> infrastructure, ZERO PROJECT AXIOMS):

Since r317 removed `native_decide`, the "or `native_decide`" clause and
the `[Lean.ofReduceBool, Lean.trustCompiler]` axiom-bar mention are
**stale**. Suggested fix: remove the "/ `native_decide`" alternative and
drop the `[Lean.ofReduceBool, Lean.trustCompiler]` reference (since
`decide` is kernel-native and doesn't introduce those axioms when it
succeeds without reflection).

**Not editing without Pablo's go-ahead** — the file is in `PF/Referee/`
and may be reviewed as-is for external audit purposes.

## Status

Task #9 ("Research: audit native_decide usage across corpus (Rank 2)")
can be marked **completed**. Corpus-wide native_decide ban is honored.
