# Follow-up extraction plan after PR #46025 close

**Date:** 2026-11-15.  **Trigger:** PR #46025 closed 2026-11-15 06:27 UTC after review comments from `@wwylele` (constructive: "extract useful lemmas first") and `@vihdzp` (one sentence: "complete AI slop") and auto-label `LLM-generated`.
**Decision (per user):** replace the single 2153-line PR with a smaller series.

## Attribution policy for all three follow-up PRs

Each PR commit message and body must state **up front, in the first sentence** that the contribution was AI-assisted, which AI model, and what shape the human/AI split takes (mathematics vs. style).  This is not a disclosure buried at the bottom; it is the first paragraph.  Honest attribution is cheaper than labels like `LLM-generated` appearing uninvited.

Each PR body must also link the Zulip thread `Fermat right triangle theorem` (`https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Fermat.20right.20triangle.20theorem/`) that `@wwylele` cited, so the placement conversation has continuity.

## PR A — Standalone Fermat n=4 descent for `2·a² = s⁴ + t⁴`

**Mathematical content.** `fermat42Double_impossible : ∀ a s t : ℤ, s ≠ 0 → t ≠ 0 → s² ≠ t² → IsCoprime s t → 2·a² ≠ s⁴ + t⁴`.  This is the classical **Fermat right triangle theorem** content and is the single largest self-contained descent in the current `FourSub.lean` (~1200 of the 2153 lines).  Fermat 1659 / Euler 1770.

**Why submit this one first.**
1. It is the result `@wwylele` referenced via the Zulip thread "Fermat right triangle theorem."
2. It is self-contained — no predicate wrapper needed, no composition with other descent branches.
3. It is useful on its own: the right-triangle-area-not-square phrasing is a classical corollary.
4. If the mathlib community accepts the Fermat-right-triangle content, PR B and PR C become viable; if they reject this specific placement, PR B and PR C are moot too.

**Scope.**
- One file at `Mathlib/NumberTheory/FLT/FourDouble.lean` OR as additions inside `Mathlib/NumberTheory/FLT/Four.lean`.  Decide after the Zulip placement reply.
- Predicate: `Fermat42Double (a s t : ℤ) : Prop := s ≠ 0 ∧ t ≠ 0 ∧ s ^ 2 ≠ t ^ 2 ∧ 2 * a ^ 2 = s ^ 4 + t ^ 4` paralleling mathlib's existing `Fermat42` for the sum form.
- Main theorem `fermat42Double_impossible`.
- Corollary `fermat_right_triangle_theorem` (phrased as the standard right-triangle-area statement).

**Style requirements.**
- NO file-level `set_option linter.* false` disables.  Fix lint issues individually at the point they arise.
- NO AI-style star emphasis (`★★★`, `**IS UNCONDITIONAL**`) in docstrings.  Pablo's rev-2 Lean cleanup already purged these from the PF-local copy; apply same discipline here.
- Factor into smaller lemmas with descriptive names.  Target: < 1000 lines per file, < 100 lines per theorem where possible.
- Proof style: hand-written feel.  Avoid identical case-split blocks that repeat; factor via helper lemmas.

**Estimated line count after cleanup.** 600–800 (down from 1200).  The reduction comes from removing per-session iteration cruft, not from skipping any mathematics.

## PR B — `Fermat42Sub` predicate + minimal-counterexample infrastructure

**Mathematical content.** Parallel to mathlib's existing `Fermat42` for the sum form:
- `Fermat42Sub (a b c : ℤ) : Prop := a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2`.
- `Fermat42Sub.Minimal` — minimal counterexample by `a.natAbs`.
- `Fermat42Sub.exists_minimal`.
- `Fermat42Sub.coprime_of_minimal` — `IsCoprime a b` on minimal counterexample.
- `Fermat42Sub.mul` — scaling bijection for coprimality reduction.

**Why second, not first.** This is predicate infrastructure; it has no standalone mathematical punchline until PR C assembles the impossibility.  Submitting the predicate alone invites a reasonable "why?" from reviewers.  Better: submit after PR A establishes the parallel structure for the sum form is welcome.

**Scope.** One file at `Mathlib/NumberTheory/FLT/FourSub.lean` (short — the predicate infrastructure only, not the full descent).  Estimated 150–250 lines.

## PR C — The assembled difference form

**Mathematical content.** `not_fermat_42_sub : ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 4 - b ^ 4 ≠ c ^ 2`.  Case A (b odd) reduces via Pythagorean classification to `2·a² = s⁴ + t⁴` and invokes PR A's `fermat42Double_impossible`.  Case B (b even) reduces directly to a strictly smaller `Fermat42Sub` and invokes PR B's `exists_minimal` for the descent.

**Dependencies.** PR A merged; PR B merged.

**Scope.** Additions to the `Mathlib.NumberTheory.FLT.FourSub` module from PR B, or a separate `Mathlib.NumberTheory.FLT.FourSubAssembly` module if the maintainers prefer.  Estimated 400–600 lines.

**Open question for reviewer.** Is the difference form `a⁴ - b⁴ ≠ c²` sufficiently important as a named mathlib theorem to warrant 400+ lines, or should it stay in the Principia Fractalis companion corpus and be cited from there?  This is the exact question `@wwylele` raised and `@vihdzp` answered dismissively.  Resolve via Zulip before preparing the PR.

## Housekeeping items from the PR #46025 review

- **Title capitalisation.**  Future PR titles start lowercase: `feat(NumberTheory/FLT): fermat right triangle theorem`.
- **Author attribution.**  Every commit on the follow-up series states AI-assistance up front.  No surprises.
- **Zulip engagement.**  Reply to the "Fermat right triangle theorem" thread before opening PR A, asking directly for placement guidance.  The question is `Mathlib/NumberTheory/FLT/Four.lean` vs. a new `FourDouble.lean` vs. not-in-mathlib.
- **Line-count discipline.**  PR-wide hard cap: no PR over 1000 lines.  If a descent naturally exceeds this, split by semantic section (parity reasoning / UFD splits / quadruple extraction / descent step / strong-induction wrapper) into sequential PRs.

## What this plan does NOT do

- It does NOT re-prove the mathematics from scratch.  The current `Fermat42SubAssembly_2026_11_14.lean` and `Fermat42DoubleImpossible_2026_11_13.lean` files in `PF_Lean4_Code/PF/` contain the proof content.  The follow-up PRs restructure the presentation; the mathematical core stays the same.
- It does NOT auto-submit anything.  Submission is the user's manual action per the existing `mathlib_submission/submit_pr.sh` convention.
- It does NOT argue with `@vihdzp`.  The one-sentence dismissal has been acknowledged in the reply comment; no further engagement is useful.

## Order of execution

1. User decides: proceed with this plan, or alternative.
2. If proceeding: user replies to the Zulip thread asking for placement guidance (PR A specifically).
3. Depending on Zulip response: either prepare PR A at the suggested location, or close out the mathlib-upstream path and keep the content in PF-local.
4. If PR A merges: prepare PR B.
5. If PR B merges: prepare PR C.
6. If PR A is rejected at the Zulip placement step: the series ends; content stays PF-local.

## HEAD at write time

Local: `bc9b8717` on `origin/master`.
Mathlib fork: `pc/not-fermat-42-sub` branch still exists at `82003dccd9`; can be deleted or kept as historical record.
PR #46025: CLOSED 2026-11-15 06:27 UTC.
