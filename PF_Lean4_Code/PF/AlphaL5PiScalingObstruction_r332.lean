/-
# r332 — L5 SETTLED: the π-scaling law is not reachable from the substrate's trace range

★ NEGATIVE / STRUCTURAL RESULT 2026-09-07 ★

`AlphaSkeletonUniqueness_r128` pins the nine-tuple from eight structural laws.
The 2026-08-24 provenance audit
(`codex/ALPHA_SKELETON_STRUCTURAL_LAW_PROVENANCE_2026-08-24.md`) classified all
eight and found **none** of provenance class A (intrinsic PF theorem). Seven are
definitional or trivial arithmetic on chosen numerals. One is different:

    L5   α_NS = α_RH · π        ("the π-scaling law")

L5 is the **only** law whose motivating gloss has no formal counterpart anywhere
in the corpus, and it is the exact equation that closes the free parameter that
`AlphaWebDegreesOfFreedom_r124` located by Gröbner elimination: without L5 the
eleven-invariant system is a one-parameter family, not a point.

The provenance audit named the deciding test and, by directive, stopped without
running it. `codex/ALPHA_RIGIDITY_AUDIT_CHARTER_2026-09-01.md` independently
reached the same target, flagging L5 as **H3, "the audit's central
adjudication"**. This module runs that test.

## The test

    ∀ a b : ℝ, MemZ13 a → MemZ13 b → a ≠ 0 → b / a ≠ π

`MemZ13` (r123) is membership in `ℤ[1/3]`, which is exactly the range of the
substrate's unique trace on `K₀(T∞)` — the substrate's complete classifying
invariant, carried onto `ℤ[1/3] ⊂ ℝ` isomorphically (Glimm/Elliott). If π is not
a ratio of two trace-range quantities, then no route that reaches the α-values
through the substrate's K-theory can ever produce L5's multiplicative π.

## Verdict: PROVABLE. L5 is not reachable by that route.

`pi_not_ktheoretic_ratio` below. The proof is short because the obstruction is
coarse: `ℤ[1/3] ⊆ ℚ` (r123 `memZ13_isRat`), so any ratio of its nonzero elements
is rational, and π is not (mathlib `irrational_pi`).

This is the L5 half of the r113/r123 trace-range obstruction (charter N2: the
substrate's trace range is `ℤ[1/3]`, and seven of nine α-values lie outside it).
r123 showed the α-*values* are unreachable. r332 shows the *ratio* L5 needs is
unreachable too — so the gap cannot be closed by relating two α's instead of
deriving each one.

## Consequence for the framework

L5 has no intrinsic derivation available through the substrate's K-theory. Since
L5 is what makes the α-skeleton rigid, **the nine α-values are not derived
constants** on this route, and the corpus should not describe them as such.
r124's one-parameter family stands as the honest picture.

## Scope — stated precisely, and narrowly

This settles L5 **against the K-theoretic trace route**, which is the route the
corpus actually has (r113, r123). It does NOT prove that L5 is underivable from
every conceivable substrate structure: a future object whose invariant range is
not confined to `ℤ[1/3]` is not addressed here. What is closed is the route on
the table.

Per the charter §8: no outcome of this line bears on any Clay problem, and none
revives the N2/N3/N4 routes.

## Status

Axiom-free beyond the mathlib three. No `sorry`. `#print axioms` at the end.

SPDX-License-Identifier: Apache-2.0
-/

import PF.AlphaFromSubstrateKTheory_r123
import Mathlib.Analysis.Real.Pi.Irrational

namespace PrincipiaTractalis
namespace AlphaL5PiScalingObstruction

open PrincipiaTractalis.AlphaFromSubstrateKTheory
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open scoped Real

/-! ## §1 — The obstruction -/

/-- **★★★ r332.A — π IS NOT A RATIO OF SUBSTRATE TRACE-RANGE QUANTITIES ★★★**

    For all `a b ∈ ℤ[1/3]` with `a ≠ 0`, `b / a ≠ π`.

    `ℤ[1/3]` is the range of the substrate's unique trace on `K₀(T∞)`. The
    quotient of two of its elements is rational; π is not. -/
theorem pi_not_ktheoretic_ratio
    {a b : ℝ} (ha : MemZ13 a) (hb : MemZ13 b) (h0 : a ≠ 0) :
    b / a ≠ Real.pi := by
  intro hEq
  obtain ⟨qa, hqa⟩ := memZ13_isRat ha
  obtain ⟨qb, hqb⟩ := memZ13_isRat hb
  exact irrational_pi ⟨qb / qa, by rw [Rat.cast_div, hqa, hqb]; exact hEq⟩

/-- **r332.B — the same statement in the provenance audit's exact wording.**

    This is the theorem
    `codex/ALPHA_SKELETON_STRUCTURAL_LAW_PROVENANCE_2026-08-24.md` recommended
    and declined to implement without authorization. -/
theorem l5_not_derivable_from_ktheoretic_ratio :
    ∀ (a b : ℝ), MemZ13 a → MemZ13 b → a ≠ 0 → b / a ≠ Real.pi :=
  fun _ _ ha hb h0 => pi_not_ktheoretic_ratio ha hb h0

/-! ## §2 — What this closes for L5 -/

/-- **r332.C — L5's π factor is not substrate-reachable.**

    L5 asserts `α_NS = α_RH · π`, i.e. `α_NS / α_RH = π` (α_RH ≠ 0). Whatever
    substrate quantities a derivation might use, if they are trace-range
    quantities then their ratio is never π. Stated contrapositively: any pair
    witnessing L5's π as a ratio must have a member outside `ℤ[1/3]`, so it is
    not supplied by the substrate's classifying invariant. -/
theorem l5_pi_factor_not_from_trace_range
    {a b : ℝ} (ha : MemZ13 a) (hb : MemZ13 b) (h0 : a ≠ 0)
    (hL5 : b / a = α_NS / α_RH) : α_NS / α_RH ≠ Real.pi := by
  intro hpi
  exact pi_not_ktheoretic_ratio ha hb h0 (hL5.trans hpi)

/-- **r332.D — the α-table's own π-ratio is exactly L5.**

    `α_NS / α_RH = π` holds numerically, by unfolding the two definitions
    (`α_NS := 3π/2`, `α_RH := 3/2`). Together with r332.A this is the whole
    finding: the identity is *true of the chosen numerals* and *unreachable*
    from the substrate's invariant. That is what "target-encoded" means. -/
theorem alpha_ns_div_alpha_rh_eq_pi : α_NS / α_RH = Real.pi := by
  unfold α_NS α_RH
  ring

/-! ## §3 — Non-vacuity, and a note on the `a ≠ 0` hypothesis -/

/-- **r332.E — r332.A is NOT vacuous: its hypotheses are satisfiable.**

    A theorem whose hypotheses cannot be met says nothing. `MemZ13` is
    inhabited — `1` and `2` are in the substrate's trace range (r123
    `memZ13_one`, `memZ13_two`, and indeed they are the only two α-values that
    are) — and the conclusion is a real constraint on that inhabited set. -/
theorem r332_hypotheses_satisfiable :
    MemZ13 (1 : ℝ) ∧ MemZ13 (2 : ℝ) ∧ (1 : ℝ) ≠ 0 ∧ (2 : ℝ) / 1 ≠ Real.pi := by
  refine ⟨memZ13_one, memZ13_two, one_ne_zero, ?_⟩
  simpa using pi_not_ktheoretic_ratio memZ13_one memZ13_two one_ne_zero

/-- **r332.F — the `a ≠ 0` hypothesis is not needed.**

    The audit's recommended wording carried `a ≠ 0`; it is decorative. In Lean
    `b / 0 = 0`, and `0 ≠ π`, so the obstruction holds on all of `ℤ[1/3]`
    without exception. Recorded because a hypothesis that does no work should
    be known not to be doing any — an unused premise can otherwise be mistaken
    for the thing that makes a statement true. -/
theorem pi_not_ktheoretic_ratio_unrestricted
    {a b : ℝ} (ha : MemZ13 a) (hb : MemZ13 b) :
    b / a ≠ Real.pi := by
  intro hEq
  obtain ⟨qa, hqa⟩ := memZ13_isRat ha
  obtain ⟨qb, hqb⟩ := memZ13_isRat hb
  exact irrational_pi ⟨qb / qa, by rw [Rat.cast_div, hqa, hqb]; exact hEq⟩

/-! ## §4 — Axiom check -/

#print axioms pi_not_ktheoretic_ratio
#print axioms l5_not_derivable_from_ktheoretic_ratio
#print axioms l5_pi_factor_not_from_trace_range
#print axioms alpha_ns_div_alpha_rh_eq_pi
#print axioms r332_hypotheses_satisfiable
#print axioms pi_not_ktheoretic_ratio_unrestricted

end AlphaL5PiScalingObstruction
end PrincipiaTractalis
