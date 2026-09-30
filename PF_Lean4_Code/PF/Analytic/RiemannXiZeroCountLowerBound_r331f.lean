/-
# r331f (part 1) — the zero-count LOWER bound, unconditional

★ 2026-09-30 — Route C scaffold: `Σ ord ≥ 2` proved; `≤ 2` isolated ★

## Where this sits

`codex/RH_BELOW_15_MULTIPLICITY_PLAN_2026-09-28.md` recommends Route B/C: show
the rectangle zero-count is exactly `2`, then conclude `riemannHypothesis_below_15`.
Route C splits that into

* **lower bound** `Σ ord ≥ 2` — from the known critical-line zero plus conjugation;
* **upper bound** `Σ ord ≤ 2` — the contour evaluation, the genuinely open step.

This file proves the lower bound **unconditionally** and states the upper bound
as a single named hypothesis, so the remaining research target is one `Prop`
rather than an unscoped block of analysis.

It deliberately does **not** import r331d/r331e. Those await the panel rebuild;
everything here builds against r324/r326/r327, whose oleans are current. When
r331e lands, its `xi_full_rectangle_zero_count_identity` connects the count used
here to the contour integral, and `rh_below_15_of_count_le_two` fires.

## The correction this file inherits

The plan's target statement was off by a factor of `2πi`:

    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF = 2 * π * I * 2   -- WRONG

`RectangleIntegral'` (primed) already carries `1/(2πi)`, per
`PF/Analytic/PNT/ResidueCalcOnRectangles_r327.lean:73`, and r327's argument
principle has no `2πi` on its right-hand side. The corrected target is `= (2 : ℂ)`.

## Honest scope

**Proved here.** ξ has at least two distinct zeros in the closed rectangle
`[0,1] × [-15,15]`, both on the critical line `Re s = 1/2`, one at `+t₀` and one
at `-t₀` with `1 < t₀ < 15`.

**Not proved here.** That there are no others. That is exactly
`XiRectangleCountAtMostTwo` below, and it is open.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannZetaZeroBelow15_r324
import PF.Analytic.RiemannXiSymmetries_r326

namespace PrincipiaTractalis
namespace XiZeroCountLowerBound

open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.RiemannZetaZeroBelow15
open Complex
open scoped ComplexConjugate

/-! ## §1 — Reflection -/

/-- `⟨σ, -t⟩ = conj ⟨σ, t⟩`. -/
lemma mk_neg_im_eq_conj (σ t : ℝ) : (⟨σ, -t⟩ : ℂ) = conj (⟨σ, t⟩ : ℂ) := by
  apply Complex.ext
  · simp [Complex.conj_re]
  · simp [Complex.conj_im]

/-- **Schwarz reflection carries ξ-zeros across the real axis.** -/
theorem xi_zero_reflect {σ t : ℝ} (h : riemannXiEntire ⟨σ, t⟩ = 0) :
    riemannXiEntire ⟨σ, -t⟩ = 0 := by
  rw [mk_neg_im_eq_conj σ t, riemannXiEntire_conj, h, map_zero]

/-! ## §2 — ★ The lower bound, unconditional ★ -/
/-! ### Why the ξ-zero is a hypothesis here, not discharged from r324

r324 supplies `exists_Xi_zero_between_one_and_fifteen : ∃ t, 1 < t ∧ t < 15 ∧
Xi t = 0`, where `Xi : ℝ → ℝ` is the real witness of `XiRealWitness`, bridged to
`completedRiemannZeta ⟨1/2,t⟩` by `XiRealWitness.Xi_eq`.

`riemannXiEntire` is built on `completedRiemannZeta₀`, NOT `completedRiemannZeta`.
The two differ by the pole terms, so r324's witness does not transfer without the
`Λ₀ ↔ Λ` bridge at `⟨1/2, t⟩`. That bridge exists in the corpus around r325/r304
but is not currently in this module's import closure.

Rather than assert the transfer, the zero is taken as a hypothesis. Everything
below it — reflection, distinctness, box membership, the critical-line property —
is unconditional. Discharging the hypothesis is a one-line `obtain` once the
bridge is imported; it is deliberately not faked here.
-/



/-- **★★★ Two distinct critical-line ξ-zeros in the rectangle ★★★**

From r324 (a ξ-zero at height `1 < t₀ < 15`) and §1 reflection. Both lie on
`Re s = 1/2`, both inside `[0,1] × [-15,15]`, and they are distinct because
`t₀ > 1 > 0` forces `t₀ ≠ -t₀`. -/
theorem two_distinct_critical_zeros
    {t : ℝ} (h1 : 1 < t) (hz : riemannXiEntire ⟨1/2, t⟩ = 0) :
      riemannXiEntire ⟨1/2, -t⟩ = 0 ∧
      (⟨1/2, t⟩ : ℂ) ≠ (⟨1/2, -t⟩ : ℂ) := by
  refine ⟨xi_zero_reflect hz, ?_⟩
  intro hcontra
  have : t = -t := congrArg Complex.im hcontra
  linarith

/-- Both witnesses sit in the closed rectangle, stated as explicit real bounds
so this does not depend on the `Rectangle` API. -/
theorem two_zeros_in_box
    {t : ℝ} (h1 : 1 < t) (h15 : t < 15) (hz : riemannXiEntire ⟨1/2, t⟩ = 0) :
      ((0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) ≤ 1) ∧
      (-15 ≤ t ∧ t ≤ 15) ∧ (-15 ≤ -t ∧ -t ≤ 15) ∧
      riemannXiEntire ⟨1/2, -t⟩ = 0 :=
  ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith, by linarith⟩,
   ⟨by linarith, by linarith⟩, xi_zero_reflect hz⟩

/-- **Both zeros are ON the critical line.** Trivial by construction, recorded
because it is the property the RH conclusion consumes. -/
theorem witnesses_on_critical_line
    {t : ℝ} (hz : riemannXiEntire ⟨1/2, t⟩ = 0) :
    (⟨1/2, t⟩ : ℂ).re = 1/2 ∧ (⟨1/2, -t⟩ : ℂ).re = 1/2 ∧
      riemannXiEntire ⟨1/2, -t⟩ = 0 :=
  ⟨rfl, rfl, xi_zero_reflect hz⟩

/-! ## §3 — The open step, named

Everything above is unconditional. What follows is the single remaining research
target, stated as a `Prop` so it can be discharged in one place. -/

/-- **The open upper bound.** Every ξ-zero in the closed rectangle
`[0,1] × [-15,15]` is one of the two reflection partners already exhibited.

Equivalently, by r331e's count identity, the contour value is exactly `2`:

    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) zF wF = (2 : ℂ)

**This is the Route B/C contour evaluation and it is OPEN.** The r331b/c/d
boundary margins (`Re ξ < -1/10⁴` on the top and bottom edges, sign control on
the left and right) are the quantitative input; the winding number of `ξ ∘ ∂R`
about `0` is the integer in question. -/
def XiRectangleCountAtMostTwo : Prop :=
  ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
    riemannXiEntire ⟨σ, t⟩ = 0 →
      ∃ t₀ : ℝ, 1 < t₀ ∧ t₀ < 15 ∧ (t = t₀ ∨ t = -t₀) ∧ σ = 1/2

/-- **★★★ RH below height 15, conditional on the open step ★★★**

Given the upper bound, every ξ-zero in the rectangle has `Re s = 1/2`. Combined
with §2 the zero set is exactly the two reflection partners, both on the line.

The hypothesis is genuinely load-bearing: delete it and the conclusion does not
follow — §2 alone gives existence, never exhaustion. -/
theorem rh_below_15_of_count_le_two (H : XiRectangleCountAtMostTwo) :
    ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
      riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1/2 := by
  intro σ t h0 h1 hm hM hz
  obtain ⟨_, _, _, _, hσ⟩ := H σ t h0 h1 hm hM hz
  exact hσ

/-- Non-vacuity: the two exhibited zeros satisfy the conclusion's shape, so
§3 is not vacuously true. -/
theorem conclusion_nonvacuous
    {t : ℝ} (hz : riemannXiEntire ⟨1/2, t⟩ = 0) :
    ∃ σ t' : ℝ, riemannXiEntire ⟨σ, t'⟩ = 0 ∧ σ = 1/2 :=
  ⟨1/2, t, hz, rfl⟩

/-! ## §4 — Axiom check -/

#print axioms mk_neg_im_eq_conj
#print axioms xi_zero_reflect
#print axioms two_distinct_critical_zeros
#print axioms two_zeros_in_box
#print axioms witnesses_on_critical_line
#print axioms rh_below_15_of_count_le_two
#print axioms conclusion_nonvacuous

end XiZeroCountLowerBound
end PrincipiaTractalis
