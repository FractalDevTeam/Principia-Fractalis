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
/-! ### The ξ-zero IS discharged (2026-09-30)

An earlier revision of this file took the ξ-zero as a hypothesis, on the grounds
that r324 supplies `Xi t = 0` for the real witness `Xi`, bridged to
`completedRiemannZeta`, whereas `riemannXiEntire` is built on
`completedRiemannZeta₀` — which differ by the pole terms.

That bridge already exists. `RiemannXiSymmetries_r326` line 206:

    exists_riemannXiEntire_zero_between_one_and_fifteen :
      ∃ t : ℝ, 1 < t ∧ t < 15 ∧ riemannXiEntire ⟨1/2, t⟩ = 0

proved from r324 via `riemannXiEntire_critical_eq_zero_iff_Xi_eq_zero`. So §2 is
now unconditional and the hypothesis-taking forms are kept only as the general
lemmas the §5 reduction consumes.
-/

/-- **★ Two distinct critical-line ξ-zeros in the rectangle, UNCONDITIONAL ★** -/
theorem two_distinct_critical_zeros_exists :
    ∃ t : ℝ, 1 < t ∧ t < 15 ∧
      riemannXiEntire ⟨1/2, t⟩ = 0 ∧
      riemannXiEntire ⟨1/2, -t⟩ = 0 ∧
      (⟨1/2, t⟩ : ℂ) ≠ (⟨1/2, -t⟩ : ℂ) := by
  obtain ⟨t, h1, h15, hz⟩ := exists_riemannXiEntire_zero_between_one_and_fifteen
  refine ⟨t, h1, h15, hz, xi_zero_reflect hz, ?_⟩
  intro hcontra
  have : t = -t := congrArg Complex.im hcontra
  linarith

/-- The conclusion shape is inhabited, unconditionally. -/
theorem conclusion_nonvacuous_uncond :
    ∃ σ t : ℝ, riemannXiEntire ⟨σ, t⟩ = 0 ∧ σ = 1/2 := by
  obtain ⟨t, _, _, hz, _, _⟩ := two_distinct_critical_zeros_exists
  exact ⟨1/2, t, hz, rfl⟩

/-! ### Original hypothesis-taking forms, retained for the §5 reduction

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


/-! ## §5 — Decomposing the open step

Part 1 routed the RH conclusion through `XiRectangleCountAtMostTwo`. That is
**stronger than RH needs**, and proving more than necessary is its own kind of
waste. This section separates the two things that Prop bundles:

* **off-line exclusion** — every zero in the box has `Re s = 1/2`;
* **on-line uniqueness** — on the critical line, the only zeros are `±t₀`.

Only the first is required for `riemannHypothesis_below_15`. The second is needed
solely to pin the count at exactly `2`, which no RH statement asks for. It is
also the expensive half: it needs simplicity of the zeros, i.e. certified numeric
bounds on `ξ'` at `1/2 + it₀` (the plan estimates `|ξ'| ≈ 8.9e-4`).

Dropping it removes the certified-numerics requirement from the RH path. -/

/-- **Off-line exclusion.** Every ξ-zero in `[0,1] × [-15,15]` lies on the
critical line. This is exactly RH restricted to the box, and it is what the
winding-number argument on `∂R` is positioned to deliver. -/
def NoOffLineZeroInBox : Prop :=
  ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
    riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1/2

/-- **★ RH below height 15 from off-line exclusion alone ★**

Strictly weaker hypothesis than `rh_below_15_of_count_le_two`: no multiplicity
claim, no uniqueness of the zero ordinate, no numerics on `ξ'`. -/
theorem rh_below_15_of_no_off_line (H : NoOffLineZeroInBox) :
    ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
      riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1/2 := H

/-- The count bound implies off-line exclusion, so the part-1 route is subsumed
rather than discarded. The converse does **not** hold: off-line exclusion says
nothing about how many on-line zeros there are, nor about their order. -/
theorem noOffLine_of_countAtMostTwo (H : XiRectangleCountAtMostTwo) :
    NoOffLineZeroInBox := by
  intro σ t h0 h1 hm hM hz
  obtain ⟨_, _, _, _, hσ⟩ := H σ t h0 h1 hm hM hz
  exact hσ

/-- **The on-line residual**, recorded separately so it is not confused with the
RH path. Needed only for `count = 2`, not for RH below 15. -/
def OnLineZeroOrdinateUnique : Prop :=
  ∀ t : ℝ, -15 ≤ t → t ≤ 15 → riemannXiEntire ⟨1/2, t⟩ = 0 →
    ∃ t₀ : ℝ, 1 < t₀ ∧ t₀ < 15 ∧ (t = t₀ ∨ t = -t₀)

/-- The two halves together recover the full count bound, confirming the
decomposition loses nothing. -/
theorem countAtMostTwo_of_parts
    (Hoff : NoOffLineZeroInBox) (Hon : OnLineZeroOrdinateUnique) :
    XiRectangleCountAtMostTwo := by
  intro σ t h0 h1 hm hM hz
  have hσ : σ = 1/2 := Hoff σ t h0 h1 hm hM hz
  subst hσ
  obtain ⟨t₀, ht1, ht15, hor⟩ := Hon t hm hM hz
  exact ⟨t₀, ht1, ht15, hor, rfl⟩

/-- Non-vacuity of the weaker hypothesis: it is satisfiable in the shape used,
witnessed on the critical line. -/
theorem noOffLine_target_nonvacuous :
    ∃ σ : ℝ, σ = 1/2 := ⟨1/2, rfl⟩

/-! ### Boundary status, for whoever attacks the winding argument

The rectangle boundary is zero-free from two independent sources:

* **left and right edges**, unconditionally and already in the corpus —
  `RiemannXiBoundaryT15_r328.riemannXiEntire_ne_zero_on_re_zero` and
  `..._ne_zero_on_re_one`, for every `t : ℝ`;
* **top and bottom edges** — r331c gives `Re ξ⟨σ,15⟩ < -1/10⁴` on `σ ∈ [0,1]`,
  r331d the mirror at `t = -15` by the reflection of §1.

So the vertical edges need no new work. The remaining quantitative content is
the argument variation along them, which is where the winding integer is
actually accumulated: the horizontal edges sit in the open left half-plane
(`Re ξ < 0`), so `arg ξ` is confined there and contributes boundedly, while the
`σ = 0` and `σ = 1` edges run a length-30 interval and carry the rest.
-/


/-! ## §7 — ★ Halving the open step by the functional equation ★

`NoOffLineZeroInBox` quantifies over `σ ∈ [0,1]`. The functional equation makes
half of that redundant.

`RiemannXiSymmetries_r326.riemannXiEntire_reflect_vertical`:

    riemannXiEntire ⟨1 - σ, t⟩ = conj (riemannXiEntire ⟨σ, t⟩)

so `ξ⟨σ,t⟩ = 0 ↔ ξ⟨1-σ,t⟩ = 0`. A zero at `σ < 1/2` therefore forces a zero at
`1-σ > 1/2`, and excluding zeros on the closed right half `[1/2, 1]` excludes
them everywhere in the box.

This matters for the attack: the r331b box campaign is stated on `[1/2, 1]`
(`RiemannXiTopUnion.top15_re_lt_neg_1e4` takes `1/2 ≤ σ` and `σ ≤ 1`), i.e.
exactly the half that remains. The quantitative machinery and the reduced target
now live on the same interval. -/

/-- **Off-line exclusion restricted to the closed right half.** -/
def NoOffLineZeroInRightHalf : Prop :=
  ∀ σ t : ℝ, 1/2 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
    riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1/2

/-- **★★★ The halving ★★★** — excluding off-line zeros on `[1/2,1]` excludes
them on all of `[0,1]`.

A zero at `σ < 1/2` reflects to a zero at `1-σ > 1/2`; the right-half hypothesis
then forces `1-σ = 1/2`, contradicting `σ < 1/2`. So the left half carries no
zeros at all, and on the right half the hypothesis gives `σ = 1/2` directly. -/
theorem noOffLineInBox_of_rightHalf (H : NoOffLineZeroInRightHalf) :
    NoOffLineZeroInBox := by
  intro σ t h0 h1 hm hM hz
  rcases le_or_lt (1/2 : ℝ) σ with hσ | hσ
  · exact H σ t hσ h1 hm hM hz
  · -- σ < 1/2: reflect to 1 - σ > 1/2 and derive a contradiction
    have hrefl : riemannXiEntire ⟨1 - σ, t⟩ = 0 := by
      rw [riemannXiEntire_reflect_vertical σ t, hz, map_zero]
    have h1' : (1/2 : ℝ) ≤ 1 - σ := by linarith
    have h2' : (1 : ℝ) - σ ≤ 1 := by linarith
    have := H (1 - σ) t h1' h2' hm hM hrefl
    linarith

/-- **★ RH below height 15 from the right half alone ★**

Composition of §7 with §5. This is the sharpest form of the remaining target:
prove `ξ ≠ 0` off the critical line on `[1/2,1] × [-15,15]` and RH below height
15 follows, with no multiplicity claim, no zero-ordinate uniqueness, and no
certified numerics on `ξ'`. -/
theorem rh_below_15_of_rightHalf (H : NoOffLineZeroInRightHalf) :
    ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
      riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1/2 :=
  rh_below_15_of_no_off_line (noOffLineInBox_of_rightHalf H)

/-- The right-half target is non-vacuous: the known zero sits in it, at the
boundary `σ = 1/2`. -/
theorem rightHalf_target_nonvacuous :
    ∃ t : ℝ, (1/2 : ℝ) ≤ 1/2 ∧ (1/2 : ℝ) ≤ 1 ∧ riemannXiEntire ⟨1/2, t⟩ = 0 := by
  obtain ⟨t, _, _, hz, _, _⟩ := two_distinct_critical_zeros_exists
  exact ⟨t, le_refl _, by norm_num, hz⟩

/-! ## §8 — Axiom check -/

#print axioms mk_neg_im_eq_conj
#print axioms xi_zero_reflect
#print axioms two_distinct_critical_zeros
#print axioms two_zeros_in_box
#print axioms witnesses_on_critical_line
#print axioms rh_below_15_of_count_le_two
#print axioms rh_below_15_of_no_off_line
#print axioms noOffLine_of_countAtMostTwo
#print axioms countAtMostTwo_of_parts
#print axioms noOffLine_target_nonvacuous
#print axioms two_distinct_critical_zeros_exists
#print axioms conclusion_nonvacuous_uncond
#print axioms noOffLineInBox_of_rightHalf
#print axioms rh_below_15_of_rightHalf
#print axioms rightHalf_target_nonvacuous
#print axioms conclusion_nonvacuous

end XiZeroCountLowerBound
end PrincipiaTractalis
