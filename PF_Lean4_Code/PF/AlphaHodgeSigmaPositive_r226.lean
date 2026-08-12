/-
# r226: α_Hodge = φ pillar — σ(α_Hodge) > 0 (envelope-growing tier).

★ 2026-08-12 r226 — elevating the Hodge pillar (α_Hodge = φ, golden ratio)
via the sharp SIGN characterisation `σ(α_Hodge) > 0`. Companion to r225
(α_P, σ < 0). Together with r221 (σ = 0: Poincaré, RH) and r224 (σ = 1: YM),
this gives FOUR of the corpus σ-sign classes explicitly formalised:

    σ = 0       α_Poincaré, α_RH        (r221 constant-amplitude tier)
    σ = 1       α_YM                     (r224 linear-growth tier)
    σ < 0       α_P                      (r225 envelope-decaying tier)
    σ > 0       α_Hodge (THIS FILE)      (envelope-growing, sub-linear tier)

The remaining irrational pillars (α_NP, α_BSD, α_QG, α_NS) have their
sign classification pending — their proofs follow the same six-step
template as r225 and r226, with different bracketing on their α values.

## What this file proves

The substrate reading at α_Hodge = φ (golden ratio):

1. `2 < √5 < 3` — elementary square comparison.
2. `3/2 < φ < 2` — via `φ = (1 + √5) / 2`.
3. `3π/2 < π · φ < 2π` — multiply by `π > 0`.
4. Let `y := 2π - π · φ`. Then `y ∈ (0, π/2)`.
5. `cos(π · φ) = cos(y)` via `cos(2π - y) = cos(y)` (2π periodicity + evenness).
6. `cos(π · φ) > 0` via `Real.cos_pos_of_mem_Ioo` on `(-π/2, π/2)` with `y ∈ (0, π/2)`.
7. `1 + 2 · cos(π · φ) > 1`.
8. **`σ(α_Hodge) > 0`** via `Real.logb_pos` on values > 1.
9. Elevated to r223: `SO_αHodge_sigma_pos` universal over data-fit.

The Hodge substrate observable therefore has envelope `a^σ` with σ > 0 —
amplitude GROWS toward the past (a → 0), but SUB-LINEARLY (σ < 1, since
`|1 + 2·cos(π·φ)| < 3` — the r224 upper bound at cos = 1). The corpus
value σ(φ) ≈ 0.496 places the growth exponent near `√a`, but formalising
that sharp bracket is future work (r212's `sigma_goldenRatio_ne_half`
already excludes exact `σ = 1/2`).

## Consistency with r212's guard rail

r212's `sigma_goldenRatio_ne_half : sigma φ ≠ 1/2` is COMPATIBLE with
r226's `σ(φ) > 0`. Both hold:
- σ(φ) > 0 (r226)
- σ(φ) ≠ 1/2 (r212)
- σ(φ) ≠ 0 and σ(φ) ≠ 1 (r212's `sigma_alphaHodge_ne_zero_one`)

Combined: σ(φ) ∈ (0, 1/2) ∪ (1/2, 1). Sharper bracket (numeric enclosure)
would decide which side of 1/2 — that is future substrate work.

## Contents

§1 `√5` brackets: `2 < √5 < 3`.
§2 `φ` brackets: `3/2 < φ < 2`.
§3 π · φ interval: `3π/2 < π · φ < 2π`.
§4 Local: `cos(x + 2π) = cos(x)` (2π periodicity via two `cos_add_pi`).
§5 `cos(π · φ) > 0` via §3 + §4.
§6 `1 < 1 + 2·cos(π · φ)` (positivity of chi-norm > 1).
§7 **`sigma_alphaHodge_gt_zero`** — the named stone.
§8 Elevated to r223: `SO_αHodge_sigma_pos`.
§9 Axiom check.

## Scope

* NOT a Hodge conjecture discharge.
* NOT a substrate derivation of `α_Hodge = φ`.
* NOT a physical claim about Hodge classes or algebraic cycles.
* IS the sharp SIGN characterisation of σ at the Hodge pillar. IS a
  substrate consequence: envelope-growing observable for α_Hodge.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.SubstrateOscillator_r223

open scoped Real

namespace PrincipiaTractalis.AlphaHodgeSigmaPositive

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 `√5` brackets. -/

lemma two_lt_sqrt_five : (2 : ℝ) < Real.sqrt 5 := by
  have h : Real.sqrt 4 < Real.sqrt 5 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
  linarith

lemma sqrt_five_lt_three : Real.sqrt 5 < 3 := by
  have h : Real.sqrt 5 < Real.sqrt 9 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)
  linarith

/-! ## §2 Golden ratio brackets. -/

lemma three_halves_lt_goldenRatio : (3 : ℝ) / 2 < Real.goldenRatio := by
  unfold Real.goldenRatio
  have := two_lt_sqrt_five
  linarith

lemma goldenRatio_lt_two : Real.goldenRatio < 2 := by
  unfold Real.goldenRatio
  have := sqrt_five_lt_three
  linarith

/-! ## §3 The `π · φ` interval. -/

lemma three_pi_div_two_lt_pi_mul_goldenRatio :
    3 * π / 2 < π * Real.goldenRatio := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := three_halves_lt_goldenRatio
  nlinarith

lemma pi_mul_goldenRatio_lt_two_pi : π * Real.goldenRatio < 2 * π := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := goldenRatio_lt_two
  nlinarith

/-! ## §4 Local: `cos(x + 2π) = cos(x)`. -/

/-- **2π periodicity of cos.**  Derived from two applications of `cos_add_pi`. -/
lemma cos_add_two_pi (x : ℝ) : Real.cos (x + 2 * π) = Real.cos x := by
  have h : x + 2 * π = (x + π) + π := by ring
  rw [h, Real.cos_add_pi, Real.cos_add_pi]
  ring

/-! ## §5 `cos(π · φ) > 0`. -/

/-- **`cos(π · φ) > 0`.**  Since `π · φ ∈ (3π/2, 2π)`, set `y := 2π - π·φ`
so `y ∈ (0, π/2)`. Then `cos(π · φ) = cos(2π - y) = cos(-y + 2π) = cos(-y)
= cos(y)`, and `cos(y) > 0` for `y ∈ (0, π/2)`. -/
lemma cos_pi_mul_goldenRatio_pos : 0 < Real.cos (π * Real.goldenRatio) := by
  set y := 2 * π - π * Real.goldenRatio with hy_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hy_pos : 0 < y := by
    rw [hy_def]; linarith [pi_mul_goldenRatio_lt_two_pi]
  have hy_lt_pi_div_two : y < π / 2 := by
    rw [hy_def]; linarith [three_pi_div_two_lt_pi_mul_goldenRatio]
  have hy_gt_neg : -(π / 2) < y := by linarith
  have heq : π * Real.goldenRatio = -y + 2 * π := by rw [hy_def]; ring
  rw [heq, cos_add_two_pi, Real.cos_neg]
  exact Real.cos_pos_of_mem_Ioo ⟨hy_gt_neg, hy_lt_pi_div_two⟩

/-! ## §6 `1 < 1 + 2 · cos(π · φ)`. -/

/-- Chi-norm at α_Hodge exceeds 1. -/
lemma one_lt_one_add_two_cos_pi_mul_goldenRatio :
    1 < 1 + 2 * Real.cos (π * Real.goldenRatio) := by
  linarith [cos_pi_mul_goldenRatio_pos]

/-- The absolute value: `|1 + 2·cos(π·φ)| > 1`. -/
lemma abs_one_add_two_cos_pi_mul_goldenRatio_gt_one :
    1 < |1 + 2 * Real.cos (π * Real.goldenRatio)| := by
  have h := one_lt_one_add_two_cos_pi_mul_goldenRatio
  rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + 2 * Real.cos (π * Real.goldenRatio))]
  exact h

/-! ## §7 The named stone — `σ(α_Hodge) > 0`. -/

/-- **`sigma_alphaHodge_gt_zero`** — the substrate sign at the Hodge pillar.

`σ(α_Hodge) > 0` where α_Hodge = φ.  Consequence: the substrate observable
at α_Hodge has envelope `a^σ` with σ > 0 — amplitude GROWS toward the past
(a → 0), sub-linearly (σ < 1, from `|1 + 2·cos(πφ)| ≤ 3` at cos = 1, and
r212's `sigma_alphaHodge_ne_zero_one` excludes the σ = 1 boundary).

r212's `sigma_goldenRatio_ne_half` further constrains: σ(φ) ≠ 1/2. So
σ(φ) ∈ (0, 1/2) ∪ (1/2, 1). Sharp decision between the two intervals is
future substrate work. -/
theorem sigma_alphaHodge_gt_zero :
    0 < PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 3)
  exact abs_one_add_two_cos_pi_mul_goldenRatio_gt_one

/-! ## §8 Elevated to r223's `SubstrateOscillator`. -/

/-- **`SO_αHodge_sigma_pos`** — the r223 `SubstrateOscillator` method form.

For every data-fit `A ≠ 0` and every `φ₀`, the α_Hodge substrate oscillator
has `sigma > 0`.  Universal over the two data-fit parameters — the sign is
pillar-intrinsic, not tuning-dependent. Companion to r225's
`SO_αP_sigma_neg` on the opposite side of zero. -/
theorem SO_αHodge_sigma_pos (A φ₀ : ℝ) (hA : A ≠ 0) :
    0 < (SO_αHodge A φ₀ hA).sigma := by
  show 0 < PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio
  exact sigma_alphaHodge_gt_zero

/-! ## §9 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.two_lt_sqrt_five
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.sqrt_five_lt_three
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.three_halves_lt_goldenRatio
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.goldenRatio_lt_two
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.three_pi_div_two_lt_pi_mul_goldenRatio
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.pi_mul_goldenRatio_lt_two_pi
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.cos_add_two_pi
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.cos_pi_mul_goldenRatio_pos
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.one_lt_one_add_two_cos_pi_mul_goldenRatio
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.abs_one_add_two_cos_pi_mul_goldenRatio_gt_one
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.sigma_alphaHodge_gt_zero
#print axioms PrincipiaTractalis.AlphaHodgeSigmaPositive.SO_αHodge_sigma_pos

end PrincipiaTractalis.AlphaHodgeSigmaPositive
