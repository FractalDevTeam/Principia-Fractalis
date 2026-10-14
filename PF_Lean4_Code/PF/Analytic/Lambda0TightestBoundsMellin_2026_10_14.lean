/-
# PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14

Tightening the Λ₀ and Λ₀' uniform bounds from `≤ 2/21` to **`≤ 1/33`** via
the same Mellin-of-theta substrate but with a sharper rational numerics step.

The analytic bound `‖Λ₀(1+it)‖ ≤ 2·exp(-π)/(π·(1-exp(-π)))` is already in
`Lambda0UniformBound_2026_10_14.lambda0_abs_uniform`. The rational step
there uses `exp(-π) ≤ 1/8, π ≥ 3` → `2/21`. Here we use:

  `exp(1) > 2.7182818284`  (mathlib's `Real.exp_one_gt_d9`)
  `exp(3) = exp(1)^3 > 20.08`  (cubing)
  `exp(π-3) ≥ 1 + (π-3) + (π-3)²/2`  (mathlib's `Real.quadratic_le_exp_of_nonneg`)
  `π > 3.141592`  (mathlib's `Real.pi_gt_3141592`)
  ⟹ `exp(π) > 20.08 · 1.1516 > 23`
  ⟹ `exp(-π) ≤ 1/23`
  ⟹ `2·(1/23)/(3·22/23) = 2/66 = 1/33`

**Pilot box ceiling under `‖Λ₀‖ ≤ 1/33`:** `(c² + c)·(1/33) ≤ 1/2` gives
`c ≤ (-1 + √67)/2 ≈ 3.59` — nearly 2× the `≈ 1.845` ceiling under `2/21`.
This unlocks pilot boxes centered at `c = 2, 5/2, 3, 7/2` and beyond.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.Lambda0UniformBound_2026_10_14
import PF.Analytic.Lambda0PrimeUniformBound_2026_10_14
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0TightestBoundsMellin20261014

open Complex Real MeasureTheory Set
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.Lambda0UniformBound20261014
open PrincipiaTractalis.Lambda0PrimeUniformBound20261014

noncomputable section

/-! ## §1 — Numerical lemma: `exp(π) ≥ 23`

The chain:
  `exp(1)^3 > 2.7182818284^3 > 20.083`
  `exp(π - 3) ≥ 1 + (π-3) + (π-3)²/2`
  `π > 3.141592`
  ⟹ `exp(π) ≥ 20.083 · 1.1516 > 23`
-/

lemma exp_three_gt_twenty : (20 : ℝ) < Real.exp 3 := by
  have h1 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    have h3 : (3 : ℝ) = 1 + 1 + 1 := by norm_num
    rw [h3, Real.exp_add, Real.exp_add]
  rw [h1]
  have h := Real.exp_one_gt_d9
  nlinarith [h, (Real.exp_pos 1).le]

lemma pi_sub_three_quadratic_le_exp :
    1 + (π - 3) + (π - 3) ^ 2 / 2 ≤ Real.exp (π - 3) := by
  apply Real.quadratic_le_exp_of_nonneg
  linarith [Real.pi_gt_three]

lemma exp_pi_gt_twentythree : (23 : ℝ) < Real.exp π := by
  have hπ_gt : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have hπ_sub_pos : (0 : ℝ) ≤ π - 3 := by linarith [Real.pi_gt_three]
  have hquad := pi_sub_three_quadratic_le_exp
  have h_quad_num : (1.1516 : ℝ) ≤ 1 + (π - 3) + (π - 3) ^ 2 / 2 := by
    nlinarith [hπ_gt, hπ_sub_pos]
  have h_quad : (1.1516 : ℝ) ≤ Real.exp (π - 3) := h_quad_num.trans hquad
  have h_exp3 := exp_three_gt_twenty
  have h_split : Real.exp π = Real.exp 3 * Real.exp (π - 3) := by
    rw [← Real.exp_add]
    congr 1; ring
  rw [h_split]
  have h_exp3_pos : (0 : ℝ) < Real.exp 3 := Real.exp_pos _
  have h_quad_nn : (0 : ℝ) ≤ Real.exp (π - 3) := (Real.exp_pos _).le
  nlinarith [h_exp3, h_quad, h_exp3_pos, h_quad_nn]

lemma exp_neg_pi_le_one_twentythird : Real.exp (-π) ≤ (1 : ℝ) / 23 := by
  rw [Real.exp_neg]
  rw [show (1 : ℝ) / 23 = (23 : ℝ)⁻¹ from by norm_num]
  exact inv_anti₀ (by norm_num : (0 : ℝ) < 23) exp_pi_gt_twentythree.le

lemma one_sub_exp_neg_pi_ge_twentytwo_twentythirds :
    (22 : ℝ) / 23 ≤ 1 - Real.exp (-π) := by
  have := exp_neg_pi_le_one_twentythird; linarith

/-! ## §2 — `‖Λ₀(1 + it)‖ ≤ 1/33` -/

theorem lambda0_abs_le_one_thirtythird (t : ℝ) :
    ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 1 / 33 := by
  refine (lambda0_abs_uniform t).trans ?_
  have hπ : (3 : ℝ) ≤ π := le_of_lt Real.pi_gt_three
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_exp := exp_neg_pi_le_one_twentythird
  have h_exp_pos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
  have h_1_sub : (22 : ℝ) / 23 ≤ 1 - Real.exp (-π) :=
    one_sub_exp_neg_pi_ge_twentytwo_twentythirds
  have h_1_sub_pos : (0 : ℝ) < 1 - Real.exp (-π) := by linarith
  have h_prod_pos : (0 : ℝ) < π * (1 - Real.exp (-π)) :=
    mul_pos hπ_pos h_1_sub_pos
  rw [div_le_iff₀ h_prod_pos]
  nlinarith [h_exp, h_exp_pos, hπ, hπ_pos, h_1_sub]

/-! ## §3 — `‖Λ₀(⟨σ, t⟩)‖ ≤ 1/33` on σ ∈ [0, 2] (strip version) -/

theorem lambda0_abs_le_one_thirtythird_strip
    {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)‖ ≤ 1 / 33 := by
  refine (lambda0_abs_uniform_strip hσ0 hσ2).trans ?_
  have hπ : (3 : ℝ) ≤ π := le_of_lt Real.pi_gt_three
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_exp := exp_neg_pi_le_one_twentythird
  have h_exp_pos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
  have h_1_sub : (22 : ℝ) / 23 ≤ 1 - Real.exp (-π) :=
    one_sub_exp_neg_pi_ge_twentytwo_twentythirds
  have h_1_sub_pos : (0 : ℝ) < 1 - Real.exp (-π) := by linarith
  have h_prod_pos : (0 : ℝ) < π * (1 - Real.exp (-π)) :=
    mul_pos hπ_pos h_1_sub_pos
  rw [div_le_iff₀ h_prod_pos]
  nlinarith [h_exp, h_exp_pos, hπ, hπ_pos, h_1_sub]

/-! ## §4 — `‖deriv Λ₀ (1 + it)‖ ≤ 1/33` (Cauchy, tightest) -/

theorem lambda0_prime_abs_le_one_thirtythird (t : ℝ) :
    ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 1 / 33 := by
  rw [show (1 / 33 : ℝ) = (1 / 33 : ℝ) / 1 from (div_one _).symm]
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos
  · apply Differentiable.diffContOnCl
    exact differentiable_completedZeta₀
  · intro z hz
    rw [Metric.mem_sphere] at hz
    have h_dist : |z.re - 1| ≤ 1 := by
      have h := abs_re_le_norm (z - (⟨1, t⟩ : ℂ))
      have h1 : (z - (⟨1, t⟩ : ℂ)).re = z.re - 1 := by simp [Complex.sub_re]
      rw [h1] at h
      rw [← dist_eq_norm] at h
      rw [hz] at h
      exact h
    have h_abs := abs_le.mp h_dist
    have hre0 : (0 : ℝ) ≤ z.re := by linarith
    have hre2 : z.re ≤ 2 := by linarith
    have hz_eq : z = (⟨z.re, z.im⟩ : ℂ) := by apply Complex.ext <;> rfl
    rw [hz_eq]
    exact lambda0_abs_le_one_thirtythird_strip hre0 hre2

end

/-! ## §Axiom check -/

#print axioms exp_three_gt_twenty
#print axioms pi_sub_three_quadratic_le_exp
#print axioms exp_pi_gt_twentythree
#print axioms exp_neg_pi_le_one_twentythird
#print axioms lambda0_abs_le_one_thirtythird
#print axioms lambda0_abs_le_one_thirtythird_strip
#print axioms lambda0_prime_abs_le_one_thirtythird

end Lambda0TightestBoundsMellin20261014
end PrincipiaTractalis
