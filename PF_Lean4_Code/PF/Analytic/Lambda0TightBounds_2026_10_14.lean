/-
# PF.Analytic.Lambda0TightBounds_2026_10_14

Tightening the Λ₀ and Λ₀' uniform bounds from `≤ 2/3` to **`≤ 2/21`**.

The integral bound `2·exp(-π)/(π·(1-exp(-π)))` is unchanged — it's the same
analytic expression. What changes is the elementary numerics step: with
`exp(-π) ≤ 1/8` and `π ≥ 3`, we get `≤ 2/21` instead of the loose `≤ 2/3`.

The tighter bound unlocks a 4× wider pilot box: `r = 1/5` on R1 (box
`[3/10, 7/10]`), closed in `PilotBoxes/R1_c0_5_r0_2_2026_10_14.lean`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.Lambda0UniformBound_2026_10_14
import PF.Analytic.Lambda0PrimeUniformBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0TightBounds20261014

open Complex Real MeasureTheory Set
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.Lambda0UniformBound20261014
open PrincipiaTractalis.Lambda0PrimeUniformBound20261014

noncomputable section

/-! ## §1 — `‖Λ₀(1 + it)‖ ≤ 2/21` -/

theorem lambda0_abs_le_two_twentyfirsts (t : ℝ) :
    ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 2 / 21 := by
  refine (lambda0_abs_uniform t).trans ?_
  have hπ : (3 : ℝ) ≤ π := le_of_lt Real.pi_gt_three
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_exp := exp_neg_pi_le_eighth
  have h_exp_pos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
  have h_prod_pos : (0 : ℝ) < π * (1 - Real.exp (-π)) := by
    have := one_sub_exp_neg_pi_pos; positivity
  rw [div_le_iff₀ h_prod_pos]
  nlinarith [h_exp, h_exp_pos, hπ, hπ_pos]

/-! ## §2 — `‖Λ₀(⟨σ, t⟩)‖ ≤ 2/21` on σ ∈ [0, 2] (strip version) -/

theorem lambda0_abs_le_two_twentyfirsts_strip
    {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)‖ ≤ 2 / 21 := by
  refine (lambda0_abs_uniform_strip hσ0 hσ2).trans ?_
  have hπ : (3 : ℝ) ≤ π := le_of_lt Real.pi_gt_three
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_exp := exp_neg_pi_le_eighth
  have h_exp_pos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
  have h_prod_pos : (0 : ℝ) < π * (1 - Real.exp (-π)) := by
    have := one_sub_exp_neg_pi_pos; positivity
  rw [div_le_iff₀ h_prod_pos]
  nlinarith [h_exp, h_exp_pos, hπ, hπ_pos]

/-! ## §3 — `‖deriv Λ₀ (1 + it)‖ ≤ 2/21` (Cauchy, tight) -/

theorem lambda0_prime_abs_le_two_twentyfirsts (t : ℝ) :
    ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 2 / 21 := by
  rw [show (2 / 21 : ℝ) = (2 / 21 : ℝ) / 1 from (div_one _).symm]
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
    exact lambda0_abs_le_two_twentyfirsts_strip hre0 hre2

end

/-! ## §Axiom check -/

#print axioms lambda0_abs_le_two_twentyfirsts
#print axioms lambda0_abs_le_two_twentyfirsts_strip
#print axioms lambda0_prime_abs_le_two_twentyfirsts

end Lambda0TightBounds20261014
end PrincipiaTractalis
