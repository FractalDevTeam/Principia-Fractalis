/-
# PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14

Second rational-numerics tightening of the Mellin-of-theta bound.

Replaces the `π ≥ 3` step in `Lambda0TightestBoundsMellin` with
`π > 157/50 = 3.14` (via `Real.pi_gt_d2`). Combined with the same
`exp(π) ≥ 23` chain:

  `exp(-π) ≤ 1/23`,  `1 − exp(-π) ≥ 22/23`,  `π > 157/50`
  ⟹ `2·exp(-π)/(π·(1−exp(-π))) ≤ 2·(1/23)/((157/50)·(22/23))`
                                 `= 100/(157·22) = 50/1727`.

**Numerical comparison:**
  `1/33 ≈ 0.03030`  (previous tight)
  `50/1727 ≈ 0.02895`  (this file, 4.7% tighter)
  `0.02875`  (true analytic value)

**Pilot ceiling under `50/1727`:** `(c² + c)·(50/1727) ≤ 1/2`
  ⟺ `c² + c ≤ 1727/100 = 17.27`
  ⟺ `c ≤ (−1 + √70.08)/2 ≈ 3.686` (vs `≈ 3.593` under 1/33).

Gain is modest — one additional pilot center `c = 18/5 = 3.6` passes.
The qualitative ceiling is still `≈ 3.7`; reaching `c = 13` requires
`|t|`-dependent decay (integration-by-parts in the Mellin representation),
not a rational-numerics step.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.Lambda0UniformBound_2026_10_14
import PF.Analytic.Lambda0PrimeUniformBound_2026_10_14
import PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0UltraTightBoundsMellin20261014

open Complex Real MeasureTheory Set
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.Lambda0UniformBound20261014
open PrincipiaTractalis.Lambda0PrimeUniformBound20261014
open PrincipiaTractalis.Lambda0TightestBoundsMellin20261014

noncomputable section

/-! ## §1 — `‖Λ₀(1 + it)‖ ≤ 50/1727` -/

theorem lambda0_abs_le_fifty_over_1727 (t : ℝ) :
    ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 50 / 1727 := by
  refine (lambda0_abs_uniform t).trans ?_
  have hπ : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hπ_rat : (157 : ℝ) / 50 < π := by linarith [hπ, show (3.14 : ℝ) = 157/50 by norm_num]
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

/-! ## §2 — strip version on σ ∈ [0, 2] -/

theorem lambda0_abs_le_fifty_over_1727_strip
    {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)‖ ≤ 50 / 1727 := by
  refine (lambda0_abs_uniform_strip hσ0 hσ2).trans ?_
  have hπ : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hπ_rat : (157 : ℝ) / 50 < π := by linarith [hπ, show (3.14 : ℝ) = 157/50 by norm_num]
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

/-! ## §3 — derivative version via Cauchy -/

theorem lambda0_prime_abs_le_fifty_over_1727 (t : ℝ) :
    ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 50 / 1727 := by
  rw [show (50 / 1727 : ℝ) = (50 / 1727 : ℝ) / 1 from (div_one _).symm]
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
    exact lambda0_abs_le_fifty_over_1727_strip hre0 hre2

end

/-! ## §Axiom check -/

#print axioms lambda0_abs_le_fifty_over_1727
#print axioms lambda0_abs_le_fifty_over_1727_strip
#print axioms lambda0_prime_abs_le_fifty_over_1727

end Lambda0UltraTightBoundsMellin20261014
end PrincipiaTractalis
