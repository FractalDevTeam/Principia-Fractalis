/-
# PF.Analytic.Lambda0PrimeUniformBound_2026_10_14

Uniform modulus bound on the derivative of the completed Riemann zeta function
on the right edge σ = 1:
  **‖(deriv completedRiemannZeta₀) (1 + it)‖ ≤ 2/3**  uniformly in `t : ℝ`.

Derivation (parallel to `Lambda0UniformBound_2026_10_14`):

1. First extend `‖Λ₀(⟨σ, t⟩)‖ ≤ 2/3` from `σ = 1` to the whole strip `σ ∈ [0, 2]`
   — the proof is identical, both exponents remain ≤ 0 on the strip.

2. Apply mathlib's Cauchy derivative bound
   `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
   on the ball of radius 1 around `1 + it`. The ball lies entirely in
   `Re(z) ∈ (0, 2)`, so the strip bound applies, giving
   `‖deriv Λ₀ (1+it)‖ ≤ (2/3) / 1 = 2/3`.

This is the pilot's `|Λ₀'(1+it)|` bound needed for the derivative-modulus chain
to `|deriv edgeRe x| ≤ L`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.Lambda0UniformBound_2026_10_14
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0PrimeUniformBound20261014

open Complex Real MeasureTheory Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes
open PrincipiaTractalis.Lambda0UniformBound20261014

noncomputable section

/-! ## §0 — Exponent real parts for general σ -/

lemma re_exp_a_sigma (σ t : ℝ) : ((⟨σ, t⟩ : ℂ) / 2 - 1).re = σ / 2 - 1 := by
  rw [exponent_a_eq]

lemma re_exp_b_sigma (σ t : ℝ) : ((1 - (⟨σ, t⟩ : ℂ)) / 2 - 1).re = (1 - σ) / 2 - 1 := by
  rw [exponent_b_eq]

/-! ## §1 — Pointwise norm bound on the integrand on the strip σ ∈ [0, 2], x ≥ 1 -/

lemma norm_integrand_bound_strip {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖((x : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)
        + (x : ℂ) ^ ((1 - (⟨σ, t⟩ : ℂ)) / 2 - 1))
      * ((omega x : ℝ) : ℂ)‖
      ≤ 2 * Real.exp (-π * x) / (1 - Real.exp (-π)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [norm_mul]
  have h_omega_norm : ‖((omega x : ℝ) : ℂ)‖ = omega x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (omega_nonneg _)]
  rw [h_omega_norm]
  have h_sum : ‖(x : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)
                 + (x : ℂ) ^ ((1 - (⟨σ, t⟩ : ℂ)) / 2 - 1)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    have ha : ‖(x : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)‖ = x ^ (σ / 2 - 1 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, re_exp_a_sigma]
    have hb : ‖(x : ℂ) ^ ((1 - (⟨σ, t⟩ : ℂ)) / 2 - 1)‖ = x ^ ((1 - σ) / 2 - 1 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, re_exp_b_sigma]
    rw [ha, hb]
    have h_a_exp_nonpos : σ / 2 - 1 ≤ 0 := by linarith
    have h_b_exp_nonpos : (1 - σ) / 2 - 1 ≤ 0 := by linarith
    have h1 : x ^ (σ / 2 - 1 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx h_a_exp_nonpos
    have h2 : x ^ ((1 - σ) / 2 - 1 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx h_b_exp_nonpos
    linarith
  have h_ω_bound : omega x ≤ Real.exp (-π * x) / (1 - Real.exp (-π)) := by
    have hω := omega_le_geometric hx0
    have h_exp_mono : Real.exp (-π * x) ≤ Real.exp (-π) := by
      apply Real.exp_le_exp.mpr; nlinarith [hπ]
    have h_den_pi_pos := one_sub_exp_neg_pi_pos
    have h_den_x_pos : (0 : ℝ) < 1 - Real.exp (-π * x) := by
      linarith [exp_neg_pi_le_eighth, h_exp_mono]
    have h_inv : (1 - Real.exp (-π * x))⁻¹ ≤ (1 - Real.exp (-π))⁻¹ :=
      inv_anti₀ h_den_pi_pos (by linarith)
    have h_num_pos := (Real.exp_pos (-π * x)).le
    calc omega x
        ≤ Real.exp (-π * x) / (1 - Real.exp (-π * x)) := hω
      _ = Real.exp (-π * x) * (1 - Real.exp (-π * x))⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp (-π * x) * (1 - Real.exp (-π))⁻¹ :=
          mul_le_mul_of_nonneg_left h_inv h_num_pos
      _ = Real.exp (-π * x) / (1 - Real.exp (-π)) := (div_eq_mul_inv _ _).symm
  have h_ω_nn : 0 ≤ omega x := omega_nonneg _
  calc ‖(x : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)
            + (x : ℂ) ^ ((1 - (⟨σ, t⟩ : ℂ)) / 2 - 1)‖ * omega x
      ≤ 2 * (Real.exp (-π * x) / (1 - Real.exp (-π))) :=
        mul_le_mul h_sum h_ω_bound h_ω_nn (by norm_num)
    _ = 2 * Real.exp (-π * x) / (1 - Real.exp (-π)) := by ring

/-! ## §2 — Uniform modulus bound on Λ₀ for σ ∈ [0, 2] -/

theorem lambda0_abs_uniform_strip {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)‖
      ≤ 2 * Real.exp (-π) / (π * (1 - Real.exp (-π))) := by
  rw [completedRiemannZeta₀_eq_theta_integral]
  have h_bound_ae :
      ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioi (1 : ℝ))),
        ‖(((x : ℝ) : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)
            + ((x : ℝ) : ℂ) ^ ((1 - (⟨σ, t⟩ : ℂ)) / 2 - 1))
          * ((omega x : ℝ) : ℂ)‖ ≤ dominating x := by
    rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx1 : (1 : ℝ) ≤ x := le_of_lt (mem_Ioi.mp hx)
    rw [dominating_eq]
    exact norm_integrand_bound_strip hσ0 hσ2 hx1
  have h_triangle := norm_integral_le_of_norm_le dominating_integrableOn h_bound_ae
  refine h_triangle.trans ?_
  have h_eval : ∫ x in Ioi (1 : ℝ), dominating x
                = 2 * (1 - Real.exp (-π))⁻¹ * (Real.exp (-π) / π) := by
    unfold dominating
    rw [MeasureTheory.integral_const_mul]
    rw [integral_exp_neg_pi_mul_Ioi 1]
    congr 1
    ring
  rw [h_eval]
  have h_den_pos := one_sub_exp_neg_pi_pos
  have h_pi_pos : (0 : ℝ) < π := Real.pi_pos
  have h_rhs_eq : 2 * (1 - Real.exp (-π))⁻¹ * (Real.exp (-π) / π)
                = 2 * Real.exp (-π) / (π * (1 - Real.exp (-π))) := by
    field_simp
  rw [h_rhs_eq]

theorem lambda0_abs_le_two_thirds_strip {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)‖ ≤ 2 / 3 := by
  refine (lambda0_abs_uniform_strip hσ0 hσ2).trans ?_
  have hπ : (3 : ℝ) ≤ π := le_of_lt Real.pi_gt_three
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_exp := exp_neg_pi_le_eighth
  have h_exp_pos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
  have h_1_sub := one_sub_exp_neg_pi_pos
  have h_prod_pos : (0 : ℝ) < π * (1 - Real.exp (-π)) := by positivity
  rw [div_le_iff₀ h_prod_pos]
  nlinarith [h_exp, h_exp_pos, hπ, hπ_pos]

/-! ## §3 — Cauchy derivative bound: `‖deriv Λ₀ (1 + it)‖ ≤ 2/3` -/

/-- **Uniform modulus bound on the derivative of Λ₀** at points of the σ = 1
line, via Cauchy's inequality on a disk of radius 1 contained in the strip
`σ ∈ (0, 2)` where `Λ₀` has the uniform bound `≤ 2/3`. -/
theorem lambda0_prime_abs_le_two_thirds (t : ℝ) :
    ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 2 / 3 := by
  -- Reduce 2/3 to (2/3) / 1
  rw [show (2 / 3 : ℝ) = (2 / 3 : ℝ) / 1 from (div_one _).symm]
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos
  · -- DiffContOnCl: Λ₀ is entire, hence differentiable everywhere, hence
    -- diff-cont on the closure of any ball.
    apply Differentiable.diffContOnCl
    exact differentiable_completedZeta₀
  · -- ‖Λ₀(z)‖ ≤ 2/3 for z on the unit sphere around 1+it.
    intro z hz
    rw [Metric.mem_sphere] at hz
    -- |Re(z - (1+it))| ≤ ‖z - (1+it)‖ = 1, so |Re(z) - 1| ≤ 1 and Re(z) ∈ [0, 2].
    have h_dist : |z.re - 1| ≤ 1 := by
      have h := abs_re_le_norm (z - (⟨1, t⟩ : ℂ))
      have h1 : (z - (⟨1, t⟩ : ℂ)).re = z.re - 1 := by
        simp [Complex.sub_re]
      rw [h1] at h
      rw [← dist_eq_norm] at h
      rw [hz] at h
      exact h
    have h_abs := abs_le.mp h_dist
    have hre0 : (0 : ℝ) ≤ z.re := by linarith
    have hre2 : z.re ≤ 2 := by linarith
    -- Rewrite z as ⟨z.re, z.im⟩
    have hz_eq : z = (⟨z.re, z.im⟩ : ℂ) := by apply Complex.ext <;> rfl
    rw [hz_eq]
    exact lambda0_abs_le_two_thirds_strip hre0 hre2

end

/-! ## §Axiom check -/

#print axioms re_exp_a_sigma
#print axioms re_exp_b_sigma
#print axioms norm_integrand_bound_strip
#print axioms lambda0_abs_uniform_strip
#print axioms lambda0_abs_le_two_thirds_strip
#print axioms lambda0_prime_abs_le_two_thirds

end Lambda0PrimeUniformBound20261014
end PrincipiaTractalis
