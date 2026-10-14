/-
# PF.Analytic.Lambda0UniformBound_2026_10_14

Uniform modulus bound on the entire completed Riemann zeta function on the
right edge σ = 1:
  **‖Λ₀(1 + it)‖ ≤ 2 · exp(−π) / (π · (1 − exp(−π)))**  uniformly in `t : ℝ`.

In particular `‖Λ₀(1 + it)‖ ≤ 2/3`, which discharges the pilot box's
hypothesis `1/4 ≤ Re ξ(1 + i/2)` via the closed form `re_xi_at_s`.

Derivation (see `codex/LAMBDA0_UNIFORM_BOUND_STRATEGY_2026-10-14.md`):

1. `completedRiemannZeta₀_eq_theta_integral` (XiThetaIntegral): the integral
   representation on all of ℂ.
2. `norm_integral_le_of_norm_le`: `‖∫f‖ ≤ ∫g` given pointwise `‖f‖ ≤ g` and
   integrable `g`.
3. Pointwise: `‖(u^a + u^b)·ω(u)‖ ≤ 2 · ω(u)` for u ≥ 1
   (`Complex.norm_cpow_eq_rpow_re_of_pos`, `Real.rpow_le_one_of_one_le_of_nonpos`).
4. `omega_le_geometric`: `ω(u) ≤ exp(-πu)/(1-exp(-π))` for u ≥ 1.
5. `integral_exp_neg_pi_mul_Ioi`: `∫_{u > 1} exp(-πu) du = exp(-π)/π`.
6. Elementary numerics: `exp(1) ≥ 2 → exp(3) ≥ 8 → exp(π) ≥ 8 → exp(-π) ≤ 1/8`.

Pilot discharge: `re_xi_at_s` at σ=1, t=1/2 + `Complex.abs_re_le_abs`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.XiThetaIntegral
import PF.Analytic.XiQuadrature
import PF.Analytic.RiemannXiThetaBoxEnclosure_r331a
import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import PF.Analytic.PilotBoxes.R1_c0_5_r0_05_2026_10_13
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0UniformBound20261014

open Complex Real MeasureTheory Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes

noncomputable section

/-! ## §0 — Elementary numerics: `exp(-π) ≤ 1/8` -/

lemma exp_one_ge_two : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

lemma exp_three_ge_eight : (8 : ℝ) ≤ Real.exp 3 := by
  have h1 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    have h3 : (3 : ℝ) = 1 + 1 + 1 := by norm_num
    rw [h3, Real.exp_add, Real.exp_add]
  rw [h1]
  have h := exp_one_ge_two
  have hpos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos _).le
  nlinarith [h, hpos]

lemma exp_pi_ge_eight : (8 : ℝ) ≤ Real.exp π := by
  have h3 := exp_three_ge_eight
  have hπ : (3 : ℝ) ≤ π := le_of_lt Real.pi_gt_three
  linarith [Real.exp_le_exp.mpr hπ]

lemma exp_neg_pi_le_eighth : Real.exp (-π) ≤ (1 : ℝ) / 8 := by
  rw [Real.exp_neg]
  rw [show (1 : ℝ) / 8 = (8 : ℝ)⁻¹ from by norm_num]
  exact inv_anti₀ (by norm_num : (0 : ℝ) < 8) exp_pi_ge_eight

lemma one_sub_exp_neg_pi_pos : (0 : ℝ) < 1 - Real.exp (-π) := by
  have := exp_neg_pi_le_eighth; linarith

/-! ## §1 — Exponent real parts at σ = 1 (via Legion's exponent lemmas) -/

lemma re_exp_a (t : ℝ) : ((⟨1, t⟩ : ℂ) / 2 - 1).re = -(1 / 2) := by
  rw [exponent_a_eq]
  show (1 : ℝ) / 2 - 1 = -(1 / 2)
  norm_num

lemma re_exp_b (t : ℝ) : ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1).re = -1 := by
  rw [exponent_b_eq]
  show (1 - (1 : ℝ)) / 2 - 1 = -1
  norm_num

/-! ## §2 — Pointwise norm bound on the integrand at σ = 1, x ≥ 1 -/

lemma norm_integrand_bound (t : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ‖((x : ℂ) ^ ((⟨1, t⟩ : ℂ) / 2 - 1)
        + (x : ℂ) ^ ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1))
      * ((omega x : ℝ) : ℂ)‖
      ≤ 2 * Real.exp (-π * x) / (1 - Real.exp (-π)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [norm_mul]
  have h_omega_norm : ‖((omega x : ℝ) : ℂ)‖ = omega x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (omega_nonneg _)]
  rw [h_omega_norm]
  have h_sum : ‖(x : ℂ) ^ ((⟨1, t⟩ : ℂ) / 2 - 1)
                 + (x : ℂ) ^ ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    have ha : ‖(x : ℂ) ^ ((⟨1, t⟩ : ℂ) / 2 - 1)‖ = x ^ (-(1 / 2) : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, re_exp_a]
    have hb : ‖(x : ℂ) ^ ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1)‖ = x ^ (-1 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, re_exp_b]
    rw [ha, hb]
    have h1 : x ^ (-(1 / 2) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
    have h2 : x ^ (-1 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
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
  calc ‖(x : ℂ) ^ ((⟨1, t⟩ : ℂ) / 2 - 1)
            + (x : ℂ) ^ ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1)‖ * omega x
      ≤ 2 * (Real.exp (-π * x) / (1 - Real.exp (-π))) :=
        mul_le_mul h_sum h_ω_bound h_ω_nn (by norm_num)
    _ = 2 * Real.exp (-π * x) / (1 - Real.exp (-π)) := by ring

/-! ## §3 — Integrability of the dominating function on Ioi 1 -/

def dominating (x : ℝ) : ℝ := 2 * (1 - Real.exp (-π))⁻¹ * Real.exp (-π * x)

lemma dominating_eq (x : ℝ) :
    dominating x = 2 * Real.exp (-π * x) / (1 - Real.exp (-π)) := by
  unfold dominating
  have h_pos := one_sub_exp_neg_pi_pos
  field_simp

lemma dominating_integrableOn : IntegrableOn dominating (Ioi 1) := by
  unfold dominating
  have h : IntegrableOn (fun x : ℝ => Real.exp (-π * x)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (a := -π) (c := 1) (by nlinarith [Real.pi_pos])
  exact h.const_mul (2 * (1 - Real.exp (-π))⁻¹)

/-! ## §4 — Main uniform modulus bound -/

theorem lambda0_abs_uniform (t : ℝ) :
    ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
      ≤ 2 * Real.exp (-π) / (π * (1 - Real.exp (-π))) := by
  rw [completedRiemannZeta₀_eq_theta_integral]
  have h_bound_ae :
      ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioi (1 : ℝ))),
        ‖(((x : ℝ) : ℂ) ^ ((⟨1, t⟩ : ℂ) / 2 - 1)
            + ((x : ℝ) : ℂ) ^ ((1 - (⟨1, t⟩ : ℂ)) / 2 - 1))
          * ((omega x : ℝ) : ℂ)‖ ≤ dominating x := by
    rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx1 : (1 : ℝ) ≤ x := le_of_lt (mem_Ioi.mp hx)
    rw [dominating_eq]
    exact norm_integrand_bound t hx1
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

/-! ## §5 — Rational-bound form: `‖Λ₀(1 + it)‖ ≤ 2/3` -/

theorem lambda0_abs_le_two_thirds (t : ℝ) :
    ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 2 / 3 := by
  refine (lambda0_abs_uniform t).trans ?_
  have hπ : (3 : ℝ) ≤ π := le_of_lt Real.pi_gt_three
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_exp := exp_neg_pi_le_eighth
  have h_exp_pos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
  have h_1_sub := one_sub_exp_neg_pi_pos
  have h_prod_pos : (0 : ℝ) < π * (1 - Real.exp (-π)) := by positivity
  rw [div_le_iff₀ h_prod_pos]
  nlinarith [h_exp, h_exp_pos, hπ, hπ_pos]

/-! ## §6 — Pilot discharge: `1/4 ≤ Re ξ(1 + i/2)` -/

theorem pilot_r1_hvalue_lb :
    (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 1 / 2⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  have hΛ := lambda0_abs_le_two_thirds (1 / 2 : ℝ)
  have h_re_abs :
      |(completedRiemannZeta₀ (⟨1, 1 / 2⟩ : ℂ)).re| ≤ 2 / 3 :=
    (abs_re_le_norm _).trans hΛ
  have h_im_abs :
      |(completedRiemannZeta₀ (⟨1, 1 / 2⟩ : ℂ)).im| ≤ 2 / 3 :=
    (abs_im_le_norm _).trans hΛ
  have h_re_bd := abs_le.mp h_re_abs
  have h_im_bd := abs_le.mp h_im_abs
  nlinarith [h_re_bd.1, h_re_bd.2, h_im_bd.1, h_im_bd.2]

end

/-! ## §Axiom check -/

#print axioms exp_one_ge_two
#print axioms exp_pi_ge_eight
#print axioms exp_neg_pi_le_eighth
#print axioms re_exp_a
#print axioms re_exp_b
#print axioms norm_integrand_bound
#print axioms dominating_integrableOn
#print axioms lambda0_abs_uniform
#print axioms lambda0_abs_le_two_thirds
#print axioms pilot_r1_hvalue_lb

end Lambda0UniformBound20261014
end PrincipiaTractalis
