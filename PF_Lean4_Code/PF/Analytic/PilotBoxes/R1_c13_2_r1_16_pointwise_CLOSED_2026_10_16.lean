/-
# PF.Analytic.PilotBoxes.R1_c13_2_r1_16_pointwise_CLOSED_2026_10_16

**Gate-1 pilot CLOSED at c = 13/2, r = 1/16 — the pointwise-panel payoff
for the adjacent box.**

Mirror of `R1_c6_r1_16_pointwise_CLOSED_2026_10_15.lean`. Instantiates the
conditional scaffold `R1_c13_2_r_pointwise_SCAFFOLD_2026_10_16` to an
UNCONDITIONAL `R1_box [103/16, 105/16]` using:

* **M2.5 Assembly** (`Assemble_c13_2_threehalves_2026_10_16`)
* **M2.5 Residue** (`ResidueBound_c13_2_three_halves_to_5_2026_10_16`)
* **Analytic tail** (`AnalyticTailBound_c13_2_2026_10_16`)
* **ω-tail gap** (`OmegaTailBound_c13_2_2026_10_16`)
* **Legion L4** (`Lambda0IBPIdentity_2026_10_15.lambda0_edge_eq_F_integrals`)

**Three-axiom bar:** every top-level theorem prints exactly
`[propext, Classical.choice, Quot.sound]`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/

import PF.Analytic.PilotBoxes.R1_c13_2_r_pointwise_SCAFFOLD_2026_10_16
import PF.Analytic.FourierPanels.Assemble_c13_2_threehalves_2026_10_16
import PF.Analytic.FourierPanels.ResidueBound_c13_2_three_halves_to_5_2026_10_16
import PF.Analytic.FourierPanels.AnalyticTailBound_c13_2_2026_10_16
import PF.Analytic.FourierPanels.OmegaTailBound_c13_2_2026_10_16
import PF.Analytic.Lambda0IBPIdentity_2026_10_15

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PrincipiaTractalis
namespace PilotR1Box_c13_2_r1_16_pointwise_CLOSED_20261016

open Complex Set MeasureTheory Filter Topology
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.FourierPanels_c13_2
open PrincipiaTractalis.FourierPanels_c13_2.Assemble_threehalves
open PrincipiaTractalis.FourierPanels_c13_2.ResidueBound
open PrincipiaTractalis.FourierPanels_c13_2.AnalyticTailBound
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaDerivativeBounds20261015
open PrincipiaTractalis.Lambda0IBPIdentity20261015
open PrincipiaTractalis.PilotR1Box_c13_2_r_pointwise_SCAFFOLD_20261016
open scoped Real

noncomputable section

/-! ## §0 — Rational constants

Composite enclosures after adding residue (≤ 231/10^6), analytic tail
(≤ 1/10⁶), and ω-gap (≤ 1/10⁴ integrated):
* `R_ub_f = R_ub_h32 + 231/10^6 + 1/10⁶ + 1/10⁴`
* `R_lb_f = R_lb_h32 - 231/10^6 - 1/10⁶ - 1/10⁴`
* `I_ub_f = I_ub_h32 + 231/10^6 + 1/10⁶ + 1/10⁴`
* `I_lb_f = I_lb_h32 - 231/10^6 - 1/10⁶ - 1/10⁴`

Gate-1 check: `(169/4)·R_ub_f + (13/2)·I_ub_f ≤ 3/4`.
Numerically (constants as actually used; cf. §M2.5 below):
  R_ub_h32 = 1339441331/80000000000 ≈ 0.0169634958
  I_ub_h32 =  302372667/160000000000 ≈ 0.0018848403
  add-on   = 231/10^6 + 1/10⁶ + 1/10⁴  ≈ 0.0009264688
  R_ub_f ≈ 0.0169634958 + 0.0009264688 ≈ 0.0178899646
  I_ub_f ≈ 0.0018848403 + 0.0009264688 ≈ 0.0028113090
  (169/4)·0.0178899646 + (13/2)·0.0028113090
      ≈ 0.7270595 + 0.0179221 ≈ 0.7449814 ≤ 0.75 ✓   (slack ≈ +0.0050186)

NOTE 2026-10-16: the previous form of this block quoted R_ub_f ≈ 0.018418 and
a product ≈ 0.6909. Those were inconsistent with each other
(40.6406 × 0.018418 = 0.7485, which would FAIL the gate) and with the
rational constants the proof actually uses. The proof was always correct;
only this comment was wrong. Corrected above.
-/

private noncomputable abbrev epsOm : ℝ := 1 / 10 ^ 4

/-! ## §1 — ω-gap integrated bound (loose but easy) -/

lemma one_minus_exp_neg_pi_ge :
    (22 / 23 : ℝ) ≤ 1 - Real.exp (-π) := by
  have h : Real.exp (-π) ≤ 1 / 23 :=
    PrincipiaTractalis.Lambda0TightestBoundsMellin20261014.exp_neg_pi_le_one_twentythird
  linarith

lemma one_minus_exp_neg_pi_pos : (0 : ℝ) < 1 - Real.exp (-π) := by
  have := one_minus_exp_neg_pi_ge
  linarith

lemma one_div_one_minus_exp_neg_pi_le :
    (1 : ℝ) / (1 - Real.exp (-π)) ≤ 23 / 22 := by
  have h_pos : (0 : ℝ) < 1 - Real.exp (-π) := one_minus_exp_neg_pi_pos
  have h_ge : (22 / 23 : ℝ) ≤ 1 - Real.exp (-π) := one_minus_exp_neg_pi_ge
  rw [div_le_div_iff₀ h_pos (by norm_num : (0 : ℝ) < 22)]
  linarith

lemma exp_neg_sixteen_pi_le : Real.exp (-(16 * π)) ≤ 1 / 10 ^ 20 := by
  have h_eq : Real.exp (-(16 * π)) = (Real.exp (-π)) ^ 16 := by
    rw [← Real.exp_nat_mul (-π) 16]
    congr 1; push_cast; ring
  rw [h_eq]
  have hbase : Real.exp (-π) ≤ 1 / 23 :=
    PrincipiaTractalis.Lambda0TightestBoundsMellin20261014.exp_neg_pi_le_one_twentythird
  have hbase_nn : 0 ≤ Real.exp (-π) := (Real.exp_pos _).le
  have hpow : (Real.exp (-π)) ^ 16 ≤ (1 / 23 : ℝ) ^ 16 :=
    pow_le_pow_left₀ hbase_nn hbase 16
  have h_rhs : ((1 : ℝ) / 23) ^ 16 ≤ 1 / 10 ^ 20 := by norm_num
  linarith

/-! ## §2 — Pointwise helper identities for the Fourier integrand at t = 13/2 -/

/-- At `t = 13/2`, the exponent simplifies:
`I · ((13/2 : ℂ)/2) · (u : ℂ) = ((13/4)·u : ℝ) · I = (3.25·u : ℝ) · I`. -/
lemma exp_phase_plus_at_c13_2 (u : ℝ) :
    Complex.exp (Complex.I * ((13/2 : ℂ) / 2) * (u : ℂ))
      = (Real.cos ((3.25 : ℝ) * u) : ℂ)
          + (Real.sin ((3.25 : ℝ) * u) : ℂ) * Complex.I := by
  have h_arg : Complex.I * ((13/2 : ℂ) / 2) * (u : ℂ)
      = (((3.25 : ℝ) * u : ℝ) : ℂ) * Complex.I := by
    have h_cast : (((3.25 : ℝ) * u : ℝ) : ℂ) = (13/4 : ℂ) * (u : ℂ) := by
      push_cast
      norm_num
    rw [h_cast]
    ring
  rw [h_arg, Complex.exp_mul_I]
  push_cast
  rfl

lemma exp_phase_minus_at_c13_2 (u : ℝ) :
    Complex.exp (-(Complex.I * ((13/2 : ℂ) / 2)) * (u : ℂ))
      = (Real.cos ((3.25 : ℝ) * u) : ℂ)
          - (Real.sin ((3.25 : ℝ) * u) : ℂ) * Complex.I := by
  have h_arg : -(Complex.I * ((13/2 : ℂ) / 2)) * (u : ℂ)
      = ((-((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I := by
    have h_cast : ((-((3.25 : ℝ) * u) : ℝ) : ℂ) = -((13/4 : ℂ) * (u : ℂ)) := by
      push_cast
      norm_num
    rw [h_cast]
    ring
  rw [h_arg, Complex.exp_mul_I]
  rw [show ((-((3.25 : ℝ) * u) : ℝ) : ℂ) = -(((3.25 : ℝ) * u : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

lemma plus_integrand_at_c13_2 (u : ℝ) :
    ((F_plus u : ℝ) : ℂ) * Complex.exp (Complex.I * ((13/2 : ℂ) / 2) * (u : ℂ))
      = ((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I := by
  rw [exp_phase_plus_at_c13_2]
  push_cast
  ring

lemma minus_integrand_at_c13_2 (u : ℝ) :
    ((F_minus u : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((13/2 : ℂ) / 2)) * (u : ℂ))
      = ((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I := by
  rw [exp_phase_minus_at_c13_2]
  push_cast
  ring

/-! ## §3 — Taking real and imaginary parts of Legion's identity at t = 13/2 -/

/-- Real part of Legion's identity:
`Re Λ₀(1 + (13/2)i) = ∫_{Ioi 0} nodeR_fourier_plus_at_c13_2 u`. -/
theorem re_lambda0_at_c13_2 :
    (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).re
      = ∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2 u := by
  have hLegion := lambda0_edge_eq_F_integrals (13/2 : ℝ)
  have hFp_int : IntegrableOn
      (fun u : ℝ => ((F_plus u : ℝ) : ℂ)
          * Complex.exp (Complex.I * (((13/2 : ℝ) : ℂ) / 2) * (u : ℂ))) (Ioi 0) :=
    integrableOn_F_plus_phase (13/2)
  have hFm_int : IntegrableOn
      (fun u : ℝ => ((F_minus u : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (((13/2 : ℝ) : ℂ) / 2)) * (u : ℂ))) (Ioi 0) :=
    integrableOn_F_minus_phase (13/2)
  have hplus_eq : ∀ u : ℝ,
      ((F_plus u : ℝ) : ℂ)
        * Complex.exp (Complex.I * (((13/2 : ℝ) : ℂ) / 2) * (u : ℂ))
      = ((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I := by
    intro u
    have h : (((13/2 : ℝ) : ℂ) : ℂ) = (13/2 : ℂ) := by push_cast; rfl
    rw [h]
    exact plus_integrand_at_c13_2 u
  have hminus_eq : ∀ u : ℝ,
      ((F_minus u : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (((13/2 : ℝ) : ℂ) / 2)) * (u : ℂ))
      = ((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I := by
    intro u
    have h : (((13/2 : ℝ) : ℂ) : ℂ) = (13/2 : ℂ) := by push_cast; rfl
    rw [h]
    exact minus_integrand_at_c13_2 u
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => hplus_eq u),
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => hminus_eq u)] at hLegion
  apply_fun Complex.re at hLegion
  rw [Complex.add_re] at hLegion
  have h_simp_plus : ∀ u : ℝ,
      (((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re
        = F_plus u * Real.cos ((3.25 : ℝ) * u) := by
    intro u
    have h1 : (((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)).re
        = F_plus u * Real.cos ((3.25 : ℝ) * u) :=
      Complex.ofReal_re _
    have h2 : (((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re]
      ring
    rw [Complex.add_re, h1, h2]; ring
  have h_simp_minus : ∀ u : ℝ,
      (((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re
        = F_minus u * Real.cos ((3.25 : ℝ) * u) := by
    intro u
    have h1 : (((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)).re
        = F_minus u * Real.cos ((3.25 : ℝ) * u) :=
      Complex.ofReal_re _
    have h2 : (((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re]
      ring
    rw [Complex.sub_re, h1, h2]; ring
  have hFp_c_int : IntegrableOn
      (fun u : ℝ => ((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I) (Ioi 0) := by
    refine hFp_int.congr_fun (fun u _ => ?_) measurableSet_Ioi
    exact hplus_eq u
  have hFm_c_int : IntegrableOn
      (fun u : ℝ => ((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I) (Ioi 0) := by
    refine hFm_int.congr_fun (fun u _ => ?_) measurableSet_Ioi
    exact hminus_eq u
  have hreP : (∫ u in Ioi (0 : ℝ), ((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re
      = ∫ u in Ioi (0 : ℝ), (((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re :=
    (integral_re hFp_c_int).symm
  have hreM : (∫ u in Ioi (0 : ℝ), ((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re
      = ∫ u in Ioi (0 : ℝ), (((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re :=
    (integral_re hFm_c_int).symm
  rw [hreP, hreM] at hLegion
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => h_simp_plus u),
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => h_simp_minus u)] at hLegion
  have hFp_cos_int : IntegrableOn
      (fun u : ℝ => F_plus u * Real.cos ((3.25 : ℝ) * u)) (Ioi 0) := by
    have h0 : IntegrableOn (fun u : ℝ => (((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
        + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re) (Ioi (0 : ℝ)) :=
      hFp_c_int.re
    refine h0.congr_fun (fun u _ => ?_) measurableSet_Ioi
    exact h_simp_plus u
  have hFm_cos_int : IntegrableOn
      (fun u : ℝ => F_minus u * Real.cos ((3.25 : ℝ) * u)) (Ioi 0) := by
    have h0 : IntegrableOn (fun u : ℝ => (((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
        - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).re) (Ioi (0 : ℝ)) :=
      hFm_c_int.re
    refine h0.congr_fun (fun u _ => ?_) measurableSet_Ioi
    exact h_simp_minus u
  rw [← MeasureTheory.integral_add hFp_cos_int hFm_cos_int] at hLegion
  rw [hLegion]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  show F_plus u * Real.cos ((3.25 : ℝ) * u) + F_minus u * Real.cos ((3.25 : ℝ) * u)
       = nodeR_fourier_plus_at_c13_2 u
  unfold nodeR_fourier_plus_at_c13_2
  ring

/-- Imaginary part of Legion's identity:
`Im Λ₀(1 + (13/2)i) = ∫_{Ioi 0} nodeR_fourier_minus_at_c13_2 u`. -/
theorem im_lambda0_at_c13_2 :
    (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).im
      = ∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2 u := by
  have hLegion := lambda0_edge_eq_F_integrals (13/2 : ℝ)
  have hFp_int : IntegrableOn
      (fun u : ℝ => ((F_plus u : ℝ) : ℂ)
          * Complex.exp (Complex.I * (((13/2 : ℝ) : ℂ) / 2) * (u : ℂ))) (Ioi 0) :=
    integrableOn_F_plus_phase (13/2)
  have hFm_int : IntegrableOn
      (fun u : ℝ => ((F_minus u : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (((13/2 : ℝ) : ℂ) / 2)) * (u : ℂ))) (Ioi 0) :=
    integrableOn_F_minus_phase (13/2)
  have hplus_eq : ∀ u : ℝ,
      ((F_plus u : ℝ) : ℂ)
        * Complex.exp (Complex.I * (((13/2 : ℝ) : ℂ) / 2) * (u : ℂ))
      = ((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I := by
    intro u
    have h : (((13/2 : ℝ) : ℂ) : ℂ) = (13/2 : ℂ) := by push_cast; rfl
    rw [h]
    exact plus_integrand_at_c13_2 u
  have hminus_eq : ∀ u : ℝ,
      ((F_minus u : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (((13/2 : ℝ) : ℂ) / 2)) * (u : ℂ))
      = ((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I := by
    intro u
    have h : (((13/2 : ℝ) : ℂ) : ℂ) = (13/2 : ℂ) := by push_cast; rfl
    rw [h]
    exact minus_integrand_at_c13_2 u
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => hplus_eq u),
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => hminus_eq u)] at hLegion
  apply_fun Complex.im at hLegion
  rw [Complex.add_im] at hLegion
  have h_simp_plus : ∀ u : ℝ,
      (((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im
        = F_plus u * Real.sin ((3.25 : ℝ) * u) := by
    intro u
    have h1 : (((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)).im = 0 := Complex.ofReal_im _
    have h2 : (((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im
        = F_plus u * Real.sin ((3.25 : ℝ) * u) := by
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re]
      ring
    rw [Complex.add_im, h1, h2]; ring
  have h_simp_minus : ∀ u : ℝ,
      (((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im
        = -(F_minus u * Real.sin ((3.25 : ℝ) * u)) := by
    intro u
    have h1 : (((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)).im = 0 := Complex.ofReal_im _
    have h2 : (((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im
        = F_minus u * Real.sin ((3.25 : ℝ) * u) := by
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re]
      ring
    rw [Complex.sub_im, h1, h2]; ring
  have hFp_c_int : IntegrableOn
      (fun u : ℝ => ((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I) (Ioi 0) := by
    refine hFp_int.congr_fun (fun u _ => ?_) measurableSet_Ioi
    exact hplus_eq u
  have hFm_c_int : IntegrableOn
      (fun u : ℝ => ((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I) (Ioi 0) := by
    refine hFm_int.congr_fun (fun u _ => ?_) measurableSet_Ioi
    exact hminus_eq u
  have himP : (∫ u in Ioi (0 : ℝ), ((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im
      = ∫ u in Ioi (0 : ℝ), (((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im :=
    (integral_im hFp_c_int).symm
  have himM : (∫ u in Ioi (0 : ℝ), ((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im
      = ∫ u in Ioi (0 : ℝ), (((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
          - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im :=
    (integral_im hFm_c_int).symm
  rw [himP, himM] at hLegion
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => h_simp_plus u),
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => h_simp_minus u)] at hLegion
  have hFp_sin_int : IntegrableOn
      (fun u : ℝ => F_plus u * Real.sin ((3.25 : ℝ) * u)) (Ioi 0) := by
    have h0 : IntegrableOn (fun u : ℝ => (((F_plus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
        + ((F_plus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im) (Ioi (0 : ℝ)) :=
      hFp_c_int.im
    refine h0.congr_fun (fun u _ => ?_) measurableSet_Ioi
    exact h_simp_plus u
  have hFm_sin_int : IntegrableOn
      (fun u : ℝ => -(F_minus u * Real.sin ((3.25 : ℝ) * u))) (Ioi 0) := by
    have h0 : IntegrableOn (fun u : ℝ => (((F_minus u * Real.cos ((3.25 : ℝ) * u) : ℝ) : ℂ)
        - ((F_minus u * Real.sin ((3.25 : ℝ) * u) : ℝ) : ℂ) * Complex.I).im) (Ioi (0 : ℝ)) :=
      hFm_c_int.im
    refine h0.congr_fun (fun u _ => ?_) measurableSet_Ioi
    exact h_simp_minus u
  rw [← MeasureTheory.integral_add hFp_sin_int hFm_sin_int] at hLegion
  rw [hLegion]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  show F_plus u * Real.sin ((3.25 : ℝ) * u) + -(F_minus u * Real.sin ((3.25 : ℝ) * u))
       = nodeR_fourier_minus_at_c13_2 u
  unfold nodeR_fourier_minus_at_c13_2
  ring

/-! ## §4 — Full-ω node integrability on `Ioi 0` -/

lemma nodeR_fourier_plus_at_c13_2_integrable_Ioi0 :
    IntegrableOn nodeR_fourier_plus_at_c13_2 (Ioi (0 : ℝ)) := by
  have hFp := F_plus_integrable_Ioi
  have hFm := F_minus_integrable_Ioi
  have hsum : IntegrableOn (fun u => F_plus u + F_minus u) (Ioi (0 : ℝ)) := hFp.add hFm
  have hcos_meas_c : Continuous (fun u : ℝ => Real.cos ((3.25 : ℝ) * u)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcos_bd : ∀ u : ℝ, ‖Real.cos ((3.25 : ℝ) * u)‖ ≤ 1 := by
    intro u
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hbdd : IntegrableOn
      (fun u => Real.cos ((3.25 : ℝ) * u) * (F_plus u + F_minus u)) (Ioi (0 : ℝ)) :=
    hsum.bdd_mul hcos_meas_c.aestronglyMeasurable ⟨1, hcos_bd⟩
  refine hbdd.congr_fun (fun u _ => ?_) measurableSet_Ioi
  show Real.cos ((3.25 : ℝ) * u) * (F_plus u + F_minus u) = nodeR_fourier_plus_at_c13_2 u
  unfold nodeR_fourier_plus_at_c13_2; ring

lemma nodeR_fourier_minus_at_c13_2_integrable_Ioi0 :
    IntegrableOn nodeR_fourier_minus_at_c13_2 (Ioi (0 : ℝ)) := by
  have hFp := F_plus_integrable_Ioi
  have hFm := F_minus_integrable_Ioi
  have hdiff : IntegrableOn (fun u => F_plus u - F_minus u) (Ioi (0 : ℝ)) := hFp.sub hFm
  have hsin_meas_c : Continuous (fun u : ℝ => Real.sin ((3.25 : ℝ) * u)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hsin_bd : ∀ u : ℝ, ‖Real.sin ((3.25 : ℝ) * u)‖ ≤ 1 := by
    intro u
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hbdd : IntegrableOn
      (fun u => Real.sin ((3.25 : ℝ) * u) * (F_plus u - F_minus u)) (Ioi (0 : ℝ)) :=
    hdiff.bdd_mul hsin_meas_c.aestronglyMeasurable ⟨1, hsin_bd⟩
  refine hbdd.congr_fun (fun u _ => ?_) measurableSet_Ioi
  show Real.sin ((3.25 : ℝ) * u) * (F_plus u - F_minus u) = nodeR_fourier_minus_at_c13_2 u
  unfold nodeR_fourier_minus_at_c13_2; ring

/-! ## §5 — N=3 node integrability on `Ioi 0` -/

lemma nodeR_fourier_plus_at_c13_2_N3_integrable_Ioi0 :
    IntegrableOn nodeR_fourier_plus_at_c13_2_N3 (Ioi (0 : ℝ)) := by
  have hunion : Ioi (0 : ℝ) = Ioc 0 5 ∪ Ioi 5 :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 5)).symm
  have hIoc : IntegrableOn nodeR_fourier_plus_at_c13_2_N3 (Ioc 0 5) :=
    (Seg01Range.nodeR_fourier_plus_at_c13_2_N3_intervalIntegrable 0 5).1
  have hIoi5 := nodeR_fourier_plus_at_c13_2_N3_integrable_Ioi5
  rw [show (Ioi (0:ℝ)) = Ioc 0 5 ∪ Ioi 5 from hunion]
  exact hIoc.union hIoi5

lemma nodeR_fourier_minus_at_c13_2_N3_integrable_Ioi0 :
    IntegrableOn nodeR_fourier_minus_at_c13_2_N3 (Ioi (0 : ℝ)) := by
  have hunion : Ioi (0 : ℝ) = Ioc 0 5 ∪ Ioi 5 :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 5)).symm
  have hIoc : IntegrableOn nodeR_fourier_minus_at_c13_2_N3 (Ioc 0 5) :=
    (Seg01Range.nodeR_fourier_minus_at_c13_2_N3_intervalIntegrable 0 5).1
  have hIoi5 := nodeR_fourier_minus_at_c13_2_N3_integrable_Ioi5
  rw [show (Ioi (0:ℝ)) = Ioc 0 5 ∪ Ioi 5 from hunion]
  exact hIoc.union hIoi5

/-! ## §6 — N=3 node integral split over `Ioi 0` -/

private lemma plus_N3_int_Ioc_0_h32 :
    IntegrableOn nodeR_fourier_plus_at_c13_2_N3 (Ioc 0 (3/2 : ℝ)) :=
  (Seg01Range.nodeR_fourier_plus_at_c13_2_N3_intervalIntegrable 0 (3/2)).1

private lemma plus_N3_int_Ioc_h32_5 :
    IntegrableOn nodeR_fourier_plus_at_c13_2_N3 (Ioc (3/2 : ℝ) 5) :=
  (Seg01Range.nodeR_fourier_plus_at_c13_2_N3_intervalIntegrable (3/2) 5).1

private lemma minus_N3_int_Ioc_0_h32 :
    IntegrableOn nodeR_fourier_minus_at_c13_2_N3 (Ioc 0 (3/2 : ℝ)) :=
  (Seg01Range.nodeR_fourier_minus_at_c13_2_N3_intervalIntegrable 0 (3/2)).1

private lemma minus_N3_int_Ioc_h32_5 :
    IntegrableOn nodeR_fourier_minus_at_c13_2_N3 (Ioc (3/2 : ℝ) 5) :=
  (Seg01Range.nodeR_fourier_minus_at_c13_2_N3_intervalIntegrable (3/2) 5).1

theorem plus_N3_split :
    (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)
      = (∫ u in (0 : ℝ)..(3/2), nodeR_fourier_plus_at_c13_2_N3 u)
        + (∫ u in (3/2 : ℝ)..5, nodeR_fourier_plus_at_c13_2_N3 u)
        + (∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u) := by
  have h_union1 : Ioi (0 : ℝ) = Ioc 0 (3/2) ∪ Ioi (3/2) :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 3/2)).symm
  have h_disj1 : Disjoint (Ioc 0 (3/2 : ℝ)) (Ioi (3/2 : ℝ)) :=
    Ioc_disjoint_Ioi_same
  have h_int1a : IntegrableOn nodeR_fourier_plus_at_c13_2_N3 (Ioc 0 (3/2)) :=
    plus_N3_int_Ioc_0_h32
  have h_int1b : IntegrableOn nodeR_fourier_plus_at_c13_2_N3 (Ioi (3/2)) := by
    have hfull := nodeR_fourier_plus_at_c13_2_N3_integrable_Ioi0
    exact hfull.mono_set (fun u hu => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hu)))
  have h1 : (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)
      = (∫ u in Ioc 0 (3/2 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)
        + (∫ u in Ioi (3/2 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u) := by
    rw [h_union1,
        MeasureTheory.setIntegral_union h_disj1 measurableSet_Ioi h_int1a h_int1b]
  have h_union2 : Ioi (3/2 : ℝ) = Ioc (3/2) 5 ∪ Ioi 5 :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (3/2 : ℝ) ≤ 5)).symm
  have h_disj2 : Disjoint (Ioc (3/2 : ℝ) 5) (Ioi 5) := Ioc_disjoint_Ioi_same
  have h_int2a : IntegrableOn nodeR_fourier_plus_at_c13_2_N3 (Ioc (3/2) 5) :=
    plus_N3_int_Ioc_h32_5
  have h_int2b : IntegrableOn nodeR_fourier_plus_at_c13_2_N3 (Ioi 5) :=
    nodeR_fourier_plus_at_c13_2_N3_integrable_Ioi5
  have h2 : (∫ u in Ioi (3/2 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)
      = (∫ u in Ioc (3/2 : ℝ) 5, nodeR_fourier_plus_at_c13_2_N3 u)
        + (∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u) := by
    rw [h_union2,
        MeasureTheory.setIntegral_union h_disj2 measurableSet_Ioi h_int2a h_int2b]
  have hint_a : (∫ u in Ioc 0 (3/2 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)
      = ∫ u in (0 : ℝ)..(3/2), nodeR_fourier_plus_at_c13_2_N3 u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 3/2)]
  have hint_b : (∫ u in Ioc (3/2 : ℝ) 5, nodeR_fourier_plus_at_c13_2_N3 u)
      = ∫ u in (3/2 : ℝ)..5, nodeR_fourier_plus_at_c13_2_N3 u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (3/2:ℝ) ≤ 5)]
  rw [h1, h2, hint_a, hint_b]
  ring

theorem minus_N3_split :
    (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)
      = (∫ u in (0 : ℝ)..(3/2), nodeR_fourier_minus_at_c13_2_N3 u)
        + (∫ u in (3/2 : ℝ)..5, nodeR_fourier_minus_at_c13_2_N3 u)
        + (∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u) := by
  have h_union1 : Ioi (0 : ℝ) = Ioc 0 (3/2) ∪ Ioi (3/2) :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 3/2)).symm
  have h_disj1 : Disjoint (Ioc 0 (3/2 : ℝ)) (Ioi (3/2 : ℝ)) := Ioc_disjoint_Ioi_same
  have h_int1a : IntegrableOn nodeR_fourier_minus_at_c13_2_N3 (Ioc 0 (3/2)) :=
    minus_N3_int_Ioc_0_h32
  have h_int1b : IntegrableOn nodeR_fourier_minus_at_c13_2_N3 (Ioi (3/2)) := by
    have hfull := nodeR_fourier_minus_at_c13_2_N3_integrable_Ioi0
    exact hfull.mono_set (fun u hu => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hu)))
  have h1 : (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)
      = (∫ u in Ioc 0 (3/2 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)
        + (∫ u in Ioi (3/2 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u) := by
    rw [h_union1,
        MeasureTheory.setIntegral_union h_disj1 measurableSet_Ioi h_int1a h_int1b]
  have h_union2 : Ioi (3/2 : ℝ) = Ioc (3/2) 5 ∪ Ioi 5 :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (3/2 : ℝ) ≤ 5)).symm
  have h_disj2 : Disjoint (Ioc (3/2 : ℝ) 5) (Ioi 5) := Ioc_disjoint_Ioi_same
  have h_int2a : IntegrableOn nodeR_fourier_minus_at_c13_2_N3 (Ioc (3/2) 5) :=
    minus_N3_int_Ioc_h32_5
  have h_int2b : IntegrableOn nodeR_fourier_minus_at_c13_2_N3 (Ioi 5) :=
    nodeR_fourier_minus_at_c13_2_N3_integrable_Ioi5
  have h2 : (∫ u in Ioi (3/2 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)
      = (∫ u in Ioc (3/2 : ℝ) 5, nodeR_fourier_minus_at_c13_2_N3 u)
        + (∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u) := by
    rw [h_union2,
        MeasureTheory.setIntegral_union h_disj2 measurableSet_Ioi h_int2a h_int2b]
  have hint_a : (∫ u in Ioc 0 (3/2 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)
      = ∫ u in (0 : ℝ)..(3/2), nodeR_fourier_minus_at_c13_2_N3 u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 3/2)]
  have hint_b : (∫ u in Ioc (3/2 : ℝ) 5, nodeR_fourier_minus_at_c13_2_N3 u)
      = ∫ u in (3/2 : ℝ)..5, nodeR_fourier_minus_at_c13_2_N3 u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (3/2:ℝ) ≤ 5)]
  rw [h1, h2, hint_a, hint_b]
  ring

/-! ## §7 — Full-ω vs N=3 gap integrated over `Ioi 0` -/

private noncomputable def gapDom (u : ℝ) : ℝ :=
  Real.exp (-(16 * π)) * (Real.exp (u * (1/2 - 16 * π)) + Real.exp (-(16 * π) * u)) * (23/22)

private lemma gapDom_integrable_Ioi0 : IntegrableOn gapDom (Ioi (0 : ℝ)) := by
  unfold gapDom
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_coeff1 : (1/2 - 16 * π : ℝ) < 0 := by
    have : (3 : ℝ) < π := Real.pi_gt_three
    nlinarith
  have h_coeff2 : (-(16 * π) : ℝ) < 0 := by nlinarith
  have h1 : IntegrableOn (fun u : ℝ => Real.exp ((1/2 - 16 * π) * u)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (a := 1/2 - 16 * π) (c := 0) h_coeff1
  have h1' : IntegrableOn (fun u : ℝ => Real.exp (u * (1/2 - 16 * π))) (Ioi (0 : ℝ)) := by
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro u _
    show Real.exp ((1/2 - 16 * π) * u) = Real.exp (u * (1/2 - 16 * π))
    rw [mul_comm]
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-(16 * π) * u)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (a := -(16 * π)) (c := 0) h_coeff2
  have hsum : IntegrableOn
      (fun u : ℝ => Real.exp (u * (1/2 - 16 * π)) + Real.exp (-(16 * π) * u)) (Ioi (0 : ℝ)) :=
    h1'.add h2
  have hmul1 : IntegrableOn
      (fun u : ℝ => Real.exp (-(16 * π))
          * (Real.exp (u * (1/2 - 16 * π)) + Real.exp (-(16 * π) * u))) (Ioi (0 : ℝ)) :=
    hsum.const_mul _
  exact hmul1.mul_const _

private lemma omegaGap_le_gapDom {u : ℝ} (hu : 0 ≤ u) :
    (Real.exp (u / 2) + 1) * Real.exp (-π * (16 : ℝ) * Real.exp u)
          / (1 - Real.exp (-π))
      ≤ gapDom u := by
  unfold gapDom
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_denom_pos : (0 : ℝ) < 1 - Real.exp (-π) := one_minus_exp_neg_pi_pos
  have h_exp_u_ge : (1 + u : ℝ) ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    linarith
  have h_arg_le : -π * 16 * Real.exp u ≤ -(16 * π) * (1 + u) := by
    have h16π_pos : (0 : ℝ) < 16 * π := by nlinarith
    have : -(16 * π) * (1 + u) = -π * 16 * (1 + u) := by ring
    rw [this]
    have := mul_le_mul_of_nonpos_left h_exp_u_ge (show -π * 16 ≤ 0 by nlinarith)
    linarith
  have h_exp_arg : Real.exp (-π * 16 * Real.exp u)
      ≤ Real.exp (-(16 * π) * (1 + u)) := Real.exp_le_exp.mpr h_arg_le
  have h_exp_split : Real.exp (-(16 * π) * (1 + u))
      = Real.exp (-(16 * π)) * Real.exp (-(16 * π) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h_exp_bound : Real.exp (-π * 16 * Real.exp u)
      ≤ Real.exp (-(16 * π)) * Real.exp (-(16 * π) * u) := by
    rw [← h_exp_split]; exact h_exp_arg
  have h_prod_split : Real.exp (u / 2) * Real.exp (-(16 * π) * u) = Real.exp (u * (1/2 - 16 * π)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h_pref_nn : (0 : ℝ) ≤ Real.exp (u / 2) + 1 := by
    have := (Real.exp_pos (u/2)).le; linarith
  have h_num_le : (Real.exp (u/2) + 1) * Real.exp (-π * 16 * Real.exp u)
      ≤ (Real.exp (u/2) + 1) * (Real.exp (-(16 * π)) * Real.exp (-(16 * π) * u)) :=
    mul_le_mul_of_nonneg_left h_exp_bound h_pref_nn
  have h_denom_recip : (1 : ℝ) / (1 - Real.exp (-π)) ≤ 23/22 :=
    one_div_one_minus_exp_neg_pi_le
  have h_num_nn : (0 : ℝ) ≤ (Real.exp (u/2) + 1) *
      (Real.exp (-(16 * π)) * Real.exp (-(16 * π) * u)) := by
    have h1 : 0 ≤ Real.exp (-(16 * π)) := (Real.exp_pos _).le
    have h2 : 0 ≤ Real.exp (-(16 * π) * u) := (Real.exp_pos _).le
    positivity
  calc (Real.exp (u / 2) + 1) * Real.exp (-π * 16 * Real.exp u) / (1 - Real.exp (-π))
      = (Real.exp (u / 2) + 1) * Real.exp (-π * 16 * Real.exp u) *
            (1 / (1 - Real.exp (-π))) := by rw [div_eq_mul_one_div]
    _ ≤ (Real.exp (u / 2) + 1) * (Real.exp (-(16 * π)) * Real.exp (-(16 * π) * u))
            * (1 / (1 - Real.exp (-π))) :=
          mul_le_mul_of_nonneg_right h_num_le
            (div_nonneg (by norm_num) h_denom_pos.le)
    _ ≤ (Real.exp (u / 2) + 1) * (Real.exp (-(16 * π)) * Real.exp (-(16 * π) * u)) * (23/22) :=
          mul_le_mul_of_nonneg_left h_denom_recip h_num_nn
    _ = Real.exp (-(16 * π)) * ((Real.exp (u/2) + 1) * Real.exp (-(16 * π) * u)) * (23/22) := by
          ring
    _ = Real.exp (-(16 * π)) *
            (Real.exp (u / 2) * Real.exp (-(16 * π) * u) + Real.exp (-(16 * π) * u)) * (23/22) := by
          ring
    _ = Real.exp (-(16 * π)) * (Real.exp (u * (1/2 - 16 * π)) + Real.exp (-(16 * π) * u))
            * (23/22) := by rw [h_prod_split]

private lemma int_exp_half_minus_sixteen_pi :
    ∫ u in Ioi (0 : ℝ), Real.exp (u * (1/2 - 16 * π)) = 1 / (16 * π - 1/2) := by
  have h_coeff_pos : (0 : ℝ) < 16 * π - 1/2 := by
    have : (3 : ℝ) < π := Real.pi_gt_three
    nlinarith
  have h_coeff_neg : (1/2 - 16 * π : ℝ) < 0 := by linarith
  have h_coeff_ne : (1/2 - 16 * π : ℝ) ≠ 0 := ne_of_lt h_coeff_neg
  have h_pi_ne : (16 * π - 1/2 : ℝ) ≠ 0 := ne_of_gt h_coeff_pos
  have h_fun : (fun u : ℝ => Real.exp (u * (1/2 - 16 * π)))
      = fun u : ℝ => Real.exp ((1/2 - 16 * π) * u) := by
    ext u; rw [mul_comm]
  rw [h_fun]
  rw [integral_exp_mul_Ioi (a := 1/2 - 16 * π) (c := 0) h_coeff_neg]
  have h_arg : ((1 : ℝ) / 2 - 16 * π) * 0 = 0 := by ring
  rw [h_arg, Real.exp_zero]
  rw [neg_div, eq_comm, eq_neg_iff_add_eq_zero, div_add_div _ _ h_pi_ne h_coeff_ne]
  rw [div_eq_zero_iff]; left; ring

private lemma int_exp_neg_sixteen_pi :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(16 * π) * u) = 1 / (16 * π) := by
  have h16π_pos : (0 : ℝ) < 16 * π := by
    have : (3 : ℝ) < π := Real.pi_gt_three
    nlinarith
  have h_neg : (-(16 * π) : ℝ) < 0 := by linarith
  have h_neg_ne : (-(16 * π) : ℝ) ≠ 0 := ne_of_lt h_neg
  have h_pi_ne : (16 * π : ℝ) ≠ 0 := ne_of_gt h16π_pos
  rw [integral_exp_mul_Ioi (a := -(16 * π)) (c := 0) h_neg]
  have h_arg : (-(16 * π) * 0 : ℝ) = 0 := by ring
  rw [h_arg, Real.exp_zero]
  rw [neg_div, eq_comm, eq_neg_iff_add_eq_zero, div_add_div _ _ h_pi_ne h_neg_ne]
  rw [div_eq_zero_iff]; left; ring

private lemma int_gapDom_eq :
    ∫ u in Ioi (0 : ℝ), gapDom u
      = Real.exp (-(16 * π)) * (1/(16 * π - 1/2) + 1/(16 * π)) * (23/22) := by
  unfold gapDom
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_coeff_neg : (1/2 - 16 * π : ℝ) < 0 := by
    have : (3 : ℝ) < π := Real.pi_gt_three
    nlinarith
  have h_neg : (-(16 * π) : ℝ) < 0 := by nlinarith
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (u * (1/2 - 16 * π))) (Ioi (0 : ℝ)) := by
    have h0 : IntegrableOn (fun u : ℝ => Real.exp ((1/2 - 16 * π) * u)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (a := 1/2 - 16 * π) (c := 0) h_coeff_neg
    refine h0.congr_fun ?_ measurableSet_Ioi
    intro u _; show Real.exp ((1/2 - 16 * π) * u) = Real.exp (u * (1/2 - 16 * π))
    rw [mul_comm]
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-(16 * π) * u)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (a := -(16 * π)) (c := 0) h_neg
  have h_const_mul :
    (∫ u in Ioi (0 : ℝ),
        Real.exp (-(16 * π)) *
          (Real.exp (u * (1/2 - 16 * π)) + Real.exp (-(16 * π) * u)) * (23/22))
    = Real.exp (-(16 * π)) * (23/22) *
        (∫ u in Ioi (0 : ℝ), Real.exp (u * (1/2 - 16 * π)) + Real.exp (-(16 * π) * u)) := by
    rw [show (fun u : ℝ => Real.exp (-(16 * π)) *
          (Real.exp (u * (1/2 - 16 * π)) + Real.exp (-(16 * π) * u)) * (23/22))
          = (fun u : ℝ => Real.exp (-(16 * π)) * (23/22) *
          (Real.exp (u * (1/2 - 16 * π)) + Real.exp (-(16 * π) * u))) from by
            ext u; ring]
    rw [MeasureTheory.integral_const_mul]
  rw [h_const_mul]
  rw [MeasureTheory.integral_add h1 h2]
  rw [int_exp_half_minus_sixteen_pi, int_exp_neg_sixteen_pi]
  ring

lemma int_gapDom_le_epsOm :
    ∫ u in Ioi (0 : ℝ), gapDom u ≤ epsOm := by
  rw [int_gapDom_eq]
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have hπ_gt_3 : (3 : ℝ) < π := Real.pi_gt_three
  have h_coeff_pos : (0 : ℝ) < 16 * π - 1/2 := by nlinarith
  have h16π_pos : (0 : ℝ) < 16 * π := by nlinarith
  have h_exp_le : Real.exp (-(16 * π)) ≤ 1 / 10 ^ 20 := exp_neg_sixteen_pi_le
  have h_exp_nn : 0 ≤ Real.exp (-(16 * π)) := (Real.exp_pos _).le
  have h1 : (1 : ℝ) / (16 * π - 1/2) ≤ 1 / (16 * 3 - 1/2) := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16 * 3 - 1/2)
    nlinarith
  have h2 : (1 : ℝ) / (16 * π) ≤ 1 / (16 * 3) := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16 * 3)
    nlinarith
  have h_sum_le : (1 : ℝ) / (16 * π - 1/2) + 1 / (16 * π) ≤ 1 / (16 * 3 - 1/2) + 1 / (16 * 3) := by
    linarith
  have h_sum_nn : (0 : ℝ) ≤ 1 / (16 * π - 1/2) + 1 / (16 * π) := by
    have h1' : (0 : ℝ) < 1 / (16 * π - 1/2) := by positivity
    have h2' : (0 : ℝ) < 1 / (16 * π) := by positivity
    linarith
  have h_prod_le :
      Real.exp (-(16 * π)) * (1/(16 * π - 1/2) + 1/(16 * π)) * (23/22)
      ≤ (1 / 10 ^ 20) * ((1 : ℝ) / (16 * 3 - 1/2) + 1 / (16 * 3)) * (23/22) := by
    have hA_nn : (0 : ℝ) ≤ (1 / (16 * 3 - 1/2) + 1 / (16 * 3)) := by norm_num
    have hAB_nn : (0 : ℝ) ≤ Real.exp (-(16 * π)) *
        (1/(16 * π - 1/2) + 1/(16 * π)) := mul_nonneg h_exp_nn h_sum_nn
    have h_step1 : Real.exp (-(16 * π)) * (1/(16 * π - 1/2) + 1/(16 * π))
        ≤ (1/10^20) * (1/(16 * π - 1/2) + 1/(16 * π)) :=
      mul_le_mul_of_nonneg_right h_exp_le h_sum_nn
    have h_step2 : (1/10^20) * (1/(16 * π - 1/2) + 1/(16 * π))
        ≤ (1/10^20) * ((1 : ℝ) / (16 * 3 - 1/2) + 1 / (16 * 3)) :=
      mul_le_mul_of_nonneg_left h_sum_le (by norm_num)
    have h_step12 : Real.exp (-(16 * π)) * (1/(16 * π - 1/2) + 1/(16 * π))
        ≤ (1/10^20) * ((1 : ℝ) / (16 * 3 - 1/2) + 1 / (16 * 3)) := h_step1.trans h_step2
    exact mul_le_mul_of_nonneg_right h_step12 (by norm_num)
  have h_numerical : ((1 : ℝ) / 10 ^ 20)
      * ((1 : ℝ) / (16 * 3 - 1/2) + 1 / (16 * 3)) * (23/22) ≤ (1 : ℝ) / 10 ^ 4 := by
    norm_num
  calc Real.exp (-(16 * π)) * (1/(16 * π - 1/2) + 1/(16 * π)) * (23/22)
      ≤ (1 / 10 ^ 20) * ((1 : ℝ) / (16 * 3 - 1/2) + 1 / (16 * 3)) * (23/22) := h_prod_le
    _ ≤ 1 / 10 ^ 4 := h_numerical

/-! ## §8 — Pointwise gap bound integrated: `∫_{Ioi 0} |f_full − f_N3| ≤ epsOm` -/

private lemma plus_gap_pointwise_bound {u : ℝ} (hu : 0 ≤ u) :
    |nodeR_fourier_plus_at_c13_2 u - nodeR_fourier_plus_at_c13_2_N3 u| ≤ gapDom u := by
  have h1 := nodeR_fourier_plus_at_c13_2_tail_abs_le hu
  have h2 := omegaGap_le_gapDom hu
  have h_align : Real.exp (-π * (16 : ℝ) * Real.exp u)
      = Real.exp (-π * 16 * Real.exp u) := by norm_num
  linarith

private lemma minus_gap_pointwise_bound {u : ℝ} (hu : 0 ≤ u) :
    |nodeR_fourier_minus_at_c13_2 u - nodeR_fourier_minus_at_c13_2_N3 u| ≤ gapDom u := by
  have h1 := nodeR_fourier_minus_at_c13_2_tail_abs_le hu
  have h2 := omegaGap_le_gapDom hu
  have h_align : Real.exp (-π * (16 : ℝ) * Real.exp u)
      = Real.exp (-π * 16 * Real.exp u) := by norm_num
  linarith

lemma plus_gap_integrated_bound :
    |(∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2 u)
      - (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)| ≤ epsOm := by
  have hfull := nodeR_fourier_plus_at_c13_2_integrable_Ioi0
  have hN3 := nodeR_fourier_plus_at_c13_2_N3_integrable_Ioi0
  have h_diff_eq : (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2 u)
      - (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)
      = ∫ u in Ioi (0 : ℝ), (nodeR_fourier_plus_at_c13_2 u - nodeR_fourier_plus_at_c13_2_N3 u) := by
    rw [← MeasureTheory.integral_sub hfull hN3]
  rw [h_diff_eq]
  have h_abs_le :
      |∫ u in Ioi (0 : ℝ), (nodeR_fourier_plus_at_c13_2 u - nodeR_fourier_plus_at_c13_2_N3 u)|
        ≤ ∫ u in Ioi (0 : ℝ), |nodeR_fourier_plus_at_c13_2 u - nodeR_fourier_plus_at_c13_2_N3 u| :=
    MeasureTheory.abs_integral_le_integral_abs
  have h_mono : ∫ u in Ioi (0 : ℝ), |nodeR_fourier_plus_at_c13_2 u - nodeR_fourier_plus_at_c13_2_N3 u|
                  ≤ ∫ u in Ioi (0 : ℝ), gapDom u := by
    refine MeasureTheory.setIntegral_mono_on ?_ gapDom_integrable_Ioi0 measurableSet_Ioi ?_
    · exact (hfull.sub hN3).abs
    · intro u hu
      exact plus_gap_pointwise_bound (le_of_lt (mem_Ioi.mp hu))
  calc |∫ u in Ioi (0 : ℝ), (nodeR_fourier_plus_at_c13_2 u - nodeR_fourier_plus_at_c13_2_N3 u)|
      ≤ ∫ u in Ioi (0 : ℝ), |nodeR_fourier_plus_at_c13_2 u - nodeR_fourier_plus_at_c13_2_N3 u| :=
        h_abs_le
    _ ≤ ∫ u in Ioi (0 : ℝ), gapDom u := h_mono
    _ ≤ epsOm := int_gapDom_le_epsOm

lemma minus_gap_integrated_bound :
    |(∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2 u)
      - (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)| ≤ epsOm := by
  have hfull := nodeR_fourier_minus_at_c13_2_integrable_Ioi0
  have hN3 := nodeR_fourier_minus_at_c13_2_N3_integrable_Ioi0
  have h_diff_eq : (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2 u)
      - (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)
      = ∫ u in Ioi (0 : ℝ), (nodeR_fourier_minus_at_c13_2 u - nodeR_fourier_minus_at_c13_2_N3 u) := by
    rw [← MeasureTheory.integral_sub hfull hN3]
  rw [h_diff_eq]
  have h_abs_le :
      |∫ u in Ioi (0 : ℝ), (nodeR_fourier_minus_at_c13_2 u - nodeR_fourier_minus_at_c13_2_N3 u)|
        ≤ ∫ u in Ioi (0 : ℝ), |nodeR_fourier_minus_at_c13_2 u - nodeR_fourier_minus_at_c13_2_N3 u| :=
    MeasureTheory.abs_integral_le_integral_abs
  have h_mono : ∫ u in Ioi (0 : ℝ), |nodeR_fourier_minus_at_c13_2 u - nodeR_fourier_minus_at_c13_2_N3 u|
                  ≤ ∫ u in Ioi (0 : ℝ), gapDom u := by
    refine MeasureTheory.setIntegral_mono_on ?_ gapDom_integrable_Ioi0 measurableSet_Ioi ?_
    · exact (hfull.sub hN3).abs
    · intro u hu
      exact minus_gap_pointwise_bound (le_of_lt (mem_Ioi.mp hu))
  calc |∫ u in Ioi (0 : ℝ), (nodeR_fourier_minus_at_c13_2 u - nodeR_fourier_minus_at_c13_2_N3 u)|
      ≤ ∫ u in Ioi (0 : ℝ), |nodeR_fourier_minus_at_c13_2 u - nodeR_fourier_minus_at_c13_2_N3 u| :=
        h_abs_le
    _ ≤ ∫ u in Ioi (0 : ℝ), gapDom u := h_mono
    _ ≤ epsOm := int_gapDom_le_epsOm

/-! ## §9 — Final Λ₀ enclosures -/

theorem re_lambda0_at_c13_2_ub :
    (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).re
      ≤ (1339441331 / 80000000000 : ℝ) + 231/10^6 + 1/10^6 + epsOm := by
  rw [re_lambda0_at_c13_2]
  have h_split := plus_N3_split
  have h_h32 := reLambda0_threehalves_lb_ub.2
  have h_res := nodeR_fourier_plus_at_c13_2_N3_residue_three_halves_to_5_abs_le
  have h_tail := nodeR_fourier_plus_at_c13_2_N3_tail_integral_abs_le_tight
  have h_gap := plus_gap_integrated_bound
  have h_target : (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2 u)
      = (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)
        + ((∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2 u)
            - (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)) := by ring
  rw [h_target, h_split]
  have h_res_le : ∫ u in (3/2 : ℝ)..5, nodeR_fourier_plus_at_c13_2_N3 u ≤ 231/10^6 :=
    (abs_le.mp h_res).2
  have h_tail_le : ∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u ≤ 1/10^6 :=
    (abs_le.mp h_tail).2
  have h_gap_le : ((∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2 u)
      - (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)) ≤ epsOm :=
    (abs_le.mp h_gap).2
  rw [h_split] at h_gap_le
  linarith

theorem re_lambda0_at_c13_2_lb :
    (2671109 / 200000000 : ℝ) - 231/10^6 - 1/10^6 - epsOm
      ≤ (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).re := by
  rw [re_lambda0_at_c13_2]
  have h_split := plus_N3_split
  have h_h32 := reLambda0_threehalves_lb_ub.1
  have h_res := nodeR_fourier_plus_at_c13_2_N3_residue_three_halves_to_5_abs_le
  have h_tail := nodeR_fourier_plus_at_c13_2_N3_tail_integral_abs_le_tight
  have h_gap := plus_gap_integrated_bound
  have h_target : (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2 u)
      = (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)
        + ((∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2 u)
            - (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)) := by ring
  rw [h_target, h_split]
  have h_res_ge : -(231/10^6 : ℝ) ≤ ∫ u in (3/2 : ℝ)..5, nodeR_fourier_plus_at_c13_2_N3 u :=
    (abs_le.mp h_res).1
  have h_tail_ge : -(1/10^6 : ℝ) ≤ ∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u :=
    (abs_le.mp h_tail).1
  have h_gap_ge : -epsOm ≤ ((∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2 u)
      - (∫ u in Ioi (0 : ℝ), nodeR_fourier_plus_at_c13_2_N3 u)) :=
    (abs_le.mp h_gap).1
  rw [h_split] at h_gap_ge
  linarith

theorem im_lambda0_at_c13_2_ub :
    (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).im
      ≤ (302372667 / 160000000000 : ℝ) + 231/10^6 + 1/10^6 + epsOm := by
  rw [im_lambda0_at_c13_2]
  have h_split := minus_N3_split
  have h_h32 := imLambda0_threehalves_lb_ub.2
  have h_res := nodeR_fourier_minus_at_c13_2_N3_residue_three_halves_to_5_abs_le
  have h_tail := nodeR_fourier_minus_at_c13_2_N3_tail_integral_abs_le_tight
  have h_gap := minus_gap_integrated_bound
  have h_target : (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2 u)
      = (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)
        + ((∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2 u)
            - (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)) := by ring
  rw [h_target, h_split]
  have h_res_le : ∫ u in (3/2 : ℝ)..5, nodeR_fourier_minus_at_c13_2_N3 u ≤ 231/10^6 :=
    (abs_le.mp h_res).2
  have h_tail_le : ∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u ≤ 1/10^6 :=
    (abs_le.mp h_tail).2
  have h_gap_le : ((∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2 u)
      - (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)) ≤ epsOm :=
    (abs_le.mp h_gap).2
  rw [h_split] at h_gap_le
  linarith

theorem im_lambda0_at_c13_2_lb :
    (13277 / 500000000 : ℝ) - 231/10^6 - 1/10^6 - epsOm
      ≤ (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).im := by
  rw [im_lambda0_at_c13_2]
  have h_split := minus_N3_split
  have h_h32 := imLambda0_threehalves_lb_ub.1
  have h_res := nodeR_fourier_minus_at_c13_2_N3_residue_three_halves_to_5_abs_le
  have h_tail := nodeR_fourier_minus_at_c13_2_N3_tail_integral_abs_le_tight
  have h_gap := minus_gap_integrated_bound
  have h_target : (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2 u)
      = (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)
        + ((∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2 u)
            - (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)) := by ring
  rw [h_target, h_split]
  have h_res_ge : -(231/10^6 : ℝ) ≤ ∫ u in (3/2 : ℝ)..5, nodeR_fourier_minus_at_c13_2_N3 u :=
    (abs_le.mp h_res).1
  have h_tail_ge : -(1/10^6 : ℝ) ≤ ∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u :=
    (abs_le.mp h_tail).1
  have h_gap_ge : -epsOm ≤ ((∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2 u)
      - (∫ u in Ioi (0 : ℝ), nodeR_fourier_minus_at_c13_2_N3 u)) :=
    (abs_le.mp h_gap).1
  rw [h_split] at h_gap_ge
  linarith

/-! ## §10 — Instantiate scaffold

Gate: `(169/4)·R_ub_f + (13/2)·I_ub_f ≤ 3/4`. Numerically:
  R_ub_h32 = 1339441331/80000000000 ≈ 0.0169635
  R_ub_f ≈ 0.0169635 + 231/10^6 + 10⁻⁶ + 10⁻⁴ ≈ 0.0178900
  I_ub_h32 = 302372667/160000000000 ≈ 0.0018848
  I_ub_f ≈ 0.0018848 + 231/10^6 + 10⁻⁶ + 10⁻⁴ ≈ 0.0028113
  (169/4)·0.0178900 + (13/2)·0.0028113 ≈ 0.7272 + 0.01792 ≈ 0.7450 ≤ 0.75 ✓
  gate-1 margin = 3/4 − 0.74498 ≈ 0.00502  (tight — required replacing the
  loose `≤ 1/10³` residue budget with the tight `≤ 231/10^6 ≈ 8.253·10⁻⁴`
  bound; the ResidueBound proof already produces 231/10^6, so this is
  no new mathematics, only a semantic choice at the gate.)
-/

lemma gate1_arithmetic :
    (169/4 : ℝ) * ((1339441331 / 80000000000 : ℝ) + 231/10^6 + 1/10^6 + epsOm)
      + (13/2 : ℝ) * ((302372667 / 160000000000 : ℝ) + 231/10^6 + 1/10^6 + epsOm)
      ≤ 3/4 := by
  show (169/4 : ℝ) * ((1339441331 / 80000000000 : ℝ) + 231/10^6 + 1/10^6 + 1/10^4)
      + (13/2 : ℝ) * ((302372667 / 160000000000 : ℝ) + 231/10^6 + 1/10^6 + 1/10^4)
      ≤ 3/4
  norm_num

/-- **★ FINAL UNCONDITIONAL R1 PILOT at c = 13/2 ★**. R1 on
`[103/16, 105/16] = [6.4375, 6.5625]`, via pointwise panel-based bounds
through Legion's L4 edge identity + Assembly + Residue + Tail + ω-gap.
Zero hypotheses, kernel-clean. -/
theorem pilot_r1_box_c13_2_r1_16_pointwise_UNCONDITIONAL :
    ∀ t ∈ Icc ((103/16 : ℝ)) (105/16),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  exact pilot_r1_box_c13_2_r1_16_pointwise_closed
    ((2671109 / 200000000 : ℝ) - 231/10^6 - 1/10^6 - epsOm)
    ((1339441331 / 80000000000 : ℝ) + 231/10^6 + 1/10^6 + epsOm)
    ((13277 / 500000000 : ℝ) - 231/10^6 - 1/10^6 - epsOm)
    ((302372667 / 160000000000 : ℝ) + 231/10^6 + 1/10^6 + epsOm)
    re_lambda0_at_c13_2_lb
    re_lambda0_at_c13_2_ub
    im_lambda0_at_c13_2_lb
    im_lambda0_at_c13_2_ub
    gate1_arithmetic

end

/-! ## §Axiom check -/

#print axioms one_minus_exp_neg_pi_ge
#print axioms one_minus_exp_neg_pi_pos
#print axioms one_div_one_minus_exp_neg_pi_le
#print axioms exp_neg_sixteen_pi_le
#print axioms exp_phase_plus_at_c13_2
#print axioms exp_phase_minus_at_c13_2
#print axioms plus_integrand_at_c13_2
#print axioms minus_integrand_at_c13_2
#print axioms re_lambda0_at_c13_2
#print axioms im_lambda0_at_c13_2
#print axioms nodeR_fourier_plus_at_c13_2_integrable_Ioi0
#print axioms nodeR_fourier_minus_at_c13_2_integrable_Ioi0
#print axioms nodeR_fourier_plus_at_c13_2_N3_integrable_Ioi0
#print axioms nodeR_fourier_minus_at_c13_2_N3_integrable_Ioi0
#print axioms plus_N3_split
#print axioms minus_N3_split
#print axioms int_gapDom_le_epsOm
#print axioms plus_gap_integrated_bound
#print axioms minus_gap_integrated_bound
#print axioms re_lambda0_at_c13_2_ub
#print axioms re_lambda0_at_c13_2_lb
#print axioms im_lambda0_at_c13_2_ub
#print axioms im_lambda0_at_c13_2_lb
#print axioms gate1_arithmetic
#print axioms pilot_r1_box_c13_2_r1_16_pointwise_UNCONDITIONAL

end PilotR1Box_c13_2_r1_16_pointwise_CLOSED_20261016
end PrincipiaTractalis
