/-
# r331b — CERTIFIED T=15 TOP EDGE + XI RECTANGLE BOUNDARY ZERO-FREE

★ 2026-08-26.  Stage 2 of the r331 chain (in progress).

## Route

Per the r331 directive: reuse r312's cpow polar-decomposition pattern
generically → derive Re/Im Λ₀ real forms at s = σ + it →
integrand pointwise interval enclosure via r331a's σ-endpoint monotone
rpow bounds + trigonometric endpoint values → σ-box `BoxRe/ImEnclosure`
witnesses → r331a consumers → `top15_re_lt_neg_1e4` → `H_TOP_proved` →
`xi_T15_boundary_zero_free` → `xi_T15_exact_zero_count_identity_unconditional`.

## Status

WORKING MODULE — not landed until the full endpoint chain lands.
See file header of shipped r331b for the completed landing.

SPDX-License-Identifier: Apache-2.0
-/
import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannXiSymmetries_r326
import PF.Analytic.RiemannXiRectangleCount_r327
import PF.Analytic.RiemannXiBoundaryT15_r328
import PF.Analytic.RiemannXiBottomEdgeUnconditional_r329b
import PF.Analytic.RiemannXiThetaBoxEnclosure_r331a
import PF.Analytic.XiThetaIntegral
import PF.Analytic.XiQuadrature

open Complex Set Topology Filter MeasureTheory
open scoped ComplexConjugate Real
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.RiemannXiRectangleCount
open PrincipiaTractalis.RiemannXiBoundaryT15
open PrincipiaTractalis.RiemannXiBottomEdgeUnconditional
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open HurwitzZeta

noncomputable section

namespace PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes

/-! ## §1 — Generic cpow polar decomposition at real positive base

Copies the r312 proof pattern
(`cpow_at_q_minus_one_re / _im` at fixed `q - 1 = ⟨-3/4, 15/2⟩`) and
generalizes to arbitrary complex exponent `⟨a, b⟩`.

For `y > 0`:
`((y : ℂ)^(⟨a, b⟩ : ℂ)).re = y^a · cos(b · log y)`
`((y : ℂ)^(⟨a, b⟩ : ℂ)).im = y^a · sin(b · log y)`. -/

theorem cpow_ofReal_re {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    ((y : ℂ) ^ (⟨a, b⟩ : ℂ)).re = y ^ a * Real.cos (b * Real.log y) := by
  have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [Complex.cpow_def_of_ne_zero hy_ne, ← Complex.ofReal_log hy.le, Complex.exp_re]
  have h_prod_re : ((Real.log y : ℂ) * (⟨a, b⟩ : ℂ)).re = a * Real.log y := by
    show (((Real.log y : ℝ) : ℂ) * (⟨a, b⟩ : ℂ)).re = a * Real.log y
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have h_prod_im : ((Real.log y : ℂ) * (⟨a, b⟩ : ℂ)).im = b * Real.log y := by
    show (((Real.log y : ℝ) : ℂ) * (⟨a, b⟩ : ℂ)).im = b * Real.log y
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring
  rw [h_prod_re, h_prod_im]
  congr 1
  rw [show a * Real.log y = Real.log y * a from mul_comm _ _,
      ← Real.rpow_def_of_pos hy]

theorem cpow_ofReal_im {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    ((y : ℂ) ^ (⟨a, b⟩ : ℂ)).im = y ^ a * Real.sin (b * Real.log y) := by
  have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [Complex.cpow_def_of_ne_zero hy_ne, ← Complex.ofReal_log hy.le, Complex.exp_im]
  have h_prod_re : ((Real.log y : ℂ) * (⟨a, b⟩ : ℂ)).re = a * Real.log y := by
    show (((Real.log y : ℝ) : ℂ) * (⟨a, b⟩ : ℂ)).re = a * Real.log y
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have h_prod_im : ((Real.log y : ℂ) * (⟨a, b⟩ : ℂ)).im = b * Real.log y := by
    show (((Real.log y : ℝ) : ℂ) * (⟨a, b⟩ : ℂ)).im = b * Real.log y
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring
  rw [h_prod_re, h_prod_im]
  congr 1
  rw [show a * Real.log y = Real.log y * a from mul_comm _ _,
      ← Real.rpow_def_of_pos hy]

/-! ## §2 — Λ₀ theta-integral exponent decomposition -/

/-- `(σ + i·t)/2 - 1 = ⟨σ/2 - 1, t/2⟩` at real σ, t. -/
lemma exponent_a_eq (σ t : ℝ) :
    ((⟨σ, t⟩ : ℂ)) / 2 - 1 = (⟨σ/2 - 1, t/2⟩ : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
          Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
          Complex.normSq_ofNat]

/-- `(1 - (σ + i·t))/2 - 1 = ⟨(1-σ)/2 - 1, -t/2⟩` at real σ, t. -/
lemma exponent_b_eq (σ t : ℝ) :
    ((1 : ℂ) - (⟨σ, t⟩ : ℂ)) / 2 - 1 = (⟨(1-σ)/2 - 1, -(t/2)⟩ : ℂ) := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.div_re, Complex.one_re, Complex.mul_re,
          Complex.normSq_ofNat]
  · simp [Complex.sub_im, Complex.div_im, Complex.one_im, Complex.mul_im,
          Complex.normSq_ofNat]
    ring

/-! ## §3 — Pointwise real form of the theta integrand -/

/-- Real integrand for Re Λ₀(σ+it) via §1-2. -/
def realThetaReIntegrand (σ t u : ℝ) : ℝ :=
  (u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1)) * Real.cos ((t / 2) * Real.log u) * omega u

/-- Real integrand for Im Λ₀(σ+it). -/
def realThetaImIntegrand (σ t u : ℝ) : ℝ :=
  (u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1)) * Real.sin ((t / 2) * Real.log u) * omega u

/-- Pointwise Re of the complex theta integrand at real (σ, t) and u > 0. -/
theorem theta_integrand_re_pointwise (σ t u : ℝ) (hu : 0 < u) :
    (((u : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)
      + (u : ℂ) ^ (((1 : ℂ) - (⟨σ, t⟩ : ℂ)) / 2 - 1))
        * ((omega u : ℝ) : ℂ)).re
      = realThetaReIntegrand σ t u := by
  rw [exponent_a_eq, exponent_b_eq]
  set A := (u : ℂ) ^ (⟨σ/2 - 1, t/2⟩ : ℂ) with hA
  set B := (u : ℂ) ^ (⟨(1-σ)/2 - 1, -(t/2)⟩ : ℂ) with hB
  set W : ℂ := ((omega u : ℝ) : ℂ) with hW
  -- Compute .re / .im of A, B, W
  have hA_re : A.re = u ^ (σ/2 - 1) * Real.cos ((t/2) * Real.log u) :=
    cpow_ofReal_re hu (σ/2 - 1) (t/2)
  have hA_im : A.im = u ^ (σ/2 - 1) * Real.sin ((t/2) * Real.log u) :=
    cpow_ofReal_im hu (σ/2 - 1) (t/2)
  have hB_re : B.re = u ^ ((1-σ)/2 - 1) * Real.cos ((-(t/2)) * Real.log u) :=
    cpow_ofReal_re hu ((1-σ)/2 - 1) (-(t/2))
  have hB_im : B.im = u ^ ((1-σ)/2 - 1) * Real.sin ((-(t/2)) * Real.log u) :=
    cpow_ofReal_im hu ((1-σ)/2 - 1) (-(t/2))
  have hW_re : W.re = omega u := by simp [hW, Complex.ofReal_re]
  have hW_im : W.im = 0 := by simp [hW, Complex.ofReal_im]
  have hcos_neg : Real.cos ((-(t/2)) * Real.log u) = Real.cos ((t/2) * Real.log u) := by
    rw [neg_mul, Real.cos_neg]
  have hsin_neg : Real.sin ((-(t/2)) * Real.log u) = -Real.sin ((t/2) * Real.log u) := by
    rw [neg_mul, Real.sin_neg]
  show ((A + B) * W).re = _
  rw [Complex.mul_re, Complex.add_re, Complex.add_im, hA_re, hB_re, hA_im, hB_im,
      hW_re, hW_im, hcos_neg, hsin_neg]
  unfold realThetaReIntegrand
  ring

/-- Pointwise Im of the complex theta integrand at real (σ, t) and u > 0. -/
theorem theta_integrand_im_pointwise (σ t u : ℝ) (hu : 0 < u) :
    (((u : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)
      + (u : ℂ) ^ (((1 : ℂ) - (⟨σ, t⟩ : ℂ)) / 2 - 1))
        * ((omega u : ℝ) : ℂ)).im
      = realThetaImIntegrand σ t u := by
  rw [exponent_a_eq, exponent_b_eq]
  set A := (u : ℂ) ^ (⟨σ/2 - 1, t/2⟩ : ℂ) with hA
  set B := (u : ℂ) ^ (⟨(1-σ)/2 - 1, -(t/2)⟩ : ℂ) with hB
  set W : ℂ := ((omega u : ℝ) : ℂ) with hW
  have hA_re : A.re = u ^ (σ/2 - 1) * Real.cos ((t/2) * Real.log u) :=
    cpow_ofReal_re hu (σ/2 - 1) (t/2)
  have hA_im : A.im = u ^ (σ/2 - 1) * Real.sin ((t/2) * Real.log u) :=
    cpow_ofReal_im hu (σ/2 - 1) (t/2)
  have hB_re : B.re = u ^ ((1-σ)/2 - 1) * Real.cos ((-(t/2)) * Real.log u) :=
    cpow_ofReal_re hu ((1-σ)/2 - 1) (-(t/2))
  have hB_im : B.im = u ^ ((1-σ)/2 - 1) * Real.sin ((-(t/2)) * Real.log u) :=
    cpow_ofReal_im hu ((1-σ)/2 - 1) (-(t/2))
  have hW_re : W.re = omega u := by simp [hW, Complex.ofReal_re]
  have hW_im : W.im = 0 := by simp [hW, Complex.ofReal_im]
  have hcos_neg : Real.cos ((-(t/2)) * Real.log u) = Real.cos ((t/2) * Real.log u) := by
    rw [neg_mul, Real.cos_neg]
  have hsin_neg : Real.sin ((-(t/2)) * Real.log u) = -Real.sin ((t/2) * Real.log u) := by
    rw [neg_mul, Real.sin_neg]
  show ((A + B) * W).im = _
  rw [Complex.mul_im, Complex.add_re, Complex.add_im, hA_re, hB_re, hA_im, hB_im,
      hW_re, hW_im, hcos_neg, hsin_neg]
  unfold realThetaImIntegrand
  ring

/-! ## §4 — Absolute bounds for the real integrands -/

/-- `|realThetaReIntegrand σ t u| ≤ 2·ω(u)` for σ ∈ [0, 1], u ≥ 1. -/
lemma abs_realThetaReIntegrand_le_two_omega {σ t u : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hu : 1 ≤ u) :
    |realThetaReIntegrand σ t u| ≤ 2 * omega u := by
  unfold realThetaReIntegrand
  have hu0 : 0 ≤ u := le_trans zero_le_one hu
  have hpow1_nn : 0 ≤ u ^ (σ / 2 - 1) := Real.rpow_nonneg hu0 _
  have hpow2_nn : 0 ≤ u ^ ((1 - σ) / 2 - 1) := Real.rpow_nonneg hu0 _
  have hpow1_le : u ^ (σ / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hpow2_le : u ^ ((1 - σ) / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hcos_abs : |Real.cos ((t / 2) * Real.log u)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hω_nn : 0 ≤ omega u := omega_nonneg u
  have hsum_nn : 0 ≤ u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1) := by linarith
  have hsum_le : u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1) ≤ 2 := by linarith
  rw [abs_mul, abs_mul, abs_of_nonneg hω_nn, abs_of_nonneg hsum_nn]
  calc (u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1))
        * |Real.cos ((t / 2) * Real.log u)| * omega u
      ≤ 2 * 1 * omega u := by
        apply mul_le_mul (mul_le_mul hsum_le hcos_abs (abs_nonneg _) (by linarith))
          le_rfl hω_nn (by positivity)
    _ = 2 * omega u := by ring

/-- `|realThetaImIntegrand σ t u| ≤ 2·ω(u)` for σ ∈ [0, 1], u ≥ 1. -/
lemma abs_realThetaImIntegrand_le_two_omega {σ t u : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hu : 1 ≤ u) :
    |realThetaImIntegrand σ t u| ≤ 2 * omega u := by
  unfold realThetaImIntegrand
  have hu0 : 0 ≤ u := le_trans zero_le_one hu
  have hpow1_nn : 0 ≤ u ^ (σ / 2 - 1) := Real.rpow_nonneg hu0 _
  have hpow2_nn : 0 ≤ u ^ ((1 - σ) / 2 - 1) := Real.rpow_nonneg hu0 _
  have hpow1_le : u ^ (σ / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hpow2_le : u ^ ((1 - σ) / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hsin_abs : |Real.sin ((t / 2) * Real.log u)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hω_nn : 0 ≤ omega u := omega_nonneg u
  have hdiff_abs_le : |u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1)| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_mul, abs_of_nonneg hω_nn]
  calc |u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1)|
        * |Real.sin ((t / 2) * Real.log u)| * omega u
      ≤ 2 * 1 * omega u := by
        apply mul_le_mul (mul_le_mul hdiff_abs_le hsin_abs (abs_nonneg _) (by linarith))
          le_rfl hω_nn (by positivity)
    _ = 2 * omega u := by ring

/-! ## §5 — Continuity + real integrability of the two real integrands -/

lemma continuousOn_realThetaReIntegrand (σ t : ℝ) :
    ContinuousOn (realThetaReIntegrand σ t) (Ioi (1 : ℝ)) := by
  unfold realThetaReIntegrand
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; left; linarith [(mem_Ioi.mp hu)]
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; left; linarith [(mem_Ioi.mp hu)]
  · -- cos((t/2) · log u) is continuous on Ioi 1 (log continuous, cos continuous)
    refine Real.continuous_cos.comp_continuousOn ?_
    refine continuousOn_const.mul ?_
    exact Real.continuousOn_log.mono (fun u hu => ne_of_gt (lt_trans zero_lt_one
      (mem_Ioi.mp hu)))
  · exact continuousOn_omega.mono (fun u hu => lt_trans zero_lt_one (mem_Ioi.mp hu))

lemma continuousOn_realThetaImIntegrand (σ t : ℝ) :
    ContinuousOn (realThetaImIntegrand σ t) (Ioi (1 : ℝ)) := by
  unfold realThetaImIntegrand
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; left; linarith [(mem_Ioi.mp hu)]
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; left; linarith [(mem_Ioi.mp hu)]
  · refine Real.continuous_sin.comp_continuousOn ?_
    refine continuousOn_const.mul ?_
    exact Real.continuousOn_log.mono (fun u hu => ne_of_gt (lt_trans zero_lt_one
      (mem_Ioi.mp hu)))
  · exact continuousOn_omega.mono (fun u hu => lt_trans zero_lt_one (mem_Ioi.mp hu))

lemma integrableOn_realThetaReIntegrand_Icc {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (t : ℝ) :
    IntegrableOn (realThetaReIntegrand σ t) (Ioi (1 : ℝ)) := by
  refine MeasureTheory.Integrable.mono integrableOn_two_omega ?_ ?_
  · exact (continuousOn_realThetaReIntegrand σ t).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have h_abs := abs_realThetaReIntegrand_le_two_omega (t := t) h0 h1 hu1
    have hω_nn : 0 ≤ omega u := omega_nonneg u
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * omega u)]
    exact h_abs

lemma integrableOn_realThetaImIntegrand_Icc {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (t : ℝ) :
    IntegrableOn (realThetaImIntegrand σ t) (Ioi (1 : ℝ)) := by
  refine MeasureTheory.Integrable.mono integrableOn_two_omega ?_ ?_
  · exact (continuousOn_realThetaImIntegrand σ t).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have h_abs := abs_realThetaImIntegrand_le_two_omega (t := t) h0 h1 hu1
    have hω_nn : 0 ≤ omega u := omega_nonneg u
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * omega u)]
    exact h_abs

/-! ## §6 — Reconstruct complex integrand from Re + Im -/

/-- Pointwise on `u > 0`: the complex theta integrand equals its real
integrand cast to ℂ plus `I` times the imaginary integrand cast to ℂ.

Direct consequence of §3 (Re/Im pointwise) + `Complex.ext`. -/
theorem complex_theta_integrand_eq_re_add_I_im (σ t u : ℝ) (hu : 0 < u) :
    ((u : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)
        + (u : ℂ) ^ (((1 : ℂ) - (⟨σ, t⟩ : ℂ)) / 2 - 1))
        * ((omega u : ℝ) : ℂ)
      = ((realThetaReIntegrand σ t u : ℝ) : ℂ)
          + ((realThetaImIntegrand σ t u : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [theta_integrand_re_pointwise σ t u hu]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  · rw [theta_integrand_im_pointwise σ t u hu]
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]

/-- Integrability of the complex theta integrand on Ioi 1 for σ ∈ [0, 1],
reconstructed from real integrability of the Re and Im parts. -/
lemma complex_theta_integrand_integrableOn_Icc {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (t : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        ((u : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)
          + (u : ℂ) ^ (((1 : ℂ) - (⟨σ, t⟩ : ℂ)) / 2 - 1))
          * ((omega u : ℝ) : ℂ))
      (Ioi (1 : ℝ)) := by
  have hRe := integrableOn_realThetaReIntegrand_Icc h0 h1 t
  have hIm := integrableOn_realThetaImIntegrand_Icc h0 h1 t
  -- ofReal cast is integrable (via linear isometry)
  have hRe_c : IntegrableOn
      (fun u : ℝ => ((realThetaReIntegrand σ t u : ℝ) : ℂ)) (Ioi (1 : ℝ)) :=
    hRe.ofReal
  have hIm_c : IntegrableOn
      (fun u : ℝ => ((realThetaImIntegrand σ t u : ℝ) : ℂ)) (Ioi (1 : ℝ)) :=
    hIm.ofReal
  have hIm_I : IntegrableOn
      (fun u : ℝ => ((realThetaImIntegrand σ t u : ℝ) : ℂ) * Complex.I)
      (Ioi (1 : ℝ)) :=
    hIm_c.mul_const Complex.I
  have hSum : IntegrableOn
      (fun u : ℝ =>
        ((realThetaReIntegrand σ t u : ℝ) : ℂ)
          + ((realThetaImIntegrand σ t u : ℝ) : ℂ) * Complex.I)
      (Ioi (1 : ℝ)) := hRe_c.add hIm_I
  refine hSum.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  refine Filter.Eventually.of_forall fun u hu => ?_
  exact (complex_theta_integrand_eq_re_add_I_im σ t u
      (lt_trans zero_lt_one (mem_Ioi.mp hu))).symm

/-! ## §7 — Re/Im Λ₀ closed real integral forms for σ ∈ [0, 1] -/

/-- Λ₀ real form via the Re + Im reconstruction of the complex integrand.
Uses `integral_add` + `integral_ofReal` + `integral_mul_const` to reduce the
complex integral to a real integral pair. -/
theorem Lambda0_eq_real_add_I_real_integral_Icc {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (t : ℝ) :
    completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)
      = (((∫ u in Ioi (1 : ℝ), realThetaReIntegrand σ t u) : ℝ) : ℂ)
        + (((∫ u in Ioi (1 : ℝ), realThetaImIntegrand σ t u) : ℝ) : ℂ) * Complex.I := by
  rw [completedRiemannZeta₀_eq_theta_integral]
  -- Rewrite complex integrand as sum of ((real : ℝ) : ℂ) forms a.e.
  have h_ae : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (1 : ℝ))),
      ((u : ℂ) ^ ((⟨σ, t⟩ : ℂ) / 2 - 1)
        + (u : ℂ) ^ (((1 : ℂ) - (⟨σ, t⟩ : ℂ)) / 2 - 1))
        * ((omega u : ℝ) : ℂ)
      = ((realThetaReIntegrand σ t u : ℝ) : ℂ)
        + ((realThetaImIntegrand σ t u : ℝ) : ℂ) * Complex.I := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall fun u hu => ?_
    exact complex_theta_integrand_eq_re_add_I_im σ t u
      (lt_trans zero_lt_one (mem_Ioi.mp hu))
  rw [MeasureTheory.integral_congr_ae h_ae]
  -- Integrable pieces
  have hRe := integrableOn_realThetaReIntegrand_Icc h0 h1 t
  have hIm := integrableOn_realThetaImIntegrand_Icc h0 h1 t
  have hRe_c : IntegrableOn
      (fun u : ℝ => ((realThetaReIntegrand σ t u : ℝ) : ℂ)) (Ioi (1 : ℝ)) :=
    hRe.ofReal
  have hIm_c : IntegrableOn
      (fun u : ℝ => ((realThetaImIntegrand σ t u : ℝ) : ℂ)) (Ioi (1 : ℝ)) :=
    hIm.ofReal
  have hIm_I : IntegrableOn
      (fun u : ℝ => ((realThetaImIntegrand σ t u : ℝ) : ℂ) * Complex.I)
      (Ioi (1 : ℝ)) :=
    hIm_c.mul_const Complex.I
  -- Split ∫ (a + b) = ∫ a + ∫ b, then ∫ (c · I) = (∫ c) · I, then integral_ofReal.
  rw [MeasureTheory.integral_add hRe_c hIm_I]
  rw [MeasureTheory.integral_mul_const]
  congr 1
  · exact integral_ofReal
  · congr 1
    exact integral_ofReal

theorem re_Lambda0_eq_real_integral_Icc {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (t : ℝ) :
    (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re
      = ∫ u in Ioi (1 : ℝ), realThetaReIntegrand σ t u := by
  rw [Lambda0_eq_real_add_I_real_integral_Icc h0 h1 t]
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]

theorem im_Lambda0_eq_real_integral_Icc {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (t : ℝ) :
    (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im
      = ∫ u in Ioi (1 : ℝ), realThetaImIntegrand σ t u := by
  rw [Lambda0_eq_real_add_I_real_integral_Icc h0 h1 t]
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]

/-! ## §8 — Uniform error envelope for the truncated theta integrand

Truncating `omega` to its first `N` terms (`omegaPartial N`) produces a
finite elementary sum directly evaluable by the certificate engine.  We
control three quantities uniformly over `σ ∈ [0, 1]` and `t : ℝ`:

* **Pointwise** `|realTheta - realThetaN| ≤ 2·|ω - ωP N|` for `u ≥ 1`
  (both real and imaginary integrands).
* **Integrated on `Ioc 1 T`** `|∫ (realTheta - realThetaN)| ≤ 2·(T-1)·δ_N`
  where `δ_N = exp(-π(N+1)²) / (1 - exp(-π))` is the uniform-over-`[1,T]`
  max of `|ω - ωP N|` from `omega_partial_error`.
* **Tail on `Ioi T`** `|∫ realTheta| ≤ 2·exp(-πT) / (π·(1 - exp(-π)))`
  via `omega_le_uniform_geom` + `integral_exp_neg_pi_mul_Ioi`.

At `N = 3`, `T = 5` the total envelope is `≈ 10⁻⁷`, tiny vs. the
`10⁻⁴` target margin of the r331b top-edge sign statement. -/

/-- Real integrand with the finite N-term theta partial in place of `omega`. -/
def realThetaReIntegrandN (N : ℕ) (σ t u : ℝ) : ℝ :=
  (u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1))
    * Real.cos ((t / 2) * Real.log u)
    * omegaPartial N u

/-- Imaginary integrand with the finite N-term theta partial. -/
def realThetaImIntegrandN (N : ℕ) (σ t u : ℝ) : ℝ :=
  (u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1))
    * Real.sin ((t / 2) * Real.log u)
    * omegaPartial N u

/-! ### §8.1 — Pointwise truncation bounds -/

lemma abs_realTheta_re_sub_N_le {N : ℕ} {σ t u : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hu : 1 ≤ u) :
    |realThetaReIntegrand σ t u - realThetaReIntegrandN N σ t u|
      ≤ 2 * |omega u - omegaPartial N u| := by
  unfold realThetaReIntegrand realThetaReIntegrandN
  have hu0 : 0 ≤ u := by linarith
  have hp1_nn : 0 ≤ u ^ (σ / 2 - 1) := Real.rpow_nonneg hu0 _
  have hp2_nn : 0 ≤ u ^ ((1 - σ) / 2 - 1) := Real.rpow_nonneg hu0 _
  have hp1_le : u ^ (σ / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hp2_le : u ^ ((1 - σ) / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hSum_nn : 0 ≤ u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1) := by linarith
  have hSum_le : u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1) ≤ 2 := by linarith
  have hSum_abs_le : |u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1)| ≤ 2 := by
    rw [abs_of_nonneg hSum_nn]; exact hSum_le
  have hcos_abs : |Real.cos ((t / 2) * Real.log u)| ≤ 1 := Real.abs_cos_le_one _
  have h_eq :
      (u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1))
          * Real.cos ((t / 2) * Real.log u) * omega u
        - (u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1))
          * Real.cos ((t / 2) * Real.log u) * omegaPartial N u
        = (u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1))
          * Real.cos ((t / 2) * Real.log u)
          * (omega u - omegaPartial N u) := by ring
  rw [h_eq, abs_mul, abs_mul]
  calc |u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1)|
          * |Real.cos ((t / 2) * Real.log u)|
          * |omega u - omegaPartial N u|
      ≤ 2 * 1 * |omega u - omegaPartial N u| := by
        gcongr
    _ = 2 * |omega u - omegaPartial N u| := by ring

lemma abs_realTheta_im_sub_N_le {N : ℕ} {σ t u : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hu : 1 ≤ u) :
    |realThetaImIntegrand σ t u - realThetaImIntegrandN N σ t u|
      ≤ 2 * |omega u - omegaPartial N u| := by
  unfold realThetaImIntegrand realThetaImIntegrandN
  have hu0 : 0 ≤ u := by linarith
  have hp1_nn : 0 ≤ u ^ (σ / 2 - 1) := Real.rpow_nonneg hu0 _
  have hp2_nn : 0 ≤ u ^ ((1 - σ) / 2 - 1) := Real.rpow_nonneg hu0 _
  have hp1_le : u ^ (σ / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hp2_le : u ^ ((1 - σ) / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by linarith)
  have hDiff_abs_le :
      |u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1)| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hsin_abs : |Real.sin ((t / 2) * Real.log u)| ≤ 1 := Real.abs_sin_le_one _
  have h_eq :
      (u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1))
          * Real.sin ((t / 2) * Real.log u) * omega u
        - (u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1))
          * Real.sin ((t / 2) * Real.log u) * omegaPartial N u
        = (u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1))
          * Real.sin ((t / 2) * Real.log u)
          * (omega u - omegaPartial N u) := by ring
  rw [h_eq, abs_mul, abs_mul]
  calc |u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1)|
          * |Real.sin ((t / 2) * Real.log u)|
          * |omega u - omegaPartial N u|
      ≤ 2 * 1 * |omega u - omegaPartial N u| := by
        gcongr
    _ = 2 * |omega u - omegaPartial N u| := by ring

/-! ### §8.2 — Continuity + integrability of the truncated integrands -/

lemma continuous_omegaPartial (N : ℕ) : Continuous (omegaPartial N) := by
  unfold omegaPartial
  refine continuous_finset_sum _ (fun n _ => ?_)
  exact Real.continuous_exp.comp (continuous_const.mul continuous_id)

lemma continuousOn_realThetaReIntegrandN_Icc (N : ℕ) (σ t T : ℝ) :
    ContinuousOn (realThetaReIntegrandN N σ t) (Icc (1 : ℝ) T) := by
  unfold realThetaReIntegrandN
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; exact Or.inl (by linarith [hu.1])
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; exact Or.inl (by linarith [hu.1])
  · refine Real.continuous_cos.comp_continuousOn ?_
    refine continuousOn_const.mul ?_
    refine Real.continuousOn_log.mono (fun u hu => ?_)
    exact ne_of_gt (show (0 : ℝ) < u by linarith [hu.1])
  · exact (continuous_omegaPartial N).continuousOn

lemma continuousOn_realThetaImIntegrandN_Icc (N : ℕ) (σ t T : ℝ) :
    ContinuousOn (realThetaImIntegrandN N σ t) (Icc (1 : ℝ) T) := by
  unfold realThetaImIntegrandN
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; exact Or.inl (by linarith [hu.1])
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; exact Or.inl (by linarith [hu.1])
  · refine Real.continuous_sin.comp_continuousOn ?_
    refine continuousOn_const.mul ?_
    refine Real.continuousOn_log.mono (fun u hu => ?_)
    exact ne_of_gt (show (0 : ℝ) < u by linarith [hu.1])
  · exact (continuous_omegaPartial N).continuousOn

lemma continuousOn_realThetaReIntegrand_Icc (σ t T : ℝ) :
    ContinuousOn (realThetaReIntegrand σ t) (Icc (1 : ℝ) T) := by
  unfold realThetaReIntegrand
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; exact Or.inl (by linarith [hu.1])
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; exact Or.inl (by linarith [hu.1])
  · refine Real.continuous_cos.comp_continuousOn ?_
    refine continuousOn_const.mul ?_
    refine Real.continuousOn_log.mono (fun u hu => ?_)
    exact ne_of_gt (show (0 : ℝ) < u by linarith [hu.1])
  · exact continuousOn_omega.mono (fun u hu => show (0 : ℝ) < u by linarith [hu.1])

lemma continuousOn_realThetaImIntegrand_Icc (σ t T : ℝ) :
    ContinuousOn (realThetaImIntegrand σ t) (Icc (1 : ℝ) T) := by
  unfold realThetaImIntegrand
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; exact Or.inl (by linarith [hu.1])
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; exact Or.inl (by linarith [hu.1])
  · refine Real.continuous_sin.comp_continuousOn ?_
    refine continuousOn_const.mul ?_
    refine Real.continuousOn_log.mono (fun u hu => ?_)
    exact ne_of_gt (show (0 : ℝ) < u by linarith [hu.1])
  · exact continuousOn_omega.mono (fun u hu => show (0 : ℝ) < u by linarith [hu.1])

lemma integrableOn_realThetaReIntegrandN_Ioc (N : ℕ) (σ t T : ℝ) :
    IntegrableOn (realThetaReIntegrandN N σ t) (Ioc (1 : ℝ) T) := by
  have hInt : IntegrableOn (realThetaReIntegrandN N σ t) (Icc 1 T) :=
    (continuousOn_realThetaReIntegrandN_Icc N σ t T).integrableOn_compact isCompact_Icc
  exact hInt.mono_set Set.Ioc_subset_Icc_self

lemma integrableOn_realThetaImIntegrandN_Ioc (N : ℕ) (σ t T : ℝ) :
    IntegrableOn (realThetaImIntegrandN N σ t) (Ioc (1 : ℝ) T) := by
  have hInt : IntegrableOn (realThetaImIntegrandN N σ t) (Icc 1 T) :=
    (continuousOn_realThetaImIntegrandN_Icc N σ t T).integrableOn_compact isCompact_Icc
  exact hInt.mono_set Set.Ioc_subset_Icc_self

lemma integrableOn_realThetaReIntegrand_Ioc (σ t T : ℝ) :
    IntegrableOn (realThetaReIntegrand σ t) (Ioc (1 : ℝ) T) := by
  have hInt : IntegrableOn (realThetaReIntegrand σ t) (Icc 1 T) :=
    (continuousOn_realThetaReIntegrand_Icc σ t T).integrableOn_compact isCompact_Icc
  exact hInt.mono_set Set.Ioc_subset_Icc_self

lemma integrableOn_realThetaImIntegrand_Ioc (σ t T : ℝ) :
    IntegrableOn (realThetaImIntegrand σ t) (Ioc (1 : ℝ) T) := by
  have hInt : IntegrableOn (realThetaImIntegrand σ t) (Icc 1 T) :=
    (continuousOn_realThetaImIntegrand_Icc σ t T).integrableOn_compact isCompact_Icc
  exact hInt.mono_set Set.Ioc_subset_Icc_self

/-! ### §8.3 — Integrated truncation bound on `Ioc 1 T`

Uses `omega_partial_error` and the monotonicity of `exp(-π(N+1)²·u)` in
`u` to bound `|ω u - ωP N u| ≤ exp(-π(N+1)²)/(1 - exp(-π))` uniformly on
`u ∈ [1, T]`. -/

lemma abs_integral_realTheta_re_sub_N_Ioc_le {N : ℕ} {σ t T : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    |(∫ u in Ioc (1 : ℝ) T, realThetaReIntegrand σ t u)
       - (∫ u in Ioc (1 : ℝ) T, realThetaReIntegrandN N σ t u)|
      ≤ 2 * (T - 1)
        * (Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π))) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hExp1 : Real.exp (-π) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hDenom_pos : 0 < 1 - Real.exp (-π) := by linarith
  have hInt1 := integrableOn_realThetaReIntegrand_Ioc σ t T
  have hInt2 := integrableOn_realThetaReIntegrandN_Ioc N σ t T
  have hδ_nn : (0 : ℝ)
      ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)) :=
    div_nonneg (Real.exp_pos _).le hDenom_pos.le
  have hC_nn : (0 : ℝ) ≤ 2 * (Real.exp (-π * ((N : ℝ) + 1) ^ 2)
      / (1 - Real.exp (-π))) := by positivity
  have h_vol : (MeasureTheory.volume (Ioc (1 : ℝ) T)).toReal = T - 1 := by
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 1)]
  have h_vol_lt_top : MeasureTheory.volume (Ioc (1 : ℝ) T) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  calc |(∫ u in Ioc (1 : ℝ) T, realThetaReIntegrand σ t u)
          - (∫ u in Ioc (1 : ℝ) T, realThetaReIntegrandN N σ t u)|
      = |∫ u in Ioc (1 : ℝ) T,
            (realThetaReIntegrand σ t u - realThetaReIntegrandN N σ t u)| := by
        rw [MeasureTheory.integral_sub hInt1 hInt2]
    _ ≤ ∫ u in Ioc (1 : ℝ) T,
            |realThetaReIntegrand σ t u - realThetaReIntegrandN N σ t u| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _u in Ioc (1 : ℝ) T,
            2 * (Real.exp (-π * ((N : ℝ) + 1) ^ 2)
                  / (1 - Real.exp (-π))) := by
        refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc ?_
        · exact (hInt1.sub hInt2).abs
        · exact MeasureTheory.integrableOn_const (hs := h_vol_lt_top.ne)
        · intro u hu
          have hu1 : (1 : ℝ) ≤ u := hu.1.le
          have h_ptwise :=
            abs_realTheta_re_sub_N_le (N := N) (t := t) hσ0 hσ1 hu1
          have h_err_bound :
              |omega u - omegaPartial N u|
                ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u)
                    / (1 - Real.exp (-π)) :=
            omega_partial_error hu1 N
          have h_exp_arg_le :
              -π * ((N : ℝ) + 1) ^ 2 * u ≤ -π * ((N : ℝ) + 1) ^ 2 := by
            have h_nn : 0 ≤ π * ((N : ℝ) + 1) ^ 2 := by positivity
            nlinarith
          have h_exp_le :
              Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u)
                ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2) :=
            Real.exp_le_exp.mpr h_exp_arg_le
          have h_step2 :
              Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u) / (1 - Real.exp (-π))
                ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)) := by
            gcongr
          have h_combined :
              |omega u - omegaPartial N u|
                ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)) :=
            le_trans h_err_bound h_step2
          have h_final :
              2 * |omega u - omegaPartial N u|
                ≤ 2 * (Real.exp (-π * ((N : ℝ) + 1) ^ 2)
                        / (1 - Real.exp (-π))) :=
            mul_le_mul_of_nonneg_left h_combined (by norm_num)
          exact le_trans h_ptwise h_final
    _ = 2 * (T - 1)
        * (Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π))) := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, h_vol]
        simp only [smul_eq_mul]; ring

lemma abs_integral_realTheta_im_sub_N_Ioc_le {N : ℕ} {σ t T : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    |(∫ u in Ioc (1 : ℝ) T, realThetaImIntegrand σ t u)
       - (∫ u in Ioc (1 : ℝ) T, realThetaImIntegrandN N σ t u)|
      ≤ 2 * (T - 1)
        * (Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π))) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hExp1 : Real.exp (-π) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hDenom_pos : 0 < 1 - Real.exp (-π) := by linarith
  have hInt1 := integrableOn_realThetaImIntegrand_Ioc σ t T
  have hInt2 := integrableOn_realThetaImIntegrandN_Ioc N σ t T
  have hδ_nn : (0 : ℝ)
      ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)) :=
    div_nonneg (Real.exp_pos _).le hDenom_pos.le
  have hC_nn : (0 : ℝ) ≤ 2 * (Real.exp (-π * ((N : ℝ) + 1) ^ 2)
      / (1 - Real.exp (-π))) := by positivity
  have h_vol : (MeasureTheory.volume (Ioc (1 : ℝ) T)).toReal = T - 1 := by
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 1)]
  have h_vol_lt_top : MeasureTheory.volume (Ioc (1 : ℝ) T) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  calc |(∫ u in Ioc (1 : ℝ) T, realThetaImIntegrand σ t u)
          - (∫ u in Ioc (1 : ℝ) T, realThetaImIntegrandN N σ t u)|
      = |∫ u in Ioc (1 : ℝ) T,
            (realThetaImIntegrand σ t u - realThetaImIntegrandN N σ t u)| := by
        rw [MeasureTheory.integral_sub hInt1 hInt2]
    _ ≤ ∫ u in Ioc (1 : ℝ) T,
            |realThetaImIntegrand σ t u - realThetaImIntegrandN N σ t u| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _u in Ioc (1 : ℝ) T,
            2 * (Real.exp (-π * ((N : ℝ) + 1) ^ 2)
                  / (1 - Real.exp (-π))) := by
        refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ioc ?_
        · exact (hInt1.sub hInt2).abs
        · exact MeasureTheory.integrableOn_const (hs := h_vol_lt_top.ne)
        · intro u hu
          have hu1 : (1 : ℝ) ≤ u := hu.1.le
          have h_ptwise :=
            abs_realTheta_im_sub_N_le (N := N) (t := t) hσ0 hσ1 hu1
          have h_err_bound :
              |omega u - omegaPartial N u|
                ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u)
                    / (1 - Real.exp (-π)) :=
            omega_partial_error hu1 N
          have h_exp_arg_le :
              -π * ((N : ℝ) + 1) ^ 2 * u ≤ -π * ((N : ℝ) + 1) ^ 2 := by
            have h_nn : 0 ≤ π * ((N : ℝ) + 1) ^ 2 := by positivity
            nlinarith
          have h_exp_le :
              Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u)
                ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2) :=
            Real.exp_le_exp.mpr h_exp_arg_le
          have h_step2 :
              Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u) / (1 - Real.exp (-π))
                ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)) := by
            gcongr
          have h_combined :
              |omega u - omegaPartial N u|
                ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)) :=
            le_trans h_err_bound h_step2
          have h_final :
              2 * |omega u - omegaPartial N u|
                ≤ 2 * (Real.exp (-π * ((N : ℝ) + 1) ^ 2)
                        / (1 - Real.exp (-π))) :=
            mul_le_mul_of_nonneg_left h_combined (by norm_num)
          exact le_trans h_ptwise h_final
    _ = 2 * (T - 1)
        * (Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π))) := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, h_vol]
        simp only [smul_eq_mul]; ring

/-! ### §8.4 — Tail bounds on `Ioi T`

Uses `omega_le_uniform_geom` (from r329b) + `integral_exp_neg_pi_mul_Ioi`
(from XiQuadrature).  The proof is the r329b/XiQuadrature `Xi_tail_bound`
template adapted from the critical-line `2·u^(-3/4)·cos` integrand to our
`(u^(σ/2-1) ± u^((1-σ)/2-1))·cos or sin` variant. -/

lemma abs_realThetaRe_le_two_omega {σ t u : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hu : 1 ≤ u) :
    |realThetaReIntegrand σ t u| ≤ 2 * omega u :=
  abs_realThetaReIntegrand_le_two_omega hσ0 hσ1 hu

lemma abs_realThetaIm_le_two_omega {σ t u : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hu : 1 ≤ u) :
    |realThetaImIntegrand σ t u| ≤ 2 * omega u :=
  abs_realThetaImIntegrand_le_two_omega hσ0 hσ1 hu

lemma abs_integral_realTheta_re_Ioi_T_le {σ t T : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    |∫ u in Ioi T, realThetaReIntegrand σ t u|
      ≤ 2 / π * Real.exp (-π * T) / (1 - Real.exp (-π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hExp1 : Real.exp (-π) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hDenom_pos : 0 < 1 - Real.exp (-π) := by linarith
  have hfInt : IntegrableOn (realThetaReIntegrand σ t) (Ioi T) :=
    (integrableOn_realThetaReIntegrand_Icc (t := t) hσ0 hσ1).mono_set
      (Set.Ioi_subset_Ioi hT)
  have hgInt :
      IntegrableOn (fun u : ℝ => 2 * Real.exp (-π * u) / (1 - Real.exp (-π)))
        (Ioi T) :=
    ((exp_neg_integrableOn_Ioi T hπ).const_mul 2).div_const _
  calc |∫ u in Ioi T, realThetaReIntegrand σ t u|
      ≤ ∫ u in Ioi T, |realThetaReIntegrand σ t u| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Ioi T, 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by
        refine MeasureTheory.setIntegral_mono_on hfInt.abs hgInt measurableSet_Ioi
          fun u hu => ?_
        have hu1 : (1 : ℝ) ≤ u := le_trans hT (mem_Ioi.mp hu).le
        have h_ptwise := abs_realThetaRe_le_two_omega (t := t) hσ0 hσ1 hu1
        have hω_bound := omega_le_uniform_geom hu1
        have h_step :
            2 * omega u ≤ 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by
          have h1 : 2 * omega u
              ≤ 2 * (Real.exp (-π * u) / (1 - Real.exp (-π))) :=
            mul_le_mul_of_nonneg_left hω_bound (by norm_num)
          have h2 : 2 * (Real.exp (-π * u) / (1 - Real.exp (-π)))
              = 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by ring
          linarith
        linarith [h_ptwise, h_step]
    _ = 2 / π * Real.exp (-π * T) / (1 - Real.exp (-π)) := by
        have hfun :
            (fun u : ℝ => 2 * Real.exp (-π * u) / (1 - Real.exp (-π)))
              = fun u : ℝ => 2 / (1 - Real.exp (-π)) * Real.exp (-π * u) := by
          funext u; ring
        rw [hfun, MeasureTheory.integral_const_mul, integral_exp_neg_pi_mul_Ioi]
        ring

lemma abs_integral_realTheta_im_Ioi_T_le {σ t T : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    |∫ u in Ioi T, realThetaImIntegrand σ t u|
      ≤ 2 / π * Real.exp (-π * T) / (1 - Real.exp (-π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hExp1 : Real.exp (-π) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hDenom_pos : 0 < 1 - Real.exp (-π) := by linarith
  have hfInt : IntegrableOn (realThetaImIntegrand σ t) (Ioi T) :=
    (integrableOn_realThetaImIntegrand_Icc (t := t) hσ0 hσ1).mono_set
      (Set.Ioi_subset_Ioi hT)
  have hgInt :
      IntegrableOn (fun u : ℝ => 2 * Real.exp (-π * u) / (1 - Real.exp (-π)))
        (Ioi T) :=
    ((exp_neg_integrableOn_Ioi T hπ).const_mul 2).div_const _
  calc |∫ u in Ioi T, realThetaImIntegrand σ t u|
      ≤ ∫ u in Ioi T, |realThetaImIntegrand σ t u| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Ioi T, 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by
        refine MeasureTheory.setIntegral_mono_on hfInt.abs hgInt measurableSet_Ioi
          fun u hu => ?_
        have hu1 : (1 : ℝ) ≤ u := le_trans hT (mem_Ioi.mp hu).le
        have h_ptwise := abs_realThetaIm_le_two_omega (t := t) hσ0 hσ1 hu1
        have hω_bound := omega_le_uniform_geom hu1
        have h_step :
            2 * omega u ≤ 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by
          have h1 : 2 * omega u
              ≤ 2 * (Real.exp (-π * u) / (1 - Real.exp (-π))) :=
            mul_le_mul_of_nonneg_left hω_bound (by norm_num)
          have h2 : 2 * (Real.exp (-π * u) / (1 - Real.exp (-π)))
              = 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by ring
          linarith
        linarith [h_ptwise, h_step]
    _ = 2 / π * Real.exp (-π * T) / (1 - Real.exp (-π)) := by
        have hfun :
            (fun u : ℝ => 2 * Real.exp (-π * u) / (1 - Real.exp (-π)))
              = fun u : ℝ => 2 / (1 - Real.exp (-π)) * Real.exp (-π * u) := by
          funext u; ring
        rw [hfun, MeasureTheory.integral_const_mul, integral_exp_neg_pi_mul_Ioi]
        ring

/-! ### §8.5 — Combined envelope: total error controlling `∫ realTheta` on `Ioi 1`

Combines §8.3 (truncation on `Ioc 1 T`) and §8.4 (tail on `Ioi T`) into a
single bound relating `∫_{Ioi 1} realTheta` (which equals `Re Λ₀` /
`Im Λ₀` by §7) to `∫_{Ioc 1 T} realThetaN` (the finite elementary
quantity certified by the generator in §9). -/

lemma integral_realThetaRe_Ioi1_eq_Ioc_add_Ioi {σ t T : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    (∫ u in Ioi (1 : ℝ), realThetaReIntegrand σ t u)
      = (∫ u in Ioc (1 : ℝ) T, realThetaReIntegrand σ t u)
          + ∫ u in Ioi T, realThetaReIntegrand σ t u := by
  have hInt := integrableOn_realThetaReIntegrand_Icc (t := t) hσ0 hσ1
  rw [← MeasureTheory.setIntegral_union
        (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hInt.mono_set Set.Ioc_subset_Ioi_self)
        (hInt.mono_set (Set.Ioi_subset_Ioi hT)),
      Set.Ioc_union_Ioi_eq_Ioi hT]

lemma integral_realThetaIm_Ioi1_eq_Ioc_add_Ioi {σ t T : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    (∫ u in Ioi (1 : ℝ), realThetaImIntegrand σ t u)
      = (∫ u in Ioc (1 : ℝ) T, realThetaImIntegrand σ t u)
          + ∫ u in Ioi T, realThetaImIntegrand σ t u := by
  have hInt := integrableOn_realThetaImIntegrand_Icc (t := t) hσ0 hσ1
  rw [← MeasureTheory.setIntegral_union
        (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hInt.mono_set Set.Ioc_subset_Ioi_self)
        (hInt.mono_set (Set.Ioi_subset_Ioi hT)),
      Set.Ioc_union_Ioi_eq_Ioi hT]

/-- **Total error envelope (real part).**  For `σ ∈ [0, 1]`, `T ≥ 1`, and
`N : ℕ`, the *unknown* `∫_{Ioi 1} realThetaRe` (which equals
`Re Λ₀(σ+it)` by §7) is within `envRe` of the *computable*
`∫_{Ioc 1 T} realThetaReN`:

  `|Re Λ₀ - ∫_{Ioc 1 T} realThetaReN|
     ≤ 2·(T-1)·exp(-π(N+1)²)/(1-exp(-π))
       + 2·exp(-πT) / (π·(1-exp(-π)))`. -/
theorem re_Lambda0_close_to_truncated_integral {N : ℕ} {σ t T : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    |(completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re
        - (∫ u in Ioc (1 : ℝ) T, realThetaReIntegrandN N σ t u)|
      ≤ 2 * (T - 1)
          * (Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)))
        + 2 / π * Real.exp (-π * T) / (1 - Real.exp (-π)) := by
  rw [re_Lambda0_eq_real_integral_Icc hσ0 hσ1 t,
      integral_realThetaRe_Ioi1_eq_Ioc_add_Ioi (t := t) hσ0 hσ1 hT]
  have hTruncBound :=
    abs_integral_realTheta_re_sub_N_Ioc_le (N := N) (t := t) hσ0 hσ1 hT
  have hTailBound :=
    abs_integral_realTheta_re_Ioi_T_le (t := t) hσ0 hσ1 hT
  have h_split :
      ((∫ u in Ioc (1 : ℝ) T, realThetaReIntegrand σ t u)
          + ∫ u in Ioi T, realThetaReIntegrand σ t u)
        - (∫ u in Ioc (1 : ℝ) T, realThetaReIntegrandN N σ t u)
        = ((∫ u in Ioc (1 : ℝ) T, realThetaReIntegrand σ t u)
              - (∫ u in Ioc (1 : ℝ) T, realThetaReIntegrandN N σ t u))
          + (∫ u in Ioi T, realThetaReIntegrand σ t u) := by ring
  rw [h_split]
  exact le_trans (abs_add _ _) (add_le_add hTruncBound hTailBound)

theorem im_Lambda0_close_to_truncated_integral {N : ℕ} {σ t T : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T) :
    |(completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im
        - (∫ u in Ioc (1 : ℝ) T, realThetaImIntegrandN N σ t u)|
      ≤ 2 * (T - 1)
          * (Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)))
        + 2 / π * Real.exp (-π * T) / (1 - Real.exp (-π)) := by
  rw [im_Lambda0_eq_real_integral_Icc hσ0 hσ1 t,
      integral_realThetaIm_Ioi1_eq_Ioc_add_Ioi (t := t) hσ0 hσ1 hT]
  have hTruncBound :=
    abs_integral_realTheta_im_sub_N_Ioc_le (N := N) (t := t) hσ0 hσ1 hT
  have hTailBound :=
    abs_integral_realTheta_im_Ioi_T_le (t := t) hσ0 hσ1 hT
  have h_split :
      ((∫ u in Ioc (1 : ℝ) T, realThetaImIntegrand σ t u)
          + ∫ u in Ioi T, realThetaImIntegrand σ t u)
        - (∫ u in Ioc (1 : ℝ) T, realThetaImIntegrandN N σ t u)
        = ((∫ u in Ioc (1 : ℝ) T, realThetaImIntegrand σ t u)
              - (∫ u in Ioc (1 : ℝ) T, realThetaImIntegrandN N σ t u))
          + (∫ u in Ioi T, realThetaImIntegrand σ t u) := by ring
  rw [h_split]
  exact le_trans (abs_add _ _) (add_le_add hTruncBound hTailBound)

/-! ## §9 — Pilot σ-box [1/2, 9/16] — conditional endpoint scaffolding

★ LOCAL SCAFFOLDING ONLY.  Not for push per r331 directive §XVI. ★

Exposes the exact rational constants the certificate generator must
produce for r331b's TOP box 0.  The `BoxReEnclosure` /
`BoxImEnclosure` premises will be discharged in a later stage by u-panel
enclosures certified via generator + §8 envelope integration.

**Numerical target constants** (from directive 2026-08-26):

* `Rlo = 2221/500000 ≈ 4.442·10⁻³`.
  Certifies uniform lower bound on `Re Λ₀(σ+15i)` for `σ ∈ [1/2, 9/16]`.
  Actual `Re Λ₀(1/2+15i) ≈ 4.4463·10⁻³`; certificate margin `≈ 4·10⁻⁶`.
* `Rhi = 1` — trivial upper bound (sufficient since `A(σ) < 0` and
  `r ≥ Rlo > 0`, so `A·r` is most negative when `r = Rlo`).
* `Ilo = -(1/10000)`, `Ihi = 1/10000`.  Certifies `|Im Λ₀(σ+15i)| ≤ 10⁻⁴`
  on the box.  Numerical estimate: `Im Λ₀(1/2+15i) = 0` exactly by
  critical-line conjugation; grows to something ≪ `10⁻⁴` at `σ = 9/16`.

**Arithmetic closure** (all rational):

* `A(σ) := σ(σ-1) - 225 ∈ [-901/4, -57663/256]` on `[1/2, 9/16]`.
* `B(σ) := 15(2σ-1) ∈ [0, 15/8]` on `[1/2, 9/16]`.
* `max A(σ)·r = (-57663/256)·(2221/500000) = -128069523/128000000`.
* `max -B(σ)·i ≤ (15/8)·(1/10000) = 15/80000 = 24000/128000000`.
* `Sum: max (A·r - B·i) ≤ -128045523/128000000`.
* `(1 + max) / 2 ≤ -45523/256000000 ≈ -1.78·10⁻⁴  <  -25600/256000000 = -1/10000`. ✓
-/

/-- Coefficient enclosure — `σ(σ-1) - 225` upper bound on `[1/2, 9/16]`.
The bound `-57663/256` is the value at `σ = 9/16`.  Since `σ(σ-1)` is
increasing on `[1/2, 1]` (derivative `2σ-1 ≥ 0`), this is a tight
uniform upper bound. -/
lemma box0_A_hi_bound {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16) :
    σ * (σ - 1) - (15 : ℝ) ^ 2 ≤ -(57663/256 : ℝ) := by
  have h_prod : (σ - 1/2) * (σ - 9/16) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith [h_prod]

/-- Coefficient enclosure — `σ(σ-1) - 225` lower bound on `[1/2, 9/16]`.
The bound `-901/4 = -(1/4 + 225)` is the value at `σ = 1/2`. -/
lemma box0_A_lo_bound {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16) :
    -(901/4 : ℝ) ≤ σ * (σ - 1) - (15 : ℝ) ^ 2 := by
  nlinarith [sq_nonneg (σ - 1/2)]

/-- Coefficient enclosure — `15(2σ-1)` lower bound on `[1/2, 9/16]`.
Value at `σ = 1/2` is `0`. -/
lemma box0_B_lo_bound {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16) :
    (0 : ℝ) ≤ 15 * (2 * σ - 1) := by
  nlinarith

/-- Coefficient enclosure — `15(2σ-1)` upper bound on `[1/2, 9/16]`.
Value at `σ = 9/16` is `15/8`. -/
lemma box0_B_hi_bound {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16) :
    (15 : ℝ) * (2 * σ - 1) ≤ 15/8 := by
  nlinarith

/-- **★ CONDITIONAL BOX 0 ★** — given certified enclosures of
`Re Λ₀(σ+15i) ≥ Rlo = 2221/500000` and `|Im Λ₀(σ+15i)| ≤ 1/10000`
uniformly over `σ ∈ [1/2, 9/16]`, conclude `Re ξ(σ+15i) < -1/10000`
for `σ ∈ [1/2, 9/16]`.

The `BoxReEnclosure` / `BoxImEnclosure` premises are the SOLE remaining
load-bearing pieces for r331b box 0.  They will be discharged in a later
stage by certified u-panel enclosures + §8 envelope integration.  Until
then this theorem is LOCAL scaffolding — not pushed. -/
theorem top15_box0_re_lt_neg_1e4_conditional
    (h_R : PrincipiaTractalis.RiemannXiThetaBoxEnclosure.BoxReEnclosure
             ((1 : ℝ) / 2) (9/16) 15 (2221/500000) 1)
    (h_I : PrincipiaTractalis.RiemannXiThetaBoxEnclosure.BoxImEnclosure
             ((1 : ℝ) / 2) (9/16) 15 (-(1/10000)) (1/10000))
    {σ : ℝ} (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16) :
    (riemannXiEntire (⟨σ, 15⟩ : ℂ)).re < -(1/10000 : ℝ) := by
  rw [PrincipiaTractalis.RiemannXiThetaBoxEnclosure.re_xi_at_s]
  have ⟨hR_lo, _hR_hi⟩ := h_R.bounds σ h0 h1
  have ⟨hI_lo, hI_hi⟩ := h_I.bounds σ h0 h1
  set r := (completedRiemannZeta₀ (⟨σ, 15⟩ : ℂ)).re
  set i := (completedRiemannZeta₀ (⟨σ, 15⟩ : ℂ)).im
  have h_A_hi := box0_A_hi_bound h0 h1
  have h_B_lo := box0_B_lo_bound h0 h1
  have h_B_hi := box0_B_hi_bound h0 h1
  have hr_nn : (0 : ℝ) ≤ r := by
    have : (2221/500000 : ℝ) ≤ r := hR_lo
    linarith
  have h_Ar_ub : (σ * (σ - 1) - (15 : ℝ) ^ 2) * r
      ≤ -(128069523/128000000 : ℝ) := by
    have step1 : (σ * (σ - 1) - (15 : ℝ) ^ 2) * r ≤ -(57663/256) * r :=
      mul_le_mul_of_nonneg_right h_A_hi hr_nn
    have step2 : (-(57663/256) : ℝ) * r ≤ -(57663/256) * (2221/500000) :=
      mul_le_mul_of_nonpos_left hR_lo (by norm_num : (-(57663/256) : ℝ) ≤ 0)
    have step3 : (-(57663/256) : ℝ) * (2221/500000)
        = -(128069523/128000000) := by norm_num
    linarith
  have h_neg_Bi_ub : -((15 : ℝ) * (2 * σ - 1)) * i ≤ 15/80000 := by
    rcases le_or_lt 0 i with hi_nn | hi_neg
    · have h_prod_nn : (0 : ℝ) ≤ 15 * (2 * σ - 1) * i :=
        mul_nonneg h_B_lo hi_nn
      linarith
    · have h_neg_i_pos : (0 : ℝ) ≤ -i := by linarith
      have h_neg_i_le : -i ≤ 1/10000 := by linarith
      calc -((15 : ℝ) * (2 * σ - 1)) * i
            = (15 * (2 * σ - 1)) * (-i) := by ring
        _ ≤ (15/8 : ℝ) * (-i) :=
              mul_le_mul_of_nonneg_right h_B_hi h_neg_i_pos
        _ ≤ (15/8 : ℝ) * (1/10000) :=
              mul_le_mul_of_nonneg_left h_neg_i_le (by norm_num)
        _ = 15/80000 := by norm_num
  have h_neg_Bi_ub' : -((15 : ℝ) * (2 * σ - 1) * i) ≤ 15/80000 := by
    have h_ring : (-((15 : ℝ) * (2 * σ - 1))) * i = -(15 * (2 * σ - 1) * i) := by ring
    linarith [h_neg_Bi_ub, h_ring]
  have h_num_ub :
      1 + (σ * (σ - 1) - (15 : ℝ) ^ 2) * r - 15 * (2 * σ - 1) * i
        ≤ -(45523/128000000 : ℝ) := by
    have h_step : (σ * (σ - 1) - (15 : ℝ) ^ 2) * r - 15 * (2 * σ - 1) * i
        ≤ -(128045523/128000000 : ℝ) := by linarith
    have h_arith : (1 : ℝ) - 128045523/128000000 = -(45523/128000000) := by norm_num
    linarith
  have h_div_ub :
      (1 + (σ * (σ - 1) - (15 : ℝ) ^ 2) * r - 15 * (2 * σ - 1) * i) / 2
        ≤ -(45523/256000000 : ℝ) := by linarith
  have h_target : -(45523/256000000 : ℝ) < -(1/10000 : ℝ) := by norm_num
  linarith

/-! ## §9.1 — Generalized elementary theta term (parameterized on exponent `a`)

Generalizes r315's fixed critical-line term `2·u^(-3/4)·cos((t/2) log u)·exp(-π(n+1)²u)`
to the σ-family:

  `thetaPowCosTerm a t n u = u^a · cos((t/2) log u) · exp(-π(n+1)²u)`
  `thetaPowSinTerm a t n u = u^a · sin((t/2) log u) · exp(-π(n+1)²u)`

Explicit first and second derivatives are computed via the standard
three-factor Leibniz decomposition `P·Q·R` with:

  `P(u) = u^a`,  `P'(u) = a·u^(a-1)`,  `P''(u) = a(a-1)·u^(a-2)`
  `Q_cos(u) = cos((t/2) log u)`, `Q_cos'(u) = -(t/2)·sin((t/2) log u)/u`,
  `Q_cos''(u) = ((t/2)·sin((t/2) log u) - (t/2)²·cos((t/2) log u))/u²`
  `Q_sin(u) = sin((t/2) log u)`, `Q_sin'(u) = (t/2)·cos((t/2) log u)/u`,
  `Q_sin''(u) = (-(t/2)·cos((t/2) log u) - (t/2)²·sin((t/2) log u))/u²`
  `R(u) = exp(-π(n+1)²·u)`, `R'(u) = -π(n+1)²·R(u)`, `R''(u) = (π(n+1)²)²·R(u)`

At `a = -3/4` the cos-branch recovers r315's `thetaTerm t n u / 2`
(dropping r315's leading factor 2 lets the r331b assembly handle both
σ-branches uniformly). -/

/-- Elementary cos-branch term of the theta series, parameterized on
exponent `a`.  For box 0, `a ∈ [-25/32, -23/32]`. -/
noncomputable def thetaPowCosTerm (a t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u ^ a * Real.cos (t / 2 * Real.log u)
    * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)

/-- Sin-branch companion. -/
noncomputable def thetaPowSinTerm (a t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u ^ a * Real.sin (t / 2 * Real.log u)
    * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)

/-- Explicit first derivative of `thetaPowCosTerm a t n` at `u > 0`. -/
noncomputable def thetaPowCosTermD1 (a t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  a * u ^ (a - 1) * Real.cos (t / 2 * Real.log u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + u ^ a * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + u ^ a * Real.cos (t / 2 * Real.log u)
      * (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))

/-- Explicit first derivative of `thetaPowSinTerm a t n` at `u > 0`. -/
noncomputable def thetaPowSinTermD1 (a t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  a * u ^ (a - 1) * Real.sin (t / 2 * Real.log u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + u ^ a * ((t / 2) * Real.cos (t / 2 * Real.log u) / u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + u ^ a * Real.sin (t / 2 * Real.log u)
      * (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))

/-- Explicit second derivative of `thetaPowCosTerm a t n` at `u > 0`:
six-term Leibniz expansion `P''QR + PQ''R + PQR'' + 2P'Q'R + 2P'QR' + 2PQ'R'`. -/
noncomputable def thetaPowCosTermD2 (a t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  a * (a - 1) * u ^ (a - 2) * Real.cos (t / 2 * Real.log u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + u ^ a
      * ((t / 2 * Real.sin (t / 2 * Real.log u)
          - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + u ^ a * Real.cos (t / 2 * Real.log u)
      * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
    + 2 * (a * u ^ (a - 1)
      * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
    + 2 * (a * u ^ (a - 1) * Real.cos (t / 2 * Real.log u)
      * (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))
    + 2 * (u ^ a * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
      * (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))

/-- Explicit second derivative of `thetaPowSinTerm a t n`. -/
noncomputable def thetaPowSinTermD2 (a t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  a * (a - 1) * u ^ (a - 2) * Real.sin (t / 2 * Real.log u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + u ^ a
      * ((-(t / 2) * Real.cos (t / 2 * Real.log u)
          - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)) / u ^ 2)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + u ^ a * Real.sin (t / 2 * Real.log u)
      * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
    + 2 * (a * u ^ (a - 1)
      * ((t / 2) * Real.cos (t / 2 * Real.log u) / u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
    + 2 * (a * u ^ (a - 1) * Real.sin (t / 2 * Real.log u)
      * (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))
    + 2 * (u ^ a * ((t / 2) * Real.cos (t / 2 * Real.log u) / u)
      * (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))

/-! ### §9.1.a — Elementary HasDerivAt building blocks

Private local reimplementations of r315's `hasDerivAt_P/P'/Q/Q'/R/R'`,
parameterized on exponent `a` and cos/sin choice.  r315's versions are
`private` so cannot be reused directly. -/

/-- `y ↦ y^a` has derivative `a·u^(a-1)` at `u > 0`. -/
private theorem hasDerivAt_powP (a : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ y ^ a) (a * u ^ (a - 1)) u :=
  Real.hasDerivAt_rpow_const (Or.inl hu.ne')

/-- `y ↦ a·y^(a-1)` has derivative `a(a-1)·u^(a-2)` at `u > 0`. -/
private theorem hasDerivAt_powP' (a : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ a * y ^ (a - 1))
      (a * (a - 1) * u ^ (a - 2)) u := by
  have h := (Real.hasDerivAt_rpow_const (p := a - 1)
    (Or.inl hu.ne')).const_mul a
  convert h using 1
  rw [show (a - 1) - 1 = a - 2 from by ring]
  ring

/-- `y ↦ cos((t/2)·log y)` has derivative `-(t/2)·sin(·)/u` at `u > 0`. -/
private theorem hasDerivAt_Qcos (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ Real.cos (t / 2 * Real.log y))
      (-(t / 2) * Real.sin (t / 2 * Real.log u) / u) u := by
  have hlog : HasDerivAt (fun y : ℝ ↦ t / 2 * Real.log y) (t / 2 * u⁻¹) u :=
    (Real.hasDerivAt_log hu.ne').const_mul (t / 2)
  convert hlog.cos using 1
  field_simp

/-- `y ↦ sin((t/2)·log y)` has derivative `(t/2)·cos(·)/u` at `u > 0`. -/
private theorem hasDerivAt_Qsin (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ Real.sin (t / 2 * Real.log y))
      (t / 2 * Real.cos (t / 2 * Real.log u) / u) u := by
  have hlog : HasDerivAt (fun y : ℝ ↦ t / 2 * Real.log y) (t / 2 * u⁻¹) u :=
    (Real.hasDerivAt_log hu.ne').const_mul (t / 2)
  convert hlog.sin using 1
  field_simp

/-- Derivative of `y ↦ -(t/2)·sin((t/2)·log y)/y`. -/
private theorem hasDerivAt_Qcos' (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ -(t / 2) * Real.sin (t / 2 * Real.log y) / y)
      ((t / 2 * Real.sin (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2) u := by
  have hlog : HasDerivAt (fun y : ℝ ↦ t / 2 * Real.log y) (t / 2 * u⁻¹) u :=
    (Real.hasDerivAt_log hu.ne').const_mul (t / 2)
  have hnum : HasDerivAt (fun y : ℝ ↦ -(t / 2) * Real.sin (t / 2 * Real.log y))
      (-(t / 2) * (Real.cos (t / 2 * Real.log u) * (t / 2 * u⁻¹))) u :=
    hlog.sin.const_mul (-(t / 2))
  have h := hnum.div (hasDerivAt_id' u) hu.ne'
  convert h using 1
  field_simp
  ring

/-- Derivative of `y ↦ (t/2)·cos((t/2)·log y)/y`. -/
private theorem hasDerivAt_Qsin' (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ (t / 2) * Real.cos (t / 2 * Real.log y) / y)
      ((-(t / 2) * Real.cos (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)) / u ^ 2) u := by
  have hlog : HasDerivAt (fun y : ℝ ↦ t / 2 * Real.log y) (t / 2 * u⁻¹) u :=
    (Real.hasDerivAt_log hu.ne').const_mul (t / 2)
  have hnum : HasDerivAt (fun y : ℝ ↦ (t / 2) * Real.cos (t / 2 * Real.log y))
      ((t / 2) * (-Real.sin (t / 2 * Real.log u) * (t / 2 * u⁻¹))) u :=
    hlog.cos.const_mul (t / 2)
  have h := hnum.div (hasDerivAt_id' u) hu.ne'
  convert h using 1
  field_simp
  ring

/-- `y ↦ exp(-π(n+1)²·y)` derivative. -/
private theorem hasDerivAt_R (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      (-π * ((n : ℝ) + 1) ^ 2
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)) u := by
  have h := ((hasDerivAt_id' u).const_mul (-π * ((n : ℝ) + 1) ^ 2)).exp
  convert h using 1
  ring

/-- `y ↦ -π(n+1)²·exp(-π(n+1)²·y)` derivative. -/
private theorem hasDerivAt_R' (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -π * ((n : ℝ) + 1) ^ 2
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      ((π * ((n : ℝ) + 1) ^ 2) ^ 2
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)) u := by
  have h := (hasDerivAt_R n u).const_mul (-π * ((n : ℝ) + 1) ^ 2)
  convert h using 1
  ring

/-- Pointwise triple-product Leibniz (r315 template). -/
private theorem hasDerivAt_mul3 {P Q R : ℝ → ℝ} {p q r u : ℝ}
    (hP : HasDerivAt P p u) (hQ : HasDerivAt Q q u) (hR : HasDerivAt R r u) :
    HasDerivAt (fun y ↦ P y * Q y * R y)
      (p * Q u * R u + P u * q * R u + P u * Q u * r) u := by
  have h := (hP.fun_mul hQ).fun_mul hR
  convert h using 1
  ring

/-! ### §9.1.b — HasDerivAt for the elementary terms and their first derivatives -/

/-- `thetaPowCosTerm a t n` has derivative `thetaPowCosTermD1 a t n u` at `u > 0`. -/
theorem hasDerivAt_thetaPowCosTerm (a t : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaPowCosTerm a t n y)
      (thetaPowCosTermD1 a t n u) u := by
  have h := hasDerivAt_mul3 (hasDerivAt_powP a hu) (hasDerivAt_Qcos t hu)
    (hasDerivAt_R n u)
  convert h using 1

/-- `thetaPowSinTerm a t n` has derivative `thetaPowSinTermD1 a t n u` at `u > 0`. -/
theorem hasDerivAt_thetaPowSinTerm (a t : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaPowSinTerm a t n y)
      (thetaPowSinTermD1 a t n u) u := by
  have h := hasDerivAt_mul3 (hasDerivAt_powP a hu) (hasDerivAt_Qsin t hu)
    (hasDerivAt_R n u)
  convert h using 1

/-- `thetaPowCosTermD1 a t n` has derivative `thetaPowCosTermD2 a t n u` at `u > 0`. -/
theorem hasDerivAt_thetaPowCosTermD1 (a t : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaPowCosTermD1 a t n y)
      (thetaPowCosTermD2 a t n u) u := by
  have h1 := hasDerivAt_mul3 (hasDerivAt_powP' a hu) (hasDerivAt_Qcos t hu)
    (hasDerivAt_R n u)
  have h2 := hasDerivAt_mul3 (hasDerivAt_powP a hu) (hasDerivAt_Qcos' t hu)
    (hasDerivAt_R n u)
  have h3 := hasDerivAt_mul3 (hasDerivAt_powP a hu) (hasDerivAt_Qcos t hu)
    (hasDerivAt_R' n u)
  have h := (h1.add h2).add h3
  convert h using 1
  simp only [thetaPowCosTermD2]
  ring

/-- `thetaPowSinTermD1 a t n` has derivative `thetaPowSinTermD2 a t n u` at `u > 0`. -/
theorem hasDerivAt_thetaPowSinTermD1 (a t : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaPowSinTermD1 a t n y)
      (thetaPowSinTermD2 a t n u) u := by
  have h1 := hasDerivAt_mul3 (hasDerivAt_powP' a hu) (hasDerivAt_Qsin t hu)
    (hasDerivAt_R n u)
  have h2 := hasDerivAt_mul3 (hasDerivAt_powP a hu) (hasDerivAt_Qsin' t hu)
    (hasDerivAt_R n u)
  have h3 := hasDerivAt_mul3 (hasDerivAt_powP a hu) (hasDerivAt_Qsin t hu)
    (hasDerivAt_R' n u)
  have h := (h1.add h2).add h3
  convert h using 1
  simp only [thetaPowSinTermD2]
  ring

/-! ### §9.1.c — Elementary factor absolute value bounds

Uniform in exponent `a ∈ [-p1, 0]` and segment lower endpoint `L ≤ u`,
`1 ≤ L`.  These are the ingredients of the six-term Leibniz D2 bound. -/

/-- `|u^a| ≤ 1` for `a ≤ 0`, `u ≥ 1`. -/
private lemma abs_powP_le_one {a u : ℝ} (ha_np : a ≤ 0) (hu : 1 ≤ u) :
    |u ^ a| ≤ 1 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  rw [abs_of_nonneg (Real.rpow_nonneg hu0.le a)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hu ha_np

/-- `|a·u^(a-1)| ≤ p1` for `|a| ≤ p1`, `a ≤ 0`, `u ≥ 1`. -/
private lemma abs_powP_D1_le {a u p1 : ℝ}
    (hp1 : |a| ≤ p1) (ha_np : a ≤ 0) (hu : 1 ≤ u) :
    |a * u ^ (a - 1)| ≤ p1 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have ha1_np : a - 1 ≤ 0 := by linarith
  have h_pw : |u ^ (a - 1)| ≤ 1 := abs_powP_le_one ha1_np hu
  have h_pw_nn : 0 ≤ u ^ (a - 1) := Real.rpow_nonneg hu0.le _
  rw [abs_mul, abs_of_nonneg h_pw_nn]
  calc |a| * u ^ (a - 1)
      ≤ p1 * u ^ (a - 1) := by
        exact mul_le_mul_of_nonneg_right hp1 h_pw_nn
    _ ≤ p1 * 1 := by
        have hp1_nn : 0 ≤ p1 := (abs_nonneg a).trans hp1
        exact mul_le_mul_of_nonneg_left
          ((abs_of_nonneg h_pw_nn ▸ h_pw : u ^ (a - 1) ≤ 1)) hp1_nn
    _ = p1 := mul_one _

/-- `|a·(a-1)·u^(a-2)| ≤ p2` for `|a·(a-1)| ≤ p2`, `a ≤ 0`, `u ≥ 1`. -/
private lemma abs_powP_D2_le {a u p2 : ℝ}
    (hp2 : |a * (a - 1)| ≤ p2) (ha_np : a ≤ 0) (hu : 1 ≤ u) :
    |a * (a - 1) * u ^ (a - 2)| ≤ p2 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have ha2_np : a - 2 ≤ 0 := by linarith
  have h_pw : |u ^ (a - 2)| ≤ 1 := abs_powP_le_one ha2_np hu
  have h_pw_nn : 0 ≤ u ^ (a - 2) := Real.rpow_nonneg hu0.le _
  rw [abs_mul, abs_of_nonneg h_pw_nn]
  calc |a * (a - 1)| * u ^ (a - 2)
      ≤ p2 * u ^ (a - 2) := mul_le_mul_of_nonneg_right hp2 h_pw_nn
    _ ≤ p2 * 1 := by
        have hp2_nn : 0 ≤ p2 := (abs_nonneg _).trans hp2
        exact mul_le_mul_of_nonneg_left
          ((abs_of_nonneg h_pw_nn ▸ h_pw : u ^ (a - 2) ≤ 1)) hp2_nn
    _ = p2 := mul_one _

/-- `|cos((t/2)·log u)| ≤ 1`. -/
private lemma abs_Qcos_le_one (t u : ℝ) :
    |Real.cos (t / 2 * Real.log u)| ≤ 1 := Real.abs_cos_le_one _

/-- `|sin((t/2)·log u)| ≤ 1`. -/
private lemma abs_Qsin_le_one (t u : ℝ) :
    |Real.sin (t / 2 * Real.log u)| ≤ 1 := Real.abs_sin_le_one _

/-- `|-(t/2)·sin((t/2)·log u)/u| ≤ |t|/2` for `u ≥ 1`. -/
private lemma abs_Qcos_D1_le {t u : ℝ} (hu : 1 ≤ u) :
    |-(t / 2) * Real.sin (t / 2 * Real.log u) / u| ≤ |t| / 2 := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have h_num : |-(t / 2) * Real.sin (t / 2 * Real.log u)| ≤ |t| / 2 := by
    rw [abs_mul, abs_neg, abs_div, abs_two]
    have hcos_bd : |Real.sin (t / 2 * Real.log u)| ≤ 1 := Real.abs_sin_le_one _
    calc |t| / 2 * |Real.sin (t / 2 * Real.log u)|
        ≤ |t| / 2 * 1 := by
          apply mul_le_mul_of_nonneg_left hcos_bd
          exact div_nonneg (abs_nonneg _) (by norm_num)
      _ = |t| / 2 := mul_one _
  rw [abs_div, abs_of_pos hu_pos]
  have h_num_nn : (0 : ℝ) ≤ |t| / 2 := div_nonneg (abs_nonneg _) (by norm_num)
  have h_uinv_le_one : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu
  have h_uinv_nn : (0 : ℝ) ≤ u⁻¹ := inv_nonneg.mpr hu_pos.le
  calc |-(t / 2) * Real.sin (t / 2 * Real.log u)| / u
      = |-(t / 2) * Real.sin (t / 2 * Real.log u)| * u⁻¹ := div_eq_mul_inv _ _
    _ ≤ (|t| / 2) * u⁻¹ := mul_le_mul_of_nonneg_right h_num h_uinv_nn
    _ ≤ (|t| / 2) * 1 := mul_le_mul_of_nonneg_left h_uinv_le_one h_num_nn
    _ = |t| / 2 := mul_one _

/-- `|(t/2)·cos((t/2)·log u)/u| ≤ |t|/2` for `u ≥ 1`. -/
private lemma abs_Qsin_D1_le {t u : ℝ} (hu : 1 ≤ u) :
    |(t / 2) * Real.cos (t / 2 * Real.log u) / u| ≤ |t| / 2 := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have h_num : |(t / 2) * Real.cos (t / 2 * Real.log u)| ≤ |t| / 2 := by
    rw [abs_mul, abs_div, abs_two]
    have hcos_bd : |Real.cos (t / 2 * Real.log u)| ≤ 1 := Real.abs_cos_le_one _
    calc |t| / 2 * |Real.cos (t / 2 * Real.log u)|
        ≤ |t| / 2 * 1 := by
          apply mul_le_mul_of_nonneg_left hcos_bd
          exact div_nonneg (abs_nonneg _) (by norm_num)
      _ = |t| / 2 := mul_one _
  rw [abs_div, abs_of_pos hu_pos]
  have h_num_nn : (0 : ℝ) ≤ |t| / 2 := div_nonneg (abs_nonneg _) (by norm_num)
  have h_uinv_le_one : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu
  have h_uinv_nn : (0 : ℝ) ≤ u⁻¹ := inv_nonneg.mpr hu_pos.le
  calc |(t / 2) * Real.cos (t / 2 * Real.log u)| / u
      = |(t / 2) * Real.cos (t / 2 * Real.log u)| * u⁻¹ := div_eq_mul_inv _ _
    _ ≤ (|t| / 2) * u⁻¹ := mul_le_mul_of_nonneg_right h_num h_uinv_nn
    _ ≤ (|t| / 2) * 1 := mul_le_mul_of_nonneg_left h_uinv_le_one h_num_nn
    _ = |t| / 2 := mul_one _

/-- `|((t/2)·sin - (t/2)²·cos)/u²| ≤ |t|/2 + (t/2)²` for `u ≥ 1`. -/
private lemma abs_Qcos_D2_le {t u : ℝ} (hu : 1 ≤ u) :
    |(t / 2 * Real.sin (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2|
      ≤ |t| / 2 + (t / 2) ^ 2 := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hu2_pos : 0 < u ^ 2 := by positivity
  have hu2_ge_one : 1 ≤ u ^ 2 := by nlinarith
  have h_num_bd :
      |t / 2 * Real.sin (t / 2 * Real.log u)
       - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)|
        ≤ |t| / 2 + (t / 2) ^ 2 := by
    calc |t / 2 * Real.sin (t / 2 * Real.log u)
          - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)|
        ≤ |t / 2 * Real.sin (t / 2 * Real.log u)|
          + |(t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)| := abs_sub _ _
      _ ≤ |t| / 2 + (t / 2) ^ 2 := by
          have h1 : |t / 2 * Real.sin (t / 2 * Real.log u)| ≤ |t| / 2 := by
            rw [abs_mul, abs_div, abs_two]
            calc |t| / 2 * |Real.sin (t / 2 * Real.log u)|
                ≤ |t| / 2 * 1 := mul_le_mul_of_nonneg_left
                    (Real.abs_sin_le_one _) (by positivity)
              _ = |t| / 2 := mul_one _
          have h2 : |(t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)| ≤ (t / 2) ^ 2 := by
            rw [abs_mul]
            calc |(t / 2) ^ 2| * |Real.cos (t / 2 * Real.log u)|
                ≤ |(t / 2) ^ 2| * 1 := mul_le_mul_of_nonneg_left
                    (Real.abs_cos_le_one _) (abs_nonneg _)
              _ = |(t / 2) ^ 2| := mul_one _
              _ = (t / 2) ^ 2 := abs_of_nonneg (sq_nonneg _)
          linarith
  rw [abs_div, abs_of_pos hu2_pos]
  have h_bd_nn : (0 : ℝ) ≤ |t| / 2 + (t / 2) ^ 2 := by positivity
  have h_u2inv_le_one : (u ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu2_ge_one
  have h_u2inv_nn : (0 : ℝ) ≤ (u ^ 2)⁻¹ := inv_nonneg.mpr hu2_pos.le
  calc |t / 2 * Real.sin (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)| / u ^ 2
      = |t / 2 * Real.sin (t / 2 * Real.log u)
          - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)| * (u ^ 2)⁻¹ :=
        div_eq_mul_inv _ _
    _ ≤ (|t| / 2 + (t / 2) ^ 2) * (u ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h_num_bd h_u2inv_nn
    _ ≤ (|t| / 2 + (t / 2) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left h_u2inv_le_one h_bd_nn
    _ = |t| / 2 + (t / 2) ^ 2 := mul_one _

/-- Sin variant of the D2 bound. -/
private lemma abs_Qsin_D2_le {t u : ℝ} (hu : 1 ≤ u) :
    |(-(t / 2) * Real.cos (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)) / u ^ 2|
      ≤ |t| / 2 + (t / 2) ^ 2 := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hu2_pos : 0 < u ^ 2 := by positivity
  have hu2_ge_one : 1 ≤ u ^ 2 := by nlinarith
  have h_num_bd :
      |-(t / 2) * Real.cos (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)|
        ≤ |t| / 2 + (t / 2) ^ 2 := by
    calc |-(t / 2) * Real.cos (t / 2 * Real.log u)
          - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)|
        ≤ |-(t / 2) * Real.cos (t / 2 * Real.log u)|
          + |(t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)| := abs_sub _ _
      _ ≤ |t| / 2 + (t / 2) ^ 2 := by
          have h1 : |-(t / 2) * Real.cos (t / 2 * Real.log u)| ≤ |t| / 2 := by
            rw [abs_mul, abs_neg, abs_div, abs_two]
            calc |t| / 2 * |Real.cos (t / 2 * Real.log u)|
                ≤ |t| / 2 * 1 := mul_le_mul_of_nonneg_left
                    (Real.abs_cos_le_one _) (by positivity)
              _ = |t| / 2 := mul_one _
          have h2 : |(t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)| ≤ (t / 2) ^ 2 := by
            rw [abs_mul]
            calc |(t / 2) ^ 2| * |Real.sin (t / 2 * Real.log u)|
                ≤ |(t / 2) ^ 2| * 1 := mul_le_mul_of_nonneg_left
                    (Real.abs_sin_le_one _) (abs_nonneg _)
              _ = |(t / 2) ^ 2| := mul_one _
              _ = (t / 2) ^ 2 := abs_of_nonneg (sq_nonneg _)
          linarith
  rw [abs_div, abs_of_pos hu2_pos]
  have h_bd_nn : (0 : ℝ) ≤ |t| / 2 + (t / 2) ^ 2 := by positivity
  have h_u2inv_le_one : (u ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu2_ge_one
  have h_u2inv_nn : (0 : ℝ) ≤ (u ^ 2)⁻¹ := inv_nonneg.mpr hu2_pos.le
  calc |-(t / 2) * Real.cos (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)| / u ^ 2
      = |-(t / 2) * Real.cos (t / 2 * Real.log u)
          - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)| * (u ^ 2)⁻¹ :=
        div_eq_mul_inv _ _
    _ ≤ (|t| / 2 + (t / 2) ^ 2) * (u ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h_num_bd h_u2inv_nn
    _ ≤ (|t| / 2 + (t / 2) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left h_u2inv_le_one h_bd_nn
    _ = |t| / 2 + (t / 2) ^ 2 := mul_one _

/-- `|exp(-π(n+1)²u)| ≤ exp(-π(n+1)²L)` for `L ≤ u`. -/
private lemma abs_R_le {n : ℕ} {L u : ℝ} (hLu : L ≤ u) :
    |Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
      ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * L) := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hπnn : 0 ≤ π * ((n : ℝ) + 1) ^ 2 := by
    have : 0 ≤ π := Real.pi_pos.le
    positivity
  nlinarith

/-- `|R'| = π(n+1)²·|exp(...)| ≤ A·exp(-A·L)` where `A = π(n+1)²`. -/
private lemma abs_R_D1_le {n : ℕ} {L u : ℝ} (hLu : L ≤ u) :
    |-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
      ≤ π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * L) := by
  have hR := abs_R_le (n := n) (L := L) (u := u) hLu
  have hπnn : 0 ≤ π * ((n : ℝ) + 1) ^ 2 := by
    have : 0 ≤ π := Real.pi_pos.le; positivity
  rw [show (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
        = -(π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
      from by ring, abs_neg, abs_mul, abs_of_nonneg hπnn]
  exact mul_le_mul_of_nonneg_left hR hπnn

/-- `|R''| ≤ A²·exp(-A·L)`. -/
private lemma abs_R_D2_le {n : ℕ} {L u : ℝ} (hLu : L ≤ u) :
    |(π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
      ≤ (π * ((n : ℝ) + 1) ^ 2) ^ 2
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * L) := by
  have hR := abs_R_le (n := n) (L := L) (u := u) hLu
  have hπnn : 0 ≤ (π * ((n : ℝ) + 1) ^ 2) ^ 2 := sq_nonneg _
  rw [abs_mul, abs_of_nonneg hπnn]
  exact mul_le_mul_of_nonneg_left hR hπnn

/-! ### §9.1.d — Explicit `M_term` bound and D2 absolute bound

`M_term` = closed-form uniform bound on `|thetaPowCosTermD2 a t n u|` and
`|thetaPowSinTermD2 a t n u|` for `a ∈ [-p1, 0]` with `|a(a-1)| ≤ p2`,
`u ∈ [L, ∞)`, `L ≥ 1`.

Structure (six terms via triangle + triple-product bound):

  `M_term(t, p1, p2, n, L) = exp(-A_n·L) · (p2 + c₁ + c₂ + A_n² + 2p1c₁ + 2p1A_n + 2c₁A_n)`

where `c₁ = |t|/2`, `c₂ = (t/2)²`, `A_n = π(n+1)²`. -/

/-- Uniform `C²` bound constant for the elementary term. -/
noncomputable def thetaPowTermM (t p1 p2 L : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-π * ((n : ℝ) + 1) ^ 2 * L) *
    (p2 + (|t| / 2 + (t / 2) ^ 2)
      + (π * ((n : ℝ) + 1) ^ 2) ^ 2
      + 2 * p1 * (|t| / 2)
      + 2 * p1 * (π * ((n : ℝ) + 1) ^ 2)
      + 2 * (|t| / 2) * (π * ((n : ℝ) + 1) ^ 2))

/-- Triple-product absolute bound from factor bounds. -/
private lemma abs_triple_le {x y z bx by' bz : ℝ}
    (hx : |x| ≤ bx) (hy : |y| ≤ by') (hz : |z| ≤ bz) :
    |x * y * z| ≤ bx * by' * bz := by
  have hbx : 0 ≤ bx := (abs_nonneg x).trans hx
  have hby : 0 ≤ by' := (abs_nonneg y).trans hy
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg y) hbx) hz (abs_nonneg z)
    (mul_nonneg hbx hby)

/-- Six-term triangle inequality matching the shape of `thetaPowCosTermD2` /
`thetaPowSinTermD2`. -/
private lemma abs_sum6_le {x₁ x₂ x₃ x₄ x₅ x₆ b₁ b₂ b₃ b₄ b₅ b₆ : ℝ}
    (h₁ : |x₁| ≤ b₁) (h₂ : |x₂| ≤ b₂) (h₃ : |x₃| ≤ b₃)
    (h₄ : |x₄| ≤ b₄) (h₅ : |x₅| ≤ b₅) (h₆ : |x₆| ≤ b₆) :
    |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅ + 2 * x₆|
      ≤ b₁ + b₂ + b₃ + 2 * b₄ + 2 * b₅ + 2 * b₆ := by
  have k₄ : |2 * x₄| ≤ 2 * b₄ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₄]
  have k₅ : |2 * x₅| ≤ 2 * b₅ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₅]
  have k₆ : |2 * x₆| ≤ 2 * b₆ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₆]
  calc |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅ + 2 * x₆|
      ≤ |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅| + |2 * x₆| := abs_add _ _
    _ ≤ |x₁ + x₂ + x₃ + 2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂ + x₃ + 2 * x₄) (2 * x₅)]
    _ ≤ |x₁ + x₂ + x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂ + x₃) (2 * x₄)]
    _ ≤ |x₁ + x₂| + |x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂) x₃]
    _ ≤ |x₁| + |x₂| + |x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add x₁ x₂]
    _ ≤ b₁ + b₂ + b₃ + 2 * b₄ + 2 * b₅ + 2 * b₆ := by linarith

/-- **C² bound on the cos-branch elementary term.**  `M_term` is uniform in
`a` (given `|a| ≤ p1`, `|a(a-1)| ≤ p2`, `a ≤ 0`) and uniform in `u` (given
`L ≤ u`, `1 ≤ L`). -/
theorem abs_thetaPowCosTermD2_le
    {a t p1 p2 L : ℝ}
    (ha_np : a ≤ 0) (hp1 : |a| ≤ p1) (hp2 : |a * (a - 1)| ≤ p2)
    (n : ℕ) {u : ℝ} (hL : 1 ≤ L) (hu : L ≤ u) :
    |thetaPowCosTermD2 a t n u| ≤ thetaPowTermM t p1 p2 L n := by
  have hLu1 : 1 ≤ u := hL.trans hu
  set E := Real.exp (-π * ((n : ℝ) + 1) ^ 2 * L)
  -- Factor bounds
  have hP : |u ^ a| ≤ 1 := abs_powP_le_one ha_np hLu1
  have hP' : |a * u ^ (a - 1)| ≤ p1 := abs_powP_D1_le hp1 ha_np hLu1
  have hP'' : |a * (a - 1) * u ^ (a - 2)| ≤ p2 := abs_powP_D2_le hp2 ha_np hLu1
  have hQ : |Real.cos (t / 2 * Real.log u)| ≤ 1 := abs_Qcos_le_one _ _
  have hQ' : |-(t / 2) * Real.sin (t / 2 * Real.log u) / u| ≤ |t| / 2 :=
    abs_Qcos_D1_le hLu1
  have hQ'' :
      |(t / 2 * Real.sin (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2|
        ≤ |t| / 2 + (t / 2) ^ 2 :=
    abs_Qcos_D2_le hLu1
  have hR : |Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)| ≤ E := abs_R_le hu
  have hR' :
      |-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ π * ((n : ℝ) + 1) ^ 2 * E := abs_R_D1_le hu
  have hR'' :
      |(π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ (π * ((n : ℝ) + 1) ^ 2) ^ 2 * E := abs_R_D2_le hu
  -- Bound each of the six Leibniz terms
  have bd1 :
      |a * (a - 1) * u ^ (a - 2) * Real.cos (t / 2 * Real.log u)
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ p2 * 1 * E := abs_triple_le hP'' hQ hR
  have bd2 :
      |u ^ a
        * ((t / 2 * Real.sin (t / 2 * Real.log u)
            - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2)
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ 1 * (|t| / 2 + (t / 2) ^ 2) * E := abs_triple_le hP hQ'' hR
  have bd3 :
      |u ^ a * Real.cos (t / 2 * Real.log u)
        * ((π * ((n : ℝ) + 1) ^ 2) ^ 2
            * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))|
        ≤ 1 * 1 * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * E) := abs_triple_le hP hQ hR''
  have bd4 :
      |a * u ^ (a - 1)
        * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ p1 * (|t| / 2) * E := abs_triple_le hP' hQ' hR
  have bd5 :
      |a * u ^ (a - 1) * Real.cos (t / 2 * Real.log u)
        * (-π * ((n : ℝ) + 1) ^ 2
            * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))|
        ≤ p1 * 1 * (π * ((n : ℝ) + 1) ^ 2 * E) := abs_triple_le hP' hQ hR'
  have bd6 :
      |u ^ a * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
        * (-π * ((n : ℝ) + 1) ^ 2
            * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))|
        ≤ 1 * (|t| / 2) * (π * ((n : ℝ) + 1) ^ 2 * E) := abs_triple_le hP hQ' hR'
  -- Sum via abs_sum6_le
  have h_sum := abs_sum6_le bd1 bd2 bd3 bd4 bd5 bd6
  -- Show LHS = |thetaPowCosTermD2| and RHS = thetaPowTermM ...
  unfold thetaPowCosTermD2 thetaPowTermM
  calc |a * (a - 1) * u ^ (a - 2) * Real.cos (t / 2 * Real.log u)
          * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
        + u ^ a * ((t / 2 * Real.sin (t / 2 * Real.log u)
              - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2)
          * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
        + u ^ a * Real.cos (t / 2 * Real.log u)
          * ((π * ((n : ℝ) + 1) ^ 2) ^ 2
              * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
        + 2 * (a * u ^ (a - 1)
          * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
          * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
        + 2 * (a * u ^ (a - 1) * Real.cos (t / 2 * Real.log u)
          * (-π * ((n : ℝ) + 1) ^ 2
              * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))
        + 2 * (u ^ a * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
          * (-π * ((n : ℝ) + 1) ^ 2
              * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))|
      ≤ p2 * 1 * E + 1 * (|t| / 2 + (t / 2) ^ 2) * E
        + 1 * 1 * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * E)
        + 2 * (p1 * (|t| / 2) * E)
        + 2 * (p1 * 1 * (π * ((n : ℝ) + 1) ^ 2 * E))
        + 2 * (1 * (|t| / 2) * (π * ((n : ℝ) + 1) ^ 2 * E)) := h_sum
    _ = E * (p2 + (|t| / 2 + (t / 2) ^ 2)
              + (π * ((n : ℝ) + 1) ^ 2) ^ 2
              + 2 * p1 * (|t| / 2)
              + 2 * p1 * (π * ((n : ℝ) + 1) ^ 2)
              + 2 * (|t| / 2) * (π * ((n : ℝ) + 1) ^ 2)) := by ring

/-- Sin-branch companion of `abs_thetaPowCosTermD2_le`. -/
theorem abs_thetaPowSinTermD2_le
    {a t p1 p2 L : ℝ}
    (ha_np : a ≤ 0) (hp1 : |a| ≤ p1) (hp2 : |a * (a - 1)| ≤ p2)
    (n : ℕ) {u : ℝ} (hL : 1 ≤ L) (hu : L ≤ u) :
    |thetaPowSinTermD2 a t n u| ≤ thetaPowTermM t p1 p2 L n := by
  have hLu1 : 1 ≤ u := hL.trans hu
  set E := Real.exp (-π * ((n : ℝ) + 1) ^ 2 * L)
  have hP : |u ^ a| ≤ 1 := abs_powP_le_one ha_np hLu1
  have hP' : |a * u ^ (a - 1)| ≤ p1 := abs_powP_D1_le hp1 ha_np hLu1
  have hP'' : |a * (a - 1) * u ^ (a - 2)| ≤ p2 := abs_powP_D2_le hp2 ha_np hLu1
  have hQ : |Real.sin (t / 2 * Real.log u)| ≤ 1 := abs_Qsin_le_one _ _
  have hQ' : |(t / 2) * Real.cos (t / 2 * Real.log u) / u| ≤ |t| / 2 :=
    abs_Qsin_D1_le hLu1
  have hQ'' :
      |(-(t / 2) * Real.cos (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)) / u ^ 2|
        ≤ |t| / 2 + (t / 2) ^ 2 :=
    abs_Qsin_D2_le hLu1
  have hR : |Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)| ≤ E := abs_R_le hu
  have hR' :
      |-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ π * ((n : ℝ) + 1) ^ 2 * E := abs_R_D1_le hu
  have hR'' :
      |(π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ (π * ((n : ℝ) + 1) ^ 2) ^ 2 * E := abs_R_D2_le hu
  have bd1 :
      |a * (a - 1) * u ^ (a - 2) * Real.sin (t / 2 * Real.log u)
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ p2 * 1 * E := abs_triple_le hP'' hQ hR
  have bd2 :
      |u ^ a
        * ((-(t / 2) * Real.cos (t / 2 * Real.log u)
            - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)) / u ^ 2)
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ 1 * (|t| / 2 + (t / 2) ^ 2) * E := abs_triple_le hP hQ'' hR
  have bd3 :
      |u ^ a * Real.sin (t / 2 * Real.log u)
        * ((π * ((n : ℝ) + 1) ^ 2) ^ 2
            * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))|
        ≤ 1 * 1 * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * E) := abs_triple_le hP hQ hR''
  have bd4 :
      |a * u ^ (a - 1)
        * ((t / 2) * Real.cos (t / 2 * Real.log u) / u)
        * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
        ≤ p1 * (|t| / 2) * E := abs_triple_le hP' hQ' hR
  have bd5 :
      |a * u ^ (a - 1) * Real.sin (t / 2 * Real.log u)
        * (-π * ((n : ℝ) + 1) ^ 2
            * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))|
        ≤ p1 * 1 * (π * ((n : ℝ) + 1) ^ 2 * E) := abs_triple_le hP' hQ hR'
  have bd6 :
      |u ^ a * ((t / 2) * Real.cos (t / 2 * Real.log u) / u)
        * (-π * ((n : ℝ) + 1) ^ 2
            * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))|
        ≤ 1 * (|t| / 2) * (π * ((n : ℝ) + 1) ^ 2 * E) := abs_triple_le hP hQ' hR'
  have h_sum := abs_sum6_le bd1 bd2 bd3 bd4 bd5 bd6
  unfold thetaPowSinTermD2 thetaPowTermM
  calc |a * (a - 1) * u ^ (a - 2) * Real.sin (t / 2 * Real.log u)
          * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
        + u ^ a * ((-(t / 2) * Real.cos (t / 2 * Real.log u)
              - (t / 2) ^ 2 * Real.sin (t / 2 * Real.log u)) / u ^ 2)
          * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
        + u ^ a * Real.sin (t / 2 * Real.log u)
          * ((π * ((n : ℝ) + 1) ^ 2) ^ 2
              * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
        + 2 * (a * u ^ (a - 1)
          * ((t / 2) * Real.cos (t / 2 * Real.log u) / u)
          * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
        + 2 * (a * u ^ (a - 1) * Real.sin (t / 2 * Real.log u)
          * (-π * ((n : ℝ) + 1) ^ 2
              * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))
        + 2 * (u ^ a * ((t / 2) * Real.cos (t / 2 * Real.log u) / u)
          * (-π * ((n : ℝ) + 1) ^ 2
              * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))|
      ≤ p2 * 1 * E + 1 * (|t| / 2 + (t / 2) ^ 2) * E
        + 1 * 1 * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * E)
        + 2 * (p1 * (|t| / 2) * E)
        + 2 * (p1 * 1 * (π * ((n : ℝ) + 1) ^ 2 * E))
        + 2 * (1 * (|t| / 2) * (π * ((n : ℝ) + 1) ^ 2 * E)) := h_sum
    _ = E * (p2 + (|t| / 2 + (t / 2) ^ 2)
              + (π * ((n : ℝ) + 1) ^ 2) ^ 2
              + 2 * p1 * (|t| / 2)
              + 2 * p1 * (π * ((n : ℝ) + 1) ^ 2)
              + 2 * (|t| / 2) * (π * ((n : ℝ) + 1) ^ 2)) := by ring

/-! ## §9.2 — Finite `N`-term sums of the elementary theta terms

Follows r315's `hasDerivAt_thetaTerm_sum` template.  Extends to the sin
branch and to the σ-parameterized generic term.  D2 sum bound reduces to
`Σ n<N, thetaPowTermM t p1 p2 L n` via `Finset.abs_sum_le_sum_abs` +
`abs_thetaPow(Cos/Sin)TermD2_le`. -/

/-- Sum over `n < N` of cos-branch elementary terms. -/
noncomputable def thetaPowCosSum (a t : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, thetaPowCosTerm a t n u

/-- Sum over `n < N` of sin-branch elementary terms. -/
noncomputable def thetaPowSinSum (a t : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, thetaPowSinTerm a t n u

/-- Sum first-derivative expression (cos branch). -/
noncomputable def thetaPowCosSumD1 (a t : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, thetaPowCosTermD1 a t n u

/-- Sum first-derivative expression (sin branch). -/
noncomputable def thetaPowSinSumD1 (a t : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, thetaPowSinTermD1 a t n u

/-- Sum second-derivative expression (cos branch). -/
noncomputable def thetaPowCosSumD2 (a t : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, thetaPowCosTermD2 a t n u

/-- Sum second-derivative expression (sin branch). -/
noncomputable def thetaPowSinSumD2 (a t : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, thetaPowSinTermD2 a t n u

/-- First derivative of the cos-branch sum. -/
theorem hasDerivAt_thetaPowCosSum (a t : ℝ) (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaPowCosSum a t N y)
      (thetaPowCosSumD1 a t N u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_thetaPowCosTerm a t n hu

/-- First derivative of the sin-branch sum. -/
theorem hasDerivAt_thetaPowSinSum (a t : ℝ) (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaPowSinSum a t N y)
      (thetaPowSinSumD1 a t N u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_thetaPowSinTerm a t n hu

/-- Second derivative of the cos-branch sum. -/
theorem hasDerivAt_thetaPowCosSumD1 (a t : ℝ) (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaPowCosSumD1 a t N y)
      (thetaPowCosSumD2 a t N u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_thetaPowCosTermD1 a t n hu

/-- Second derivative of the sin-branch sum. -/
theorem hasDerivAt_thetaPowSinSumD1 (a t : ℝ) (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaPowSinSumD1 a t N y)
      (thetaPowSinSumD2 a t N u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_thetaPowSinTermD1 a t n hu

/-- Absolute-value bound on the cos-branch sum D2, uniform in `a` and `u`. -/
theorem abs_thetaPowCosSumD2_le
    {a t p1 p2 L : ℝ}
    (ha_np : a ≤ 0) (hp1 : |a| ≤ p1) (hp2 : |a * (a - 1)| ≤ p2)
    (N : ℕ) {u : ℝ} (hL : 1 ≤ L) (hu : L ≤ u) :
    |thetaPowCosSumD2 a t N u|
      ≤ ∑ n ∈ Finset.range N, thetaPowTermM t p1 p2 L n :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun n _ ↦ abs_thetaPowCosTermD2_le ha_np hp1 hp2 n hL hu)

/-- Absolute-value bound on the sin-branch sum D2, uniform in `a` and `u`. -/
theorem abs_thetaPowSinSumD2_le
    {a t p1 p2 L : ℝ}
    (ha_np : a ≤ 0) (hp1 : |a| ≤ p1) (hp2 : |a * (a - 1)| ≤ p2)
    (N : ℕ) {u : ℝ} (hL : 1 ≤ L) (hu : L ≤ u) :
    |thetaPowSinSumD2 a t N u|
      ≤ ∑ n ∈ Finset.range N, thetaPowTermM t p1 p2 L n :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun n _ ↦ abs_thetaPowSinTermD2_le ha_np hp1 hp2 n hL hu)

/-! ## §9.3 — Assembly identities: connect §8 `realThetaN` to sum form

Distribute `(u^(σ/2-1) + u^((1-σ)/2-1)) · cos((t/2) log u) · omegaPartial N u`
into `Σ_{n<N} [thetaPowCosTerm (σ/2-1) t n u + thetaPowCosTerm ((1-σ)/2-1) t n u]`.

Same for sin variant with `-` between branches. -/

/-- Assembly identity for the real truncated integrand. -/
theorem realThetaReIntegrandN_eq_sum (N : ℕ) (σ t u : ℝ) :
    realThetaReIntegrandN N σ t u
      = thetaPowCosSum (σ / 2 - 1) t N u
        + thetaPowCosSum ((1 - σ) / 2 - 1) t N u := by
  unfold realThetaReIntegrandN thetaPowCosSum thetaPowCosTerm omegaPartial
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- Assembly identity for the imaginary truncated integrand. -/
theorem realThetaImIntegrandN_eq_sum (N : ℕ) (σ t u : ℝ) :
    realThetaImIntegrandN N σ t u
      = thetaPowSinSum (σ / 2 - 1) t N u
        - thetaPowSinSum ((1 - σ) / 2 - 1) t N u := by
  unfold realThetaImIntegrandN thetaPowSinSum thetaPowSinTerm omegaPartial
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-! ## §9.4 — D1 and D2 for `realThetaReIntegrandN` / `realThetaImIntegrandN`

Explicit derivative expressions plus HasDerivAt witnesses via §9.2 sums
and §9.3 assembly.  These are the `f'` and `f''` witnesses that
`XiQuadrature.composite_midpoint_error` will consume per segment. -/

/-- First derivative of `realThetaReIntegrandN` via §9.3 assembly. -/
noncomputable def realThetaReIntegrandND1 (N : ℕ) (σ t u : ℝ) : ℝ :=
  thetaPowCosSumD1 (σ / 2 - 1) t N u
    + thetaPowCosSumD1 ((1 - σ) / 2 - 1) t N u

/-- Second derivative of `realThetaReIntegrandN`. -/
noncomputable def realThetaReIntegrandND2 (N : ℕ) (σ t u : ℝ) : ℝ :=
  thetaPowCosSumD2 (σ / 2 - 1) t N u
    + thetaPowCosSumD2 ((1 - σ) / 2 - 1) t N u

/-- First derivative of `realThetaImIntegrandN`. -/
noncomputable def realThetaImIntegrandND1 (N : ℕ) (σ t u : ℝ) : ℝ :=
  thetaPowSinSumD1 (σ / 2 - 1) t N u
    - thetaPowSinSumD1 ((1 - σ) / 2 - 1) t N u

/-- Second derivative of `realThetaImIntegrandN`. -/
noncomputable def realThetaImIntegrandND2 (N : ℕ) (σ t u : ℝ) : ℝ :=
  thetaPowSinSumD2 (σ / 2 - 1) t N u
    - thetaPowSinSumD2 ((1 - σ) / 2 - 1) t N u

/-- HasDerivAt for the real truncated integrand. -/
theorem hasDerivAt_realThetaReIntegrandN (N : ℕ) (σ t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ realThetaReIntegrandN N σ t y)
      (realThetaReIntegrandND1 N σ t u) u := by
  have h_eq :
      (fun y : ℝ ↦ realThetaReIntegrandN N σ t y)
        = fun y : ℝ ↦ thetaPowCosSum (σ / 2 - 1) t N y
            + thetaPowCosSum ((1 - σ) / 2 - 1) t N y := by
    funext y; exact realThetaReIntegrandN_eq_sum N σ t y
  rw [h_eq]
  exact (hasDerivAt_thetaPowCosSum (σ / 2 - 1) t N hu).add
    (hasDerivAt_thetaPowCosSum ((1 - σ) / 2 - 1) t N hu)

/-- HasDerivAt for the imag truncated integrand. -/
theorem hasDerivAt_realThetaImIntegrandN (N : ℕ) (σ t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ realThetaImIntegrandN N σ t y)
      (realThetaImIntegrandND1 N σ t u) u := by
  have h_eq :
      (fun y : ℝ ↦ realThetaImIntegrandN N σ t y)
        = fun y : ℝ ↦ thetaPowSinSum (σ / 2 - 1) t N y
            - thetaPowSinSum ((1 - σ) / 2 - 1) t N y := by
    funext y; exact realThetaImIntegrandN_eq_sum N σ t y
  rw [h_eq]
  exact (hasDerivAt_thetaPowSinSum (σ / 2 - 1) t N hu).sub
    (hasDerivAt_thetaPowSinSum ((1 - σ) / 2 - 1) t N hu)

/-- D1→D2 for the real truncated integrand. -/
theorem hasDerivAt_realThetaReIntegrandND1 (N : ℕ) (σ t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ realThetaReIntegrandND1 N σ t y)
      (realThetaReIntegrandND2 N σ t u) u :=
  (hasDerivAt_thetaPowCosSumD1 (σ / 2 - 1) t N hu).add
    (hasDerivAt_thetaPowCosSumD1 ((1 - σ) / 2 - 1) t N hu)

/-- D1→D2 for the imag truncated integrand. -/
theorem hasDerivAt_realThetaImIntegrandND1 (N : ℕ) (σ t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ realThetaImIntegrandND1 N σ t y)
      (realThetaImIntegrandND2 N σ t u) u :=
  (hasDerivAt_thetaPowSinSumD1 (σ / 2 - 1) t N hu).sub
    (hasDerivAt_thetaPowSinSumD1 ((1 - σ) / 2 - 1) t N hu)

/-! ## §9.5 — Uniform `C²` bound on `realThetaRe/ImIntegrandND2`

For box 0 (`σ ∈ [1/2, 9/16]`) with `p1 = 25/32`, `p2 = 1425/1024`:
both exponents `a₁, a₂` land in `[-25/32, -23/32]`, hence in `[-p1, 0]`
with `|a·(a-1)| ≤ p2`.  The D2 sum bounds add (via triangle) to
`2·Σ_{n<N} thetaPowTermM t p1 p2 L n` — the per-coordinate bound
matching the smoke test's Msegment(L). -/

/-- Box 0 exponent-range hypothesis for `a₁ = σ/2 - 1`. -/
lemma box0_a1_range {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16) :
    -(25/32 : ℝ) ≤ σ / 2 - 1 ∧ σ / 2 - 1 ≤ -(23/32 : ℝ) := by
  refine ⟨by linarith, by linarith⟩

/-- Box 0 exponent-range hypothesis for `a₂ = (1-σ)/2 - 1`. -/
lemma box0_a2_range {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16) :
    -(25/32 : ℝ) ≤ (1 - σ) / 2 - 1 ∧ (1 - σ) / 2 - 1 ≤ -(23/32 : ℝ) := by
  refine ⟨by linarith, by linarith⟩

/-- Any `a ∈ [-25/32, -23/32]` satisfies `a ≤ 0`, `|a| ≤ 25/32`, `|a(a-1)| ≤ 1425/1024`. -/
lemma box0_a_pow_bounds {a : ℝ}
    (h_lo : -(25/32 : ℝ) ≤ a) (h_hi : a ≤ -(23/32 : ℝ)) :
    a ≤ 0 ∧ |a| ≤ 25/32 ∧ |a * (a - 1)| ≤ 1425/1024 := by
  refine ⟨by linarith, ?_, ?_⟩
  · rw [abs_le]; refine ⟨by linarith, by linarith⟩
  · -- |a·(a-1)| = |a|·|a-1|; a < 0, a-1 < 0, so a(a-1) > 0
    have ha_neg : a < 0 := by linarith
    have ha1_neg : a - 1 < 0 := by linarith
    have h_prod_pos : 0 < a * (a - 1) := mul_pos_of_neg_of_neg ha_neg ha1_neg
    rw [abs_of_pos h_prod_pos]
    -- Show a * (a-1) ≤ 1425/1024
    -- a ∈ [-25/32, -23/32], a-1 ∈ [-57/32, -55/32].
    -- max of a·(a-1) = (-25/32)·(-57/32) = 1425/1024.
    nlinarith [h_lo, h_hi, sq_nonneg (a + 25/32), sq_nonneg (a + 23/32)]

/-- Uniform C² bound on `realThetaReIntegrandND2` on box 0, per segment [L, ∞). -/
theorem abs_realThetaReIntegrandND2_le_box0 {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16)
    {L : ℝ} (hL : 1 ≤ L)
    (N : ℕ) {u : ℝ} (hu : L ≤ u) :
    |realThetaReIntegrandND2 N σ 15 u|
      ≤ 2 * ∑ n ∈ Finset.range N,
          thetaPowTermM 15 (25/32) (1425/1024) L n := by
  have ⟨ha1_lo, ha1_hi⟩ := box0_a1_range h0 h1
  have ⟨ha2_lo, ha2_hi⟩ := box0_a2_range h0 h1
  have ⟨ha1_np, ha1_p1, ha1_p2⟩ := box0_a_pow_bounds ha1_lo ha1_hi
  have ⟨ha2_np, ha2_p1, ha2_p2⟩ := box0_a_pow_bounds ha2_lo ha2_hi
  have hb1 := abs_thetaPowCosSumD2_le (t := 15) (p1 := 25/32) (p2 := 1425/1024)
    ha1_np ha1_p1 ha1_p2 N hL hu
  have hb2 := abs_thetaPowCosSumD2_le (t := 15) (p1 := 25/32) (p2 := 1425/1024)
    ha2_np ha2_p1 ha2_p2 N hL hu
  unfold realThetaReIntegrandND2
  calc |thetaPowCosSumD2 (σ / 2 - 1) 15 N u
          + thetaPowCosSumD2 ((1 - σ) / 2 - 1) 15 N u|
      ≤ |thetaPowCosSumD2 (σ / 2 - 1) 15 N u|
        + |thetaPowCosSumD2 ((1 - σ) / 2 - 1) 15 N u| := abs_add _ _
    _ ≤ (∑ n ∈ Finset.range N, thetaPowTermM 15 (25/32) (1425/1024) L n)
        + (∑ n ∈ Finset.range N, thetaPowTermM 15 (25/32) (1425/1024) L n) := by
        exact add_le_add hb1 hb2
    _ = 2 * ∑ n ∈ Finset.range N,
              thetaPowTermM 15 (25/32) (1425/1024) L n := by ring

/-- Uniform C² bound on `realThetaImIntegrandND2` on box 0, per segment [L, ∞). -/
theorem abs_realThetaImIntegrandND2_le_box0 {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16)
    {L : ℝ} (hL : 1 ≤ L)
    (N : ℕ) {u : ℝ} (hu : L ≤ u) :
    |realThetaImIntegrandND2 N σ 15 u|
      ≤ 2 * ∑ n ∈ Finset.range N,
          thetaPowTermM 15 (25/32) (1425/1024) L n := by
  have ⟨ha1_lo, ha1_hi⟩ := box0_a1_range h0 h1
  have ⟨ha2_lo, ha2_hi⟩ := box0_a2_range h0 h1
  have ⟨ha1_np, ha1_p1, ha1_p2⟩ := box0_a_pow_bounds ha1_lo ha1_hi
  have ⟨ha2_np, ha2_p1, ha2_p2⟩ := box0_a_pow_bounds ha2_lo ha2_hi
  have hb1 := abs_thetaPowSinSumD2_le (t := 15) (p1 := 25/32) (p2 := 1425/1024)
    ha1_np ha1_p1 ha1_p2 N hL hu
  have hb2 := abs_thetaPowSinSumD2_le (t := 15) (p1 := 25/32) (p2 := 1425/1024)
    ha2_np ha2_p1 ha2_p2 N hL hu
  unfold realThetaImIntegrandND2
  calc |thetaPowSinSumD2 (σ / 2 - 1) 15 N u
          - thetaPowSinSumD2 ((1 - σ) / 2 - 1) 15 N u|
      ≤ |thetaPowSinSumD2 (σ / 2 - 1) 15 N u|
        + |thetaPowSinSumD2 ((1 - σ) / 2 - 1) 15 N u| := abs_sub _ _
    _ ≤ (∑ n ∈ Finset.range N, thetaPowTermM 15 (25/32) (1425/1024) L n)
        + (∑ n ∈ Finset.range N, thetaPowTermM 15 (25/32) (1425/1024) L n) := by
        exact add_le_add hb1 hb2
    _ = 2 * ∑ n ∈ Finset.range N,
              thetaPowTermM 15 (25/32) (1425/1024) L n := by ring

/-! ## §9.6 — Per-segment midpoint error wrappers for box 0

Thin wrappers around `XiQuadrature.composite_midpoint_error` specialized to
box 0's `realThetaRe/ImIntegrandN 3 σ 15 u`.  Consume §9.4's derivative
witnesses and §9.5's uniform C² bounds. -/

/-- Composite midpoint rule error for `realThetaReIntegrandN 3 σ 15` on a
segment `[L, U] ⊆ [1, ∞)` uniformly for `σ ∈ [1/2, 9/16]`. -/
theorem box0_re_midpoint_error_on_segment
    {σ L U : ℝ} {n : ℕ} (N : ℕ)
    (hσlo : (1 : ℝ) / 2 ≤ σ) (hσhi : σ ≤ 9/16)
    (hL : 1 ≤ L) (hLU : L ≤ U) (hn : 0 < n) :
    |(∫ u in L..U, realThetaReIntegrandN N σ 15 u)
       - (U - L) / n
         * ∑ i ∈ Finset.range n,
             realThetaReIntegrandN N σ 15
               (L + (U - L) / n * (i + 1/2))|
      ≤ (2 * ∑ n' ∈ Finset.range N,
              thetaPowTermM 15 (25/32) (1425/1024) L n')
        * (U - L) ^ 3 / (24 * n ^ 2) := by
  refine PrincipiaTractalis.XiQuadrature.composite_midpoint_error
    (f := fun u => realThetaReIntegrandN N σ 15 u)
    (f' := fun u => realThetaReIntegrandND1 N σ 15 u)
    (f'' := fun u => realThetaReIntegrandND2 N σ 15 u)
    hn hLU ?_ ?_ ?_
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans hL hx.1)
    exact hasDerivAt_realThetaReIntegrandN N σ 15 hx_pos
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans hL hx.1)
    exact hasDerivAt_realThetaReIntegrandND1 N σ 15 hx_pos
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    exact abs_realThetaReIntegrandND2_le_box0 hσlo hσhi hL N hx.1

/-- Companion for the imaginary integrand. -/
theorem box0_im_midpoint_error_on_segment
    {σ L U : ℝ} {n : ℕ} (N : ℕ)
    (hσlo : (1 : ℝ) / 2 ≤ σ) (hσhi : σ ≤ 9/16)
    (hL : 1 ≤ L) (hLU : L ≤ U) (hn : 0 < n) :
    |(∫ u in L..U, realThetaImIntegrandN N σ 15 u)
       - (U - L) / n
         * ∑ i ∈ Finset.range n,
             realThetaImIntegrandN N σ 15
               (L + (U - L) / n * (i + 1/2))|
      ≤ (2 * ∑ n' ∈ Finset.range N,
              thetaPowTermM 15 (25/32) (1425/1024) L n')
        * (U - L) ^ 3 / (24 * n ^ 2) := by
  refine PrincipiaTractalis.XiQuadrature.composite_midpoint_error
    (f := fun u => realThetaImIntegrandN N σ 15 u)
    (f' := fun u => realThetaImIntegrandND1 N σ 15 u)
    (f'' := fun u => realThetaImIntegrandND2 N σ 15 u)
    hn hLU ?_ ?_ ?_
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans hL hx.1)
    exact hasDerivAt_realThetaImIntegrandN N σ 15 hx_pos
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans hL hx.1)
    exact hasDerivAt_realThetaImIntegrandND1 N σ 15 hx_pos
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    exact abs_realThetaImIntegrandND2_le_box0 hσlo hσhi hL N hx.1

/-! ## §9.7 — Box-0 power-sum / power-difference nonnegativity + endpoint enclosures

For `σ ∈ [1/2, 9/16]` and `u ≥ 1`:
* `0 ≤ u^(σ/2-1) - u^((1-σ)/2-1)` (positive because exponents differ favorably)
* `0 ≤ u^(σ/2-1) + u^((1-σ)/2-1)` (sum of positives)

Plus scalar enclosures via r331a:
* `u^(-3/4) ≤ u^(σ/2-1) ≤ u^(-23/32)`
* `u^(-25/32) ≤ u^((1-σ)/2-1) ≤ u^(-3/4)`

These let per-node midpoint certification depend only on scalar bounds of
`u^(-3/4)`, `u^(-23/32)`, `u^(-25/32)`, `cos((15/2) log u)`,
`sin((15/2) log u)`, `omegaPartial 3 u` — no σ arithmetic per node. -/

/-- Power sum nonneg on `u ≥ 1`. -/
lemma box0_pow_sum_nonneg (σ : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    (0 : ℝ) ≤ u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1) := by
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu
  exact add_nonneg (Real.rpow_nonneg hu0 _) (Real.rpow_nonneg hu0 _)

/-- Power difference nonneg on `σ ∈ [1/2, 9/16]`, `u ≥ 1`. -/
lemma box0_pow_diff_nonneg {σ : ℝ}
    (hσlo : (1 : ℝ) / 2 ≤ σ) {u : ℝ} (hu : 1 ≤ u) :
    (0 : ℝ) ≤ u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1) := by
  have h_exp_le : (1 - σ) / 2 - 1 ≤ σ / 2 - 1 := by linarith
  have := Real.rpow_le_rpow_of_exponent_le hu h_exp_le
  linarith

/-- σ-uniform lower bound `u^(σ/2-1) ≥ u^(-3/4)` on `[1/2, 9/16]`, `u ≥ 1`. -/
lemma box0_pow_a1_lb {σ : ℝ} (hσlo : (1 : ℝ) / 2 ≤ σ)
    {u : ℝ} (hu : 1 ≤ u) :
    u ^ (-(3 / 4) : ℝ) ≤ u ^ (σ / 2 - 1) := by
  have : (-(3 / 4) : ℝ) ≤ σ / 2 - 1 := by linarith
  exact Real.rpow_le_rpow_of_exponent_le hu this

/-- σ-uniform upper bound `u^(σ/2-1) ≤ u^(-23/32)` on `[1/2, 9/16]`, `u ≥ 1`. -/
lemma box0_pow_a1_ub {σ : ℝ} (hσhi : σ ≤ 9/16)
    {u : ℝ} (hu : 1 ≤ u) :
    u ^ (σ / 2 - 1) ≤ u ^ (-(23 / 32) : ℝ) := by
  have : σ / 2 - 1 ≤ -(23 / 32 : ℝ) := by linarith
  exact Real.rpow_le_rpow_of_exponent_le hu this

/-- σ-uniform lower bound `u^((1-σ)/2-1) ≥ u^(-25/32)` on `[1/2, 9/16]`, `u ≥ 1`. -/
lemma box0_pow_a2_lb {σ : ℝ} (hσhi : σ ≤ 9/16)
    {u : ℝ} (hu : 1 ≤ u) :
    u ^ (-(25 / 32) : ℝ) ≤ u ^ ((1 - σ) / 2 - 1) := by
  have : (-(25 / 32) : ℝ) ≤ (1 - σ) / 2 - 1 := by linarith
  exact Real.rpow_le_rpow_of_exponent_le hu this

/-- σ-uniform upper bound `u^((1-σ)/2-1) ≤ u^(-3/4)` on `[1/2, 9/16]`, `u ≥ 1`. -/
lemma box0_pow_a2_ub {σ : ℝ} (hσlo : (1 : ℝ) / 2 ≤ σ)
    {u : ℝ} (hu : 1 ≤ u) :
    u ^ ((1 - σ) / 2 - 1) ≤ u ^ (-(3 / 4) : ℝ) := by
  have : (1 - σ) / 2 - 1 ≤ -(3 / 4 : ℝ) := by linarith
  exact Real.rpow_le_rpow_of_exponent_le hu this

/-- σ-uniform lower bound on the power sum. -/
lemma box0_pow_sum_lb {σ : ℝ}
    (hσlo : (1 : ℝ) / 2 ≤ σ) (hσhi : σ ≤ 9/16)
    {u : ℝ} (hu : 1 ≤ u) :
    u ^ (-(3 / 4) : ℝ) + u ^ (-(25 / 32) : ℝ)
      ≤ u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1) := by
  have h1 := box0_pow_a1_lb hσlo hu
  have h2 := box0_pow_a2_lb hσhi hu
  linarith

/-- σ-uniform upper bound on the power sum. -/
lemma box0_pow_sum_ub {σ : ℝ}
    (hσlo : (1 : ℝ) / 2 ≤ σ) (hσhi : σ ≤ 9/16)
    {u : ℝ} (hu : 1 ≤ u) :
    u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1)
      ≤ u ^ (-(23 / 32) : ℝ) + u ^ (-(3 / 4) : ℝ) := by
  have h1 := box0_pow_a1_ub hσhi hu
  have h2 := box0_pow_a2_ub hσlo hu
  linarith

/-- σ-uniform upper bound on the power difference. -/
lemma box0_pow_diff_ub {σ : ℝ}
    (hσlo : (1 : ℝ) / 2 ≤ σ) (hσhi : σ ≤ 9/16)
    {u : ℝ} (hu : 1 ≤ u) :
    u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1)
      ≤ u ^ (-(23 / 32) : ℝ) - u ^ (-(25 / 32) : ℝ) := by
  have h1 := box0_pow_a1_ub hσhi hu
  have h2 := box0_pow_a2_lb hσhi hu
  linarith

/-- omegaPartial nonneg — re-export from XiQuadrature. -/
lemma omegaPartial_nonneg_here (N : ℕ) (u : ℝ) :
    (0 : ℝ) ≤ omegaPartial N u :=
  PrincipiaTractalis.XiQuadrature.omegaPartial_nonneg N u

/-! ## §9.7-TIGHT — Correlated power-sum bounds

The loose bounds `box0_pow_sum_lb/ub` decouple the two rpow branches and
over-estimate by factor ~100.  These TIGHT bounds exploit the SYMMETRY
`(σ/2-1) + ((1-σ)/2-1) = -3/2` (independent of σ) to get exactly:

* `2·u^(-3/4) ≤ u^(σ/2-1) + u^((1-σ)/2-1)`  (AM-GM, tight at σ=1/2)
* `u^(σ/2-1) + u^((1-σ)/2-1) ≤ u^(-23/32) + u^(-25/32)`  (monotonicity in |σ-1/2|, tight at σ=9/16)

Both proven algebraically (no derivatives, no cosh imports).  Only these
two theorems replace `box0_pow_sum_lb/ub` at generator time; the D2 sum
bound `abs_realThetaRe/ImIntegrandND2_le_box0` is UNCHANGED (its branch-
wise triangle inequality does not benefit from value-sum cancellation). -/

/-- Tight σ-uniform lower bound on the power sum via AM-GM.
`u^a + u^b ≥ 2·u^((a+b)/2)`.  Here `(a+b)/2 = -3/4` is constant in σ. -/
lemma box0_pow_sum_tight_lb {σ u : ℝ} (hu : 1 ≤ u)
    (hσ0 : (1 : ℝ) / 2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    2 * u ^ (-(3/4 : ℝ)) ≤ u ^ (σ/2 - 1) + u ^ ((1-σ)/2 - 1) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  set x := u ^ ((σ/2 - 1) / 2) with hx_def
  set y := u ^ (((1-σ)/2 - 1) / 2) with hy_def
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hu0 _
  have hy_pos : 0 < y := Real.rpow_pos_of_pos hu0 _
  have hx_sq : x * x = u ^ (σ/2 - 1) := by
    rw [hx_def, ← Real.rpow_add hu0]
    congr 1; ring
  have hy_sq : y * y = u ^ ((1-σ)/2 - 1) := by
    rw [hy_def, ← Real.rpow_add hu0]
    congr 1; ring
  have hxy : x * y = u ^ (-(3/4 : ℝ)) := by
    rw [hx_def, hy_def, ← Real.rpow_add hu0]
    congr 1; ring
  have h_sq : 0 ≤ (x - y)^2 := sq_nonneg _
  have h_expand : (x - y)^2 = x*x + y*y - 2*(x*y) := by ring
  have h_ge : 2 * (x * y) ≤ x*x + y*y := by linarith
  rw [hxy, hx_sq, hy_sq] at h_ge
  exact h_ge

/-- Tight σ-uniform upper bound on the power sum, via monotonicity of
`u^a + u^(-3/2-a)` in `a` on `[-3/4, -23/32]` for `u ≥ 1`.

Algebraic identity: with `δ = b - a ≥ 0`:
`(u^b + u^(-3/2-b)) - (u^a + u^(-3/2-a)) = (u^δ - 1)·(u^a - u^(-3/2-b))`
Both factors are `≥ 0` when `u ≥ 1`, `δ ≥ 0`, and `a + b ≥ -3/2`. -/
lemma box0_pow_sum_tight_ub {σ u : ℝ} (hu : 1 ≤ u)
    (hσ0 : (1 : ℝ) / 2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    u ^ (σ/2 - 1) + u ^ ((1-σ)/2 - 1)
      ≤ u ^ (-(23/32 : ℝ)) + u ^ (-(25/32 : ℝ)) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  set a := σ/2 - 1 with ha_def
  set b := (-(23/32) : ℝ) with hb_def
  set δ := b - a with hδ_def
  have h_conj_a : (1-σ)/2 - 1 = -(3/2 : ℝ) - a := by rw [ha_def]; ring
  have h_conj_b : (-(25/32) : ℝ) = -(3/2 : ℝ) - b := by rw [hb_def]; norm_num
  rw [h_conj_a, h_conj_b]
  have hδ_nn : 0 ≤ δ := by
    rw [hδ_def, hb_def, ha_def]; linarith
  have h_ab_sum : -(3/2 : ℝ) ≤ a + b := by
    rw [ha_def, hb_def]; linarith
  have h_a_ge : -(3/2 : ℝ) - b ≤ a := by linarith
  have h_uδ_ge_one : 1 ≤ u^δ := by
    have h0 : u^(0 : ℝ) = 1 := Real.rpow_zero u
    rw [← h0]
    exact Real.rpow_le_rpow_of_exponent_le hu hδ_nn
  have h_pw_ge : u^(-(3/2 : ℝ) - b) ≤ u^a :=
    Real.rpow_le_rpow_of_exponent_le hu h_a_ge
  have h_ub_eq : u^b = u^a * u^δ := by
    have h_exp : b = a + δ := by rw [hδ_def]; ring
    rw [h_exp, Real.rpow_add hu0]
  have h_uconj_eq : u^(-(3/2 : ℝ) - a) = u^(-(3/2 : ℝ) - b) * u^δ := by
    have h_exp : -(3/2 : ℝ) - a = (-(3/2 : ℝ) - b) + δ := by rw [hδ_def]; ring
    rw [h_exp, Real.rpow_add hu0]
  rw [h_ub_eq, h_uconj_eq]
  -- Goal: u^a + u^(-(3/2) - b) * u^δ ≤ u^a * u^δ + u^(-(3/2) - b)
  -- Key: (u^δ - 1) · (u^a - u^(-(3/2) - b)) ≥ 0
  have h_diff_nn : 0 ≤ u^δ - 1 := by linarith
  have h_pw_diff_nn : 0 ≤ u^a - u^(-(3/2 : ℝ) - b) := by linarith
  have key : 0 ≤ (u^δ - 1) * (u^a - u^(-(3/2 : ℝ) - b)) :=
    mul_nonneg h_diff_nn h_pw_diff_nn
  nlinarith [key]

/-! ## §9.8 — Generic sign-consumer node lemmas

Reusable lemmas that take **scalar** rational/real bounds on amplitude,
trig, and omega, plus sign hypotheses, and produce σ-uniform Re/Im
integrand enclosures at any single u.

These are consumed by the 530 generated node theorems: each generated
proof supplies scalar interval bounds `Alo/Ahi/Clo/Chi/Wlo/Whi` from
the vendored Interval machinery, then invokes the appropriate sign
consumer to derive the final `realThetaRe/ImIntegrandN` enclosure.

**Sign cases:**
* `Re × cos ≤ 0` at u★: `Re = A·C·W`, `A ≥ 0`, `C ≤ 0`, `W ≥ 0`. `Re ≤ 0`.
  Most negative: `A_hi · C_lo · W_hi`.  Least negative: `A_lo · C_hi · W_lo`.
* `Re × cos ≥ 0`: `Re ≥ 0`. Standard monotone product.
* `Im × sin ≤ 0` at u★: `Im = D·S·W`, `D ≥ 0`, `S ≤ 0`, `W ≥ 0`. `Im ≤ 0`.
  Most negative: `D_hi · S_lo · W_hi`.  Least negative: `D_lo · S_hi · W_lo`.
* `Im × sin ≥ 0`: `Im ≥ 0`. Standard monotone product.

Every generated node theorem hits ONE of these four consumers.  Sign
straddling is handled by an existing `Interval` mul-widening product
lemma at the vendored library level, not here. -/

/-- **Re × cos ≤ 0 scalar consumer.**  For `A ∈ [A_lo, A_hi]` with `A_lo ≥ 0`,
`C ∈ [C_lo, C_hi]` with `C_hi ≤ 0`, `W ∈ [W_lo, W_hi]` with `W_lo ≥ 0`,
concludes `A_hi · C_lo · W_hi ≤ A · C · W ≤ A_lo · C_hi · W_lo`.

This is the generic sign-consumer that every generated node theorem at
a u★ with cos((15/2)·log u★) ≤ 0 will invoke. -/
lemma re_scalar_bounds_cos_neg
    {A_lo A_hi C_lo C_hi W_lo W_hi : ℝ}
    (hAlo_nn : (0 : ℝ) ≤ A_lo) (hAloAhi : A_lo ≤ A_hi)
    (hClo_np : C_lo ≤ 0) (hCloChi : C_lo ≤ C_hi) (hChi_np : C_hi ≤ 0)
    (hWlo_nn : (0 : ℝ) ≤ W_lo) (hWloWhi : W_lo ≤ W_hi)
    {A C W : ℝ}
    (hA_lo : A_lo ≤ A) (hA_hi : A ≤ A_hi)
    (hC_lo : C_lo ≤ C) (hC_hi : C ≤ C_hi)
    (hW_lo : W_lo ≤ W) (hW_hi : W ≤ W_hi) :
    A_hi * C_lo * W_hi ≤ A * C * W ∧ A * C * W ≤ A_lo * C_hi * W_lo := by
  have hA_nn : (0 : ℝ) ≤ A := le_trans hAlo_nn hA_lo
  have hAhi_nn : (0 : ℝ) ≤ A_hi := le_trans hA_nn hA_hi
  have hW_nn : (0 : ℝ) ≤ W := le_trans hWlo_nn hW_lo
  have hWhi_nn : (0 : ℝ) ≤ W_hi := le_trans hW_nn hW_hi
  have hCW_np : C * W ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_trans hC_hi hChi_np) hW_nn
  have hAhi_nn : (0 : ℝ) ≤ A_hi := le_trans hA_nn hA_hi
  have hAW_nn : (0 : ℝ) ≤ A * W := mul_nonneg hA_nn hW_nn
  have hAhiW_nn : (0 : ℝ) ≤ A_hi * W := mul_nonneg hAhi_nn hW_nn
  have hAhiWhi_nn : (0 : ℝ) ≤ A_hi * W_hi := mul_nonneg hAhi_nn (le_trans hW_nn hW_hi)
  refine ⟨?_, ?_⟩
  · -- Lower: A_hi · C_lo · W_hi ≤ A · C · W
    -- Use nlinarith with product bounds as hints
    nlinarith [hA_lo, hA_hi, hC_lo, hC_hi, hW_lo, hW_hi, hAlo_nn, hAhi_nn,
               hWlo_nn, hCloChi, hClo_np, hChi_np,
               mul_nonneg hAhi_nn hW_nn, mul_nonneg hA_nn hW_nn,
               mul_nonneg hAhi_nn (le_trans hW_nn hW_hi),
               mul_nonpos_of_nonneg_of_nonpos hAhi_nn hChi_np,
               mul_le_mul_of_nonneg_right hA_hi hW_nn,
               mul_le_mul_of_nonneg_left hW_hi hAhi_nn]
  · -- Upper: A · C · W ≤ A_lo · C_hi · W_lo
    nlinarith [hA_lo, hA_hi, hC_lo, hC_hi, hW_lo, hW_hi, hAlo_nn, hAhi_nn,
               hWlo_nn, hCloChi, hClo_np, hChi_np,
               mul_nonneg hA_nn hW_nn,
               mul_nonpos_of_nonneg_of_nonpos hA_nn hChi_np,
               mul_nonpos_of_nonpos_of_nonneg hChi_np hWlo_nn,
               mul_le_mul_of_nonneg_right hA_lo hWlo_nn,
               mul_le_mul_of_nonneg_left hW_lo hA_nn]

/-- Re × cos NONNEGATIVE consumer. -/
lemma re_scalar_bounds_cos_nonneg
    {A_lo A_hi C_lo C_hi W_lo W_hi : ℝ}
    (hAlo_nn : (0 : ℝ) ≤ A_lo) (hAloAhi : A_lo ≤ A_hi)
    (hClo_nn : (0 : ℝ) ≤ C_lo) (hCloChi : C_lo ≤ C_hi)
    (hWlo_nn : (0 : ℝ) ≤ W_lo) (hWloWhi : W_lo ≤ W_hi)
    {A C W : ℝ}
    (hA_lo : A_lo ≤ A) (hA_hi : A ≤ A_hi)
    (hC_lo : C_lo ≤ C) (hC_hi : C ≤ C_hi)
    (hW_lo : W_lo ≤ W) (hW_hi : W ≤ W_hi) :
    A_lo * C_lo * W_lo ≤ A * C * W ∧ A * C * W ≤ A_hi * C_hi * W_hi := by
  have hA_nn : (0 : ℝ) ≤ A := le_trans hAlo_nn hA_lo
  have hC_nn : (0 : ℝ) ≤ C := le_trans hClo_nn hC_lo
  have hW_nn : (0 : ℝ) ≤ W := le_trans hWlo_nn hW_lo
  refine ⟨?_, ?_⟩
  · calc A_lo * C_lo * W_lo
        ≤ A * C_lo * W_lo := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA_lo hClo_nn) hWlo_nn
      _ ≤ A * C * W_lo := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hC_lo hA_nn) hWlo_nn
      _ ≤ A * C * W := mul_le_mul_of_nonneg_left hW_lo (mul_nonneg hA_nn hC_nn)
  · have hChi_nn : (0 : ℝ) ≤ C_hi := le_trans hC_nn hC_hi
    have hAhi_nn : (0 : ℝ) ≤ A_hi := le_trans hA_nn hA_hi
    calc A * C * W
        ≤ A * C * W_hi := mul_le_mul_of_nonneg_left hW_hi (mul_nonneg hA_nn hC_nn)
      _ ≤ A * C_hi * W_hi := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hC_hi hA_nn) (le_trans hW_nn hW_hi)
      _ ≤ A_hi * C_hi * W_hi := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA_hi hChi_nn) (le_trans hW_nn hW_hi)

/-- Im × sin NEGATIVE consumer (for u where `sin((15/2) log u) ≤ 0`).
Given `D ∈ [D_lo, D_hi]` (D_lo ≥ 0), `S ∈ [S_lo, S_hi]` (S_hi ≤ 0),
`W ∈ [W_lo, W_hi]` (W_lo ≥ 0):
* Most negative: `D_hi · S_lo · W_hi ≤ D · S · W`
* Least negative: `D · S · W ≤ D_lo · S_hi · W_lo`. -/
lemma im_scalar_bounds_sin_neg
    {D_lo D_hi S_lo S_hi W_lo W_hi : ℝ}
    (hDlo_nn : (0 : ℝ) ≤ D_lo) (hDloDhi : D_lo ≤ D_hi)
    (hSlo_np : S_lo ≤ 0) (hSloShi : S_lo ≤ S_hi) (hShi_np : S_hi ≤ 0)
    (hWlo_nn : (0 : ℝ) ≤ W_lo) (hWloWhi : W_lo ≤ W_hi)
    {D S W : ℝ}
    (hD_lo : D_lo ≤ D) (hD_hi : D ≤ D_hi)
    (hS_lo : S_lo ≤ S) (hS_hi : S ≤ S_hi)
    (hW_lo : W_lo ≤ W) (hW_hi : W ≤ W_hi) :
    D_hi * S_lo * W_hi ≤ D * S * W ∧ D * S * W ≤ D_lo * S_hi * W_lo :=
  re_scalar_bounds_cos_neg (A_lo := D_lo) (A_hi := D_hi)
    (C_lo := S_lo) (C_hi := S_hi) (W_lo := W_lo) (W_hi := W_hi)
    hDlo_nn hDloDhi hSlo_np hSloShi hShi_np hWlo_nn hWloWhi
    hD_lo hD_hi hS_lo hS_hi hW_lo hW_hi

/-- Im × sin NONNEGATIVE consumer. -/
lemma im_scalar_bounds_sin_nonneg
    {D_lo D_hi S_lo S_hi W_lo W_hi : ℝ}
    (hDlo_nn : (0 : ℝ) ≤ D_lo) (hDloDhi : D_lo ≤ D_hi)
    (hSlo_nn : (0 : ℝ) ≤ S_lo) (hSloShi : S_lo ≤ S_hi)
    (hWlo_nn : (0 : ℝ) ≤ W_lo) (hWloWhi : W_lo ≤ W_hi)
    {D S W : ℝ}
    (hD_lo : D_lo ≤ D) (hD_hi : D ≤ D_hi)
    (hS_lo : S_lo ≤ S) (hS_hi : S ≤ S_hi)
    (hW_lo : W_lo ≤ W) (hW_hi : W ≤ W_hi) :
    D_lo * S_lo * W_lo ≤ D * S * W ∧ D * S * W ≤ D_hi * S_hi * W_hi :=
  re_scalar_bounds_cos_nonneg (A_lo := D_lo) (A_hi := D_hi)
    (C_lo := S_lo) (C_hi := S_hi) (W_lo := W_lo) (W_hi := W_hi)
    hDlo_nn hDloDhi hSlo_nn hSloShi hWlo_nn hWloWhi
    hD_lo hD_hi hS_lo hS_hi hW_lo hW_hi

end PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.cpow_ofReal_re
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.cpow_ofReal_im
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.exponent_a_eq
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.exponent_b_eq
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.theta_integrand_re_pointwise
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.theta_integrand_im_pointwise
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_realThetaReIntegrand_le_two_omega
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_realThetaImIntegrand_le_two_omega
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.integrableOn_realThetaReIntegrand_Icc
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.integrableOn_realThetaImIntegrand_Icc
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.complex_theta_integrand_eq_re_add_I_im
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.complex_theta_integrand_integrableOn_Icc
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.Lambda0_eq_real_add_I_real_integral_Icc
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.re_Lambda0_eq_real_integral_Icc
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.im_Lambda0_eq_real_integral_Icc
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_realTheta_re_sub_N_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_realTheta_im_sub_N_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_integral_realTheta_re_sub_N_Ioc_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_integral_realTheta_im_sub_N_Ioc_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_integral_realTheta_re_Ioi_T_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_integral_realTheta_im_Ioi_T_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.re_Lambda0_close_to_truncated_integral
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.im_Lambda0_close_to_truncated_integral
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_A_hi_bound
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_A_lo_bound
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_B_lo_bound
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_B_hi_bound
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.top15_box0_re_lt_neg_1e4_conditional
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_thetaPowCosTerm
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_thetaPowSinTerm
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_thetaPowCosTermD1
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_thetaPowSinTermD1
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_thetaPowCosTermD2_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_thetaPowSinTermD2_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_thetaPowCosSum
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_thetaPowSinSum
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_thetaPowCosSumD1
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_thetaPowSinSumD1
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_thetaPowCosSumD2_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_thetaPowSinSumD2_le
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.realThetaReIntegrandN_eq_sum
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.realThetaImIntegrandN_eq_sum
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_realThetaReIntegrandN
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_realThetaImIntegrandN
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_realThetaReIntegrandND1
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.hasDerivAt_realThetaImIntegrandND1
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_realThetaReIntegrandND2_le_box0
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.abs_realThetaImIntegrandND2_le_box0
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_re_midpoint_error_on_segment
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_im_midpoint_error_on_segment
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_pow_sum_nonneg
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_pow_diff_nonneg
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_pow_sum_lb
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_pow_sum_ub
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_pow_diff_ub
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.re_scalar_bounds_cos_neg
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.re_scalar_bounds_cos_nonneg
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.im_scalar_bounds_sin_neg
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.im_scalar_bounds_sin_nonneg
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_pow_sum_tight_lb
#print axioms PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.box0_pow_sum_tight_ub
