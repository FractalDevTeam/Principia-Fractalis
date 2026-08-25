/-
# r329b — BOTTOM EDGE OF THE T=15 ξ RECTANGLE: DISCHARGED UNCONDITIONALLY

★ 2026-08-25.  Closes the `BottomEdgeZeroFree` residual of r328
  UNCONDITIONALLY, using PF's own symmetric theta representation
  (`completedRiemannZeta₀_eq_theta_integral` in `XiThetaIntegral.lean`)
  together with the already-proved `omega_le_geometric` bound and
  mathlib's `integral_exp_mul_Ioi` (also present in PF as
  `integral_exp_neg_pi_mul_Ioi`).  No numerical panels; no smuggled
  "ζ ≠ 0 on real (0, 1)".

## Route

For real `σ ∈ [0, 1]` the theta integral

    Λ₀(σ) = ∫_{u > 1} (u^(σ/2 - 1) + u^((1 - σ)/2 - 1)) · ω(u) du

has REAL nonneg integrand (both `u^(σ/2 - 1)` and `u^((1-σ)/2 - 1)` are
positive reals for `u ≥ 1`, exponents ≤ 0, `ω ≥ 0`), and each of the two
powers is `≤ 1` (u ≥ 1, exp ≤ 0), so the integrand is
`≤ 2 · ω(u)`.

Then
`ω(u) ≤ exp(-πu)/(1 - exp(-πu)) ≤ exp(-πu)/(1 - exp(-π))` for `u ≥ 1`
(`omega_le_geometric` + monotonicity of `1 - exp(-πu)` on `[1, ∞)`), so

    Λ₀(σ).re ≤ 2 · ∫_{u > 1} exp(-πu)/(1 - exp(-π)) du
            = 2 · exp(-π) / (π · (1 - exp(-π))).

Loose rational bounds `exp(-π) < 1/2` (from `2 < e = Real.exp 1` via
`Real.exp_one_gt_d9` + `Real.exp_strictMono`) and `π > 3`
(`Real.pi_gt_three`) give

    Λ₀(σ).re < 2 · (1/2) / (3 · (1/2)) = 2/3 < 1.

By r329's `bottomEdgeZeroFree_of_lambda0_bound`, `BottomEdgeZeroFree`
holds unconditionally.  Combined with r328's boundary reduction,
r329b lands a simplified boundary reduction requiring ONLY the H_TOP
residual — plus the analogous simplified count identity.

## What lands (kernel-clean)

- `realThetaIntegrand` — the real-valued integrand at real `σ`.
- `theta_integrand_ofReal_form` — pointwise equality on `u > 0`.
- `realThetaIntegrand_nonneg` / `_le_two_omega` — pointwise bounds on `u ≥ 1`.
- `omega_le_uniform_geom` — uniform ω-tail bound on `u ≥ 1`.
- Integrability of `2 · ω` and `2 · exp(-πu)/(1 - exp(-π))` on `Ioi 1`.
- Integrability of `realThetaIntegrand σ` on `Ioi 1` from the theta formula.
- `completedRiemannZeta₀_real_re` — closed real form.
- `completedRiemannZeta₀_real_Icc_nonneg` — `0 ≤ Λ₀(σ).re` on `[0, 1]`.
- `completedRiemannZeta₀_real_Icc_lt_one` — `Λ₀(σ).re < 1` on `[0, 1]`.
- `bottomEdgeZeroFree_proved` — UNCONDITIONAL discharge.
- `riemannXiEntire_real_Icc_pos` — strict `Re ξ > 0` on `[0, 1]`.
- `boundary_zero_free_of_top_right_half` — simplified r328 boundary
  reduction requiring only H_TOP.
- `xi_T15_exact_zero_count_identity_top_only` — simplified r327 count
  identity requiring only H_TOP.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Zero project axioms.

SPDX-License-Identifier: Apache-2.0
-/
import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannXiSymmetries_r326
import PF.Analytic.RiemannXiRectangleCount_r327
import PF.Analytic.RiemannXiBoundaryT15_r328
import PF.Analytic.RiemannXiBottomEdge_r329
import PF.Analytic.XiThetaIntegral
import PF.Analytic.XiQuadrature
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.ExpDecay

open Complex Set Topology Filter MeasureTheory
open scoped ComplexConjugate Real
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.RiemannXiBoundaryT15
open PrincipiaTractalis.RiemannXiBottomEdge
open PrincipiaTractalis.RiemannXiRectangleCount
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open Zeta23.Analytic

noncomputable section

namespace PrincipiaTractalis.RiemannXiBottomEdgeUnconditional

/-! ## §1 — Real form of the theta integrand at real `σ` -/

/-- The real-valued theta integrand at real `σ`, `u ≥ 1`:
`(u^(σ/2-1) + u^((1-σ)/2-1)) · ω(u)`. -/
def realThetaIntegrand (σ u : ℝ) : ℝ :=
  (u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1)) * omega u

/-- Pointwise: on `u > 0`, the complex integrand at `s = (σ : ℂ)` equals
the real integrand cast to ℂ. -/
lemma theta_integrand_ofReal_form (σ u : ℝ) (hu : 0 < u) :
    ((u : ℂ) ^ ((σ : ℂ) / 2 - 1) + (u : ℂ) ^ (((1 : ℂ) - (σ : ℂ)) / 2 - 1))
        * ((omega u : ℝ) : ℂ)
      = ((realThetaIntegrand σ u : ℝ) : ℂ) := by
  unfold realThetaIntegrand
  have h1 : ((σ : ℂ)) / 2 - 1 = (((σ / 2 - 1 : ℝ)) : ℂ) := by
    push_cast; ring
  have h2 : (((1 : ℂ) - (σ : ℂ)) / 2 - 1) = ((((1 - σ) / 2 - 1 : ℝ)) : ℂ) := by
    push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow hu.le, ← Complex.ofReal_cpow hu.le]
  push_cast
  ring

/-! ## §2 — `Λ₀(σ)` is real; closed real form for `Re Λ₀(σ)` -/

/-- The full theta integrand as a complex-valued function of `u`. -/
private def cIntegrand (σ : ℝ) (u : ℝ) : ℂ :=
  ((u : ℂ) ^ ((σ : ℂ) / 2 - 1) + (u : ℂ) ^ (((1 : ℂ) - (σ : ℂ)) / 2 - 1))
    * ((omega u : ℝ) : ℂ)

lemma cIntegrand_eq_ofReal (σ u : ℝ) (hu : 0 < u) :
    cIntegrand σ u = ((realThetaIntegrand σ u : ℝ) : ℂ) :=
  theta_integrand_ofReal_form σ u hu

/-- Λ₀ at real `σ` collapses to the real integral, as a complex-cast form. -/
lemma completedRiemannZeta₀_real_ofReal (σ : ℝ) :
    completedRiemannZeta₀ (σ : ℂ)
      = (((∫ u in Ioi (1 : ℝ), realThetaIntegrand σ u) : ℝ) : ℂ) := by
  rw [completedRiemannZeta₀_eq_theta_integral]
  -- Rewrite integrand as ((real : ℝ) : ℂ) a.e. on Ioi 1 (with u : ℝ)
  have h_ae : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (1:ℝ))),
      ((u : ℂ) ^ ((σ : ℂ) / 2 - 1) + (u : ℂ) ^ (((1 : ℂ) - (σ : ℂ)) / 2 - 1))
          * ((omega u : ℝ) : ℂ)
        = ((realThetaIntegrand σ u : ℝ) : ℂ) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    exact theta_integrand_ofReal_form σ u (lt_trans zero_lt_one (mem_Ioi.mp hu))
  rw [MeasureTheory.integral_congr_ae h_ae]
  exact integral_ofReal

lemma completedRiemannZeta₀_real_re (σ : ℝ) :
    (completedRiemannZeta₀ (σ : ℂ)).re
      = ∫ u in Ioi (1 : ℝ), realThetaIntegrand σ u := by
  rw [completedRiemannZeta₀_real_ofReal σ]
  simp

/-! ## §3 — Pointwise bounds on `realThetaIntegrand` -/

lemma realThetaIntegrand_nonneg {σ u : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (hu : 1 ≤ u) :
    0 ≤ realThetaIntegrand σ u := by
  unfold realThetaIntegrand
  have hu0 : 0 ≤ u := le_trans zero_le_one hu
  have hpow1 : 0 ≤ u ^ (σ / 2 - 1) := Real.rpow_nonneg hu0 _
  have hpow2 : 0 ≤ u ^ ((1 - σ) / 2 - 1) := Real.rpow_nonneg hu0 _
  have hω : 0 ≤ omega u := omega_nonneg u
  have hsum : 0 ≤ u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1) := by linarith
  exact mul_nonneg hsum hω

lemma realThetaIntegrand_le_two_omega {σ u : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (hu : 1 ≤ u) :
    realThetaIntegrand σ u ≤ 2 * omega u := by
  unfold realThetaIntegrand
  have hexp1 : σ / 2 - 1 ≤ 0 := by linarith
  have hexp2 : (1 - σ) / 2 - 1 ≤ 0 := by linarith
  have h1' : u ^ (σ / 2 - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu hexp1
  have h2' : u ^ ((1 - σ) / 2 - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu hexp2
  have hω_nn : 0 ≤ omega u := omega_nonneg u
  nlinarith

/-! ## §4 — Uniform `ω` bound on `Ioi 1` -/

/-- Uniform tail: for `u ≥ 1`, `ω(u) ≤ exp(-πu) / (1 - exp(-π))`.
Derived from `omega_le_geometric` by replacing the pointwise
denominator `(1 - exp(-πu))` with the smaller `(1 - exp(-π))`. -/
lemma omega_le_uniform_geom {u : ℝ} (hu : 1 ≤ u) :
    omega u ≤ Real.exp (-π * u) / (1 - Real.exp (-π)) := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hπ : (0 : ℝ) < π := Real.pi_pos
  -- exp(-π) < 1
  have hExpLt1 : Real.exp (-π) < 1 := by
    apply Real.exp_lt_one_iff.mpr; linarith
  have hDenom : 0 < 1 - Real.exp (-π) := by linarith
  -- exp(-πu) ≤ exp(-π) for u ≥ 1
  have hExpMono : Real.exp (-π * u) ≤ Real.exp (-π) := by
    have hstep : -π * u ≤ -π := by nlinarith
    exact Real.exp_le_exp.mpr hstep
  -- 1 - exp(-πu) ≥ 1 - exp(-π) > 0
  have hDenom_u : 0 < 1 - Real.exp (-π * u) := by
    have hExpLt1_u : Real.exp (-π * u) < 1 :=
      lt_of_le_of_lt hExpMono hExpLt1
    linarith
  have hDenomLE : 1 - Real.exp (-π) ≤ 1 - Real.exp (-π * u) := by linarith
  -- omega u ≤ exp(-πu)/(1-exp(-πu)) ≤ exp(-πu)/(1-exp(-π))
  have hGeo := omega_le_geometric hu_pos
  have hNumNn : (0 : ℝ) ≤ Real.exp (-π * u) := (Real.exp_pos _).le
  refine le_trans hGeo ?_
  exact div_le_div_of_nonneg_left hNumNn hDenom hDenomLE

/-! ## §5 — Integrability of the bounds and of `realThetaIntegrand` -/

lemma integrableOn_two_omega : IntegrableOn (fun u : ℝ => 2 * omega u) (Ioi (1 : ℝ)) := by
  -- Comparison: |2 · ω(u)| ≤ 2 · exp(-πu)/(1-exp(-π)) and RHS integrable.
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hExpLt1 : Real.exp (-π) < 1 := by
    apply Real.exp_lt_one_iff.mpr; linarith
  have hDenom_pos : 0 < 1 - Real.exp (-π) := by linarith
  set c : ℝ := 2 / (1 - Real.exp (-π))
  have hc_pos : 0 < c := div_pos (by norm_num) hDenom_pos
  -- exp(-πu) is integrable on Ioi 1
  have hExpInt : IntegrableOn (fun u : ℝ => Real.exp (-π * u)) (Ioi (1 : ℝ)) :=
    exp_neg_integrableOn_Ioi 1 hπ
  -- c · exp(-πu) is integrable
  have hIntBound : IntegrableOn (fun u : ℝ => c * Real.exp (-π * u)) (Ioi (1 : ℝ)) :=
    hExpInt.const_mul c
  -- 2·ω(u) is bounded by c · exp(-πu) on Ioi 1 (via omega_le_uniform_geom)
  refine MeasureTheory.Integrable.mono hIntBound ?_ ?_
  · -- StronglyMeasurable / AEStronglyMeasurable
    apply MeasureTheory.AEStronglyMeasurable.const_mul
    exact (continuousOn_omega.mono (fun u hu => lt_trans zero_lt_one (mem_Ioi.mp hu)))
      |>.aestronglyMeasurable measurableSet_Ioi
  · -- pointwise |2·ω u| ≤ c · exp(-πu) on Ioi 1
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hω_nn : 0 ≤ omega u := omega_nonneg u
    have hω_bound := omega_le_uniform_geom hu1
    have habs : |2 * omega u| = 2 * omega u := by
      rw [abs_of_nonneg]; linarith
    rw [Real.norm_eq_abs, habs]
    -- 2 · omega u ≤ 2 · exp(-πu)/(1-exp(-π)) = c · exp(-πu)
    have hRHS : c * Real.exp (-π * u) = 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by
      show (2 / (1 - Real.exp (-π))) * Real.exp (-π * u)
        = 2 * Real.exp (-π * u) / (1 - Real.exp (-π))
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · rw [hRHS]
      have hL : 2 * omega u ≤ 2 * (Real.exp (-π * u) / (1 - Real.exp (-π))) :=
        mul_le_mul_of_nonneg_left hω_bound (by norm_num)
      have hEq : 2 * (Real.exp (-π * u) / (1 - Real.exp (-π)))
          = 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by ring
      linarith
    · exact mul_nonneg hc_pos.le (Real.exp_pos _).le

/-- Continuity of the real theta integrand on `Ioi 1`. -/
lemma continuousOn_realThetaIntegrand (σ : ℝ) :
    ContinuousOn (realThetaIntegrand σ) (Ioi (1 : ℝ)) := by
  unfold realThetaIntegrand
  refine ContinuousOn.mul ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; left; linarith [(mem_Ioi.mp hu)]
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro u hu; left; linarith [(mem_Ioi.mp hu)]
  · exact continuousOn_omega.mono (fun u hu => lt_trans zero_lt_one (mem_Ioi.mp hu))

/-- Integrability of the real theta integrand on `Ioi 1` for `σ ∈ [0, 1]`
via comparison with `2 · ω`. -/
lemma integrableOn_realThetaIntegrand_Icc {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    IntegrableOn (realThetaIntegrand σ) (Ioi (1 : ℝ)) := by
  refine MeasureTheory.Integrable.mono integrableOn_two_omega ?_ ?_
  · exact (continuousOn_realThetaIntegrand σ).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have h_nn := realThetaIntegrand_nonneg h0 h1 hu1
    have h_le := realThetaIntegrand_le_two_omega h0 h1 hu1
    have hω_nn : 0 ≤ omega u := omega_nonneg u
    rw [Real.norm_eq_abs, abs_of_nonneg h_nn, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact h_le

/-! ## §6 — Numerical bounds on `exp(-π)` and the key integral -/

lemma exp_neg_pi_lt_half : Real.exp (-π) < 1/2 := by
  -- exp(-π) < exp(-1) < 1/2 (since 2 < e)
  have h_pi_gt_1 : (1 : ℝ) < π := by linarith [Real.pi_gt_three]
  have h_exp_mono : Real.exp (-π) < Real.exp (-1) := by
    apply Real.exp_strictMono; linarith
  have h_exp_neg_one : Real.exp (-1) = 1 / Real.exp 1 := by
    rw [Real.exp_neg]; ring
  have h_two_lt_e : (2 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h_inv : Real.exp (-1) < 1/2 := by
    rw [h_exp_neg_one]
    exact one_div_lt_one_div_of_lt (by norm_num) h_two_lt_e
  linarith

lemma two_exp_neg_pi_over_bound_lt_one :
    2 * Real.exp (-π) / (π * (1 - Real.exp (-π))) < 1 := by
  have hExpLt : Real.exp (-π) < 1/2 := exp_neg_pi_lt_half
  have hExpPos : 0 < Real.exp (-π) := Real.exp_pos _
  have hπ3 : (3 : ℝ) < π := Real.pi_gt_three
  have hDenom : 0 < 1 - Real.exp (-π) := by linarith
  have hDenomLB : (1/2 : ℝ) < 1 - Real.exp (-π) := by linarith
  have hπ_pos : (0 : ℝ) < π := by linarith
  have hπDenom_pos : 0 < π * (1 - Real.exp (-π)) := mul_pos hπ_pos hDenom
  -- Numerator: 2 · exp(-π) < 2 · (1/2) = 1.
  have hNumer : 2 * Real.exp (-π) < 1 := by linarith
  -- Denominator: π · (1 - exp(-π)) > 3 · (1/2) = 3/2.
  have hπDenomLB : (3/2 : ℝ) < π * (1 - Real.exp (-π)) := by
    have h1 : (3 : ℝ) * (1/2) < π * (1 - Real.exp (-π)) := by
      apply mul_lt_mul hπ3 (le_of_lt hDenomLB) (by norm_num) (by linarith)
    linarith
  -- ratio < 1 / (3/2) = 2/3 < 1.
  rw [div_lt_one hπDenom_pos]
  linarith

/-! ## §7 — Assembly: `Λ₀(σ).re ≥ 0` and `Λ₀(σ).re < 1` on `[0, 1]` -/

theorem completedRiemannZeta₀_real_Icc_nonneg
    {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    0 ≤ (completedRiemannZeta₀ (σ : ℂ)).re := by
  rw [completedRiemannZeta₀_real_re σ]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun u hu => ?_)
  exact realThetaIntegrand_nonneg h0 h1 (le_of_lt (mem_Ioi.mp hu))

theorem completedRiemannZeta₀_real_Icc_lt_one
    {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    (completedRiemannZeta₀ (σ : ℂ)).re < 1 := by
  rw [completedRiemannZeta₀_real_re σ]
  -- Λ₀.re = ∫ realThetaIntegrand ≤ ∫ 2·ω ≤ ∫ 2·exp(-πu)/(1-exp(-π))
  --      = 2·exp(-π)/(π·(1-exp(-π))) < 1
  have h_int1 : ∫ u in Ioi (1 : ℝ), realThetaIntegrand σ u
      ≤ ∫ u in Ioi (1 : ℝ), 2 * omega u := by
    refine MeasureTheory.setIntegral_mono_on
      (integrableOn_realThetaIntegrand_Icc h0 h1) integrableOn_two_omega
      measurableSet_Ioi ?_
    intro u hu
    exact realThetaIntegrand_le_two_omega h0 h1 (le_of_lt (mem_Ioi.mp hu))
  -- Now bound ∫ 2·ω ≤ ∫ 2·exp(-πu)/(1-exp(-π))
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hExpLt1 : Real.exp (-π) < 1 := by
    apply Real.exp_lt_one_iff.mpr; linarith
  have hDenom_pos : 0 < 1 - Real.exp (-π) := by linarith
  set c : ℝ := 2 / (1 - Real.exp (-π))
  have hc_pos : 0 < c := div_pos (by norm_num) hDenom_pos
  have hExpInt : IntegrableOn (fun u : ℝ => Real.exp (-π * u)) (Ioi (1 : ℝ)) :=
    exp_neg_integrableOn_Ioi 1 hπ
  have hIntBound : IntegrableOn (fun u : ℝ => c * Real.exp (-π * u)) (Ioi (1 : ℝ)) :=
    hExpInt.const_mul c
  have h_int2 : ∫ u in Ioi (1 : ℝ), 2 * omega u
      ≤ ∫ u in Ioi (1 : ℝ), c * Real.exp (-π * u) := by
    refine MeasureTheory.setIntegral_mono_on integrableOn_two_omega hIntBound
      measurableSet_Ioi ?_
    intro u hu
    have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hω_bound := omega_le_uniform_geom hu1
    show 2 * omega u ≤ (2 / (1 - Real.exp (-π))) * Real.exp (-π * u)
    have hstep : 2 * omega u ≤ 2 * (Real.exp (-π * u) / (1 - Real.exp (-π))) :=
      mul_le_mul_of_nonneg_left hω_bound (by norm_num)
    have hRHS : (2 / (1 - Real.exp (-π))) * Real.exp (-π * u)
        = 2 * (Real.exp (-π * u) / (1 - Real.exp (-π))) := by ring
    linarith [hstep, hRHS]
  -- Evaluate ∫ c · exp(-πu) du = c · exp(-π)/π
  have h_int3 : ∫ u in Ioi (1 : ℝ), c * Real.exp (-π * u)
      = c * (Real.exp (-π) / π) := by
    rw [MeasureTheory.integral_const_mul, integral_exp_neg_pi_mul_Ioi 1]
    ring_nf
  -- c · exp(-π)/π = 2 · exp(-π) / (π · (1 - exp(-π)))
  have hc_def : c = 2 / (1 - Real.exp (-π)) := rfl
  have hπ_ne : π ≠ 0 := ne_of_gt hπ
  have hDenom_ne : 1 - Real.exp (-π) ≠ 0 := ne_of_gt hDenom_pos
  have h_c_val : c * (Real.exp (-π) / π)
      = 2 * Real.exp (-π) / (π * (1 - Real.exp (-π))) := by
    rw [hc_def]
    field_simp
  -- Chain everything: Λ₀.re ≤ 2·exp(-π)/(π·(1-exp(-π))) < 1.
  have h_key := two_exp_neg_pi_over_bound_lt_one
  calc ∫ u in Ioi (1 : ℝ), realThetaIntegrand σ u
      ≤ ∫ u in Ioi (1 : ℝ), 2 * omega u := h_int1
    _ ≤ ∫ u in Ioi (1 : ℝ), c * Real.exp (-π * u) := h_int2
    _ = c * (Real.exp (-π) / π) := h_int3
    _ = 2 * Real.exp (-π) / (π * (1 - Real.exp (-π))) := h_c_val
    _ < 1 := h_key

/-! ## §8 — Unconditional discharge -/

/-- **★★★ `bottomEdgeZeroFree_proved` ★★★** — the r328 bottom-edge
residual is TRUE, unconditionally.  Follows from r329's structural
reduction + the two Λ₀ bound theorems above. -/
theorem bottomEdgeZeroFree_proved : BottomEdgeZeroFree := by
  refine bottomEdgeZeroFree_of_lambda0_bound
    (fun σ h0 h1 => completedRiemannZeta₀_real_Icc_nonneg h0 h1) ?_
  intro σ h0 h1
  have h := completedRiemannZeta₀_real_Icc_lt_one h0 h1
  linarith

/-- Strict positivity of `Re ξ` on the real interval `[0, 1]`.  Sharper
than `bottomEdgeZeroFree_proved` — gives an actual sign. -/
theorem riemannXiEntire_real_Icc_pos {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    0 < (riemannXiEntire (σ : ℂ)).re := by
  rw [riemannXiEntire_real_re σ]
  -- (1 + σ(σ-1)·Λ₀.re)/2 > 0 iff 1 + σ(σ-1)·Λ₀.re > 0
  have hL_nn : 0 ≤ (completedRiemannZeta₀ (σ : ℂ)).re :=
    completedRiemannZeta₀_real_Icc_nonneg h0 h1
  have hL_lt : (completedRiemannZeta₀ (σ : ℂ)).re < 1 :=
    completedRiemannZeta₀_real_Icc_lt_one h0 h1
  have ⟨hσ_lo, hσ_hi⟩ := sigma_mul_sub_one_bounds h0 h1
  -- σ(σ-1)·Λ₀.re ∈ [-1/4, 0] · [0, 1)
  -- Specifically ≥ -1/4 · 1 = -1/4, so 1 + · ≥ 3/4 > 0.
  have hprod_lo : -(1/4 : ℝ) ≤ σ * (σ - 1) * (completedRiemannZeta₀ (σ : ℂ)).re := by
    rcases eq_or_lt_of_le hL_nn with hL_eq | hL_pos
    · rw [← hL_eq, mul_zero]; norm_num
    · nlinarith [hσ_lo, hL_lt, hL_pos]
  have hnum_pos : 0 < 1 + σ * (σ - 1) * (completedRiemannZeta₀ (σ : ℂ)).re := by
    linarith
  linarith

/-! ## §9 — Simplified boundary reduction requiring only H_TOP -/

/-- **`boundary_zero_free_of_top_right_half`** — simplified r328 boundary
reduction consuming ONLY the H_TOP residual (H_BOTTOM is discharged
unconditionally in this module). -/
theorem boundary_zero_free_of_top_right_half
    (hTop : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire ⟨σ, 15⟩ ≠ 0) :
    ∀ s ∈ RectangleBorder z15 w15, riemannXiEntire s ≠ 0 :=
  boundary_zero_free_of_top_right_half_and_bottom hTop bottomEdgeZeroFree_proved

/-! ## §10 — Simplified T = 15 zero-count identity requiring only H_TOP -/

/-- **`xi_T15_exact_zero_count_identity_top_only`** — the r328 count
identity specialized: the ONLY remaining residual after r329b is the
top half-edge H_TOP.  The finite interior zero set is still produced
automatically from `finite_zeros_rectangle`. -/
theorem xi_T15_exact_zero_count_identity_top_only
    (hTop : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire ⟨σ, 15⟩ ≠ 0) :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) z15 w15
      = ∑ ρ ∈ (finite_zeros_rectangle
              (riemannXiEntire_analyticOnNhd _)
              (rectangleBorder_subset_rectangle z15 w15 z15_mem_RectangleBorder)
              (boundary_zero_free_of_top_right_half hTop z15
                  z15_mem_RectangleBorder)).toFinset,
          (analyticOrderNatAt riemannXiEntire ρ : ℂ) :=
  xi_T15_exact_zero_count_identity hTop bottomEdgeZeroFree_proved

end PrincipiaTractalis.RiemannXiBottomEdgeUnconditional

/-! ## §Axiom check -/

#print axioms
  PrincipiaTractalis.RiemannXiBottomEdgeUnconditional.completedRiemannZeta₀_real_Icc_nonneg
#print axioms
  PrincipiaTractalis.RiemannXiBottomEdgeUnconditional.completedRiemannZeta₀_real_Icc_lt_one
#print axioms PrincipiaTractalis.RiemannXiBottomEdgeUnconditional.bottomEdgeZeroFree_proved
#print axioms PrincipiaTractalis.RiemannXiBottomEdgeUnconditional.riemannXiEntire_real_Icc_pos
#print axioms
  PrincipiaTractalis.RiemannXiBottomEdgeUnconditional.boundary_zero_free_of_top_right_half
#print axioms
  PrincipiaTractalis.RiemannXiBottomEdgeUnconditional.xi_T15_exact_zero_count_identity_top_only
