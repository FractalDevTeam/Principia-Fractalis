/-
# PF.YangMills.WilsonMuGibbsMuBaseBounds_2026_11_12

**Step 3c.4c ingredient**: `μ_Gibbs ≤ M · μ_base` and `μ_base ≤ (1/m) ·
μ_Gibbs` as measure inequalities, where `M, m` are the
`exp(-β·wilsonActionTotal)` bounds.

These yield the L²-norm comparison
`‖f‖²_{L²(μ_Gibbs)} ≤ M · ‖f‖²_{L²(μ_base)}` and reverse, which is the
layer that reduces the `WilsonAvgMinusL2Bound` on `μ_Gibbs` to the
L²-contraction of `avgMinus` on `μ_base` (which is a conditional-
expectation contraction on the product measure).

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonActionTotalBounds_2026_11_12
import PF.YangMills.WilsonMeasure_2026_10_17

namespace PF.YangMills

open MeasureTheory ENNReal

variable {L : ℕ} [NeZero L]

/-- `lintegral` of any nonneg measurable `f` against `μ_Gibbs` is at
most `M` times its `lintegral` against `μ_base`, where `M` is any
upper bound on `exp(-β · wilsonActionTotal)`. -/
theorem wilsonGibbs_lintegral_le_const_mul_base
    (β : ℝ) (M : ℝ)
    (hM : ∀ U : GaugeField L, Real.exp (-β * wilsonActionTotal U) ≤ M)
    (f : GaugeField L → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ U, f U ∂(wilsonGibbsMeasure L β)
      ≤ ENNReal.ofReal M * ∫⁻ U, f U ∂(wilsonBaseMeasure L) := by
  have h_density_meas :
      Measurable (fun U : GaugeField L =>
        ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U))) := by
    refine Measurable.ennreal_ofReal ?_
    exact Real.measurable_exp.comp
      (measurable_const.mul wilsonActionTotal_measurable)
  unfold wilsonGibbsMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ h_density_meas hf]
  simp only [Pi.mul_apply]
  calc ∫⁻ U,
          ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U)) * f U
            ∂(wilsonBaseMeasure L)
      ≤ ∫⁻ U, ENNReal.ofReal M * f U ∂(wilsonBaseMeasure L) := by
        refine lintegral_mono fun U => ?_
        exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hM U)) _
    _ = ENNReal.ofReal M * ∫⁻ U, f U ∂(wilsonBaseMeasure L) := by
        rw [lintegral_const_mul _ hf]

/-- `lintegral` of any nonneg measurable `f` against `μ_base` is at
most `1/m` times its `lintegral` against `μ_Gibbs`, where `m > 0` is
any lower bound on `exp(-β · wilsonActionTotal)`. -/
theorem wilsonBase_lintegral_le_const_mul_gibbs
    (β : ℝ) (m : ℝ) (hm_pos : 0 < m)
    (hm : ∀ U : GaugeField L, m ≤ Real.exp (-β * wilsonActionTotal U))
    (f : GaugeField L → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ U, f U ∂(wilsonBaseMeasure L)
      ≤ ENNReal.ofReal (1 / m) * ∫⁻ U, f U ∂(wilsonGibbsMeasure L β) := by
  have h_density_meas :
      Measurable (fun U : GaugeField L =>
        ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U))) := by
    refine Measurable.ennreal_ofReal ?_
    exact Real.measurable_exp.comp
      (measurable_const.mul wilsonActionTotal_measurable)
  unfold wilsonGibbsMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ h_density_meas hf]
  simp only [Pi.mul_apply]
  have h_ofReal_m_pos : (0 : ℝ≥0∞) < ENNReal.ofReal m :=
    ENNReal.ofReal_pos.mpr hm_pos
  have hmul :
      ENNReal.ofReal m * ∫⁻ U, f U ∂(wilsonBaseMeasure L)
      ≤ ∫⁻ U, ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U)) * f U
          ∂(wilsonBaseMeasure L) := by
    rw [← lintegral_const_mul _ hf]
    refine lintegral_mono fun U => ?_
    exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hm U)) _
  have h_m_ne_top : (ENNReal.ofReal m) ≠ ∞ := ENNReal.ofReal_ne_top
  have h_m_ne_zero : (ENNReal.ofReal m) ≠ 0 := h_ofReal_m_pos.ne'
  have hcalc : ∫⁻ U, f U ∂(wilsonBaseMeasure L)
      = (ENNReal.ofReal m)⁻¹ *
        (ENNReal.ofReal m * ∫⁻ U, f U ∂(wilsonBaseMeasure L)) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel h_m_ne_zero h_m_ne_top, one_mul]
  rw [hcalc]
  have h_one_div : (1 : ℝ) / m = m⁻¹ := one_div m
  rw [h_one_div, ← ENNReal.ofReal_inv_of_pos hm_pos]
  exact mul_le_mul_left' hmul _

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonGibbs_lintegral_le_const_mul_base
#print axioms PF.YangMills.wilsonBase_lintegral_le_const_mul_gibbs
