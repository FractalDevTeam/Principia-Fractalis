/-
# PF.YangMills.WilsonMuGibbsMuBaseELpNorm_2026_11_12

**Step 3c.4c ingredient**: `eLpNorm f 2 μ_Gibbs` vs `eLpNorm f 2 μ_base`,
lifted from the `lintegral`-level comparison in
`WilsonMuGibbsMuBaseBounds_2026_11_12`.

Delivers (for `0 < m ≤ exp(-β·S) ≤ M`):

* `eLpNorm f 2 μ_Gibbs ≤ ENNReal.ofReal (Real.sqrt M) · eLpNorm f 2 μ_base`
* `eLpNorm f 2 μ_base ≤ ENNReal.ofReal (Real.sqrt (1/m)) · eLpNorm f 2 μ_Gibbs`

The standard `eLpNorm_eq_lintegral_rpow_enorm` identity reduces `eLpNorm`²
to the `lintegral` of `‖·‖ₑ^2`, and raising to the 1/2 power turns
multiplicative constants into their square roots.

This is the layer that reduces `WilsonAvgMinusL2Bound L β` on `μ_Gibbs`
to the L²-contraction of `avgMinus` on `μ_base` (which is a
conditional-expectation contraction on the product measure).

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonMuGibbsMuBaseBounds_2026_11_12

namespace PF.YangMills

open MeasureTheory ENNReal

variable {L : ℕ} [NeZero L]

/-- The `lintegral` form of `‖f‖ₑ^2` against `μ_Gibbs` is at most `M`
times the same against `μ_base`. Direct specialisation of
`wilsonGibbs_lintegral_le_const_mul_base`. -/
theorem wilsonGibbs_lintegral_enorm_sq_le_const_mul_base
    {ε : Type*} [TopologicalSpace ε] [ENorm ε] [MeasurableSpace ε]
    (β : ℝ) (M : ℝ)
    (hM : ∀ U : GaugeField L, Real.exp (-β * wilsonActionTotal U) ≤ M)
    (f : GaugeField L → ε) (hf : Measurable (fun U => (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ))) :
    ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonGibbsMeasure L β)
      ≤ ENNReal.ofReal M *
        ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonBaseMeasure L) :=
  wilsonGibbs_lintegral_le_const_mul_base β M hM _ hf

/-- The `lintegral` form of `‖f‖ₑ^2` against `μ_base` is at most `1/m`
times the same against `μ_Gibbs`. Direct specialisation of
`wilsonBase_lintegral_le_const_mul_gibbs`. -/
theorem wilsonBase_lintegral_enorm_sq_le_const_mul_gibbs
    {ε : Type*} [TopologicalSpace ε] [ENorm ε] [MeasurableSpace ε]
    (β : ℝ) (m : ℝ) (hm_pos : 0 < m)
    (hm : ∀ U : GaugeField L, m ≤ Real.exp (-β * wilsonActionTotal U))
    (f : GaugeField L → ε) (hf : Measurable (fun U => (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ))) :
    ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonBaseMeasure L)
      ≤ ENNReal.ofReal (1 / m) *
        ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonGibbsMeasure L β) :=
  wilsonBase_lintegral_le_const_mul_gibbs β m hm_pos hm _ hf

/-- **`eLpNorm 2` comparison μ_Gibbs ↔ μ_base.** For any continuous
`f : GaugeField L → ℂ`, we have
`eLpNorm f 2 μ_Gibbs ≤ √M · eLpNorm f 2 μ_base`, where `M` is any
nonneg upper bound on `exp(-β·wilsonActionTotal)`. -/
theorem wilsonGibbs_eLpNorm_two_le_const_mul_base
    (β : ℝ) (M : ℝ) (hM_nonneg : 0 ≤ M)
    (hM : ∀ U : GaugeField L, Real.exp (-β * wilsonActionTotal U) ≤ M)
    (f : GaugeField L → ℂ) (hf : Continuous f) :
    eLpNorm f 2 (wilsonGibbsMeasure L β)
      ≤ ENNReal.ofReal (Real.sqrt M) * eLpNorm f 2 (wilsonBaseMeasure L) := by
  -- Measurability of `fun U => ‖f U‖ₑ^2`.
  have hf_meas : Measurable f := hf.measurable
  have h_enorm_sq_meas :
      Measurable (fun U : GaugeField L => (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) := by
    refine Measurable.pow_const ?_ (2 : ℝ)
    exact hf_meas.enorm
  -- Rewrite both eLpNorms as `(∫⁻ ‖·‖ₑ² d·)^(1/2)`.
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
  have h_toReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h_toReal]
  -- Apply the lintegral bound to the integrand `‖f ·‖ₑ^2`.
  have h_lint_bd :
      ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonGibbsMeasure L β)
        ≤ ENNReal.ofReal M *
          ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonBaseMeasure L) :=
    wilsonGibbs_lintegral_enorm_sq_le_const_mul_base β M hM f h_enorm_sq_meas
  -- Raise both sides to the power 1/2 using monotonicity of rpow.
  have h_half_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h_mono :
      (∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonGibbsMeasure L β)) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal M *
              ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonBaseMeasure L))
            ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow h_lint_bd h_half_nonneg
  refine h_mono.trans ?_
  -- Factor the rpow over the product.
  rw [ENNReal.mul_rpow_of_nonneg _ _ h_half_nonneg]
  -- Identify `(ENNReal.ofReal M)^(1/2)` with `ENNReal.ofReal √M`.
  have h_ofReal_rpow :
      (ENNReal.ofReal M) ^ (1 / (2 : ℝ)) = ENNReal.ofReal (Real.sqrt M) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hM_nonneg h_half_nonneg,
        ← Real.sqrt_eq_rpow]
  rw [h_ofReal_rpow]

/-- **`eLpNorm 2` comparison μ_base ↔ μ_Gibbs.** For any continuous
`f : GaugeField L → ℂ`, we have
`eLpNorm f 2 μ_base ≤ √(1/m) · eLpNorm f 2 μ_Gibbs`, where `m > 0` is
any lower bound on `exp(-β·wilsonActionTotal)`. -/
theorem wilsonBase_eLpNorm_two_le_const_mul_gibbs
    (β : ℝ) (m : ℝ) (hm_pos : 0 < m)
    (hm : ∀ U : GaugeField L, m ≤ Real.exp (-β * wilsonActionTotal U))
    (f : GaugeField L → ℂ) (hf : Continuous f) :
    eLpNorm f 2 (wilsonBaseMeasure L)
      ≤ ENNReal.ofReal (Real.sqrt (1 / m)) * eLpNorm f 2 (wilsonGibbsMeasure L β) := by
  have hf_meas : Measurable f := hf.measurable
  have h_enorm_sq_meas :
      Measurable (fun U : GaugeField L => (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) := by
    refine Measurable.pow_const ?_ (2 : ℝ)
    exact hf_meas.enorm
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
  have h_toReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h_toReal]
  have h_lint_bd :
      ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonBaseMeasure L)
        ≤ ENNReal.ofReal (1 / m) *
          ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonGibbsMeasure L β) :=
    wilsonBase_lintegral_enorm_sq_le_const_mul_gibbs β m hm_pos hm f h_enorm_sq_meas
  have h_half_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h_mono :
      (∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonBaseMeasure L)) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal (1 / m) *
              ∫⁻ U, (‖f U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonGibbsMeasure L β))
            ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow h_lint_bd h_half_nonneg
  refine h_mono.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ h_half_nonneg]
  have h_one_div_m_nonneg : (0 : ℝ) ≤ 1 / m := by positivity
  have h_ofReal_rpow :
      (ENNReal.ofReal (1 / m)) ^ (1 / (2 : ℝ))
        = ENNReal.ofReal (Real.sqrt (1 / m)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg h_one_div_m_nonneg h_half_nonneg,
        ← Real.sqrt_eq_rpow]
  rw [h_ofReal_rpow]

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonGibbs_eLpNorm_two_le_const_mul_base
#print axioms PF.YangMills.wilsonBase_eLpNorm_two_le_const_mul_gibbs
