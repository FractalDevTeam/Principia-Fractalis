/-
# Nontriviality of `LogWeightedL2`

This file proves `Nontrivial LogWeightedL2`, discharging half of the
(W1) → (W1) reduction in the RH chain's Banach–Alaoglu route
(per the 2026-05-24 RH audit / "Realistic 1-day deliverable").

`LogWeightedL2 := MeasureTheory.Lp ℂ 2 (logWeightedMeasure.restrict (Ioo 0 1))`,
where `logWeightedMeasure = volume.withDensity (1/x)`. The space is
`Nontrivial` (has ≥ 2 distinct elements) because the indicator-constant
`(1 : ℂ)` on the measurable, finite, nonnull subset
`Ioo (1/2) 1 ⊆ Ioo 0 1` lifts to a nonzero `Lp` element distinct from `0`.

ZERO axioms. ZERO sorries.
-/

import PF.TransferOperator
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace PrincipiaTractalis

open MeasureTheory Set
open scoped ENNReal

/-- The intersection `Ioo (1/2) 1 ∩ Ioo 0 1 = Ioo (1/2) 1`. -/
private lemma Ioo_half_one_inter_Ioo_zero_one :
    Ioo (1/2 : ℝ) 1 ∩ Ioo (0:ℝ) 1 = Ioo (1/2 : ℝ) 1 := by
  apply Set.inter_eq_left.mpr
  intro x hx
  exact ⟨lt_trans (by norm_num : (0:ℝ) < 1/2) hx.1, hx.2⟩

/-- The restricted log-weighted measure of `Ioo (1/2) 1` is finite.

    Density `1/x ≤ 2` on `Ioo (1/2) 1` and `volume (Ioo (1/2) 1) = 1/2`,
    so the integral is bounded above by `2 · (1/2) = 1 < ∞`. -/
private lemma logWeightedMeasure_restrict_Ioo_half_one_ne_top :
    (logWeightedMeasure.restrict (Ioo (0:ℝ) 1)) (Ioo (1/2 : ℝ) 1) ≠ ∞ := by
  rw [Measure.restrict_apply measurableSet_Ioo,
      Ioo_half_one_inter_Ioo_zero_one,
      logWeightedMeasure_def,
      withDensity_apply _ measurableSet_Ioo]
  -- Goal: ∫⁻ x in Ioo(1/2,1), logWeightDensity x ∂volume ≠ ∞
  apply ne_of_lt
  calc (∫⁻ x in Ioo (1/2 : ℝ) 1, logWeightDensity x ∂volume)
      ≤ ∫⁻ _ in Ioo (1/2 : ℝ) 1, (2 : ℝ≥0∞) ∂volume := by
        refine setLIntegral_mono measurable_const (fun x hx => ?_)
        have hx_pos : (0:ℝ) < x := lt_trans (by norm_num) hx.1
        unfold logWeightDensity
        rw [if_neg (not_le.mpr hx_pos)]
        -- Show: ENNReal.ofReal (1/x) ≤ 2.
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
          rfl
        rw [h2]
        apply ENNReal.ofReal_le_ofReal
        rw [div_le_iff₀ hx_pos]
        linarith [hx.1]
    _ = (2 : ℝ≥0∞) * volume (Ioo (1/2 : ℝ) 1) := setLIntegral_const _ _
    _ < ∞ := by
        apply ENNReal.mul_lt_top ENNReal.ofNat_lt_top
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top

/-- The restricted log-weighted measure of `Ioo (1/2) 1` is nonzero.

    `volume (Ioo (1/2) 1 ∩ Ioi 0) = volume (Ioo (1/2) 1) = 1/2 > 0`,
    and `volume`-positive implies `μ_log`-positive via the contrapositive
    of `volume_pos_null_of_logWeightedMeasure_null`. -/
private lemma logWeightedMeasure_restrict_Ioo_half_one_ne_zero :
    (logWeightedMeasure.restrict (Ioo (0:ℝ) 1)) (Ioo (1/2 : ℝ) 1) ≠ 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo,
      Ioo_half_one_inter_Ioo_zero_one]
  intro h_zero
  have h_vol_zero : volume (Ioo (1/2 : ℝ) 1 ∩ Ioi (0:ℝ)) = 0 :=
    volume_pos_null_of_logWeightedMeasure_null measurableSet_Ioo h_zero
  -- But the intersection is `Ioo (1/2) 1`, of volume 1/2.
  have h_inter : Ioo (1/2 : ℝ) 1 ∩ Ioi (0:ℝ) = Ioo (1/2 : ℝ) 1 := by
    apply Set.inter_eq_left.mpr
    intro x hx
    exact lt_trans (by norm_num : (0:ℝ) < 1/2) hx.1
  rw [h_inter, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h_vol_zero
  linarith

/-- **★ `Nontrivial LogWeightedL2` ★** (axiom-free).

    Discharges half of the (W1)→(W1) bundle reduction in the RH chain's
    Banach–Alaoglu route. The nonzero witness is the `Lp` indicator-constant
    of `Ioo (1/2) 1` with value `(1 : ℂ)`; its norm
    `‖f‖ = 1 · μ.real(s) ^ (1/2)` is strictly positive because
    `μ.real(s) > 0`. -/
theorem LogWeightedL2_nontrivial : Nontrivial LogWeightedL2 := by
  -- The candidate witness.
  let hs : MeasurableSet (Ioo (1/2 : ℝ) 1) := measurableSet_Ioo
  let μ : Measure ℝ := logWeightedMeasure.restrict (Ioo (0:ℝ) 1)
  let hμs_ne_top : μ (Ioo (1/2 : ℝ) 1) ≠ ∞ :=
    logWeightedMeasure_restrict_Ioo_half_one_ne_top
  let hμs_ne_zero : μ (Ioo (1/2 : ℝ) 1) ≠ 0 :=
    logWeightedMeasure_restrict_Ioo_half_one_ne_zero
  let f : LogWeightedL2 :=
    (indicatorConstLp 2 hs hμs_ne_top (1 : ℂ) :
      Lp ℂ 2 (logWeightedMeasure.restrict (Ioo (0:ℝ) 1)))
  refine ⟨f, 0, ?_⟩
  intro hf_eq
  -- ‖f‖ = ‖(1:ℂ)‖ · μ.real(s) ^ (1/2)  via `norm_indicatorConstLp'`.
  have hp : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_norm_indicator :
      ‖f‖ = ‖(1 : ℂ)‖ * (μ.real (Ioo (1/2 : ℝ) 1)) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    change ‖indicatorConstLp 2 hs hμs_ne_top (1 : ℂ)‖ = _
    exact norm_indicatorConstLp' hp hμs_ne_zero
  -- From `f = 0`, get `‖f‖ = 0`.
  have h_norm_zero : ‖f‖ = 0 := by
    rw [show f = 0 from hf_eq, norm_zero]
  -- Combine: `μ.real(s) ^ (1/2) = 0`, hence `μ.real(s) = 0`.
  rw [h_norm_indicator, norm_one, one_mul] at h_norm_zero
  have h_toreal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h_toreal] at h_norm_zero
  have h_half_ne_zero : (1/2 : ℝ) ≠ 0 := by norm_num
  have h_real_nonneg : 0 ≤ μ.real (Ioo (1/2 : ℝ) 1) := measureReal_nonneg
  have h_real_zero : μ.real (Ioo (1/2 : ℝ) 1) = 0 :=
    (Real.rpow_eq_zero h_real_nonneg h_half_ne_zero).mp h_norm_zero
  -- But μ.real(s) = (μ(s)).toReal, and μ(s) ≠ 0 and μ(s) ≠ ∞ ⟹ toReal ≠ 0.
  have h_toreal_zero : (μ (Ioo (1/2 : ℝ) 1)).toReal = 0 := h_real_zero
  rw [ENNReal.toReal_eq_zero_iff] at h_toreal_zero
  exact h_toreal_zero.elim hμs_ne_zero hμs_ne_top

end PrincipiaTractalis
