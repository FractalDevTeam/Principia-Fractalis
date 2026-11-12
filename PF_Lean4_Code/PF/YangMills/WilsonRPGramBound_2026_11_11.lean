/-
# PF.YangMills.WilsonRPGramBound_2026_11_11

**Step 1 of the YM L²-extension plan:** the Cauchy–Schwarz / Hölder bound
on θ-crossed Gram entries.

For any two `L²(wilsonGibbsMeasure)` functions `F G : GaugeField L → ℂ`,

   `‖∫ star(F(θU)) · G(U) ∂μ_Gibbs‖
      ≤ (∫ ‖F U‖² ∂μ_Gibbs)^(1/2) · (∫ ‖G U‖² ∂μ_Gibbs)^(1/2)`

The proof chain:

  1. Triangle inequality for Bochner integrals
     (`norm_integral_le_integral_norm`).
  2. Pointwise `‖star z · w‖ = ‖z‖ · ‖w‖` (direct via `norm_mul`, `norm_star`).
  3. Hölder with conjugate exponents `p = q = 2`
     (`integral_mul_le_Lp_mul_Lq_of_nonneg` + `HolderConjugate.two_two`).
  4. Isometry of the `L²` norm under `θ` on `μ_Gibbs`
     (`integral_norm_sq_wilsonGibbs_timeReflection`, from step 2 of
     `YM_L2_EXTENSION_SCOPING_2026-11-11.md`).

Hypotheses on the test functions: `MemLp F 2 μ_Gibbs` and
`MemLp G 2 μ_Gibbs`.  These are automatic for continuous test functions
on the finite Gibbs measure, but the lemma is stated in `MemLp` form so
a future density argument can apply.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.YangMills.WilsonGibbsMeasurePreserving_2026_11_11
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **Cauchy–Schwarz / Hölder bound on the θ-crossed Gram entry.**  For any
`F, G : GaugeField L → ℂ` with `MemLp · 2 μ_Gibbs`, the complex-valued
integral `∫ star(F(θU)) · G(U) dμ_Gibbs` is bounded in norm by the
product of the `L²` norms. -/
theorem wilson_rp_gram_bound (β : ℝ) (F G : GaugeField L → ℂ)
    (hF : MemLp F 2 (wilsonGibbsMeasure L β))
    (hG : MemLp G 2 (wilsonGibbsMeasure L β)) :
    ‖∫ U, star (F (timeReflectionGaugeField U)) * G U
        ∂(wilsonGibbsMeasure L β)‖
      ≤ (∫ U, ‖F U‖ ^ 2 ∂(wilsonGibbsMeasure L β)) ^ ((1 : ℝ) / 2)
        * (∫ U, ‖G U‖ ^ 2 ∂(wilsonGibbsMeasure L β)) ^ ((1 : ℝ) / 2) := by
  set μ := wilsonGibbsMeasure L β
  -- Lift `F` through `θ`, using `MemLp.comp_measurePreserving` + the
  -- just-landed θ-invariance of `μ_Gibbs`.
  have hF_theta : MemLp (F ∘ timeReflectionGaugeField) 2 μ :=
    hF.comp_measurePreserving
      (wilsonGibbsMeasure_measurePreserving_timeReflection β)
  -- `MemLp.norm` lifts to the pointwise norm.
  have hF_theta_norm : MemLp (fun U => ‖F (timeReflectionGaugeField U)‖) 2 μ :=
    hF_theta.norm
  have hG_norm : MemLp (fun U => ‖G U‖) 2 μ :=
    hG.norm
  -- Triangle inequality + pointwise identity `‖star z · w‖ = ‖z‖ · ‖w‖`.
  have hTri :
      ‖∫ U, star (F (timeReflectionGaugeField U)) * G U ∂μ‖
        ≤ ∫ U, ‖F (timeReflectionGaugeField U)‖ * ‖G U‖ ∂μ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards with U
    rw [norm_mul, norm_star]
  -- Hölder with `p = q = 2`.
  have hHolder :
      ∫ U, ‖F (timeReflectionGaugeField U)‖ * ‖G U‖ ∂μ
        ≤ (∫ U, ‖F (timeReflectionGaugeField U)‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)
          * (∫ U, ‖G U‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
    have hpq : Real.HolderConjugate 2 2 := .two_two
    refine integral_mul_le_Lp_mul_Lq_of_nonneg hpq ?_ ?_ ?_ ?_
    · filter_upwards with U using norm_nonneg _
    · filter_upwards with U using norm_nonneg _
    · simpa [ENNReal.ofReal_ofNat] using hF_theta_norm
    · simpa [ENNReal.ofReal_ofNat] using hG_norm
  -- Convert `rpow 2` to `^ 2` (nonneg norms, so this is `pow_two`).
  have hFsq :
      (∫ U, ‖F (timeReflectionGaugeField U)‖ ^ (2 : ℝ) ∂μ)
        = ∫ U, ‖F (timeReflectionGaugeField U)‖ ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with U
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hGsq :
      (∫ U, ‖G U‖ ^ (2 : ℝ) ∂μ) = ∫ U, ‖G U‖ ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with U
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hFsq, hGsq] at hHolder
  -- Apply the `θ`-isometry to the `F(θU)` norm.
  rw [integral_norm_sq_wilsonGibbs_timeReflection] at hHolder
  exact le_trans hTri hHolder

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilson_rp_gram_bound
