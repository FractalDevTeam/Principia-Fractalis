/-
# PF.YangMills.WilsonGibbsMeasurePreserving_2026_11_11

**`wilsonGibbsMeasure` is `θ`-invariant** — the Gibbs measure is preserved
under time reflection.

Combines two facts already in the tree:

* `timeReflectionGaugeField_measurePreserving` — θ preserves `wilsonBaseMeasure`.
* `wilsonActionTotal_timeReflection` — `S ∘ θ = S`.

Since `wilsonGibbsMeasure = wilsonBaseMeasure.withDensity (exp(-β S))` and
both ingredients of this `withDensity` are θ-equivariant (the base measure,
and the density `exp(-β S)` since `S ∘ θ = S` and `exp` is a function),
pushing forward under θ returns the Gibbs measure to itself.

**Why we want this.** The L² extension of `wilson_reflection_positivity_of_continuous`
(see `codex/MILLENNIUM_STATUS_2026-11-11.md` §3) needs
`‖F ∘ θ‖_{L²(μ_Gibbs)} = ‖F‖_{L²(μ_Gibbs)}`. That's exactly what measure
preservation gives, via `MeasurePreserving.integral_comp` applied to `|F|²`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.YangMills.WilsonActionReflectionInvariance_2026_10_18
import PF.YangMills.WilsonActionContinuity_2026_10_20
import PF.YangMills.WilsonReflectionMeasurePreservingApply_2026_10_21
import PF.YangMills.WilsonMeasure_2026_10_17

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **`wilsonGibbsMeasure` is θ-invariant.** Push-forward of
`wilsonGibbsMeasure L β` under `timeReflectionGaugeField` equals
`wilsonGibbsMeasure L β` itself. -/
theorem wilsonGibbsMeasure_measurePreserving_timeReflection (β : ℝ) :
    MeasurePreserving
      (timeReflectionGaugeField : GaugeField L → GaugeField L)
      (wilsonGibbsMeasure L β) (wilsonGibbsMeasure L β) := by
  have hθ_mp : MeasurePreserving
      (timeReflectionGaugeField : GaugeField L → GaugeField L)
      (wilsonBaseMeasure L) (wilsonBaseMeasure L) :=
    timeReflectionGaugeField_measurePreserving
  have hθ_meas : Measurable
      (timeReflectionGaugeField : GaugeField L → GaugeField L) :=
    timeReflectionGaugeField_measurable
  have hw_meas : Measurable
      (fun U : GaugeField L => ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U))) :=
    (Real.measurable_exp.comp
      (measurable_const.mul wilsonActionTotal_measurable)).ennreal_ofReal
  refine ⟨hθ_meas, ?_⟩
  -- Goal: (wilsonGibbsMeasure L β).map θ = wilsonGibbsMeasure L β.
  unfold wilsonGibbsMeasure
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hθ_meas hs]
  rw [withDensity_apply _ hs, withDensity_apply _ (hθ_meas hs)]
  -- LHS = ∫⁻ U in θ⁻¹ s, w U ∂μ_base
  -- RHS = ∫⁻ U in s, w U ∂μ_base
  -- Step 1: On θ⁻¹ s, w U = w (θ U) by wilsonActionTotal_timeReflection.
  have hcong :
      ∫⁻ U in (timeReflectionGaugeField : GaugeField L → GaugeField L) ⁻¹' s,
          ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U))
        ∂(wilsonBaseMeasure L)
      = ∫⁻ U in (timeReflectionGaugeField : GaugeField L → GaugeField L) ⁻¹' s,
          ENNReal.ofReal (Real.exp
            (-β * wilsonActionTotal (timeReflectionGaugeField U)))
        ∂(wilsonBaseMeasure L) := by
    apply setLIntegral_congr_fun (hθ_meas hs)
    intro U _hU
    simp only [wilsonActionTotal_timeReflection]
  rw [hcong]
  -- Step 2: Change of variable via θ MP on μ_base.
  exact hθ_mp.setLIntegral_comp_preimage hs hw_meas

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonGibbsMeasure_measurePreserving_timeReflection
