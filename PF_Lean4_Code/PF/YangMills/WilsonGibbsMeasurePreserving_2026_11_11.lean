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

/-! ## §2 — integral- and L²-norm-level consequences

The measure-preservation lemma immediately gives the integral invariance
`∫ F(θU) dμ_Gibbs = ∫ F(U) dμ_Gibbs` via `MeasurePreserving.integral_comp`
on the measurable involutive embedding `θ`.  In particular, squared L²
norms are θ-invariant: `∫ |F(θU)|² dμ_Gibbs = ∫ |F(U)|² dμ_Gibbs`.  This
is the isometry at the heart of the L²-extension density argument.
-/

/-- `θ` as a `MeasurableEmbedding` (follows from being an involutive
measurable map, via `MeasurableEquiv.ofInvolutive`). -/
theorem timeReflectionGaugeField_measurableEmbedding :
    MeasurableEmbedding
      (timeReflectionGaugeField : GaugeField L → GaugeField L) :=
  (MeasurableEquiv.ofInvolutive timeReflectionGaugeField
    timeReflectionGaugeField_involutive
    timeReflectionGaugeField_measurable).measurableEmbedding

/-- **Integral invariance on the Gibbs measure.** -/
theorem integral_wilsonGibbs_timeReflection (β : ℝ)
    (F : GaugeField L → ℂ) :
    ∫ U, F (timeReflectionGaugeField U) ∂(wilsonGibbsMeasure L β)
      = ∫ U, F U ∂(wilsonGibbsMeasure L β) :=
  (wilsonGibbsMeasure_measurePreserving_timeReflection β).integral_comp
    timeReflectionGaugeField_measurableEmbedding F

/-- **Real-valued integral invariance on the Gibbs measure.** -/
theorem integral_wilsonGibbs_timeReflection_real (β : ℝ)
    (F : GaugeField L → ℝ) :
    ∫ U, F (timeReflectionGaugeField U) ∂(wilsonGibbsMeasure L β)
      = ∫ U, F U ∂(wilsonGibbsMeasure L β) :=
  (wilsonGibbsMeasure_measurePreserving_timeReflection β).integral_comp
    timeReflectionGaugeField_measurableEmbedding F

/-- **Squared-L²-norm invariance on the Gibbs measure.** The integral of
`|F(θU)|² = |F(U)|²` as a real number: direct application of
`integral_wilsonGibbs_timeReflection_real` to `fun U => ‖F U‖²`. -/
theorem integral_norm_sq_wilsonGibbs_timeReflection (β : ℝ)
    (F : GaugeField L → ℂ) :
    ∫ U, ‖F (timeReflectionGaugeField U)‖ ^ 2 ∂(wilsonGibbsMeasure L β)
      = ∫ U, ‖F U‖ ^ 2 ∂(wilsonGibbsMeasure L β) :=
  integral_wilsonGibbs_timeReflection_real β (fun U => ‖F U‖ ^ 2)

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonGibbsMeasure_measurePreserving_timeReflection
#print axioms PF.YangMills.timeReflectionGaugeField_measurableEmbedding
#print axioms PF.YangMills.integral_wilsonGibbs_timeReflection
#print axioms PF.YangMills.integral_wilsonGibbs_timeReflection_real
#print axioms PF.YangMills.integral_norm_sq_wilsonGibbs_timeReflection
