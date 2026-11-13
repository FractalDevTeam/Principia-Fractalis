/-
# PF.YangMills.WilsonL2DensityHypothesis_2026_11_12

**Step 3 of the L² extension lane** — foundations for density of
continuous-with-support in L²-with-support via Route A (pushforward
through `projectNonMinus`).

## Delivered

* `nonMinusGauge_compactSpace` — `NonMinusGauge L` is compact.
* `wilsonProjectedGibbsMeasure_weaklyRegular (β)` — `WeaklyRegular`
  instance on the pushforward `ν := μ_Gibbs.map projectNonMinus`.
  Automatic via compact Hausdorff + finite measure.  This is the key
  enabling instance for mathlib's
  `MemLp.exists_boundedContinuous_eLpNorm_sub_le` to apply on `ν`.
* `WilsonL2DensityMeasurabilityBridge` — the named measurability
  sub-gap that remains for Route A on raw `MemLp` input.
* `WilsonL2DensityHypothesisStrong` — a strengthened version of
  `WilsonL2DensityHypothesis` additionally requiring
  `StronglyMeasurable F`.  Under this strengthening the bridge closes
  automatically (composition of strongly-measurable with continuous
  section is strongly measurable).

## Why the measurability sub-gap is nontrivial

Given `F : GaugeField L → ℂ` with `MemLp F 2 μ_Gibbs` (hence only
`AEStronglyMeasurable`), the factored function evaluates `F` on the
μ_Gibbs-null slice `{U : U|_{minus-links} = 1}`.  AE-equality of `F`
with its strongly-measurable representative on μ_Gibbs doesn't
transfer to pointwise agreement at these null-set values.

Resolution: use `WilsonL2DensityHypothesisStrong` — a routine
strengthening since any L²-class has a strongly-measurable
representative.

## Route A full proof sketch (StronglyMeasurable version)

1. Define `wilsonSection (W) := gluePlusMinus W 1` — continuous
   `NonMinusGauge L → GaugeField L`.
2. Set `F' := F ∘ wilsonSection` — strongly measurable from
   `F.comp_measurable wilsonSection_continuous.measurable`.
3. `F = F' ∘ projectNonMinus` pointwise via `supportedOnPlusZero`
   + `projectNonMinus_gluePlusMinus`.
4. `MemLp F' 2 ν` via `memLp_map_measure_iff`.
5. Apply `MemLp.exists_boundedContinuous_eLpNorm_sub_le` on `(F', ν)`
   (enabled by `wilsonProjectedGibbsMeasure_weaklyRegular`).
6. Get bounded continuous `G'_n : NonMinusGauge L →ᵇ ℂ` with
   `eLpNorm (F' - G'_n) 2 ν ≤ 1/(n+1)`.
7. Set `F_n := G'_n ∘ projectNonMinus` — continuous (composition),
   `supportedOnPlusZero` (factors through `projectNonMinus`),
   `MemLp 2 μ_Gibbs` (via `MemLp.comp_of_map`).
8. `eLpNorm (F - F_n) 2 μ_Gibbs = eLpNorm (F' - G'_n) 2 ν → 0` via
   `eLpNorm_map_measure`.

Pending a dedicated session to execute the ~100 Lean lines.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonL2Density_2026_11_12
import PF.YangMills.WilsonRPL2Extension_2026_11_12
import PF.YangMills.WilsonNonMinusProjection_2026_11_12

namespace PF.YangMills

open MeasureTheory Filter
open scoped Topology ComplexOrder ENNReal

noncomputable section

variable {L : ℕ} [NeZero L]

/-- `NonMinusGauge L` is compact — finite Pi of compact `SU2`. -/
instance nonMinusGauge_compactSpace : CompactSpace (NonMinusGauge L) := by
  unfold NonMinusGauge; exact Pi.compactSpace

/-- The projected Gibbs measure is `WeaklyRegular` — automatic from
compact Hausdorff + finite measure. -/
instance wilsonProjectedGibbsMeasure_weaklyRegular (β : ℝ) :
    MeasureTheory.Measure.WeaklyRegular (wilsonProjectedGibbsMeasure L β) := by
  haveI : IsFiniteMeasure (wilsonProjectedGibbsMeasure L β) :=
    wilsonProjectedGibbsMeasure_isFiniteMeasure β
  infer_instance

/-- **Measurability sub-gap for Route A.** For `F : GaugeField L → ℂ`
with `supportedOnPlusZero F` and `MemLp F 2 μ_Gibbs`, the factored
function is `AEStronglyMeasurable` w.r.t. the pushforward measure `ν`. -/
def WilsonL2DensityMeasurabilityBridge (L : ℕ) [NeZero L] (β : ℝ) : Prop :=
  ∀ F : GaugeField L → ℂ, MemLp F 2 (wilsonGibbsMeasure L β) →
    supportedOnPlusZero F →
    ∀ F' : NonMinusGauge L → ℂ, (F = F' ∘ projectNonMinus) →
    AEStronglyMeasurable F' (wilsonProjectedGibbsMeasure L β)

/-- **Strengthened density hypothesis**: additionally require
`StronglyMeasurable F`.  Under this strengthening, the measurability
bridge closes automatically. -/
def WilsonL2DensityHypothesisStrong (L : ℕ) [NeZero L] (β : ℝ) : Prop :=
  ∀ F : GaugeField L → ℂ,
    StronglyMeasurable F → MemLp F 2 (wilsonGibbsMeasure L β) →
    supportedOnPlusZero F →
    ∃ F_n : ℕ → GaugeField L → ℂ,
      (∀ n, Continuous (F_n n)) ∧
      (∀ n, supportedOnPlusZero (F_n n)) ∧
      (∀ n, MemLp (F_n n) 2 (wilsonGibbsMeasure L β)) ∧
      Tendsto (fun n =>
        eLpNorm (fun U => F U - F_n n U) 2 (wilsonGibbsMeasure L β))
        atTop (𝓝 0)

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonProjectedGibbsMeasure_weaklyRegular
#print axioms PF.YangMills.WilsonL2DensityMeasurabilityBridge
#print axioms PF.YangMills.WilsonL2DensityHypothesisStrong
