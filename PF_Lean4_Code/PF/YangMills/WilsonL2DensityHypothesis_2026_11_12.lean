/-
# PF.YangMills.WilsonL2DensityHypothesis_2026_11_12

**Step 3 of the L² extension lane** — foundations for density of
continuous-with-support in L²-with-support via Route A (pushforward
through `projectNonMinus`).

## Delivered

* `nonMinusGauge_compactSpace` — `NonMinusGauge L` is compact.
* `wilsonProjectedGibbsMeasure_weaklyRegular (β)` — `WeaklyRegular`
  instance on the pushforward measure `ν := μ_Gibbs.map projectNonMinus`.
  Enables mathlib's `MemLp.exists_boundedContinuous_eLpNorm_sub_le` to
  apply on `ν`.
* `WilsonL2DensityMeasurabilityBridge` — the named sub-gap for the
  AEStronglyMeasurable chain Route A needs.  Standard mathlib argument
  via strongly-measurable representatives + AE-null transfer; ~30-50
  Lean lines pending a dedicated session.

Once this sub-gap discharges, `WilsonL2DensityHypothesis L β` follows
by:
1. Factor `F = F' ∘ projectNonMinus` via `supportedOnPlusZero_iff_factors`.
2. `MemLp F' 2 ν` via `memLp_map_measure_iff`.
3. Apply `MemLp.exists_boundedContinuous_eLpNorm_sub_le` on `(F', ν)`.
4. Lift `G'_n ∘ projectNonMinus` back to `GaugeField L`.
5. `eLpNorm` convergence via `eLpNorm_map_measure`.

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
compact Hausdorff + finite measure.  This is the key enabling instance
for applying mathlib's density machinery `MemLp.exists_boundedContinuous_eLpNorm_sub_le`
on the pushforward `ν`. -/
instance wilsonProjectedGibbsMeasure_weaklyRegular (β : ℝ) :
    MeasureTheory.Measure.WeaklyRegular (wilsonProjectedGibbsMeasure L β) := by
  haveI : IsFiniteMeasure (wilsonProjectedGibbsMeasure L β) :=
    wilsonProjectedGibbsMeasure_isFiniteMeasure β
  infer_instance

/-- **Measurability sub-gap for Route A.** For `F : GaugeField L → ℂ`
with `supportedOnPlusZero F` and `MemLp F 2 μ_Gibbs`, the factored
function (from `supportedOnPlusZero_iff_factors`) is
`AEStronglyMeasurable` w.r.t. the pushforward measure `ν`.

Standard argument via taking the strongly-measurable representative of
`F` and tracking AE-null transfer under the pushforward.  Stated as a
named hypothesis to isolate this bridge and enable the full density
proof via Route A. -/
def WilsonL2DensityMeasurabilityBridge (L : ℕ) [NeZero L] (β : ℝ) : Prop :=
  ∀ F : GaugeField L → ℂ, MemLp F 2 (wilsonGibbsMeasure L β) →
    supportedOnPlusZero F →
    ∀ F' : NonMinusGauge L → ℂ, (F = F' ∘ projectNonMinus) →
    AEStronglyMeasurable F' (wilsonProjectedGibbsMeasure L β)

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonProjectedGibbsMeasure_weaklyRegular
#print axioms PF.YangMills.WilsonL2DensityMeasurabilityBridge
