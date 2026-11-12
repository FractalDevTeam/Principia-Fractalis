/-
# PF.YangMills.WilsonL2Density_2026_11_12

**Step 3c (foundations)** for the YM L²-extension plan — pushforward
measure setup and finiteness.

Defines:
* `wilsonProjectedGibbsMeasure L β := (wilsonGibbsMeasure L β).map projectNonMinus`
  — the pushforward of the Gibbs measure to `NonMinusGauge L` under
  the non-minus projection.
* `IsFiniteMeasure (wilsonProjectedGibbsMeasure L β)` as an instance,
  via mathlib's `Measure.isFiniteMeasure_map` applied to
  `wilsonGibbsMeasure_isFiniteMeasure`.

These are the measure-theoretic ingredients that the remaining density
lift (step 3c proper) will use.  The density lift itself requires
threading `AEStronglyMeasurable` through the factoring
`F = F' ∘ projectNonMinus`, which has a subtle interaction with the
non-injectivity of `projectNonMinus` (many `U` map to the same `U'`).

## Route A — pushforward (attempted this session, obstructed)

Apply mathlib's `MemLp.exists_boundedContinuous_eLpNorm_sub_le` to the
factored `F'` on `(wilsonProjectedGibbsMeasure L β)`.  **Obstruction**:
the AEStronglyMeasurable chain for `F'` on the pushforward would
require `projectNonMinus` to be a measurable embedding, which it is
not (many-to-one).  A workaround via a strongly-measurable
ae-representative fails because the ae-null-set transfer
`A μ_Gibbs-null → collapseMinus⁻¹ A ν-null` does not hold in general —
`collapseMinus` sends ν-measurable sets to the minus-1 slice (which is
μ_Gibbs-null for continuous base measure), so preimages don't cleanly
transfer.

## Route B — conditional expectation (recommended)

Apply mathlib's density directly to `F` on `μ_Gibbs` (which is
`WeaklyRegular` as a finite measure on a Polish space).  Get bounded
continuous `G_n` with `eLpNorm (F - G_n) 2 μ_Gibbs ≤ 1/n`.  Project
`G_n` via the **minus-link averaging operator** (conditional
expectation):

    `(avg G_n)(U) := ∫ G_n(gluePlusMinus U.nonMinus V.minus) d Haar_minus V`.

This operator is linear, continuous (parametric integration on
compact), `supportedOnPlusZero`-preserving, and an L² contraction
(Jensen).  So `eLpNorm (F - avg G_n) 2 μ_Gibbs ≤ eLpNorm (F - G_n) 2
μ_Gibbs → 0`.

Estimated ~70-100 lines of mathlib navigation (product-measure
factoring + parametric integral continuity + Jensen contraction).
Pending a dedicated session.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonNonMinusProjection_2026_11_12
import PF.YangMills.WilsonGibbsMeasurePreserving_2026_11_11

namespace PF.YangMills

open MeasureTheory

variable {L : ℕ} [NeZero L]

/-- The pushforward of `wilsonGibbsMeasure L β` under the non-minus
projection.  Lives on `NonMinusGauge L`. -/
noncomputable def wilsonProjectedGibbsMeasure (L : ℕ) [NeZero L] (β : ℝ) :
    Measure (NonMinusGauge L) :=
  (wilsonGibbsMeasure L β).map projectNonMinus

/-- The pushforward measure is finite: pushforward of a finite measure
is finite (mathlib's `Measure.isFiniteMeasure_map`). -/
instance wilsonProjectedGibbsMeasure_isFiniteMeasure (β : ℝ) :
    IsFiniteMeasure (wilsonProjectedGibbsMeasure L β) := by
  unfold wilsonProjectedGibbsMeasure
  haveI : IsFiniteMeasure (wilsonGibbsMeasure L β) :=
    wilsonGibbsMeasure_isFiniteMeasure β
  infer_instance

/-- Convenience: the pushforward has the expected integral change-of-
variable identity.  For any `g : NonMinusGauge L → ℂ` strongly
measurable on the pushforward,

  `∫ U', g U' ∂ν = ∫ U, g (projectNonMinus U) ∂μ_Gibbs`.

Proof: `MeasurePreserving.integral_comp`-style; projectNonMinus is
measurable (not an embedding), so we use the general
`integral_map_of_strongly_measurable` form via mathlib. -/
theorem integral_wilsonProjectedGibbsMeasure (β : ℝ) (g : NonMinusGauge L → ℂ)
    (hg : AEStronglyMeasurable g (wilsonProjectedGibbsMeasure L β)) :
    ∫ U', g U' ∂(wilsonProjectedGibbsMeasure L β)
      = ∫ U, g (projectNonMinus U) ∂(wilsonGibbsMeasure L β) := by
  unfold wilsonProjectedGibbsMeasure
  exact integral_map projectNonMinus_measurable.aemeasurable hg

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonProjectedGibbsMeasure_isFiniteMeasure
#print axioms PF.YangMills.integral_wilsonProjectedGibbsMeasure
