/-
# NS Route A item 3 — constant-pull discharge.

★ 2026-11-15 — discharges the third of the three named residuals in
`PF/Analytic/YoungConvolutionL1L2_2026_11_15.lean`:

  `YoungL1L2_IntegrableConstantPull` (residual #3)
      — now closed under a mild joint-measurability hypothesis.

Together with `pointwise_cauchy_schwarz_discharge` (residual #1,
`PF/Analytic/YoungConvolutionL1L2_CSDischarge_2026_11_15.lean`), two
of the three named residuals of the Young L¹⋆L²→L² bound are now
discharged.  One residual remains: `YoungL1L2_FubiniTonelliSwap`.

## Discharge technique

The named residual asserts:
    `∫⁻ x, (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * g (x - t) ^ 2 ∂μ) ∂μ
      = (∫⁻ t, f t ∂μ) * ∫⁻ x, ∫⁻ t, f t * g (x - t) ^ 2 ∂μ ∂μ`.

The RHS pulls the `x`-independent factor `(∫⁻ t, f t ∂μ)` out of the
outer `x`-integral.  Apply mathlib's `lintegral_const_mul''` directly,
given AEMeasurable of `fun x => ∫⁻ t, f t * g (x - t) ^ 2 ∂μ`
(parameter-measurability of lintegral via
`AEMeasurable.lintegral_prod_right`).

Routine mathlib lemma composition.  Three-axiom bar.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.Analytic.YoungConvolutionL1L2_2026_11_15

open MeasureTheory
open scoped ENNReal

namespace PF.Analytic.YoungConvolutionL1L2

variable {G : Type*} [MeasurableSpace G] [AddGroup G]

/-! ## §1 — Discharge of the constant-pull named residual. -/

/-- **`constant_pull_discharge`** — unconditional discharge of the
named residual `YoungL1L2_IntegrableConstantPull`, under the mild
joint-measurability hypothesis that the inner-integrand parameter-map
is AEMeasurable.

For any σ-finite measure `μ` and any non-negative measurable
`f g : G → ℝ≥0∞`, under AEMeasurable of
`fun x => ∫⁻ t, f t * g (x - t) ^ 2 ∂μ`,
    `∫⁻ x, (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * g (x - t) ^ 2 ∂μ) ∂μ
      = (∫⁻ t, f t ∂μ) * ∫⁻ x, ∫⁻ t, f t * g (x - t) ^ 2 ∂μ ∂μ`.

Direct application of `lintegral_const_mul''`. -/
theorem constant_pull_discharge
    (μ : Measure G) (f g : G → ℝ≥0∞)
    (hInner : AEMeasurable
        (fun x => ∫⁻ t, f t * g (x - t) ^ 2 ∂μ) μ) :
    YoungL1L2_IntegrableConstantPull μ f g := by
  unfold YoungL1L2_IntegrableConstantPull
  exact lintegral_const_mul'' (∫⁻ t, f t ∂μ) hInner

/-! ## §2 — Axiom audit. -/

#check @constant_pull_discharge

end PF.Analytic.YoungConvolutionL1L2
