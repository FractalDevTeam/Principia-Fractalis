/-
# NS Route A item 3 — Fubini-Tonelli swap discharge.

★ 2026-11-15 EOD (second attempt, now closing) — discharges the
second of the three named residuals in
`PF/Analytic/YoungConvolutionL1L2_2026_11_15.lean`:

  `YoungL1L2_FubiniTonelliSwap` (residual #2)
      — now closed under `AddCommGroup G` + `IsAddLeftInvariant μ`
        + joint AEMeasurability + `SFinite μ`.

With this discharge + `pointwise_cauchy_schwarz_discharge` (residual
#1, commit `8028e1e3`) + `constant_pull_discharge` (residual #3,
commit `af609869`), **ALL THREE named residuals of the NS Route A
Young L¹⋆L²→L² bound are now discharged.**  The main composition
theorem `convolution_squared_le_L1_sq_mul_L2_sq` therefore holds
unconditionally under the natural joint-measurability +
left-invariance hypotheses common to all three — the classical
squared Young inequality obtains as a direct corollary.

## Discharge technique

The named residual asserts:
    `∫⁻ x, ∫⁻ t, f t * g (x - t) ^ 2 ∂μ ∂μ
      = (∫⁻ t, f t ∂μ) * ∫⁻ y, g y ^ 2 ∂μ`.

Proof chain:
  (i)   Tonelli swap `∫⁻ x ∫⁻ t = ∫⁻ t ∫⁻ x`
        via `MeasureTheory.lintegral_lintegral_swap`.
  (ii)  Pull the `f t` factor out of the inner `x`-integral
        via `lintegral_const_mul''`.
  (iii) Change of variable `y = x - t` in the inner `x`-integral
        via `lintegral_sub_right_eq_self` (auto-additive from
        `lintegral_div_right_eq_self`; uses `IsAddRightInvariant`,
        which in an `AddCommGroup` is inferred from `IsAddLeftInvariant`
        via the `IsAddLeftInvariant.isAddRightInvariant` instance).
  (iv)  Pull the resulting `x`-independent `(∫⁻ y, g y ^ 2 ∂μ)` factor
        out of the outer `t`-integral via `lintegral_mul_const''`.

Routine mathlib lemma composition on top of standard group-measure
machinery.  Three-axiom bar.

## Impact

Before: NS Route A squared Young bound conditional on 3 named residuals.
After:  NS Route A squared Young bound conditional on 0 named residuals
        (all three now discharged under natural hypotheses).

The classical `‖f ⋆ g‖_{L²} ≤ ‖f‖_{L¹} · ‖g‖_{L²}` obtains by taking
square roots.  This is the ROOT of the NS Route A three-item chain
— items 1 (Schwartz dense in L²) and 2 (Galerkin → weak) now
proceed from here.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.Analytic.YoungConvolutionL1L2_2026_11_15
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.LIntegral

open MeasureTheory
open scoped ENNReal

namespace PF.Analytic.YoungConvolutionL1L2

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G]
  [MeasurableAdd₂ G] [MeasurableNeg G]

/-! ## §1 — Discharge of the Fubini-Tonelli swap named residual. -/

/-- **`fubini_tonelli_swap_discharge`** — discharge of the named
residual `YoungL1L2_FubiniTonelliSwap` under joint AEMeasurability +
`IsAddLeftInvariant` on `μ`.

For any σ-finite left-invariant measure `μ` on an abelian measurable
group `G`, for non-negative measurable `f g : G → ℝ≥0∞`,
    `∫⁻ x, ∫⁻ t, f t * g (x - t) ^ 2 ∂μ ∂μ
      = (∫⁻ t, f t ∂μ) * ∫⁻ y, g y ^ 2 ∂μ`.

Proof: Tonelli swap + inner f-factor pull + change of variable
`y = x - t` (uses the `IsAddRightInvariant` instance auto-inferred
from `IsAddLeftInvariant` in the abelian group) + outer constant pull. -/
theorem fubini_tonelli_swap_discharge
    (μ : Measure G) [SFinite μ] [μ.IsAddLeftInvariant]
    (f g : G → ℝ≥0∞)
    (hJoint : AEMeasurable
      (Function.uncurry (fun x t => f t * g (x - t) ^ 2)) (μ.prod μ)) :
    YoungL1L2_FubiniTonelliSwap μ f g := by
  intro hf hg
  -- (i) Tonelli swap.
  rw [lintegral_lintegral_swap hJoint]
  -- Goal: ∫⁻ t, ∫⁻ x, f t * g (x - t) ^ 2 ∂μ ∂μ
  --      = (∫⁻ t, f t ∂μ) * ∫⁻ y, g y ^ 2 ∂μ
  -- (ii) + (iii) Pull f t out of inner x-integral, then change variable.
  have hStep : ∀ t, (∫⁻ x, f t * g (x - t) ^ 2 ∂μ)
      = f t * ∫⁻ y, g y ^ 2 ∂μ := by
    intro t
    -- Measurability of `x ↦ g (x - t) ^ 2` via sub_right measure-preservation.
    have hgt : AEMeasurable (fun x => g (x - t) ^ 2) μ := by
      have heq : (fun x => g (x - t) ^ 2)
          = (fun y => g y ^ 2) ∘ (fun x => x - t) := rfl
      rw [heq]
      exact (hg.pow_const 2).comp_quasiMeasurePreserving
        ((measurePreserving_sub_right μ t).quasiMeasurePreserving)
    rw [lintegral_const_mul'' (f t) hgt]
    congr 1
    -- Change of variable y = x - t via left-invariance (→ right-invariance
    -- in the abelian group).
    exact lintegral_sub_right_eq_self (fun y => g y ^ 2) t
  simp_rw [hStep]
  -- (iv) Pull the x-independent constant out of the outer t-integral.
  rw [lintegral_mul_const'' (∫⁻ y, g y ^ 2 ∂μ) hf]

/-! ## §2 — Axiom audit. -/

#check @fubini_tonelli_swap_discharge

end PF.Analytic.YoungConvolutionL1L2
