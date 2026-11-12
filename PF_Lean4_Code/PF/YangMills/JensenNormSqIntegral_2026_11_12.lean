/-
# PF.YangMills.JensenNormSqIntegral_2026_11_12

**Utility lemma**: Jensen's inequality for the squared norm on a
probability measure.

For any normed vector space `E` over `ℝ`, probability measure `μ` on
`α`, and `f : α → E` integrable with `‖f‖²` integrable,

  `‖∫ x, f x ∂μ‖² ≤ ∫ x, ‖f x‖² ∂μ`.

Standard mathlib argument: Bochner `norm_integral_le_integral_norm`
gives `‖∫f‖ ≤ ∫‖f‖`; squaring and applying Cauchy-Schwarz /
`ConvexOn.map_integral_le` with `g = fun x => x^2` convex on `Ici 0`
gives the result.

Used downstream by the base-measure L²-contraction of `avgMinus` via
Fubini on the sector split.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace PF.YangMills

open MeasureTheory

/-- **Jensen's inequality for the squared norm on a probability measure.**
For a probability measure `μ` on `α` and `f : α → E` with `f` and
`‖f‖²` integrable, the squared norm of the integral is at most the
integral of the squared norms. -/
theorem norm_sq_integral_le_integral_norm_sq
    {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α → E) (hf : Integrable f μ) (hf_sq : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  -- Step 1: Bochner `‖∫f‖ ≤ ∫‖f‖`.
  have h_bochner : ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ :=
    norm_integral_le_integral_norm f
  have h_nonneg : (0 : ℝ) ≤ ∫ x, ‖f x‖ ∂μ := by
    refine integral_nonneg ?_
    intro x
    exact norm_nonneg _
  -- Step 2: Jensen's inequality with `g = fun x => x^2` convex on `Ici 0`
  -- applied to `fun x => ‖f x‖ : α → ℝ`.
  have h_norm_int : Integrable (fun x => ‖f x‖) μ := hf.norm
  have hg_convex : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ 2) :=
    convexOn_pow 2
  have hg_cont : ContinuousOn (fun x : ℝ => x ^ 2) (Set.Ici 0) :=
    (continuous_pow 2).continuousOn
  have hs_closed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
  have hfs : ∀ᵐ x ∂μ, (fun x => ‖f x‖) x ∈ Set.Ici (0 : ℝ) := by
    filter_upwards with x
    exact norm_nonneg _
  have h_jensen :
      (fun x : ℝ => x ^ 2) (∫ x, ‖f x‖ ∂μ)
        ≤ ∫ x, (fun x : ℝ => x ^ 2) ‖f x‖ ∂μ := by
    refine ConvexOn.map_integral_le hg_convex hg_cont hs_closed hfs h_norm_int ?_
    exact hf_sq
  -- Step 3: Combine `‖∫f‖ ≤ ∫‖f‖` and `(∫‖f‖)^2 ≤ ∫‖f‖^2`.
  have h_sq_mono : ‖∫ x, f x ∂μ‖ ^ 2 ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) h_bochner 2
  exact h_sq_mono.trans h_jensen

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.norm_sq_integral_le_integral_norm_sq
