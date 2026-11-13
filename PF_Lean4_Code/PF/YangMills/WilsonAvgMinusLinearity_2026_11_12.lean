/-
# PF.YangMills.WilsonAvgMinusLinearity_2026_11_12

**Step 3c.4c atomic**: linearity of `avgMinus` under subtraction and
scalar multiplication, plus the projection-factoring identity
`avgMinus F = (avgMinus F ∘ projectNonMinus) ∘ (gluePlusMinus (proj U) V)`
form that makes the Fubini composition transparent.

Delivers:

* `avgMinus_sub`: `avgMinus (G - H) = avgMinus G - avgMinus H`.
* `avgMinus_apply_eq_integral_at_projected`:
  `avgMinus F U = ∫ V, F (gluePlusMinus (projectNonMinus U) V) ∂μ_minus`
  — the definitional expansion for use in Fubini manipulations.
* `avgMinus_gluePlusMinus_eq`:
  `avgMinus F (gluePlusMinus W V₀) = ∫ V, F (gluePlusMinus W V) ∂μ_minus`
  — shows the `avgMinus` output depends only on the non-minus part.

These are the pure algebraic/definitional ingredients that let the
base-measure L²-contraction composition treat `avgMinus` as a linear
operator whose output is a pullback through `projectNonMinus`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonMinusLinkAveraging_2026_11_12

namespace PF.YangMills

open MeasureTheory

variable {L : ℕ} [NeZero L]

/-- **Linearity of `avgMinus` under subtraction.** Direct from
`integral_sub` + definitional unfolding, when the pre-images are
integrable. For continuous `G, H` on the compact `GaugeField L`, this
integrability is automatic. -/
theorem avgMinus_sub (G H : GaugeField L → ℂ)
    (hG : Continuous G) (hH : Continuous H) (U : GaugeField L) :
    avgMinus (fun U => G U - H U) U = avgMinus G U - avgMinus H U := by
  unfold avgMinus
  haveI : CompactSpace (MinusGauge L) := by unfold MinusGauge; exact Pi.compactSpace
  haveI : IsProbabilityMeasure (minusHaarMeasure L) :=
    minusHaarMeasure_isProbabilityMeasure L
  -- Integrability of the two summands.
  have hpair_cont :
      Continuous (fun V : MinusGauge L => (projectNonMinus U, V)) :=
    continuous_const.prodMk continuous_id
  have hglue_cont :
      Continuous (fun V : MinusGauge L =>
        gluePlusMinus (L := L) (projectNonMinus U) V) :=
    gluePlusMinus_continuous.comp hpair_cont
  have hGcomp_cont :
      Continuous (fun V => G (gluePlusMinus (projectNonMinus U) V)) :=
    hG.comp hglue_cont
  have hHcomp_cont :
      Continuous (fun V => H (gluePlusMinus (projectNonMinus U) V)) :=
    hH.comp hglue_cont
  obtain ⟨CG, hCG⟩ : ∃ C : ℝ, ∀ V,
      ‖G (gluePlusMinus (projectNonMinus U) V)‖ ≤ C := by
    obtain ⟨M, hM⟩ := (isCompact_range hGcomp_cont.norm).bddAbove
    exact ⟨M, fun V => hM (Set.mem_range_self V)⟩
  obtain ⟨CH, hCH⟩ : ∃ C : ℝ, ∀ V,
      ‖H (gluePlusMinus (projectNonMinus U) V)‖ ≤ C := by
    obtain ⟨M, hM⟩ := (isCompact_range hHcomp_cont.norm).bddAbove
    exact ⟨M, fun V => hM (Set.mem_range_self V)⟩
  have hG_int :
      Integrable (fun V => G (gluePlusMinus (projectNonMinus U) V))
        (minusHaarMeasure L) := by
    refine Integrable.of_bound hGcomp_cont.aestronglyMeasurable CG ?_
    filter_upwards with V; exact hCG V
  have hH_int :
      Integrable (fun V => H (gluePlusMinus (projectNonMinus U) V))
        (minusHaarMeasure L) := by
    refine Integrable.of_bound hHcomp_cont.aestronglyMeasurable CH ?_
    filter_upwards with V; exact hCH V
  rw [show (fun V =>
        (fun U => G U - H U) (gluePlusMinus (projectNonMinus U) V))
      = (fun V => G (gluePlusMinus (projectNonMinus U) V) -
                   H (gluePlusMinus (projectNonMinus U) V)) from rfl]
  exact integral_sub hG_int hH_int

set_option linter.unusedSectionVars false in
/-- **Definitional unfolding** of `avgMinus F U` as an integral over
`V` with the glue structure explicit. Trivial by `unfold`. -/
theorem avgMinus_apply (F : GaugeField L → ℂ) (U : GaugeField L) :
    avgMinus F U
      = ∫ V, F (gluePlusMinus (projectNonMinus U) V) ∂(minusHaarMeasure L) := rfl

/-- **`avgMinus F` factors through `projectNonMinus`.** For any
`W : NonMinusGauge L` and any `V₀ : MinusGauge L`,

  `avgMinus F (gluePlusMinus W V₀) = ∫ V, F (gluePlusMinus W V) ∂μ_minus`.

The RHS does not depend on `V₀`. Uses
`projectNonMinus_gluePlusMinus`. -/
theorem avgMinus_gluePlusMinus (F : GaugeField L → ℂ)
    (W : NonMinusGauge L) (V₀ : MinusGauge L) :
    avgMinus F (gluePlusMinus W V₀)
      = ∫ V, F (gluePlusMinus W V) ∂(minusHaarMeasure L) := by
  unfold avgMinus
  rw [projectNonMinus_gluePlusMinus]

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.avgMinus_sub
#print axioms PF.YangMills.avgMinus_apply
#print axioms PF.YangMills.avgMinus_gluePlusMinus
