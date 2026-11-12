/-
# PF.YangMills.WilsonAvgMinusPointwiseJensen_2026_11_12

**Step 3c.4c atomic**: pointwise application of the squared-norm Jensen
inequality to `avgMinus`.

For any `F : GaugeField L → ℂ` continuous (hence integrable on the
compact `GaugeField L`), and any `U : GaugeField L`, Jensen gives

  `‖avgMinus F U‖² ≤ ∫ V, ‖F (gluePlusMinus (projectNonMinus U) V)‖²
                      ∂(minusHaarMeasure L)(V)`

via `norm_sq_integral_le_integral_norm_sq` applied to the integrand
`V ↦ F(gluePlusMinus (projectNonMinus U) V)` on the probability
measure `minusHaarMeasure L`.

This is the pointwise-in-U Jensen step. The base-measure L²-contraction
`WilsonAvgMinusL2ContractionBase L` then follows by integrating this
bound over `U ∂μ_base(U)` and applying Fubini on the sector split via
`wilsonBaseMeasure_integral_split`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.JensenNormSqIntegral_2026_11_12
import PF.YangMills.WilsonMinusLinkAveraging_2026_11_12

namespace PF.YangMills

open MeasureTheory

variable {L : ℕ} [NeZero L]

/-- **Pointwise Jensen bound for `avgMinus`.** For any continuous
`F : GaugeField L → ℂ` and any `U : GaugeField L`,

  `‖avgMinus F U‖² ≤ ∫ V, ‖F (gluePlusMinus (projectNonMinus U) V)‖²
                      ∂(minusHaarMeasure L)(V)`.

Direct application of `norm_sq_integral_le_integral_norm_sq` to the
integrand `V ↦ F(gluePlusMinus (projectNonMinus U) V)`.

Measurability/integrability: continuity of `F` + continuity of
`gluePlusMinus (projectNonMinus U)` + compactness of `MinusGauge L`
gives bounded continuous integrand ⇒ integrable, and also `‖·‖²`
integrable. -/
theorem norm_sq_avgMinus_le_integral_norm_sq
    (F : GaugeField L → ℂ) (hF : Continuous F) (U : GaugeField L) :
    ‖avgMinus F U‖ ^ 2
      ≤ ∫ V, ‖F (gluePlusMinus (projectNonMinus U) V)‖ ^ 2
          ∂(minusHaarMeasure L) := by
  -- Define the integrand `h V := F(gluePlusMinus (projectNonMinus U) V)`.
  set h : MinusGauge L → ℂ := fun V =>
    F (gluePlusMinus (projectNonMinus U) V) with hdef_h
  -- Continuity of h.  Factor through `(fun V => (projectNonMinus U, V))`
  -- then compose with `gluePlusMinus` and `F`.
  have hpair_cont :
      Continuous (fun V : MinusGauge L => (projectNonMinus U, V)) :=
    continuous_const.prodMk continuous_id
  have hglue_partial_cont :
      Continuous (fun V : MinusGauge L =>
        gluePlusMinus (L := L) (projectNonMinus U) V) :=
    gluePlusMinus_continuous.comp hpair_cont
  have hh_cont : Continuous h := hF.comp hglue_partial_cont
  -- `MinusGauge L` is compact — finite product of compact `SU2`.
  -- Since `GaugeField L` is compact (via `gaugeField_compactSpace`) and
  -- `MinusGauge L` is a factor of it under the sector split, compactness
  -- transfers.  More directly: `MinusGauge L = MinusLinks L → SU2` is a
  -- `Pi` of compact spaces, hence compact.
  haveI : CompactSpace (MinusGauge L) := by
    unfold MinusGauge
    exact Pi.compactSpace
  haveI : IsProbabilityMeasure (minusHaarMeasure L) :=
    minusHaarMeasure_isProbabilityMeasure L
  -- A continuous function on a compact space is bounded.
  obtain ⟨Cmax, hCmax⟩ : ∃ C : ℝ, ∀ V, ‖h V‖ ≤ C := by
    obtain ⟨M, hM⟩ := (isCompact_range hh_cont.norm).bddAbove
    refine ⟨M, fun V => ?_⟩
    exact hM (Set.mem_range_self V)
  -- Integrability of h on the probability measure minusHaarMeasure.
  have hh_int : Integrable h (minusHaarMeasure L) := by
    refine Integrable.of_bound hh_cont.aestronglyMeasurable Cmax ?_
    filter_upwards with V
    exact hCmax V
  -- Integrability of ‖h‖².
  have hh_normsq_cont : Continuous (fun V => ‖h V‖ ^ 2) :=
    (hh_cont.norm).pow 2
  have hh_normsq_int : Integrable (fun V => ‖h V‖ ^ 2) (minusHaarMeasure L) := by
    refine Integrable.of_bound hh_normsq_cont.aestronglyMeasurable
      (Cmax ^ 2) ?_
    filter_upwards with V
    have hnV : 0 ≤ ‖h V‖ := norm_nonneg _
    have hCV : ‖h V‖ ≤ Cmax := hCmax V
    have h_nonneg : 0 ≤ Cmax := le_trans hnV hCV
    calc ‖(‖h V‖ ^ 2 : ℝ)‖
        = ‖h V‖ ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          positivity
      _ ≤ Cmax ^ 2 := pow_le_pow_left₀ hnV hCV 2
  -- `avgMinus F U = ∫ V, h V ∂minusHaarMeasure`.
  have havg_eq :
      avgMinus F U = ∫ V, h V ∂(minusHaarMeasure L) := by
    unfold avgMinus; simp [hdef_h]
  rw [havg_eq]
  -- Apply the atomic Jensen lemma.
  exact norm_sq_integral_le_integral_norm_sq (minusHaarMeasure L) h hh_int hh_normsq_int

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.norm_sq_avgMinus_le_integral_norm_sq
