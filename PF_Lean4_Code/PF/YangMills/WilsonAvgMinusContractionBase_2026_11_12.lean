/-
# PF.YangMills.WilsonAvgMinusContractionBase_2026_11_12

**Step 3c.4c closure**: ENNReal-level pointwise Jensen for `avgMinus`.

Lifts `norm_sq_avgMinus_le_integral_norm_sq` (real-valued Jensen) to
the ENNReal/enorm level, as required by the `eLpNorm`-based
`WilsonAvgMinusL2ContractionBase` statement.

For continuous `K : GaugeField L → ℂ` and any `W : NonMinusGauge L`,
any `V₀ : MinusGauge L`,

  `‖avgMinus K (gluePlusMinus W V₀)‖ₑ ^ 2
      ≤ ∫⁻ V, ‖K (gluePlusMinus W V)‖ₑ ^ 2 ∂(minusHaarMeasure L)`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonAvgMinusLinearity_2026_11_12
import PF.YangMills.WilsonAvgMinusPointwiseJensen_2026_11_12

namespace PF.YangMills

open MeasureTheory ENNReal

variable {L : ℕ} [NeZero L]

/-- Helper: for a real `r ≥ 0`, `ENNReal.ofReal (r^2) = (ENNReal.ofReal r)^2`. -/
private lemma ofReal_sq (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (r ^ 2) = (ENNReal.ofReal r) ^ 2 := by
  rw [show (r ^ 2 : ℝ) = r * r from by ring, ENNReal.ofReal_mul hr]
  ring

/-- **ENNReal pointwise Jensen for `avgMinus` at `glue W V₀`.** -/
theorem enorm_sq_avgMinus_at_glue_le
    (K : GaugeField L → ℂ) (hK : Continuous K)
    (W : NonMinusGauge L) (V₀ : MinusGauge L) :
    (‖avgMinus K (gluePlusMinus W V₀)‖ₑ : ℝ≥0∞) ^ 2
      ≤ ∫⁻ V, (‖K (gluePlusMinus W V)‖ₑ : ℝ≥0∞) ^ 2
          ∂(minusHaarMeasure L) := by
  -- Rewrite avgMinus at the glue as the integral directly.
  rw [avgMinus_gluePlusMinus]
  -- Target: ‖∫ V, K(glue W V) dμ_minus‖ₑ² ≤ ∫⁻ V, ‖K(glue W V)‖ₑ² dμ_minus.
  -- Compactness + probability measure setup.
  haveI : CompactSpace (MinusGauge L) := by unfold MinusGauge; exact Pi.compactSpace
  haveI : IsProbabilityMeasure (minusHaarMeasure L) :=
    minusHaarMeasure_isProbabilityMeasure L
  -- Continuity + integrability of the glued function.
  have hpair_cont :
      Continuous (fun V : MinusGauge L => (W, V)) :=
    continuous_const.prodMk continuous_id
  have hglue_W_cont :
      Continuous (fun V : MinusGauge L => gluePlusMinus W V) :=
    gluePlusMinus_continuous.comp hpair_cont
  have hK_glue_cont : Continuous (fun V => K (gluePlusMinus W V)) :=
    hK.comp hglue_W_cont
  have hnorm_sq_cont : Continuous (fun V => ‖K (gluePlusMinus W V)‖ ^ 2) :=
    hK_glue_cont.norm.pow 2
  -- Compact-+ bound
  obtain ⟨Cmax, hCmax⟩ : ∃ C : ℝ, ∀ V, ‖K (gluePlusMinus W V)‖ ≤ C := by
    obtain ⟨M, hM⟩ := (isCompact_range hK_glue_cont.norm).bddAbove
    exact ⟨M, fun V => hM (Set.mem_range_self V)⟩
  have hK_glue_int : Integrable (fun V => K (gluePlusMinus W V))
      (minusHaarMeasure L) := by
    refine Integrable.of_bound hK_glue_cont.aestronglyMeasurable Cmax ?_
    filter_upwards with V; exact hCmax V
  have hK_sq_int : Integrable (fun V => ‖K (gluePlusMinus W V)‖ ^ 2)
      (minusHaarMeasure L) := by
    refine Integrable.of_bound hnorm_sq_cont.aestronglyMeasurable
      (Cmax ^ 2) ?_
    filter_upwards with V
    have hnV : 0 ≤ ‖K (gluePlusMinus W V)‖ := norm_nonneg _
    have hCV : ‖K (gluePlusMinus W V)‖ ≤ Cmax := hCmax V
    calc ‖(‖K (gluePlusMinus W V)‖ ^ 2 : ℝ)‖
        = ‖K (gluePlusMinus W V)‖ ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg]; positivity
      _ ≤ Cmax ^ 2 := pow_le_pow_left₀ hnV hCV 2
  -- Apply the atomic Jensen.
  have hJ : ‖∫ V, K (gluePlusMinus W V) ∂(minusHaarMeasure L)‖ ^ 2
          ≤ ∫ V, ‖K (gluePlusMinus W V)‖ ^ 2 ∂(minusHaarMeasure L) :=
    norm_sq_integral_le_integral_norm_sq (minusHaarMeasure L)
      (fun V => K (gluePlusMinus W V)) hK_glue_int hK_sq_int
  -- Lift to ENNReal.
  have h_LHS_real_nn :
      (0 : ℝ) ≤ ‖∫ V, K (gluePlusMinus W V) ∂(minusHaarMeasure L)‖ := norm_nonneg _
  have h_norm_nn : ∀ V, (0 : ℝ) ≤ ‖K (gluePlusMinus W V)‖ :=
    fun V => norm_nonneg _
  have hJ_enn :
      ENNReal.ofReal (‖∫ V, K (gluePlusMinus W V) ∂(minusHaarMeasure L)‖ ^ 2)
        ≤ ENNReal.ofReal
            (∫ V, ‖K (gluePlusMinus W V)‖ ^ 2 ∂(minusHaarMeasure L)) :=
    ENNReal.ofReal_le_ofReal hJ
  -- LHS: ENNReal.ofReal (‖·‖^2) = (‖·‖ₑ)^2.
  have h_LHS_eq :
      ENNReal.ofReal (‖∫ V, K (gluePlusMinus W V) ∂(minusHaarMeasure L)‖ ^ 2)
        = (‖∫ V, K (gluePlusMinus W V) ∂(minusHaarMeasure L)‖ₑ : ℝ≥0∞) ^ 2 := by
    rw [ofReal_sq _ h_LHS_real_nn, ofReal_norm_eq_enorm]
  -- RHS: ENNReal.ofReal (∫‖·‖²) = ∫⁻ ENNReal.ofReal(‖·‖²) = ∫⁻ (‖·‖ₑ)².
  have h_RHS_eq :
      ENNReal.ofReal
          (∫ V, ‖K (gluePlusMinus W V)‖ ^ 2 ∂(minusHaarMeasure L))
        = ∫⁻ V, (‖K (gluePlusMinus W V)‖ₑ : ℝ≥0∞) ^ 2
            ∂(minusHaarMeasure L) := by
    rw [ofReal_integral_eq_lintegral_ofReal hK_sq_int
        (Filter.Eventually.of_forall (fun V => by positivity))]
    refine lintegral_congr fun V => ?_
    rw [ofReal_sq _ (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [← h_LHS_eq, ← h_RHS_eq]
  exact hJ_enn

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.enorm_sq_avgMinus_at_glue_le
