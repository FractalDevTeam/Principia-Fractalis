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

import PF.YangMills.WilsonAvgMinusL2Composition_2026_11_12
import PF.YangMills.WilsonAvgMinusLinearity_2026_11_12
import PF.YangMills.WilsonAvgMinusPointwiseJensen_2026_11_12
import PF.YangMills.WilsonBaseFubiniCollapse_2026_11_12

namespace PF.YangMills

open MeasureTheory ENNReal

variable {L : ℕ} [NeZero L]

/-- Helper: for a real `r ≥ 0`, `ENNReal.ofReal (r^2) = (ENNReal.ofReal r)^(2:ℝ)`. -/
private lemma ofReal_sq (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (r ^ 2) = (ENNReal.ofReal r) ^ (2 : ℝ) := by
  rw [show (r ^ 2 : ℝ) = r * r from by ring, ENNReal.ofReal_mul hr,
      ENNReal.rpow_two, sq]

/-- **ENNReal pointwise Jensen for `avgMinus` at `glue W V₀`.** -/
theorem enorm_sq_avgMinus_at_glue_le
    (K : GaugeField L → ℂ) (hK : Continuous K)
    (W : NonMinusGauge L) (V₀ : MinusGauge L) :
    (‖avgMinus K (gluePlusMinus W V₀)‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
      ≤ ∫⁻ V, (‖K (gluePlusMinus W V)‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
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
  -- LHS: ENNReal.ofReal (‖·‖^2) = (‖·‖ₑ)^(2:ℝ).
  have h_LHS_eq :
      ENNReal.ofReal (‖∫ V, K (gluePlusMinus W V) ∂(minusHaarMeasure L)‖ ^ 2)
        = (‖∫ V, K (gluePlusMinus W V) ∂(minusHaarMeasure L)‖ₑ : ℝ≥0∞)
            ^ (2 : ℝ) := by
    rw [ofReal_sq _ h_LHS_real_nn, ofReal_norm_eq_enorm]
  -- RHS: ENNReal.ofReal (∫‖·‖²) = ∫⁻ ENNReal.ofReal(‖·‖²) = ∫⁻ (‖·‖ₑ)^(2:ℝ).
  have h_RHS_eq :
      ENNReal.ofReal
          (∫ V, ‖K (gluePlusMinus W V)‖ ^ 2 ∂(minusHaarMeasure L))
        = ∫⁻ V, (‖K (gluePlusMinus W V)‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
            ∂(minusHaarMeasure L) := by
    rw [ofReal_integral_eq_lintegral_ofReal hK_sq_int
        (Filter.Eventually.of_forall (fun V => by positivity))]
    refine lintegral_congr fun V => ?_
    rw [ofReal_sq _ (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [← h_LHS_eq, ← h_RHS_eq]
  exact hJ_enn

/-! ## §Final composition — close `WilsonAvgMinusL2ContractionBase L`. -/

open BoundedContinuousFunction

/-- **`WilsonAvgMinusL2ContractionBase L` holds.**  Composition of:
* `avgMinus_sub` — linearity.
* `wilsonBaseMeasure_lintegral_collapse_projectNonMinus` — outer collapse.
* `enorm_sq_avgMinus_at_glue_le` — ENNReal pointwise Jensen.
* `wilsonBaseMeasure_lintegral_reassemble_glue` — Fubini reassemble.
* `eLpNorm_eq_lintegral_rpow_enorm` — eLpNorm↔lintegral bridge. -/
theorem wilsonAvgMinusL2ContractionBase_holds :
    WilsonAvgMinusL2ContractionBase L := by
  intro G H
  -- Set K := G - H, continuous.
  set K : GaugeField L → ℂ := fun U => (G : GaugeField L → ℂ) U -
                                        (H : GaugeField L → ℂ) U with hK_def
  have hK_cont : Continuous K := G.continuous.sub H.continuous
  -- Rewrite LHS using avgMinus_sub.
  have hLHS_integrand_eq :
      (fun U => avgMinus (G : GaugeField L → ℂ) U -
                avgMinus (H : GaugeField L → ℂ) U)
        = fun U => avgMinus K U := by
    funext U
    exact (avgMinus_sub G H G.continuous H.continuous U).symm
  rw [hLHS_integrand_eq]
  -- Reduce eLpNorm to the lintegral of enorm².
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_toReal : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top, h_toReal]
  -- Suffices: ∫⁻ U, ‖avgMinus K U‖ₑ² ∂μ_base ≤ ∫⁻ U, ‖K U‖ₑ² ∂μ_base.
  refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  -- Pick an arbitrary V₀ to collapse avgMinus through.
  classical
  -- `MinusGauge L` is nonempty (it's a Pi of SU2, which is nonempty).
  haveI : Nonempty (MinusGauge L) := by
    exact ⟨fun _ => 1⟩
  obtain ⟨V₀⟩ : Nonempty (MinusGauge L) := inferInstance
  -- LHS factors through projectNonMinus via avgMinus_gluePlusMinus.
  have h_LHS_collapse :
      ∫⁻ U, (‖avgMinus K U‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(wilsonBaseMeasure L)
        = ∫⁻ W, (‖avgMinus K (gluePlusMinus W V₀)‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
            ∂(nonMinusHaarMeasure L) := by
    -- First: avgMinus K U depends only on projectNonMinus U; identify with lifted h.
    set h : NonMinusGauge L → ℝ≥0∞ :=
      fun W => (‖avgMinus K (gluePlusMinus W V₀)‖ₑ : ℝ≥0∞) ^ (2 : ℝ) with hdef_h
    have h_meas : Measurable h := by
      have hav_cont : Continuous (fun W : NonMinusGauge L =>
          avgMinus K (gluePlusMinus W V₀)) := by
        -- avgMinus_gluePlusMinus shows this equals ∫ V, K(glue W V) dμ_minus.
        -- Continuity: parametric integral on compact.
        -- Cleaner: use avgMinus_continuous composed with glue.
        -- But avgMinus_continuous takes BoundedContinuousFunction, not raw.
        -- Fall back: `W ↦ gluePlusMinus W V₀` is continuous, and
        -- `avgMinus K ∘ ·` depends continuously (parametric integral).
        -- Easier: use avgMinus K U = avgMinus K (glue (proj U) V₀) via collapse.
        -- Replace with a direct parametric integral continuity.
        have : Continuous (fun W : NonMinusGauge L =>
            ∫ V, K (gluePlusMinus W V) ∂(minusHaarMeasure L)) := by
          -- Dominated convergence or continuity under integral.
          -- Use `continuous_of_dominated` or similar; or lift from
          -- `avgMinus_continuous` on the BoundedContinuousFunction K.
          -- For a direct proof: use continuity of `(W, V) ↦ K(glue W V)`
          -- jointly + compactness of V-domain + bounded.
          -- Mathlib: `continuous_of_integral_locallyBoundedContinuous`
          -- or `MeasureTheory.continuous_integral_of_dominated`.
          -- Simpler: use `BoundedContinuousFunction` structure.
          -- Since G, H are BoundedContinuousFunction, `K` factors through.
          -- Use: continuous parametric integral for jointly continuous+bounded.
          refine MeasureTheory.continuous_of_dominated
            (F := fun W V => K (gluePlusMinus W V))
            (bound := fun _ =>
              ‖(G : BoundedContinuousFunction (GaugeField L) ℂ)‖ +
              ‖(H : BoundedContinuousFunction (GaugeField L) ℂ)‖)
            ?_ ?_ ?_ ?_
          · intro W; exact (hK_cont.comp
              (gluePlusMinus_continuous.comp
                (continuous_const.prodMk continuous_id))
              ).aestronglyMeasurable
          · intro W
            filter_upwards with V
            calc ‖K (gluePlusMinus W V)‖
                = ‖(G : GaugeField L → ℂ) (gluePlusMinus W V) -
                    (H : GaugeField L → ℂ) (gluePlusMinus W V)‖ := rfl
              _ ≤ ‖(G : GaugeField L → ℂ) (gluePlusMinus W V)‖ +
                  ‖(H : GaugeField L → ℂ) (gluePlusMinus W V)‖ :=
                  norm_sub_le _ _
              _ ≤ ‖(G : BoundedContinuousFunction (GaugeField L) ℂ)‖ +
                  ‖(H : BoundedContinuousFunction (GaugeField L) ℂ)‖ := by
                  gcongr
                  · exact G.norm_coe_le_norm _
                  · exact H.norm_coe_le_norm _
          · exact integrable_const _
          · filter_upwards with V
            exact hK_cont.comp
              (gluePlusMinus_continuous.comp
                (continuous_id.prodMk continuous_const))
        -- Rewrite avgMinus K = integral form via avgMinus_gluePlusMinus.
        have h_pt : ∀ W : NonMinusGauge L,
            avgMinus K (gluePlusMinus W V₀)
              = ∫ V, K (gluePlusMinus W V) ∂(minusHaarMeasure L) := by
          intro W; exact avgMinus_gluePlusMinus K W V₀
        simpa [h_pt] using this
      -- Measurability of h = fun W => ‖avgMinus K (glue W V₀)‖ₑ ^ (2:ℝ).
      show Measurable (fun W => (‖avgMinus K (gluePlusMinus W V₀)‖ₑ : ℝ≥0∞)
        ^ (2 : ℝ))
      exact ENNReal.continuous_rpow_const.measurable.comp hav_cont.enorm.measurable
    -- Now use the collapse identity.
    -- Verify `avgMinus K U = avgMinus K (gluePlusMinus (projectNonMinus U) V₀)`.
    have h_collapse_integrand :
        (fun U => (‖avgMinus K U‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = fun U => h (projectNonMinus U) := by
      funext U
      simp only [hdef_h]
      congr 1
      -- avgMinus K U = avgMinus K (gluePlusMinus (projectNonMinus U) V₀)
      -- Both equal ∫ V, K(glue (proj U) V) dμ_minus.
      unfold avgMinus
      rw [projectNonMinus_gluePlusMinus]
    rw [h_collapse_integrand]
    exact wilsonBaseMeasure_lintegral_collapse_projectNonMinus h h_meas
  -- Apply pointwise ENNReal Jensen.
  have h_pointwise : ∀ W : NonMinusGauge L,
      (‖avgMinus K (gluePlusMinus W V₀)‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
        ≤ ∫⁻ V, (‖K (gluePlusMinus W V)‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
            ∂(minusHaarMeasure L) := by
    intro W
    exact enorm_sq_avgMinus_at_glue_le K hK_cont W V₀
  -- Combine: LHS ≤ ∫⁻ W, ∫⁻ V, ‖K(glue W V)‖ₑ² dμ_minus dμ_nonMinus.
  rw [h_LHS_collapse]
  have h_step :
      ∫⁻ W, (‖avgMinus K (gluePlusMinus W V₀)‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          ∂(nonMinusHaarMeasure L)
        ≤ ∫⁻ W, ∫⁻ V, (‖K (gluePlusMinus W V)‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
            ∂(minusHaarMeasure L) ∂(nonMinusHaarMeasure L) :=
    lintegral_mono h_pointwise
  refine h_step.trans ?_
  -- Reassemble: ∫⁻ W, ∫⁻ V, ‖K(glue W V)‖ₑ² = ∫⁻ U, ‖K U‖ₑ².
  have h_K_enorm_sq_meas :
      Measurable (fun U : GaugeField L =>
        (‖K U‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) := by
    refine ENNReal.continuous_rpow_const.measurable.comp ?_
    exact hK_cont.measurable.enorm
  have hReassemble := wilsonBaseMeasure_lintegral_reassemble_glue
    (fun U => (‖K U‖ₑ : ℝ≥0∞) ^ (2 : ℝ)) h_K_enorm_sq_meas
  exact hReassemble.le

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.enorm_sq_avgMinus_at_glue_le
#print axioms PF.YangMills.wilsonAvgMinusL2ContractionBase_holds
