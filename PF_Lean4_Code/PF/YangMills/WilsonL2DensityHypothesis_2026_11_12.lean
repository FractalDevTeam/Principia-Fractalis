/-
# PF.YangMills.WilsonL2DensityHypothesis_2026_11_12

**Step 3 of the L² extension lane** — density of continuous-with-support
in L²-with-support via Route A (pushforward through `projectNonMinus`).

Delivers `wilsonL2DensityHypothesisStrong_holds` — the strengthened
density hypothesis is live.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonL2Density_2026_11_12
import PF.YangMills.WilsonRPL2Extension_2026_11_12
import PF.YangMills.WilsonNonMinusProjection_2026_11_12
import PF.YangMills.WilsonMinusLinkAveraging_2026_11_12
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace PF.YangMills

open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology ComplexOrder ENNReal

noncomputable section

variable {L : ℕ} [NeZero L]

/-- `NonMinusGauge L` is compact — finite Pi of compact `SU2`. -/
instance nonMinusGauge_compactSpace : CompactSpace (NonMinusGauge L) := by
  unfold NonMinusGauge; exact Pi.compactSpace

/-- The projected Gibbs measure is `WeaklyRegular`. -/
instance wilsonProjectedGibbsMeasure_weaklyRegular (β : ℝ) :
    MeasureTheory.Measure.WeaklyRegular (wilsonProjectedGibbsMeasure L β) := by
  haveI : IsFiniteMeasure (wilsonProjectedGibbsMeasure L β) :=
    wilsonProjectedGibbsMeasure_isFiniteMeasure β
  infer_instance

/-- Continuous section of `projectNonMinus`: `W ↦ gluePlusMinus W 1`. -/
def wilsonSection (W : NonMinusGauge L) : GaugeField L :=
  gluePlusMinus W (1 : MinusGauge L)

theorem wilsonSection_continuous :
    Continuous (wilsonSection : NonMinusGauge L → GaugeField L) := by
  unfold wilsonSection
  exact gluePlusMinus_continuous.comp
    (Continuous.prodMk continuous_id continuous_const)

theorem wilsonSection_measurable :
    Measurable (wilsonSection : NonMinusGauge L → GaugeField L) :=
  wilsonSection_continuous.measurable

set_option linter.unusedSectionVars false in
/-- `(wilsonSection W) ℓ = W ⟨ℓ, hℓ⟩` for non-minus `ℓ`. -/
theorem wilsonSection_apply_nonMinus (W : NonMinusGauge L)
    {ℓ : LatticeLink L} (hℓ : linkSector ℓ ≠ LinkSector.minus) :
    (wilsonSection W) ℓ = W ⟨ℓ, hℓ⟩ := by
  unfold wilsonSection gluePlusMinus
  rw [dif_pos hℓ]

/-- **Measurability sub-gap for Route A.** -/
def WilsonL2DensityMeasurabilityBridge (L : ℕ) [NeZero L] (β : ℝ) : Prop :=
  ∀ F : GaugeField L → ℂ, MemLp F 2 (wilsonGibbsMeasure L β) →
    supportedOnPlusZero F →
    ∀ F' : NonMinusGauge L → ℂ, (F = F' ∘ projectNonMinus) →
    AEStronglyMeasurable F' (wilsonProjectedGibbsMeasure L β)

/-- **Strengthened density hypothesis**: additionally require
`StronglyMeasurable F`. -/
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

/-- **`1/(n+1) → 0` in `ℝ≥0∞`.** -/
private lemma ENNReal_one_div_add_one_tendsto_zero :
    Tendsto (fun n : ℕ => (1 : ℝ≥0∞) / (n + 1)) atTop (𝓝 0) := by
  have h_shift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => ?_⟩
    omega
  have h_eq : (fun n : ℕ => (1 : ℝ≥0∞) / (n + 1))
      = (fun k : ℕ => ((k : ℝ≥0∞))⁻¹) ∘ (fun n : ℕ => n + 1) := by
    funext n
    simp only [Function.comp, one_div, Nat.cast_add, Nat.cast_one]
  rw [h_eq]
  exact ENNReal.tendsto_inv_nat_nhds_zero.comp h_shift

/-- **The strengthened density hypothesis holds.** -/
theorem wilsonL2DensityHypothesisStrong_holds (β : ℝ) :
    WilsonL2DensityHypothesisStrong L β := by
  intro F hF_sm hF_memLp hF_supp
  have hF'_sm : StronglyMeasurable (F ∘ wilsonSection : NonMinusGauge L → ℂ) :=
    hF_sm.comp_measurable wilsonSection_measurable
  -- F = (F ∘ wilsonSection) ∘ projectNonMinus pointwise.
  have hF_eq : ∀ U, F U = (F ∘ wilsonSection) (projectNonMinus U) := by
    intro U
    show F U = F (wilsonSection (projectNonMinus U))
    apply hF_supp
    intro ℓ hℓ
    rw [wilsonSection_apply_nonMinus (projectNonMinus U) hℓ]
    rfl
  -- MemLp (F ∘ wilsonSection) 2 (wilsonProjectedGibbsMeasure L β).
  have h_comp_eq :
      ((F ∘ wilsonSection : NonMinusGauge L → ℂ) ∘ projectNonMinus) = F := by
    funext U; exact (hF_eq U).symm
  have hF'_memLp :
      MemLp (F ∘ wilsonSection : NonMinusGauge L → ℂ) 2
        (wilsonProjectedGibbsMeasure L β) := by
    unfold wilsonProjectedGibbsMeasure
    rw [memLp_map_measure_iff hF'_sm.aestronglyMeasurable
        projectNonMinus_measurable.aemeasurable]
    rw [h_comp_eq]
    exact hF_memLp
  -- Apply mathlib density.
  have h_density : ∀ n : ℕ, ∃ G' : NonMinusGauge L →ᵇ ℂ,
      eLpNorm ((F ∘ wilsonSection : NonMinusGauge L → ℂ) -
               (G' : NonMinusGauge L → ℂ)) 2
          (wilsonProjectedGibbsMeasure L β) ≤ (1 : ℝ≥0∞) / (n + 1) ∧
      MemLp (G' : NonMinusGauge L → ℂ) 2 (wilsonProjectedGibbsMeasure L β) := by
    intro n
    have hε_ne : (1 : ℝ≥0∞) / (n + 1) ≠ 0 := by
      refine ENNReal.div_ne_zero.mpr ⟨by norm_num, ?_⟩
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩
    exact MeasureTheory.MemLp.exists_boundedContinuous_eLpNorm_sub_le
      (p := 2) (f := (F ∘ wilsonSection : NonMinusGauge L → ℂ))
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hF'_memLp hε_ne
  choose G'_n hG'_n_le hG'_n_memLp using h_density
  refine ⟨fun n U => (G'_n n : NonMinusGauge L → ℂ) (projectNonMinus U),
          ?_, ?_, ?_, ?_⟩
  · intro n
    exact (G'_n n).continuous.comp projectNonMinus_continuous
  · intro n U₁ U₂ hU
    show (G'_n n : NonMinusGauge L → ℂ) (projectNonMinus U₁)
      = (G'_n n : NonMinusGauge L → ℂ) (projectNonMinus U₂)
    congr 1
    funext ℓ
    show U₁ ℓ.1 = U₂ ℓ.1
    exact hU ℓ.1 ℓ.2
  · intro n
    exact (hG'_n_memLp n).comp_of_map projectNonMinus_measurable.aemeasurable
  · -- eLpNorm (F - F_n) 2 μ_Gibbs → 0 via pushforward identity.
    have h_eq : ∀ n,
        eLpNorm (fun U => F U - (G'_n n : NonMinusGauge L → ℂ) (projectNonMinus U))
          2 (wilsonGibbsMeasure L β)
          = eLpNorm ((F ∘ wilsonSection : NonMinusGauge L → ℂ) -
                     (G'_n n : NonMinusGauge L → ℂ)) 2
              (wilsonProjectedGibbsMeasure L β) := by
      intro n
      have h_fn :
          (fun U => F U - (G'_n n : NonMinusGauge L → ℂ) (projectNonMinus U))
            = ((F ∘ wilsonSection : NonMinusGauge L → ℂ) -
               (G'_n n : NonMinusGauge L → ℂ)) ∘ projectNonMinus := by
        funext U
        show F U - (G'_n n : NonMinusGauge L → ℂ) (projectNonMinus U)
          = (F ∘ wilsonSection : NonMinusGauge L → ℂ) (projectNonMinus U) -
             (G'_n n : NonMinusGauge L → ℂ) (projectNonMinus U)
        rw [hF_eq U]
      rw [h_fn]
      have h_aesm : AEStronglyMeasurable
          ((F ∘ wilsonSection : NonMinusGauge L → ℂ) -
           (G'_n n : NonMinusGauge L → ℂ))
          ((wilsonGibbsMeasure L β).map projectNonMinus) :=
        hF'_sm.aestronglyMeasurable.sub
          (G'_n n).continuous.aestronglyMeasurable
      unfold wilsonProjectedGibbsMeasure
      exact (eLpNorm_map_measure h_aesm
        projectNonMinus_measurable.aemeasurable).symm
    simp_rw [h_eq]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ENNReal_one_div_add_one_tendsto_zero
      (fun n => zero_le _) (fun n => hG'_n_le n)

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonProjectedGibbsMeasure_weaklyRegular
#print axioms PF.YangMills.wilsonSection_continuous
#print axioms PF.YangMills.wilsonL2DensityHypothesisStrong_holds
