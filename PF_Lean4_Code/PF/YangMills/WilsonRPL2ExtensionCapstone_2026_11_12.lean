/-
# PF.YangMills.WilsonRPL2ExtensionCapstone_2026_11_12

**CAPSTONE of the YM L² extension lane**: Wilson reflection positivity
for L² test functions, unconditional on three-axiom bar.

Delivers `wilson_reflection_positivity_of_L2_strong`: given a family
`F : Fin K → GaugeField L → ℂ` with each `F i` strongly measurable,
`MemLp 2 μ_Gibbs`, and `supportedOnPlusZero`, the θ-crossed Gram
matrix is `PosSemidef`.

This composes:
* `wilsonL2DensityHypothesisStrong_holds` — step 3 (density).
* `wilsonL2GramEntryTendsto_holds` — step 5a (Gram convergence).
* `wilson_reflection_positivity_of_continuous` (r385) — PSD for
  continuous input.
* `Matrix.PosSemidef.of_tendsto_entries` — step 4 (PSD limit).

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-13.
-/

import PF.YangMills.WilsonL2DensityHypothesis_2026_11_12
import PF.YangMills.WilsonL2GramEntryTendsto_2026_11_12

namespace PF.YangMills

open MeasureTheory Filter
open scoped Topology ComplexOrder ENNReal

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **Wilson reflection positivity for L² test functions.**

For a family `F : Fin K → GaugeField L → ℂ` of strongly-measurable,
L²-integrable, `supportedOnPlusZero` functions, the θ-crossed Gram
matrix is `PosSemidef`.

This is the full unconditional L² reflection positivity theorem.
Composes density (step 3), Gram convergence (step 5a), r385 (PSD on
continuous), and PSD entrywise-limit closure (step 4). -/
theorem wilson_reflection_positivity_of_L2_strong
    (hL : Even L) (β : ℝ)
    {K : ℕ} (F : Fin K → GaugeField L → ℂ)
    (hF_sm : ∀ i : Fin K, StronglyMeasurable (F i))
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (hF_mem : ∀ i : Fin K, MemLp (F i) 2 (wilsonGibbsMeasure L β)) :
    (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).PosSemidef := by
  -- For each `i`, pick an approximating sequence via the strong density hypothesis.
  choose F_n hF_n_cont hF_n_support hF_n_mem hF_n_tendsto using
    fun i => wilsonL2DensityHypothesisStrong_holds (L := L) β (F i)
      (hF_sm i) (hF_mem i) (hF_support i)
  -- Each M_n := Gram matrix of F_·,n is PosSemidef via r385.
  set M_n : ℕ → Matrix (Fin K) (Fin K) ℂ := fun n =>
    Matrix.of (fun i j : Fin K =>
      ∫ U, star (F_n i n (timeReflectionGaugeField U)) * F_n j n U
        ∂(wilsonGibbsMeasure L β)) with hM_n_def
  have hPSD_n : ∀ n, (M_n n).PosSemidef := by
    intro n
    exact wilson_reflection_positivity_of_continuous (hL := hL) (β := β)
      (K := K) (F := fun i => F_n i n)
      (hF_support := fun i => hF_n_support i n)
      (hF_cont := fun i => hF_n_cont i n)
  -- Gram entries converge via step 5a (wilsonL2GramEntryTendsto_holds).
  have h_entry_tendsto : ∀ i j : Fin K,
      Tendsto (fun n => M_n n i j) atTop
        (𝓝 (∫ U, star (F i (timeReflectionGaugeField U)) * F j U
              ∂(wilsonGibbsMeasure L β))) := by
    intro i j
    simpa [M_n, hM_n_def, Matrix.of_apply] using
      wilsonL2GramEntryTendsto_holds (L := L) β
        (F i) (F j) (fun n => F_n i n) (fun n => F_n j n)
        (hF_mem i) (hF_mem j) (fun n => hF_n_mem i n) (fun n => hF_n_mem j n)
        (hF_n_tendsto i) (hF_n_tendsto j)
  -- PSD closed under entrywise limit.
  exact Matrix.PosSemidef.of_tendsto_entries hPSD_n h_entry_tendsto

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilson_reflection_positivity_of_L2_strong
