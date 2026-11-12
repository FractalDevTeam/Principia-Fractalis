/-
# PF.YangMills.WilsonRPL2Extension_2026_11_12

**Step 5 of the YM L²-extension plan (scoping)** — the assembly statement
and its two remaining ingredients.

After steps 1 (`wilson_rp_gram_bound`, Cauchy–Schwarz bound), 2
(`wilsonGibbsMeasure_measurePreserving_timeReflection`, θ-invariance),
and 4 (`Matrix.PosSemidef.of_tendsto_entries`, entrywise-limit closure)
landed on 2026-11-11, the final assembly rests on **two** still-open
ingredients:

* **Step 3 (`WilsonL2DensityHypothesis`)** — for every `MemLp 2 ∧
  supportedOnPlusZero` function, there is a sequence of continuous
  `supportedOnPlusZero` functions converging in `L²`.

* **Step 5a (`gram_entry_tendsto_of_L2_tendsto`)** — bilinear
  convergence: if `F_n → F` and `G_n → G` in `L²(μ_Gibbs)`, then
  `∫ star(F_n(θU)) · G_n(U) dμ_Gibbs → ∫ star(F(θU)) · G(U) dμ_Gibbs`.

This file defines `WilsonL2DensityHypothesis` and states the target
theorem.  Its full proof (the ε/2 argument on Gram entries) will land
once step 5a is a named lemma.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonRPGramBound_2026_11_11
import PF.YangMills.MatrixPosSemidefLimit_2026_11_11
import PF.YangMills.WilsonFubiniClosed_r385

namespace PF.YangMills

open MeasureTheory Filter
open scoped Topology ComplexOrder

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **Density of continuous-with-support in `L²`-with-support**, as a
hypothesis.  Each `MemLp 2 ∧ supportedOnPlusZero` function admits a
sequence of continuous `supportedOnPlusZero` approximants converging in
`L²(μ_Gibbs)`.

This is step 3 of the L² extension plan.  See
`codex/YM_L2_EXTENSION_SCOPING_2026-11-11.md` for the approach to
proving it (conditional expectation / minus-link averaging). -/
def WilsonL2DensityHypothesis (L : ℕ) [NeZero L] (β : ℝ) : Prop :=
  ∀ F : GaugeField L → ℂ,
    MemLp F 2 (wilsonGibbsMeasure L β) → supportedOnPlusZero F →
    ∃ F_n : ℕ → GaugeField L → ℂ,
      (∀ n, Continuous (F_n n)) ∧
      (∀ n, supportedOnPlusZero (F_n n)) ∧
      (∀ n, MemLp (F_n n) 2 (wilsonGibbsMeasure L β)) ∧
      Tendsto (fun n =>
        eLpNorm (fun U => F U - F_n n U) 2 (wilsonGibbsMeasure L β))
        atTop (𝓝 0)

/-- **Bilinear convergence of Gram entries under `L²` convergence of
test functions** — a named placeholder for step 5a.

Given two pairs `(F, F_n)` and `(G, G_n)` with `F_n → F` and
`G_n → G` in `L²(μ_Gibbs)`, the Gram entry

   `∫ star(F_n n (θU)) * G_n n U ∂μ_Gibbs`

converges to `∫ star(F (θU)) * G U ∂μ_Gibbs`.

The proof is a standard ε/2 argument: split `⟨F_n, G_n⟩ - ⟨F, G⟩` as
`⟨F_n - F, G_n⟩ + ⟨F, G_n - G⟩`, apply `wilson_rp_gram_bound` (step 1)
to each term, use boundedness of `‖G_n‖` (eventually) via the triangle
inequality, and conclude.

Estimated proof size: 50–80 Lean lines.  Named here so that
`wilson_reflection_positivity_of_L2` can cite it. -/
def WilsonL2GramEntryTendsto (L : ℕ) [NeZero L] (β : ℝ) : Prop :=
  ∀ (F G : GaugeField L → ℂ) (F_n G_n : ℕ → GaugeField L → ℂ),
    MemLp F 2 (wilsonGibbsMeasure L β) →
    MemLp G 2 (wilsonGibbsMeasure L β) →
    (∀ n, MemLp (F_n n) 2 (wilsonGibbsMeasure L β)) →
    (∀ n, MemLp (G_n n) 2 (wilsonGibbsMeasure L β)) →
    Tendsto (fun n =>
      eLpNorm (fun U => F U - F_n n U) 2 (wilsonGibbsMeasure L β))
      atTop (𝓝 0) →
    Tendsto (fun n =>
      eLpNorm (fun U => G U - G_n n U) 2 (wilsonGibbsMeasure L β))
      atTop (𝓝 0) →
    Tendsto (fun n =>
      ∫ U, star (F_n n (timeReflectionGaugeField U)) * G_n n U
        ∂(wilsonGibbsMeasure L β)) atTop
      (𝓝 (∫ U, star (F (timeReflectionGaugeField U)) * G U
        ∂(wilsonGibbsMeasure L β)))

/-- **Wilson reflection positivity extended to `L²` test functions,
conditional on `WilsonL2DensityHypothesis` + `WilsonL2GramEntryTendsto`.**

Given `F : Fin K → GaugeField L → ℂ` with each `F i` in `L²(μ_Gibbs)`
and `supportedOnPlusZero`, the θ-crossed Gram matrix is `PosSemidef`.

The two hypotheses encapsulate the one open mathlib-interaction (density
of continuous-with-support in L²-with-support, step 3) and one bounded
proof-engineering task (bilinear convergence of Gram entries, step 5a).
Both are scoped with concrete proof sketches in the codex. -/
theorem wilson_reflection_positivity_of_L2
    (hL : Even L) (β : ℝ)
    (h_density : WilsonL2DensityHypothesis L β)
    (h_gram_tendsto : WilsonL2GramEntryTendsto L β)
    {K : ℕ} (F : Fin K → GaugeField L → ℂ)
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (hF_mem : ∀ i : Fin K, MemLp (F i) 2 (wilsonGibbsMeasure L β)) :
    (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).PosSemidef := by
  -- For each `i`, pick an approximating sequence by the density hypothesis.
  choose F_n hF_n_cont hF_n_support hF_n_mem hF_n_tendsto using
    fun i => h_density (F i) (hF_mem i) (hF_support i)
  -- Set up the K×K Gram matrix sequence `M_n` and its limit `M`.
  set M_n : ℕ → Matrix (Fin K) (Fin K) ℂ := fun n =>
    Matrix.of (fun i j : Fin K =>
      ∫ U, star (F_n i n (timeReflectionGaugeField U)) * F_n j n U
        ∂(wilsonGibbsMeasure L β)) with hM_n_def
  -- Each `M_n` is PosSemidef by r385.
  have hPSD_n : ∀ n, (M_n n).PosSemidef := by
    intro n
    exact wilson_reflection_positivity_of_continuous (hL := hL) (β := β)
      (K := K) (F := fun i => F_n i n)
      (hF_support := fun i => hF_n_support i n)
      (hF_cont := fun i => hF_n_cont i n)
  -- The Gram entries converge entrywise by the bilinear-convergence hypothesis.
  have h_entry_tendsto : ∀ i j : Fin K,
      Tendsto (fun n => M_n n i j) atTop
        (𝓝 (∫ U, star (F i (timeReflectionGaugeField U)) * F j U
              ∂(wilsonGibbsMeasure L β))) := by
    intro i j
    simpa [M_n, hM_n_def, Matrix.of_apply] using
      h_gram_tendsto (F i) (F j) (fun n => F_n i n) (fun n => F_n j n)
        (hF_mem i) (hF_mem j) (fun n => hF_n_mem i n) (fun n => hF_n_mem j n)
        (hF_n_tendsto i) (hF_n_tendsto j)
  -- PSD closed under entrywise limit (step 4).
  exact Matrix.PosSemidef.of_tendsto_entries hPSD_n h_entry_tendsto

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.WilsonL2DensityHypothesis
#print axioms PF.YangMills.WilsonL2GramEntryTendsto
#print axioms PF.YangMills.wilson_reflection_positivity_of_L2
