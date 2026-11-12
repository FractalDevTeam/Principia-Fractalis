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

## Proof outline — pushforward-through-projection approach

The cleanest proof uses the fact that `LatticeLink L` partitions into
`minusLinks` (where `linkSector = .minus`) and `nonMinusLinks` (where
`linkSector ≠ .minus`).  Define:

* `nonMinusGauge L := NonMinusLinks L → SU2`,
* `projectNonMinus : GaugeField L → nonMinusGauge L` (natural projection
  by domain restriction).
* `ν := (μ_Gibbs).map projectNonMinus` (pushforward measure on
  `nonMinusGauge L`).

**Key observation.** `supportedOnPlusZero F` is exactly the statement
that `F` **factors through** `projectNonMinus`: there exists
`F_restricted : nonMinusGauge L → ℂ` with `F = F_restricted ∘ projectNonMinus`.

Under this factoring:

1. `MemLp F 2 μ_Gibbs ↔ MemLp F_restricted 2 ν`
2. `L²(μ_Gibbs)` norms on `F` match `L²(ν)` norms on `F_restricted` (by
   the change-of-variable formula for pushforward).
3. On `nonMinusGauge L` — a finite product of compact Lie groups, hence
   Polish — `ν` is a finite measure and so weakly regular.

Apply mathlib's `MemLp.exists_boundedContinuous_eLpNorm_sub_le` to
`F_restricted` with measure `ν`: get `G'_n : nonMinusGauge L → ℂ`
bounded-continuous with `eLpNorm (F_restricted - G'_n) 2 ν → 0`.

**Lift back.** Define `F_n := G'_n ∘ projectNonMinus`. Then:
* `F_n` is continuous (composition).
* `F_n` is `supportedOnPlusZero` by construction
  (`projectNonMinus U = projectNonMinus U'` whenever `U, U'` agree on
  non-minus links, which is exactly `supportedOnPlusZero`).
* `eLpNorm (F - F_n) 2 μ_Gibbs = eLpNorm (F_restricted - G'_n) 2 ν → 0`.

## Lean-side cost

Estimated 80–150 Lean lines across 3 ingredients:
1. Define `NonMinusLinks`, `nonMinusGauge`, `projectNonMinus` and prove
   measurability and continuity.  (~30 lines)
2. `supportedOnPlusZero F ↔ ∃ F', F = F' ∘ projectNonMinus`. (~25 lines)
3. The L²-norm pushforward identity + mathlib density composition. (~40
   lines, incl. the `WeaklyRegular` inferencing on `ν`.)

Pending a dedicated session. -/
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

## Proof outline

The proof is a standard ε/2 argument with ENNReal-Real bridging. Explicit
steps:

1. **Convert the `eLpNorm` Tendsto hypotheses to real form.**  For each
   `MemLp f 2 μ`, `(eLpNorm f 2 μ).toReal = (∫ ‖f‖² ∂μ)^(1/2)` via
   `eLpNorm_eq_integral_rpow_norm` (with `p = 2`).  Compose with
   `ENNReal.tendsto_toReal` applied at `0` (which is ≠ ∞) to get
   `Tendsto (fun n => (∫ ‖F - F_n n‖² ∂μ)^(1/2)) atTop (𝓝 0)` in ℝ.

2. **Algebraic split.**  Write `star(F_n(θU)) * G_n U - star(F(θU)) * G U`
   as `star((F_n - F)(θU)) * G_n U + star(F(θU)) * (G_n - G) U` and
   apply `integral_add` (both summands integrable via `MemLp.integrable_mul`
   + `MemLp.comp_measurePreserving` on the `F ∘ θ` side).

3. **Bound each summand via `wilson_rp_gram_bound`.**
   - `‖∫ star((F_n - F)(θU)) * G_n U‖ ≤ ‖F_n - F‖_{L²} · ‖G_n‖_{L²}`.
   - `‖∫ star(F(θU)) * (G_n - G) U‖ ≤ ‖F‖_{L²} · ‖G_n - G‖_{L²}`.

4. **Bound `‖G_n‖_{L²}` eventually.**  Triangle: `‖G_n‖ ≤ ‖G‖ + ‖G_n - G‖`.
   Since `‖G_n - G‖ → 0`, eventually `‖G_n‖ ≤ ‖G‖ + 1`.  So there's a
   global bound `M = ‖G‖ + 1` on `‖G_n‖` for all large `n`.

5. **ε/2 argument.**  Given ε > 0, pick `N` so large that for `n ≥ N`:
   - `‖F_n - F‖_{L²} · M < ε / 2`
   - `‖F‖_{L²} · ‖G_n - G‖_{L²} < ε / 2`
   - Triangle: `‖∫ ... - ∫ ...‖ < ε`.

Estimated full proof size: 80–120 Lean lines, dominated by the
`eLpNorm`–integral bridge in step 1 and the integrability bookkeeping
in step 2.  Named here so that `wilson_reflection_positivity_of_L2`
can cite it.  Build-committed as a hypothesis pending a focused
dedicated session. -/
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
