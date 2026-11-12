/-
# PF.YangMills.WilsonAvgMinusL2Composition_2026_11_12

**Step 3c.4c composition**: derive `WilsonAvgMinusL2Bound L β` from
(a) the exp(-βS) sandwich `m ≤ exp(-βS) ≤ M` (supplied by
`WilsonActionTotalBounds_2026_11_12`), (b) the measure-level comparison
`μ_Gibbs ↔ μ_base` (supplied by `WilsonMuGibbsMuBaseELpNorm_2026_11_12`),
and (c) the L²-contraction of `avgMinus` on the *base* measure (the
only remaining gap — the conditional-expectation Jensen bound on the
product measure).

The composition chain:

    eLpNorm (avgMinus G - avgMinus H) 2 μ_Gibbs
      ≤ √M · eLpNorm (avgMinus G - avgMinus H) 2 μ_base    [μ_Gibbs ≤ M·μ_base]
      ≤ √M · 1 · eLpNorm (G - H) 2 μ_base                   [Jensen contraction]
      ≤ √M · √(1/m) · eLpNorm (G - H) 2 μ_Gibbs             [μ_base ≤ (1/m)·μ_Gibbs]
      = √(M/m) · eLpNorm (G - H) 2 μ_Gibbs

yielding `C = √(M/m)`.

The remaining gap — `WilsonAvgMinusL2ContractionBase` — is stated here
as a named hypothesis. It is the standard Jensen bound for the inner
minus-link integral on the product base measure μ_{nonminus} ⊗ μ_minus,
i.e., a conditional-expectation L² contraction. Discharging it is
bounded-session work on top of the existing Fubini/product-measure
infrastructure (`wilsonBase_measurePreserving_split`, etc.).

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonMuGibbsMuBaseELpNorm_2026_11_12
import PF.YangMills.WilsonMinusLinkAveraging_2026_11_12

namespace PF.YangMills

open MeasureTheory ENNReal BoundedContinuousFunction

variable {L : ℕ} [NeZero L]

/-- **The L²-contraction of `avgMinus` on the base (product Haar)
measure**, stated as a named hypothesis.

This is the standard Jensen bound: `avgMinus` is a conditional
expectation on the product base measure, so by Jensen it is an L²
contraction. Formally:

  `eLpNorm (avgMinus G - avgMinus H) 2 μ_base ≤ eLpNorm (G - H) 2 μ_base`

Discharging it uses the Fubini product-measure factoring
`μ_base = μ_{nonminus} ⊗ μ_minus` (via `wilsonBase_measurePreserving_split`)
together with Jensen's inequality for the inner integral over the minus
links. Bounded-session work. -/
def WilsonAvgMinusL2ContractionBase (L : ℕ) [NeZero L] : Prop :=
  ∀ G H : BoundedContinuousFunction (GaugeField L) ℂ,
    eLpNorm (fun U => avgMinus (G : GaugeField L → ℂ) U -
                      avgMinus (H : GaugeField L → ℂ) U) 2
      (wilsonBaseMeasure L)
      ≤ eLpNorm (fun U => (G : GaugeField L → ℂ) U -
                           (H : GaugeField L → ℂ) U) 2
          (wilsonBaseMeasure L)

/-- **The composition theorem.** Given the base-measure L²-contraction
hypothesis and the sandwich `m ≤ exp(-βS) ≤ M`, `WilsonAvgMinusL2Bound`
holds with constant `C = √(M/m)`.

The proof chain uses:
* `wilsonGibbs_eLpNorm_two_le_const_mul_base` — μ_Gibbs ≤ √M · μ_base.
* The base-measure Jensen contraction hypothesis.
* `wilsonBase_eLpNorm_two_le_const_mul_gibbs` — μ_base ≤ √(1/m) · μ_Gibbs.

Only step 2 of the three is a true gap; the other two are fully proved
in this session. -/
theorem wilsonAvgMinusL2Bound_of_base_contraction
    (β : ℝ) (M m : ℝ) (hM_nonneg : 0 ≤ M) (hm_pos : 0 < m)
    (hM : ∀ U : GaugeField L, Real.exp (-β * wilsonActionTotal U) ≤ M)
    (hm : ∀ U : GaugeField L, m ≤ Real.exp (-β * wilsonActionTotal U))
    (hBase : WilsonAvgMinusL2ContractionBase L) :
    WilsonAvgMinusL2Bound L β := by
  refine ⟨Real.sqrt M * Real.sqrt (1 / m),
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  intro G H
  -- Both `avgMinus G` and `avgMinus H` are continuous (step 3c.4a
  -- `avgMinus_continuous`), so their difference is continuous.
  have hG_cont : Continuous (avgMinus (G : GaugeField L → ℂ)) :=
    avgMinus_continuous G
  have hH_cont : Continuous (avgMinus (H : GaugeField L → ℂ)) :=
    avgMinus_continuous H
  have hDiffAvg_cont :
      Continuous (fun U => avgMinus (G : GaugeField L → ℂ) U -
                           avgMinus (H : GaugeField L → ℂ) U) :=
    hG_cont.sub hH_cont
  have hDiff_cont :
      Continuous (fun U : GaugeField L =>
        (G : GaugeField L → ℂ) U - (H : GaugeField L → ℂ) U) :=
    G.continuous.sub H.continuous
  -- Step A: μ_Gibbs bound by √M · μ_base for `avgMinus G - avgMinus H`.
  have hA :
      eLpNorm (fun U => avgMinus (G : GaugeField L → ℂ) U -
                        avgMinus (H : GaugeField L → ℂ) U) 2
          (wilsonGibbsMeasure L β)
        ≤ ENNReal.ofReal (Real.sqrt M) *
          eLpNorm (fun U => avgMinus (G : GaugeField L → ℂ) U -
                             avgMinus (H : GaugeField L → ℂ) U) 2
            (wilsonBaseMeasure L) :=
    wilsonGibbs_eLpNorm_two_le_const_mul_base β M hM_nonneg hM _ hDiffAvg_cont
  -- Step B: base-measure Jensen contraction (hypothesis).
  have hB :
      eLpNorm (fun U => avgMinus (G : GaugeField L → ℂ) U -
                        avgMinus (H : GaugeField L → ℂ) U) 2
          (wilsonBaseMeasure L)
        ≤ eLpNorm (fun U => (G : GaugeField L → ℂ) U -
                             (H : GaugeField L → ℂ) U) 2
            (wilsonBaseMeasure L) := hBase G H
  -- Step C: μ_base bound by √(1/m) · μ_Gibbs for `G - H`.
  have hC :
      eLpNorm (fun U => (G : GaugeField L → ℂ) U -
                        (H : GaugeField L → ℂ) U) 2
          (wilsonBaseMeasure L)
        ≤ ENNReal.ofReal (Real.sqrt (1 / m)) *
          eLpNorm (fun U => (G : GaugeField L → ℂ) U -
                             (H : GaugeField L → ℂ) U) 2
            (wilsonGibbsMeasure L β) :=
    wilsonBase_eLpNorm_two_le_const_mul_gibbs β m hm_pos hm _ hDiff_cont
  -- Compose A → B → C.
  calc eLpNorm (fun U => avgMinus (G : GaugeField L → ℂ) U -
                        avgMinus (H : GaugeField L → ℂ) U) 2
          (wilsonGibbsMeasure L β)
      ≤ ENNReal.ofReal (Real.sqrt M) *
          eLpNorm (fun U => avgMinus (G : GaugeField L → ℂ) U -
                             avgMinus (H : GaugeField L → ℂ) U) 2
            (wilsonBaseMeasure L) := hA
    _ ≤ ENNReal.ofReal (Real.sqrt M) *
          eLpNorm (fun U => (G : GaugeField L → ℂ) U -
                             (H : GaugeField L → ℂ) U) 2
            (wilsonBaseMeasure L) := by
          exact mul_le_mul_left' hB _
    _ ≤ ENNReal.ofReal (Real.sqrt M) *
          (ENNReal.ofReal (Real.sqrt (1 / m)) *
            eLpNorm (fun U => (G : GaugeField L → ℂ) U -
                               (H : GaugeField L → ℂ) U) 2
              (wilsonGibbsMeasure L β)) := by
          exact mul_le_mul_left' hC _
    _ = (ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal (Real.sqrt (1 / m))) *
          eLpNorm (fun U => (G : GaugeField L → ℂ) U -
                             (H : GaugeField L → ℂ) U) 2
            (wilsonGibbsMeasure L β) := by ring
    _ = ENNReal.ofReal (Real.sqrt M * Real.sqrt (1 / m)) *
          eLpNorm (fun U => (G : GaugeField L → ℂ) U -
                             (H : GaugeField L → ℂ) U) 2
            (wilsonGibbsMeasure L β) := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.WilsonAvgMinusL2ContractionBase
#print axioms PF.YangMills.wilsonAvgMinusL2Bound_of_base_contraction
