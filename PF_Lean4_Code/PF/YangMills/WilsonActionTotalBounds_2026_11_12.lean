/-
# PF.YangMills.WilsonActionTotalBounds_2026_11_12

**Step 3c.4c ingredient**: bounds on `exp(-β · wilsonActionTotal)` on
the compact gauge-field space.  Companion to
`WilsonSectorActionBounded_r360` (which handles the sector-split
actions `wilsonAction{PlusR, Zero, MinusR}`); this file handles the
full `wilsonActionTotal` directly.

Delivers:
* `wilsonActionTotal_bddAbove` — `∃ M, ∀ U, wilsonActionTotal U ≤ M`.
* `wilsonActionTotal_bddBelow` — `∃ m, ∀ U, m ≤ wilsonActionTotal U`.
* `expWilsonActionTotal_bddAbove_pos` — `∃ M > 0, ∀ U,
  exp(-β · wilsonActionTotal U) ≤ M`.
* `expWilsonActionTotal_bddBelow_pos` — `∃ m > 0, ∀ U,
  m ≤ exp(-β · wilsonActionTotal U)`.

All via compactness of `GaugeField L` + continuity of
`wilsonActionTotal` + monotonicity of `exp`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonActionContinuity_2026_10_20
import PF.YangMills.WilsonMeasure_2026_10_17

namespace PF.YangMills

open MeasureTheory

variable {L : ℕ} [NeZero L]

/-- **`wilsonActionTotal` is bounded above on `GaugeField L`.**
Via continuity on compact (`GaugeField L` is a finite product of
compact `SU2`). -/
theorem wilsonActionTotal_bddAbove :
    ∃ M : ℝ, ∀ U : GaugeField L, wilsonActionTotal U ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_range (wilsonActionTotal_continuous (L := L))).bddAbove
  exact ⟨M, fun U => hM (Set.mem_range_self U)⟩

/-- **`wilsonActionTotal` is bounded below on `GaugeField L`.** -/
theorem wilsonActionTotal_bddBelow :
    ∃ m : ℝ, ∀ U : GaugeField L, m ≤ wilsonActionTotal U := by
  obtain ⟨m, hm⟩ := (isCompact_range (wilsonActionTotal_continuous (L := L))).bddBelow
  exact ⟨m, fun U => hm (Set.mem_range_self U)⟩

/-- **`exp(-β · wilsonActionTotal)` is bounded above by a positive
constant.** For β ∈ ℝ (any sign): uses the lower bound on
`wilsonActionTotal` combined with monotonicity of `exp` under
negation. -/
theorem expWilsonActionTotal_bddAbove_pos (β : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ U : GaugeField L,
      Real.exp (-β * wilsonActionTotal U) ≤ M := by
  -- Pick the sup of the continuous function `exp(-β·wilsonActionTotal)`.
  have hcont : Continuous (fun U : GaugeField L =>
      Real.exp (-β * wilsonActionTotal U)) :=
    Real.continuous_exp.comp (continuous_const.mul wilsonActionTotal_continuous)
  obtain ⟨M, hM⟩ := (isCompact_range hcont).bddAbove
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun U => ?_⟩
  exact le_trans (hM (Set.mem_range_self U)) (le_max_left _ _)

/-- **`exp(-β · wilsonActionTotal)` is bounded below by a positive
constant.** Since `exp(-β·wilsonActionTotal)` is continuous and
strictly positive on the compact nonempty space `GaugeField L`, the
infimum is attained and is positive. -/
theorem expWilsonActionTotal_bddBelow_pos (β : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ U : GaugeField L,
      m ≤ Real.exp (-β * wilsonActionTotal U) := by
  -- Use `wilsonActionTotal_bddAbove` to bound `-β · wilsonActionTotal`
  -- from below (for β ≥ 0) or above (for β < 0).  Either way monotone
  -- exp gives a positive lower bound.
  obtain ⟨M_up, hM_up⟩ := wilsonActionTotal_bddAbove (L := L)
  obtain ⟨M_lo, hM_lo⟩ := wilsonActionTotal_bddBelow (L := L)
  -- For any β, `-β · S ∈ [-β · M_up, -β · M_lo]` or the reverse.
  -- Take `m := min (exp(-β · M_up)) (exp(-β · M_lo))` — both positive.
  refine ⟨min (Real.exp (-β * M_up)) (Real.exp (-β * M_lo)),
          lt_min (Real.exp_pos _) (Real.exp_pos _), fun U => ?_⟩
  have hU_up : wilsonActionTotal U ≤ M_up := hM_up U
  have hU_lo : M_lo ≤ wilsonActionTotal U := hM_lo U
  -- Bound `-β · wilsonActionTotal U` from below by the min of the two endpoints.
  rcases le_or_gt 0 β with hβ | hβ
  · -- β ≥ 0: -β · S ≥ -β · M_up, so exp(-β · S) ≥ exp(-β · M_up).
    have : -β * M_up ≤ -β * wilsonActionTotal U := by
      have : -β ≤ 0 := neg_nonpos_of_nonneg hβ
      nlinarith [hM_up U, hβ]
    calc min (Real.exp (-β * M_up)) (Real.exp (-β * M_lo))
        ≤ Real.exp (-β * M_up) := min_le_left _ _
      _ ≤ Real.exp (-β * wilsonActionTotal U) := Real.exp_le_exp.mpr this
  · -- β < 0: -β > 0, so -β · S ≥ -β · M_lo, so exp(-β · S) ≥ exp(-β · M_lo).
    have : -β * M_lo ≤ -β * wilsonActionTotal U := by
      have h_neg : 0 < -β := neg_pos.mpr hβ
      exact mul_le_mul_of_nonneg_left hU_lo h_neg.le
    calc min (Real.exp (-β * M_up)) (Real.exp (-β * M_lo))
        ≤ Real.exp (-β * M_lo) := min_le_right _ _
      _ ≤ Real.exp (-β * wilsonActionTotal U) := Real.exp_le_exp.mpr this

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonActionTotal_bddAbove
#print axioms PF.YangMills.wilsonActionTotal_bddBelow
#print axioms PF.YangMills.expWilsonActionTotal_bddAbove_pos
#print axioms PF.YangMills.expWilsonActionTotal_bddBelow_pos
