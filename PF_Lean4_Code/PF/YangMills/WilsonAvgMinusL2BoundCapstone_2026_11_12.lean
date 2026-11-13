/-
# PF.YangMills.WilsonAvgMinusL2BoundCapstone_2026_11_12

**Step 3c.4c capstone**: `WilsonAvgMinusL2Bound L β` is an
UNCONDITIONAL theorem for every `L : ℕ` with `[NeZero L]` and every
`β : ℝ`.

Combines:
* `expWilsonActionTotal_bddAbove_pos` — M upper sandwich.
* `expWilsonActionTotal_bddBelow_pos` — m > 0 lower sandwich.
* `wilsonAvgMinusL2Bound_of_base_contraction` — the composition theorem.
* `wilsonAvgMinusL2ContractionBase_holds` — the Jensen contraction on μ_base.

Head output: the L²-boundedness of `avgMinus` on `μ_Gibbs` is a live
theorem for Wilson Yang-Mills on arbitrary lattice size L ≥ 1 and
arbitrary coupling β.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonActionTotalBounds_2026_11_12
import PF.YangMills.WilsonAvgMinusContractionBase_2026_11_12

namespace PF.YangMills

open MeasureTheory

variable {L : ℕ} [NeZero L]

/-- **`WilsonAvgMinusL2Bound L β` holds unconditionally.**

For any lattice size `L ≥ 1` and coupling `β`, the operator `avgMinus`
is L²-bounded on `wilsonGibbsMeasure L β`:

  `∃ C ≥ 0, ∀ G H : BoundedContinuousFunction (GaugeField L) ℂ,
    eLpNorm (avgMinus G - avgMinus H) 2 μ_Gibbs
      ≤ C · eLpNorm (G - H) 2 μ_Gibbs`.

Constant: `C = √(M/m)` where M, m are the exp(-β·S_W) sandwich bounds.

This closes step 3c.4c of the L²-extension lane for Wilson reflection
positivity.  Combined with step 4 (PSD limit, LANDED earlier) and
step 5a (bilinear Gram convergence, remaining), it delivers the full
L² reflection positivity theorem. -/
theorem wilsonAvgMinusL2Bound_holds (β : ℝ) :
    WilsonAvgMinusL2Bound L β := by
  obtain ⟨M, hM_pos, hM⟩ := expWilsonActionTotal_bddAbove_pos (L := L) β
  obtain ⟨m, hm_pos, hm⟩ := expWilsonActionTotal_bddBelow_pos (L := L) β
  exact wilsonAvgMinusL2Bound_of_base_contraction β M m hM_pos.le hm_pos hM hm
    wilsonAvgMinusL2ContractionBase_holds

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonAvgMinusL2Bound_holds
