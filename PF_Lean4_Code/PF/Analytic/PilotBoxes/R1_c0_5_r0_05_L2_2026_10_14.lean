/-
# PF.Analytic.PilotBoxes.R1_c0_5_r0_05_L2_2026_10_14

**THE FIRST FULL CENTERED-FORM PILOT BOX, CLOSED END-TO-END, KERNEL-CLEAN.**

Specialises `CenteredFormBridge20261013.R1_box_centered_of_lb` at the pilot
box `(c = 1/2, r = 1/20)` with producer-friendly parameters:

  * `Mc_lb = 1/4`  — center-value lower bound (discharged by
    `Lambda0UniformBound20261014.pilot_r1_hvalue_lb`)
  * `L = 2`        — derivative modulus bound (discharged by
    `EdgeReDerivBound20261014.pilot_r1_hbound`)
  * margin check   — `L · r = 2 · 1/20 = 1/10 < 1/4 = Mc_lb` ✓ by `norm_num`.

The conclusion `0 < Re ξ(1 + it)` holds throughout `[9/20, 11/20]` — a
positive-length segment of R1 on the right edge, kernel-clean, zero project
axioms.

This is the first full pilot box of the Rank-1.5 centered-form campaign.
Scaling the same recipe (point-value + derivative bound + margin check per
box) closes the rest of R1 ∪ R2 via a batched campaign.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0UniformBound_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c0_5_r0_05_L2_20261014

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UniformBound20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-- **THE FIRST FULL PILOT BOX, CLOSED.** R1 on `[9/20, 11/20]` — zero
hypotheses, kernel-clean, zero project axioms. -/
theorem pilot_r1_box_c0_5_r0_05_L2_closed :
    ∀ t ∈ Icc ((9 : ℝ) / 20) (11 / 20),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((9 : ℝ) / 20) (11 / 20)
      = Icc ((1 / 2 : ℝ) - 1 / 20) ((1 / 2 : ℝ) + 1 / 20) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 1 / 2) (r := 1 / 20) (L := 2) (Mc_lb := 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 20)
    pilot_r1_hvalue_lb
    ?_
    (by norm_num : (2 : ℝ) * (1 / 20) < 1 / 4)
  intro x hx
  -- hx : x ∈ Icc (1/2 - 1/20) (1/2 + 1/20) = Icc (9/20) (11/20)
  have hx' : x ∈ Icc ((9 : ℝ) / 20) (11 / 20) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_box_c0_5_r0_05_L2_closed

end PilotR1Box_c0_5_r0_05_L2_20261014
end PrincipiaTractalis
