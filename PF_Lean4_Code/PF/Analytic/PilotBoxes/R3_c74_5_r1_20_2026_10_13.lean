/-
# PilotBoxes/R3_c74_5_r1_20_2026-10-13 — pilot box of the Rank-1.5 campaign

Specialises `CenteredFormBridge20261013.R3_box_centered_of_ub` at the concrete pilot
box `(c = 74 / 5, r = 1 / 20)` on the R3 segment.

CONDITIONAL theorem — the certified producer must discharge `hvalue_ub`
and `hbound`. Margin check `L · r < Mc_ub = -1 / 2000` holds by `norm_num`
on the chosen conservative rationals.

Emitted by `scripts/emit_centered_pilot_box.py`.

### No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-13.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotBox_R3_c74_5_r1_20_2026_10_13

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013

noncomputable section

/-- Pilot box: R3 on `[74 / 5 - 1 / 20, 74 / 5 + 1 / 20]` from the
certified producer's bound on `Re ξ(1 + i·74 / 5)` plus the derivative
modulus bound. -/
theorem pilot_r3_box_c74_5_r1_20
    (hvalue_ub : (riemannXiEntire (⟨1, 74 / 5⟩ : ℂ)).re ≤ (-1 / 2000 : ℝ))
    (hbound :
      ∀ x ∈ Icc ((74 / 5 : ℝ) - 1 / 20) ((74 / 5 : ℝ) + 1 / 20),
        |deriv edgeRe x| ≤ 1 / 1000) :
    ∀ t ∈ Icc ((74 / 5 : ℝ) - 1 / 20) ((74 / 5 : ℝ) + 1 / 20),
      (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0 :=
  R3_box_centered_of_ub
    (c := 74 / 5) (r := 1 / 20) (L := 1 / 1000) (Mc_ub := -1 / 2000)
    (by norm_num : (0 : ℝ) ≤ 1 / 20)
    hvalue_ub
    hbound
    (by norm_num : (-1 / 2000 : ℝ) < -((1 / 1000) * (1 / 20)))

end

/-! ## §Axiom check -/

#print axioms pilot_r3_box_c74_5_r1_20

end PilotBox_R3_c74_5_r1_20_2026_10_13
end PrincipiaTractalis
