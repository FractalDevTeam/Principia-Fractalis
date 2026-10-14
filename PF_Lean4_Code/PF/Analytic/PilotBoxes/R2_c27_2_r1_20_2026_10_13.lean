/-
# PilotBoxes/R2_c27_2_r1_20_2026-10-13 — pilot box of the Rank-1.5 campaign

Specialises `CenteredFormBridge20261013.R2_box_centered_of_lb` at the concrete pilot
box `(c = 27 / 2, r = 1 / 20)` on the R2 segment.

CONDITIONAL theorem — the certified producer must discharge `hvalue_lb`
and `hbound`. Margin check `L · r < Mc_lb = 1 / 1000` holds by `norm_num`
on the chosen conservative rationals.

Emitted by `scripts/emit_centered_pilot_box.py`.

### No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-13.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotBox_R2_c27_2_r1_20_2026_10_13

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013

noncomputable section

/-- Pilot box: R2 on `[27 / 2 - 1 / 20, 27 / 2 + 1 / 20]` from the
certified producer's bound on `Im ξ(1 + i·27 / 2)` plus the derivative
modulus bound. -/
theorem pilot_r2_box_c27_2_r1_20
    (hvalue_lb : (1 / 1000 : ℝ) ≤ (riemannXiEntire (⟨1, 27 / 2⟩ : ℂ)).im)
    (hbound :
      ∀ x ∈ Icc ((27 / 2 : ℝ) - 1 / 20) ((27 / 2 : ℝ) + 1 / 20),
        |deriv edgeIm x| ≤ 1 / 100) :
    ∀ t ∈ Icc ((27 / 2 : ℝ) - 1 / 20) ((27 / 2 : ℝ) + 1 / 20),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im :=
  R2_box_centered_of_lb
    (c := 27 / 2) (r := 1 / 20) (L := 1 / 100) (Mc_lb := 1 / 1000)
    (by norm_num : (0 : ℝ) ≤ 1 / 20)
    hvalue_lb
    hbound
    (by norm_num : (1 / 100 : ℝ) * (1 / 20) < 1 / 1000)

end

/-! ## §Axiom check -/

#print axioms pilot_r2_box_c27_2_r1_20

end PilotBox_R2_c27_2_r1_20_2026_10_13
end PrincipiaTractalis
