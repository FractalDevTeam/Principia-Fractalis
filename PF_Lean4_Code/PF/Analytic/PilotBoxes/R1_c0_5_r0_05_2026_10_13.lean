/-
# PilotBoxes/R1_c0_5_r0_05_2026_10_13 — the first pilot box of the Rank-1.5 campaign

Specialises `CenteredFormBridge20261013.R1_box_centered_of_lb` at the concrete
first pilot box `(c = 1/2, r = 1/20)` on the R1 segment `t ∈ [0, 13]`.

The theorem is CONDITIONAL on the two certificates the (not-yet-built)
centered-form producer will discharge: a certified lower bound on
`Re ξ(1 + i/2)` and a certified upper bound on `|deriv edgeRe x|` across the
box. Once a certified producer supplies them, this one pilot box closes R1 on
the positive-length segment `[9/20, 11/20] = [1/2 - 1/20, 1/2 + 1/20]`, feeding
the chain

    pilot_r1_box_c0_5_r0_05  ⟶  (one step in forall_Icc_cover)
                              ⟶  R1  ⟶  rh_below_15_conditional.

Numerics the producer must beat (mpmath dps=100, sampled 201 pts — see
`codex/PILOT_R1_FEASIBILITY_2026-10-13.md`):

| quantity | measured | pilot's conservative rational | margin |
|---|---|---|---|
| `Re ξ(1 + i/2)` | ≈ 0.49709  | `Mc_lb = 1/4 = 0.25`           | measured 1.99× above threshold |
| `max |deriv edgeRe|` on `[9/20, 11/20]` | ≈ 0.01276 | `L = 1/10 = 0.1` | 7.84× headroom |
| margin check `L · r < Mc_lb` | — | `1/10 · 1/20 = 1/200 = 0.005 < 1/4` | 50× over margin |

The pilot box uses deliberately loose rational bounds (`1/4` and `1/10`) to
make the margin pass with `norm_num` on arithmetic alone. A tighter producer
output (say `Mc_lb = 4/10`, `L = 2/100`) would still pass; the pilot is agnostic
to the exact producer precision — only that it beats these conservative
numbers.

### Scope — unchanged honesty

* **CONDITIONAL theorem.** The two certified-producer hypotheses are not
  discharged in this file; a certified panel generator (Rank 1.5 engineering,
  Legion's day-scale estimate) is the remaining piece.
* **One box, not R1.** This file closes R1 on `[9/20, 11/20]`, a 1/10-wide
  slice of the full `[0, 13]` segment. R1 remains open; chaining ~50 such
  pilot boxes closes the whole segment.
* **No bearing on the open Riemann Hypothesis.** `rh_below_15_conditional` is
  RH on one finite rectangle, classically known since Riemann and Gram.

### No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-13.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c0_5_r0_05_20261013

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013

noncomputable section

/-- **The first pilot box.** Given the two certified-producer hypotheses, R1
holds throughout `[1/2 - 1/20, 1/2 + 1/20]`. -/
theorem pilot_r1_box_c0_5_r0_05
    (hvalue_lb :
      (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 1 / 2⟩ : ℂ)).re)
    (hbound :
      ∀ x ∈ Icc ((1 / 2 : ℝ) - 1 / 20) ((1 / 2 : ℝ) + 1 / 20),
        |deriv edgeRe x| ≤ 1 / 10) :
    ∀ t ∈ Icc ((1 / 2 : ℝ) - 1 / 20) ((1 / 2 : ℝ) + 1 / 20),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re :=
  R1_box_centered_of_lb
    (c := 1 / 2) (r := 1 / 20) (L := 1 / 10) (Mc_lb := 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 20)
    hvalue_lb
    hbound
    (by norm_num : (1 / 10 : ℝ) * (1 / 20) < 1 / 4)

/-- Restated with the simplified endpoint `[9/20, 11/20]` form. -/
theorem pilot_r1_box_c0_5_r0_05'
    (hvalue_lb :
      (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 1 / 2⟩ : ℂ)).re)
    (hbound :
      ∀ x ∈ Icc ((9 / 20 : ℝ)) (11 / 20), |deriv edgeRe x| ≤ 1 / 10) :
    ∀ t ∈ Icc ((9 / 20 : ℝ)) (11 / 20),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have heq : Icc ((9 / 20 : ℝ)) (11 / 20)
      = Icc ((1 / 2 : ℝ) - 1 / 20) ((1 / 2 : ℝ) + 1 / 20) := by
    congr 1 <;> norm_num
  rw [heq] at hbound ⊢
  exact pilot_r1_box_c0_5_r0_05 hvalue_lb hbound

end

/-! ## §Axiom check -/

#print axioms pilot_r1_box_c0_5_r0_05
#print axioms pilot_r1_box_c0_5_r0_05'

end PilotR1Box_c0_5_r0_05_20261013
end PrincipiaTractalis
