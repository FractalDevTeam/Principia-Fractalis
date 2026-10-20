/-
# PF.Analytic.PilotBoxes.R1_c27_4_r1_16_HYBRID_2026_10_19

**The c = 27/4 R1 pilot box, hybrid scheme — Gate-1 and Gate-2 both
discharged unconditionally.**

R1 (`Re ξ(1+it) > 0`) on `[27/4 − 1/16, 27/4 + 1/16] = [107/16, 109/16]
= [6.6875, 6.8125]`.

## What is discharged here, and what is left

| ingredient | status |
|---|---|
| **Gate-1** `(729/16)·R_ub + (27/4)·I_ub ≤ 3/4` | **discharged** — `gate1_arithmetic_c27_4_hybrid`, margin `+0.0571` |
| **Gate-2** `\|deriv edgeRe x\| ≤ 1` on the box | **discharged** — `abs_deriv_edgeRe_le_one_le_fourteen` (`15ddbf2e`), no `K_sum` hypothesis |
| the two `Λ₀(1+i·27/4)` upper bounds | **hypotheses** — see below |

Those two upper bounds are exactly what the three add-on modules supply at
`c = 13/2` (`ResidueBoundTight_c13_2`, `AnalyticTailBound_c13_2`,
`OmegaTailBound_c13_2`, composed in the `CLOSED` pilot). **Those modules do not
exist at `c = 27/4`** — the `c = 27/4` pack is `CoreDefs` plus twelve segment
files and nothing else. So this pilot is stated in the `…_closed` style the
`c = 13/2` scaffold uses: the moment the three add-ons land at `27/4`, the
unconditional pilot is a four-line application, with no further Gate work.

The arithmetic those add-ons must satisfy is already fixed by the hybrid
enclosure proved in `Assemble_c27_4_threehalves_HYBRID_2026_10_19`:

  `R_ub = 4802446903/320000000000 + 7/10^7 + 12/10^8 + epsOm`
  `I_ub = 21496359/16000000000 + 7/10^7 + 12/10^8 + epsOm`

and `gate1_arithmetic_c27_4_hybrid` proves the Gate-1 inequality for those
values for any `epsOm ≤ 1/10^21`.

## Why hybrid

Neither panel scheme closes Gate-1 at `c = 27/4` alone. All range-brick gives
`0.75566065 > 3/4` — a **failure by `0.00566`**. The hybrid (midpoint on
segments 1-2, range-brick on 3-6) gives `0.69289757`, passing by `0.05710`.
See the assemble module for the structural reason the crossover exists.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-19.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0PrimeThetaLogBound_2026_10_19
import PF.Analytic.FourierPanels.Assemble_c27_4_threehalves_HYBRID_2026_10_19

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c27_4_r1_16_HYBRID_20261019

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.EdgeReDerivBound20261014
open PrincipiaTractalis.Lambda0PrimeThetaLogBound20261019
open PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID

noncomputable section

/-! ## §1 — Centre value: `1/8 ≤ Re ξ(1 + i·27/4)` from the Gate-1 inequality -/

/-- The centre-value lower bound `Mc_lb = 1/8`, from upper bounds on
`Re Λ₀` and `Im Λ₀` at `t = 27/4` together with the Gate-1 inequality.

`Re ξ(1+it) = (1 + (σ(σ−1) − t²)·Re Λ₀ − t(2σ−1)·Im Λ₀)/2` at `σ = 1`
specialises to `(1 − t²·Re Λ₀ − t·Im Λ₀)/2`, so `1/8 ≤ Re ξ` is exactly
`t²·Re Λ₀ + t·Im Λ₀ ≤ 3/4`. -/
theorem pilot_r1_hvalue_lb_at_c27_4
    (R_ub I_ub : ℝ)
    (hR_ub : (completedRiemannZeta₀ (⟨1, 27/4⟩ : ℂ)).re ≤ R_ub)
    (hI_ub : (completedRiemannZeta₀ (⟨1, 27/4⟩ : ℂ)).im ≤ I_ub)
    (h_gate : (729/16 : ℝ) * R_ub + (27/4) * I_ub ≤ 3/4) :
    (1 / 8 : ℝ) ≤ (riemannXiEntire (⟨1, 27/4⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  set re := (completedRiemannZeta₀ (⟨1, 27/4⟩ : ℂ)).re with hre_def
  set im := (completedRiemannZeta₀ (⟨1, 27/4⟩ : ℂ)).im with him_def
  have h_combo : (729/16 : ℝ) * re + (27/4 : ℝ) * im ≤ 3/4 := by
    have h_c2 : (729/16 : ℝ) * re ≤ (729/16 : ℝ) * R_ub :=
      mul_le_mul_of_nonneg_left hR_ub (by norm_num : (0 : ℝ) ≤ 729/16)
    have h_c : (27/4 : ℝ) * im ≤ (27/4 : ℝ) * I_ub :=
      mul_le_mul_of_nonneg_left hI_ub (by norm_num : (0 : ℝ) ≤ 27/4)
    linarith
  have hNum :
      (1 * (1 - 1) - (27/4 : ℝ) ^ 2) * re - (27/4 : ℝ) * (2 * 1 - 1) * im
        = -((729/16 : ℝ) * re + (27/4) * im) := by ring
  linarith

/-! ## §2 — Gate-2 on the box, unconditionally -/

/-- **Gate-2 at `c = 27/4`, radius `1/16`.** From
`abs_deriv_edgeRe_le_one_le_fourteen` (`15ddbf2e`), since the box's upper edge
is `109/16 = 6.8125 ≤ 14`.

Note this box is *not* covered by that file's `pilot_r1_hbound_box`, whose
range is `[55/8, 13]`: `27/4 = 6.75 < 55/8 = 6.875`. The box lemma was written
for the centres the old Gate-2 ceiling of `6.886` had blocked, and `27/4` is
precisely the last centre that was already passing — so the `|t| ≤ 14`
primitive is the right entry point here.

Before the log-weighted `Λ₀'` bound this was unreachable: the old pair
`(50/1727, 50/1727)` caps Gate-2 at `|t| ≤ 6.886`, and the box's upper edge is
`109/16 = 6.8125` — inside, but the *next* box at `55/8` was not, which is why
the march stopped here. -/
theorem pilot_r1_hbound_c27_4_r1_16 :
    ∀ x ∈ Icc ((27/4 : ℝ) - 1/16) ((27/4 : ℝ) + 1/16), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_pos : (0 : ℝ) < x := by linarith [hx.1]
  have hx_abs : |x| = x := abs_of_pos hx_pos
  refine abs_deriv_edgeRe_le_one_le_fourteen ?_
  rw [hx_abs]
  linarith [hx.2]

/-! ## §3 — The pilot box -/

/-- **R1 pilot box at `c = 27/4`, radius `1/16`** — conditional only on the
two `Λ₀` upper bounds at the centre. Gate-1 and Gate-2 are both discharged. -/
theorem pilot_r1_box_c27_4_r1_16_closed
    (R_ub I_ub : ℝ)
    (hR_ub : (completedRiemannZeta₀ (⟨1, 27/4⟩ : ℂ)).re ≤ R_ub)
    (hI_ub : (completedRiemannZeta₀ (⟨1, 27/4⟩ : ℂ)).im ≤ I_ub)
    (h_gate : (729/16 : ℝ) * R_ub + (27/4) * I_ub ≤ 3/4) :
    ∀ t ∈ Icc ((27/4 : ℝ) - 1/16) ((27/4 : ℝ) + 1/16),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re :=
  R1_box_centered_of_lb
    (c := 27/4) (r := 1/16) (L := 1) (Mc_lb := 1/8)
    (by norm_num : (0 : ℝ) ≤ 1/16)
    (pilot_r1_hvalue_lb_at_c27_4 R_ub I_ub hR_ub hI_ub h_gate)
    pilot_r1_hbound_c27_4_r1_16
    (by norm_num : (1 : ℝ) * (1/16) < 1/8)

/-- **The pilot, with the hybrid Gate-1 arithmetic already substituted.**

The only remaining inputs are the two `Λ₀` upper bounds in the exact shape the
three `c = 27/4` add-on modules will produce. Nothing else is left to prove. -/
theorem pilot_r1_box_c27_4_r1_16_from_addons
    {epsOm : ℝ} (hEps : epsOm ≤ 1 / 10 ^ 21)
    (hR_ub : (completedRiemannZeta₀ (⟨1, 27/4⟩ : ℂ)).re
        ≤ (4802446903/320000000000 : ℝ) + 7/10^7 + 12/10^8 + epsOm)
    (hI_ub : (completedRiemannZeta₀ (⟨1, 27/4⟩ : ℂ)).im
        ≤ (21496359/16000000000 : ℝ) + 7/10^7 + 12/10^8 + epsOm) :
    ∀ t ∈ Icc ((27/4 : ℝ) - 1/16) ((27/4 : ℝ) + 1/16),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re :=
  pilot_r1_box_c27_4_r1_16_closed _ _ hR_ub hI_ub
    (gate1_arithmetic_c27_4_hybrid hEps)

end

end PilotR1Box_c27_4_r1_16_HYBRID_20261019
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.PilotR1Box_c27_4_r1_16_HYBRID_20261019.pilot_r1_hvalue_lb_at_c27_4
#print axioms PrincipiaTractalis.PilotR1Box_c27_4_r1_16_HYBRID_20261019.pilot_r1_hbound_c27_4_r1_16
#print axioms PrincipiaTractalis.PilotR1Box_c27_4_r1_16_HYBRID_20261019.pilot_r1_box_c27_4_r1_16_closed
#print axioms PrincipiaTractalis.PilotR1Box_c27_4_r1_16_HYBRID_20261019.pilot_r1_box_c27_4_r1_16_from_addons
