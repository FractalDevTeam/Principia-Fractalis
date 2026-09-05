/-
# PF.Analytic.RiemannXiT15Endgame

**The T = 15 endgame: top-edge union -> boundary zero-free -> count identity.**

STAGED, NOT YET BUILT.  This module consumes `RiemannXiTopUnion.H_TOP_discharged`,
which exists only once EVERY box in the partition of [1/2, 1] has a kernel-green
capstone.  Building it before then will fail at the import, by design -- it must
never appear to succeed on a partial union.

## What this module needs, exactly

Reading the literal r327/r328/r329b statements, the entire downstream chain requires
exactly ONE hypothesis:

    hTop : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire ⟨σ, 15⟩ ≠ 0

Everything else is already discharged unconditionally in the repository:

| piece | source | status |
|---|---|---|
| right vertical `ξ⟨1,t⟩ ≠ 0` | `r328.riemannXiEntire_ne_zero_on_re_one` | proved, no hypotheses |
| left vertical `ξ⟨0,t⟩ ≠ 0` | `r328.riemannXiEntire_ne_zero_on_re_zero` | proved, no hypotheses |
| corners `ξ(0) = ξ(1) = 1/2` | `r328.riemannXiEntire_zero/one_ne_zero` | proved |
| top edge left half `[0,1/2]` | `r328.top_edge_nonvanishing_of_right_half` | proved from r326 reflection |
| bottom edge `[0,1]` | `r329b.bottomEdgeZeroFree_proved` | **DISCHARGED unconditionally** |
| SW-corner witness | `r328.riemannXiEntire_z15_ne_zero` | proved |
| argument principle | `r327.rectangleZeroCount_riemannXiEntire_self_contained` | proved |

So the top half-edge is the sole residual, and the r331b box campaign discharges it.

## Note on r330

`RiemannXiTopEdgeScaffolding_r330` reaches the same `hTop` shape
(`H_TOP_of_taylor_hypotheses`) but only CONDITIONALLY: it still requires an unproven
uniform second-derivative bound `|f''| ≤ 1/1000` on `[1/2, 1]` as the hypothesis
`hTaylor`.  The r331b box route needs no such hypothesis.  r330 is therefore an
alternative route that this module does NOT use, and after this lands it is
superseded scaffolding rather than a load-bearing dependency.  It should not be
deleted without a separate decision, but the release notes must not present it as
part of the proved chain.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiTopUnion
import PF.Analytic.RiemannXiBottomEdgeUnconditional_r329b

namespace PrincipiaTractalis.RiemannXiT15Endgame

open Complex Set MeasureTheory
open scoped Real
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiRectangleCount
open PrincipiaTractalis.RiemannXiBoundaryT15
open PrincipiaTractalis.RiemannXiBottomEdgeUnconditional
-- `finite_zeros_rectangle`, `RectangleIntegral'` and
-- `rectangleBorder_subset_rectangle` live in `Zeta23.Analytic`;
-- r328 (line 73) and r329b (line 83) both open it.
open Zeta23.Analytic

/-! ## §1 — H_TOP, discharged by the r331b box campaign -/

/-- **H_TOP** — the sole residual of the r328/r329b boundary reduction, now
discharged unconditionally by the 18-box certified partition of `[1/2, 1]`. -/
theorem H_TOP :
    ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → riemannXiEntire (⟨σ, 15⟩ : ℂ) ≠ 0 :=
  PrincipiaTractalis.RiemannXiTopUnion.H_TOP_discharged

/-! ## §2 — Full rectangle boundary zero-free -/

/-- **`boundary_zero_free_T15`** — `ξ` does not vanish anywhere on the border of
the `T = 15` rectangle `[0,1] × [0,15]`.  Unconditional. -/
theorem boundary_zero_free_T15 :
    ∀ s ∈ RectangleBorder z15 w15, riemannXiEntire s ≠ 0 :=
  boundary_zero_free_of_top_right_half H_TOP

/-! ## §3 — The unconditional exact zero-count identity -/

/-- **★★★ `xi_T15_zero_count_identity_unconditional` ★★★** — the exact zero-count
identity for the classical entire Riemann ξ on the `T = 15` rectangle, with NO
remaining hypotheses.

The statement is copied verbatim from
`RiemannXiBottomEdgeUnconditional.xi_T15_exact_zero_count_identity_top_only` so that
any drift in that statement is a build error here rather than a silent mismatch. -/
theorem xi_T15_zero_count_identity_unconditional :
    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) z15 w15
      = ∑ ρ ∈ (finite_zeros_rectangle
              (riemannXiEntire_analyticOnNhd _)
              (rectangleBorder_subset_rectangle z15 w15 z15_mem_RectangleBorder)
              (boundary_zero_free_of_top_right_half H_TOP z15
                  z15_mem_RectangleBorder)).toFinset,
          (analyticOrderNatAt riemannXiEntire ρ : ℂ) :=
  xi_T15_exact_zero_count_identity_top_only H_TOP

end PrincipiaTractalis.RiemannXiT15Endgame

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.RiemannXiT15Endgame.H_TOP
#print axioms PrincipiaTractalis.RiemannXiT15Endgame.boundary_zero_free_T15
#print axioms PrincipiaTractalis.RiemannXiT15Endgame.xi_T15_zero_count_identity_unconditional
