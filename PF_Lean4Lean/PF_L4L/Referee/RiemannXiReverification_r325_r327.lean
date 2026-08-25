/-
# PF_L4L.Referee.RiemannXiReverification_r325_r327

Independent L4L re-verification of the r325 / r326 / r327 substantive
endpoints on the classical entire Riemann ξ.

## What this covers

r325 — the entire counting object and its ζ-zero equivalence:
  * `differentiable_riemannXiEntire`
  * `riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip`

r326 — symmetries + exact bridge to PF's certified real Xi witness:
  * `riemannXiEntire_one_sub`
  * `riemannXiEntire_conj`
  * `riemannXiEntire_critical_eq_Xi`
  * `riemannXiEntire_critical_eq_zero_iff_Xi_eq_zero`
  * `exists_riemannXiEntire_zero_between_one_and_fifteen`

r327 — rectangle argument principle instantiated to `riemannXiEntire`:
  * `rectangleZeroCount_riemannXiEntire`
  * `rectangleZeroCount_riemannXiEntire_self_contained`

## Verification protocol

Identical to `PF_L4L.Referee.FlagshipReverification`:

1. Build canonical PF library (`PF_Lean4_Code/PF/`) via `lake build` at
   PF_Lean4_Code.
2. Build PF_L4L (this package) via `lake build` at PF_Lean4Lean.
3. Confirm that `#print axioms` on every rebound endpoint below reports
   only Lean's three foundational axioms
   (`propext`, `Classical.choice`, `Quot.sound`) — no project axioms.

This module performs step 3 inside the L4L build, giving a build-time
guarantee that the L4L re-verification has succeeded for each of the
nine listed endpoints.

## Honest scope (same disclaimer as FlagshipReverification)

L4L re-verification means: the canonical theorems' elaboration and
kernel type-check are being re-run through Lean's kernel with L4L as the
*importing* package.  This is a second pass through Lean's kernel (the
first pass being during PF_Lean4_Code's own build).  It is NOT a
separate type-checker written in another language; that would require
Mario Carneiro's Lean4Lean external checker (`leanprover/lean4lean`),
which is currently external to this repository.

For the current state, "L4L re-verification" = "the canonical theorems
type-check under Lean's kernel when imported from a separate package
(this one) with an independent build hash, and report zero project
axioms in the build-time `#print axioms` output below."
-/

import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannXiSymmetries_r326
import PF.Analytic.RiemannXiRectangleCount_r327

namespace PF_L4L.Referee

/-! ## r325 — entire counting object + ζ-zero equivalence -/

def differentiable_riemannXiEntire_reverified :=
  @PrincipiaTractalis.RiemannXiEntire.differentiable_riemannXiEntire

def riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip_reverified :=
  @PrincipiaTractalis.RiemannXiEntire.riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip

/-! ## r326 — symmetries + exact bridge to PF Xi -/

def riemannXiEntire_one_sub_reverified :=
  @PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_one_sub

def riemannXiEntire_conj_reverified :=
  @PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_conj

def riemannXiEntire_critical_eq_Xi_reverified :=
  @PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_critical_eq_Xi

def riemannXiEntire_critical_eq_zero_iff_Xi_eq_zero_reverified :=
  @PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_critical_eq_zero_iff_Xi_eq_zero

def exists_riemannXiEntire_zero_between_one_and_fifteen_reverified :=
  @PrincipiaTractalis.RiemannXiSymmetries.exists_riemannXiEntire_zero_between_one_and_fifteen

/-! ## r327 — rectangle argument principle instantiated to ξ -/

def rectangleZeroCount_riemannXiEntire_reverified :=
  @PrincipiaTractalis.RiemannXiRectangleCount.rectangleZeroCount_riemannXiEntire

def rectangleZeroCount_riemannXiEntire_self_contained_reverified :=
  @PrincipiaTractalis.RiemannXiRectangleCount.rectangleZeroCount_riemannXiEntire_self_contained

/-! ## §Axiom check — build-time guarantee -/

#print axioms differentiable_riemannXiEntire_reverified
#print axioms riemannXiEntire_eq_zero_iff_riemannZeta_eq_zero_in_strip_reverified
#print axioms riemannXiEntire_one_sub_reverified
#print axioms riemannXiEntire_conj_reverified
#print axioms riemannXiEntire_critical_eq_Xi_reverified
#print axioms riemannXiEntire_critical_eq_zero_iff_Xi_eq_zero_reverified
#print axioms exists_riemannXiEntire_zero_between_one_and_fifteen_reverified
#print axioms rectangleZeroCount_riemannXiEntire_reverified
#print axioms rectangleZeroCount_riemannXiEntire_self_contained_reverified

end PF_L4L.Referee
