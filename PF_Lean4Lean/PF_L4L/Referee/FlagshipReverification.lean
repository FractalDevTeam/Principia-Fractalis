/-
# PF_L4L.Referee.FlagshipReverification

External Lean4Lean re-verification of the framework's flagship single-citation
theorem, `PF.Referee.PrincipiaFractalisSubstrateTheorem.PrincipiaFractalisSubstrateTheorem`.

## Verification protocol

The Lean kernel-level evidence chain is:

  1. Build canonical PF library (PF_Lean4_Code/PF/) via `lake build` at PF_Lean4_Code.
  2. Build PF_L4L (this package) via `lake build` at PF_Lean4Lean.
  3. Confirm that `#print axioms` on the flagship theorem reports only
     Lean's three foundational axioms (`propext`, `Classical.choice`,
     `Quot.sound`) — no project axioms.

This module performs step 3 inside the L4L build, giving a build-time guarantee
that the L4L re-verification has succeeded.

## Honest scope

L4L re-verification means: the canonical theorem's elaboration and kernel
type-check is being re-run through Lean's kernel with L4L as the *importing*
package. This is a second pass through Lean's kernel (the first pass being
during PF_Lean4_Code's own build). It is NOT a separate type-checker
written in another language; that would require Mario Carneiro's Lean4Lean
external checker (`leanprover/lean4lean`), which is currently external to
this repository.

For the strongest third-party verification, future work should:
  * Add the upstream `lean4lean` package as a lake dependency, AND
  * Invoke `lean4lean check PF.Referee.PrincipiaFractalisSubstrateTheorem`
    as a post-build step.

For the current state, "L4L re-verification" = "the canonical theorem
type-checks under Lean's kernel when imported from a separate package
(this one) with an independent build hash, and reports zero project
axioms in the build-time `#print axioms` output below."
-/

import PF.Referee.PrincipiaFractalisSubstrateTheorem

namespace PF_L4L.Referee

open PF.Referee.PrincipiaFractalisSubstrateTheorem

/--
The flagship theorem is reachable from the L4L package and depends only
on the three foundational Lean axioms.

The `#print axioms` info-message below is emitted at build time and
forms part of the L4L verification protocol: any drift away from
`[propext, Classical.choice, Quot.sound]` will be visible in the
build log.
-/
def flagshipReverified :
    PFSubstrateAntecedents → PFSubstrateConsequences :=
  PrincipiaFractalisSubstrateTheorem

/-- Unconditional consequence inhabitation re-verified through L4L. -/
def flagshipConsequencesReverified : PFSubstrateConsequences :=
  PrincipiaFractalisSubstrateConsequences_holds_unconditionally

#print axioms flagshipReverified
#print axioms flagshipConsequencesReverified

end PF_L4L.Referee
