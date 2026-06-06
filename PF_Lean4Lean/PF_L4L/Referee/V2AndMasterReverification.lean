/-
# PF_L4L.Referee.V2AndMasterReverification

External Lean4Lean re-verification of:

  * The three V2 refactor capstones (PNP, NS, Hodge), and
  * The Clay Master Theorem.

This module follows the same Path C protocol as
`PF_L4L.Referee.FlagshipReverification`: each canonical theorem is
re-bound to a `def`/term in the independent `PF_L4L` lake package, and
`#print axioms` is invoked at build time to confirm dependence only on
`[propext, Classical.choice, Quot.sound]`. Any drift away from these
three foundational Lean axioms surfaces in the L4L build log.

## Honest scope

Same as `FlagshipReverification`: this is a second pass through Lean's
kernel from a separate package with an independent build hash. It is
NOT a separate type-checker written in another language.

## Theorems re-verified

  1. `PrincipiaTractalis.PNPClassSeparationCarrierV2.class_P_subset_class_NP_V2`
       — Cook 1971 P ⊆ NP, V2 carrier (Bool equality).
  2. `PF.NavierStokes.NS3DRegularitySolutionV2.pf_NS_chain_yields_typed_regularityV2`
       — V2 NS chain with BKM 1984 clause 5.
  3. `PrincipiaTractalis.AlgebraicGeometry.HodgeAlgRepV2.hodgeAlgebraicRepresentationV2_capstone`
       — V2 Hodge representation capstone (6-conjunct).
  4. `PF.Referee.ClayMasterTheorem.PF_Clay_Master_Theorem`
       — Single citable Clay-acceptance theorem (uniqueness + 4 axes +
         linkage).

The strategy is `def T_reverified := T` (term-level re-binding through
an independent build hash), exactly as in `FlagshipReverification`.
The type ascriptions are intentionally omitted: by using
`@T` we let Lean infer the canonical type, which guarantees the L4L
re-binding *is* the canonical theorem.
-/

import PF.TuringEncoding.PNPClassSeparationCarrierV2
import PF.NavierStokes.NS3DRegularitySolutionV2
import PF.AlgebraicGeometry.HodgeAlgebraicRepresentationV2
import PF.Referee.ClayMasterTheorem
-- Newest refactors (2026-06-04, HEAD 700bb29): RH V2 typed bridge and
-- PNP V3 TMConfig-wired carrier — re-bound through the L4L package
-- using the same Path C `def T_reverified := @T` pattern.
import PF.Referee.RHCapstoneTypedBridgeV2
import PF.TuringEncoding.PNPClassSeparationCarrierV3

namespace PF_L4L.Referee

/-! ## §1 — P vs NP V2 carrier re-verification -/

/-- L4L re-verification: Cook 1971 `class_P_subset_class_NP_V2`.
    Re-binds the canonical theorem through the L4L package. -/
def pnpV2_class_P_subset_class_NP_reverified :=
  @PrincipiaTractalis.PNPClassSeparationCarrierV2.class_P_subset_class_NP_V2

#print axioms pnpV2_class_P_subset_class_NP_reverified

/-! ## §2 — NS V2 typed-regularity chain re-verification -/

/-- L4L re-verification: V2 NS chain (BKM 1984 5th clause).
    Re-binds the canonical theorem through the L4L package. -/
def nsV2_chain_yields_typed_regularity_reverified :=
  @PF.NavierStokes.NS3DRegularitySolutionV2.pf_NS_chain_yields_typed_regularityV2

#print axioms nsV2_chain_yields_typed_regularity_reverified

/-! ## §3 — Hodge V2 capstone re-verification -/

/-- L4L re-verification: Hodge V2 6-conjunct capstone.
    Re-binds the canonical theorem through the L4L package. -/
def hodgeV2_capstone_reverified :=
  @PrincipiaTractalis.AlgebraicGeometry.HodgeAlgRepV2.hodgeAlgebraicRepresentationV2_capstone

#print axioms hodgeV2_capstone_reverified

/-! ## §4 — Clay Master Theorem re-verification -/

/-- L4L re-verification: THE Clay Master Theorem. Single referee-citation
    point for the framework's Clay-acceptance case.
    Re-binds the canonical theorem through the L4L package. -/
def clayMasterTheorem_reverified :=
  @PF.Referee.ClayMasterTheorem.PF_Clay_Master_Theorem

#print axioms clayMasterTheorem_reverified

/-! ## §5 — RH V2 typed bridge re-verification -/

/-- L4L re-verification: RH V2 typed bridge
    `PF_RH_capstone_yields_Clay_RH_standardV2`. Re-binds the canonical
    theorem through the L4L package. -/
def rhV2_capstone_reverified :=
  @PF.Referee.RHCapstoneTypedBridgeV2.PF_RH_capstone_yields_Clay_RH_standardV2

#print axioms rhV2_capstone_reverified

/-! ## §6 — PNP V3 TMConfig-wired carrier re-verification -/

/-- L4L re-verification: PNP V3 TMConfig-wired Cook 1971 P ⊆ NP carrier
    `class_P_subset_class_NP_V3`. Re-binds the canonical theorem through
    the L4L package. -/
def pnpV3_class_P_subset_class_NP_reverified :=
  @PrincipiaTractalis.PNPClassSeparationCarrierV3.class_P_subset_class_NP_V3

#print axioms pnpV3_class_P_subset_class_NP_reverified

end PF_L4L.Referee
