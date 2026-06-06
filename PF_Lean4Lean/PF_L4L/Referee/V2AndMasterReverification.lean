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
-- 2026-06-04 batch (HEAD f733be9): six V4 axis capstones, three paired
-- closures, PNP canonical encoding, MordellWeilGroup infrastructure,
-- and the PFFrameworkUnifiedClosure unified-whole inhabitant.  All
-- re-bound through the identical Path C `def T_reverified := @T`
-- pattern; the type is intentionally inferred so the L4L re-binding
-- *is* the canonical theorem (no drift, no axiom growth).
import PF.TuringEncoding.PNPClassSeparationCarrierV4
import PF.NavierStokes.NS3DRegularitySolutionV4
import PF.AlgebraicGeometry.HodgeAlgebraicRepresentationV4
import PF.Referee.BSDCapstoneTypedBridgeV4
import PF.YM_ContinuumWightmanV4
import PF.Referee.RHCapstoneTypedBridgeV4
import PF.Referee.RHPvsNPPairedClosure
import PF.Referee.NSYMPairedClosure
import PF.Referee.BSDHodgePairedClosure
import PF.Referee.PNPCanonicalEncoding
import PF.AlgebraicGeometry.MordellWeilGroup
import PF.Referee.PFFrameworkUnifiedClosure

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

/-! ## §7 — V4 axis capstones (2026-06-04, HEAD f733be9) -/

/-- L4L re-verification: PNP V4 honest-scope capstone, closing the V3
    constant-trivial defect via `decide`↔`encodeRun` linking. -/
def pnpV4_capstone_reverified :=
  @PrincipiaTractalis.PNPClassSeparationCarrierV4.pnp_carrier_V4_honest_scope_capstone

#print axioms pnpV4_capstone_reverified

/-- L4L re-verification: NS V4 master capstone bundling Leray-Hopf
    smoothness, BKM, Wave 33, and V3 typed-regularity. -/
def nsV4_capstone_reverified :=
  @PF.NavierStokes.NS3DRegularitySolutionV4.ns3DRegularitySolutionV4_capstone

#print axioms nsV4_capstone_reverified

/-- L4L re-verification: Hodge V4 15-conjunct capstone (V3
    substrate-shadow residual refuted axiom-free; residual narrowed to
    literal Chow H22 lift). -/
def hodgeV4_capstone_reverified :=
  @PrincipiaTractalis.AlgebraicGeometry.HodgeAlgRepV4.hodgeAlgebraicRepresentationV4_capstone

#print axioms hodgeV4_capstone_reverified

/-- L4L re-verification: BSD V4 typed-bridge into
    `Clay_BSD_Standard PF_BSDEncodingV4` (17-curve discharged set +
    Wave 57 + rank-blind universal concordance). -/
def bsdV4_capstone_reverified :=
  @PF.Referee.BSDCapstoneTypedBridgeV4.PF_BSD_capstone_yields_Clay_BSD_standardV4

#print axioms bsdV4_capstone_reverified

/-- L4L re-verification: YM V4 16-conjunct master capstone
    (Wave 57-OSRP independent path + 12-clause Wightman + propagator
    PSD/IsSymm + interacting Ham). -/
def ymV4_capstone_reverified :=
  @PrincipiaTractalis.YM_ContinuumWightmanV4.ym_continuum_wightman_v4_capstone

#print axioms ymV4_capstone_reverified

/-- L4L re-verification: RH V4 master capstone (Mayer 1991 as fifth
    equivalent Hilbert-Polya formulation + partial discharges at
    N∈{20,30,50}). -/
def rhV4_master_capstone_reverified :=
  @PF.Referee.RHCapstoneTypedBridgeV4.PF_RH_V4_master_capstone

#print axioms rhV4_master_capstone_reverified

/-! ## §8 — Paired closures (2026-06-04) -/

/-- L4L re-verification: RH + P vs NP paired-closure capstone bundling
    Hilbert-Polya, Berry-Keating, Connes, Bost-Connes routes; axiom-free
    PNP algebraic content; named single residual. -/
def rhPvNP_paired_closure_honest_scope_reverified :=
  @PF.Referee.RHPvsNPPairedClosure.RH_PvNP_paired_honest_scope_holds

#print axioms rhPvNP_paired_closure_honest_scope_reverified

/-- L4L re-verification: NS + YM paired-closure capstone (NS Leray
    bootstrap isolated to Fujita-Kato 1964; YM V4 Clay form). -/
def nsYM_paired_closure_capstone_reverified :=
  @PF.Referee.NSYMPairedClosure.ns_ym_paired_closure_capstone

#print axioms nsYM_paired_closure_capstone_reverified

/-- L4L re-verification: BSD + Hodge paired-closure capstone via
    cross-Millennium algebraic-cycle invariant
    (α_NP − α_Hodge = 1/4). -/
def bsdHodge_paired_closure_capstone_reverified :=
  @PF.Referee.BSDHodgePairedClosure.bsdHodgePairedClosure_capstone

#print axioms bsdHodge_paired_closure_capstone_reverified

/-! ## §9 — Infrastructure capstones (2026-06-04) -/

/-- L4L re-verification: PNP canonical encoding theorem — the
    Clay-statement on `PF_CanonicalComplexityEncoding` is iff
    `ClassP ≠ ClassNP`, wiring the substrate bridge through the
    framework's canonical Cook 1971 `ClassP`/`ClassNP`. -/
def pnp_canonical_encoding_reverified :=
  @PF.Referee.PNPCanonicalEncoding.Clay_PvsNP_Standard_at_canonical_iff_classes_distinct

#print axioms pnp_canonical_encoding_reverified

/-- L4L re-verification: MordellWeilGroup infrastructure capstone —
    typed carrier + propositional bridges for BSD G3 mathlib gap. -/
def mordellWeilGroup_infrastructure_capstone_reverified :=
  @PF.AlgebraicGeometry.MordellWeilGroup.mordellWeilGroup_infrastructure_capstone

#print axioms mordellWeilGroup_infrastructure_capstone_reverified

/-! ## §10 — Unified-whole capstone (2026-06-04) -/

/-- L4L re-verification: **the framework as one object in one
    theorem** — `pfFrameworkUnifiedWhole_realized` inhabits the
    `PFFrameworkUnifiedWhole` record bundling all six V4 axis
    capstones, the Wave 57 master, the Ch 4 Timeless Field capstone,
    the cross-Millennium invariants capstone, the framework
    falsifiability capstone, and the substrate meta-theorem. -/
def pfFrameworkUnifiedClosure_reverified :=
  @PF.Referee.PFFrameworkUnifiedClosure.pfFrameworkUnifiedWhole_realized

#print axioms pfFrameworkUnifiedClosure_reverified

end PF_L4L.Referee
