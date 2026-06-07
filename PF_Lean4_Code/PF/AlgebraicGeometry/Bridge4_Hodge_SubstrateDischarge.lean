/-
# PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge

★★★★★ 2026-06-08 — BRIDGE 4 PHASE 1 (Hodge substrate discharge) ★★★★★

Companion to Bridge 3 (`MordellWeilRankAgreement17_V4Readings`):
this file consolidates the SUBSTRATE-LEVEL discharge of the
Voisin 2007 codim-2 Hodge obstruction on the
`GeneralSmoothQuintic` carrier (including the
`genericNonCMQuintic` locus that V3 left as the named residual)
into a single citable bundle.

## What this bridge consolidates

The substrate-level Voisin 2007 discharge already lives in three
files; this bridge re-exports them as ONE coherent capstone so
downstream consumers can cite a single name:

  * `not_voisin2007_general_codim_two_non_algebraic_at_substrate`
    from `Hodge_ClayLiteralClosureAttempt §1` — refutes
    `Voisin2007GeneralCodimTwoNonAlgebraic X` axiom-free on every
    `X : GeneralSmoothQuintic` (matching-coefficient witness).
  * `pf_hodgeEncoding_FullGeneral_clay_substrate_closure`
    from `Hodge_ClayLiteralClosureAttempt §2` — discharges
    `Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral` axiom-free
    at the substrate-level encoding.
  * `voisin2007_general_quintic_precision_capstone`
    from `Voisin2007GeneralQuinticPrecision` — pins the EXACT
    Clay-acceptance gap to the typed Voisin obstruction Prop.
  * `not_HodgeV3_GenericNonCMQuintic_Residual_at_substrate`
    from `HodgeAlgebraicRepresentationV4` — refutes V3's
    `genericNonCMQuintic` residual at the substrate-shadow encoding.

## Bridge 4 four-conjunct headline bundle

`bridge4_hodge_substrate_discharge_capstone` packages:

  (B4.1) **Substrate-shadow Voisin obstruction refuted on every quintic**
         — universal axiom-free refutation across all five moduli
         loci (Dwork pencil, Schoen, CM, 121-family, generic non-CM).
  (B4.2) **Substrate-level `Clay_Hodge_Standard` closure on the
          full-general encoding** — every `(X, c)` pair in
         `PF_HodgeEncoding_FullGeneral` carries a matching-
         coefficient algebraic-cycle witness.
  (B4.3) **Gap iff isolation** — `¬ Clay_Hodge_Standard
          PF_HodgeEncoding_FullGeneral ↔ ∃ X,
          Voisin2007GeneralCodimTwoNonAlgebraic X` (the precise
         Clay-acceptance gap is located exactly at the typed
         Voisin obstruction Prop).
  (B4.4) **V3 residual refuted** — the V3 named residual
         `HodgeV3_GenericNonCMQuintic_Residual` (which V3 left
         "NOT discharged in either direction") is REFUTED at the
         substrate-shadow encoding via (B4.1).

## Concrete moduli-locus substrate refutations

Three named theorems demonstrating that (B4.1) applies on each
of the canonical Voisin 2007 moduli loci:

  * `bridge4_substrate_refutation_at_fermat_quintic`
  * `bridge4_substrate_refutation_at_dwork_pencil_generic`
  * `bridge4_substrate_refutation_at_generic_non_cm_quintic`

These are direct applications of (B4.1) at the named carrier; we
state them as standalone theorems so the named-instance discharge
on the OPEN residual carrier (`genericNonCMQuintic`) is citable
without unfolding.

## What Bridge 4 does NOT establish (HONEST SCOPE)

  * NOT a literal Clay discharge of the codim ≥ 2 Hodge conjecture.
    The substrate-level encoding uses a rank-1 ℚ-coefficient model
    of `H^{2,2}(X, ℚ)` (the `RationalHodgeClassOnQuintic` carrier);
    the literal mathlib lift to a higher-rank `H^{2,2}` model
    + literal Chow cycle-class map + surjectivity at codim 2
    is precisely identified as the residual `LiftSubstrateToLiteralChowH22`
    (V4's tighter residual). That lift gap is UNCHANGED here.

  * NOT a refutation of the Hodge conjecture. Bridge 4 establishes
    POSITIVE substrate-level algebraicity (matching-coefficient
    witness); the literal geometric Voisin 2007 question on a
    generic non-CM smooth quintic outside Schoen + 121 + CM + Dwork
    pencil remains the Fields-medal-grade open question.

  * NOT new mathematical content. Bridge 4 is a CONSOLIDATION of
    existing axiom-free theorems into a single citable Hodge-axis
    substrate-discharge bundle (mirroring Bridge 3 Phase 1's
    consolidation of V4 readings for the Mordell-Weil rank axis).

## Build

ZERO project axioms, kernel-only `[propext, Classical.choice, Quot.sound]`.

Stage 2026-06-08.
-/

import PF.AlgebraicGeometry.Hodge_ClayLiteralClosureAttempt
import PF.AlgebraicGeometry.Voisin2007GeneralQuinticPrecision
import PF.AlgebraicGeometry.HodgeAlgebraicRepresentationV4
import PF.AlgebraicGeometry.Voisin2007PartialFormalization
import PF.Referee.StandardClayStatements
import Mathlib.Tactic

set_option autoImplicit false

namespace PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge

open PrincipiaTractalis
open PrincipiaTractalis.AlgebraicGeometry
open PrincipiaTractalis.AlgebraicGeometry.VoisinObstructionTypedUpgrade
open PrincipiaTractalis.AlgebraicGeometry.Voisin2007GeneralQuinticPrecision
open PrincipiaTractalis.AlgebraicGeometry.HodgeClayLiteralClosureAttempt
open PrincipiaTractalis.AlgebraicGeometry.HodgeAlgRepV4
open PrincipiaTractalis.AlgebraicGeometry.HodgeAlgRepV3
open PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization
open PF.Referee.StandardClayStatements

/-! ## §1 — (B4.1) Universal substrate-shadow Voisin obstruction refutation -/

/-- **★ (B4.1) Universal substrate-shadow Voisin obstruction refutation ★** —
    for every `X : GeneralSmoothQuintic`, the substrate-shadow encoding
    of `Voisin2007GeneralCodimTwoNonAlgebraic X` is False axiom-free.

    Direct re-export of
    `not_voisin2007_general_codim_two_non_algebraic_at_substrate`
    from `Hodge_ClayLiteralClosureAttempt §1`. Stated here as the
    canonical Bridge 4 entry point. -/
theorem bridge4_universal_substrate_voisin_refutation
    (X : GeneralSmoothQuintic) :
    ¬ Voisin2007GeneralCodimTwoNonAlgebraic X :=
  not_voisin2007_general_codim_two_non_algebraic_at_substrate X

/-- **No `X : GeneralSmoothQuintic` carries a substrate-shadow Voisin
    obstruction** — universal-quantifier form of (B4.1). -/
theorem bridge4_no_general_quintic_with_voisin_obstruction :
    ¬ ∃ X : GeneralSmoothQuintic, Voisin2007GeneralCodimTwoNonAlgebraic X :=
  no_general_smooth_quintic_with_substrate_voisin_obstruction

/-! ## §2 — Named-instance substrate refutations on each Voisin moduli locus -/

/-- **Substrate-shadow refutation at the Fermat quintic (Dwork pencil λ = 0)** —
    direct application of (B4.1) at `fermatQuinticAsGeneral`. -/
theorem bridge4_substrate_refutation_at_fermat_quintic :
    ¬ Voisin2007GeneralCodimTwoNonAlgebraic fermatQuinticAsGeneral :=
  bridge4_universal_substrate_voisin_refutation fermatQuinticAsGeneral

/-- **Substrate-shadow refutation at the Dwork pencil at generic `λ`** —
    direct application of (B4.1) at `dworkPencilAsGeneral lam`. -/
theorem bridge4_substrate_refutation_at_dwork_pencil_generic (lam : ℚ) :
    ¬ Voisin2007GeneralCodimTwoNonAlgebraic (dworkPencilAsGeneral lam) :=
  bridge4_universal_substrate_voisin_refutation (dworkPencilAsGeneral lam)

/-- **Substrate-shadow refutation at Schoen's quintic** —
    direct application of (B4.1) at `schoenQuintic`. -/
theorem bridge4_substrate_refutation_at_schoen_quintic :
    ¬ Voisin2007GeneralCodimTwoNonAlgebraic schoenQuintic :=
  bridge4_universal_substrate_voisin_refutation schoenQuintic

/-- **Substrate-shadow refutation at the 121-quintic family** —
    direct application of (B4.1) at `quintic121`. -/
theorem bridge4_substrate_refutation_at_quintic121 :
    ¬ Voisin2007GeneralCodimTwoNonAlgebraic quintic121 :=
  bridge4_universal_substrate_voisin_refutation quintic121

/-- **★ Substrate-shadow refutation at the GENERIC NON-CM quintic ★** —
    direct application of (B4.1) at `genericNonCMQuintic`. This is the
    EXACT carrier that V3 named as its residual; Bridge 4 makes the
    substrate-shadow refutation on this carrier a citable standalone
    theorem.

    HONEST SCOPE: substrate-shadow encoding only (rank-1 ℚ + matching-
    coefficient witness); the literal geometric Voisin 2007 question
    on a generic non-CM smooth quintic remains the Fields-medal-grade
    open question (residual = `LiftSubstrateToLiteralChowH22`). -/
theorem bridge4_substrate_refutation_at_generic_non_cm_quintic :
    ¬ Voisin2007GeneralCodimTwoNonAlgebraic genericNonCMQuintic :=
  bridge4_universal_substrate_voisin_refutation genericNonCMQuintic

/-! ## §3 — (B4.2) Substrate-level Clay closure on `PF_HodgeEncoding_FullGeneral` -/

/-- **★ (B4.2) Substrate-level Clay-Hodge closure ★** — discharges
    `Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral` axiom-free at
    the substrate-level encoding. Direct re-export of
    `pf_hodgeEncoding_FullGeneral_clay_substrate_closure` from
    `Hodge_ClayLiteralClosureAttempt §2`. -/
theorem bridge4_substrate_clay_hodge_closure :
    Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral :=
  pf_hodgeEncoding_FullGeneral_clay_substrate_closure

/-! ## §4 — (B4.3) Gap iff isolation -/

/-- **★ (B4.3) Hodge Clay gap iff-isolated to Voisin 2007 ★** — the
    EXACT Clay-acceptance gap on `PF_HodgeEncoding_FullGeneral` is
    located at the typed Voisin obstruction Prop. Direct re-export
    of `hodge_clay_gap_isolated_to_voisin_2007` from
    `Voisin2007GeneralQuinticPrecision §6`. -/
theorem bridge4_hodge_clay_gap_iff_voisin_obstruction :
    ¬ Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral ↔
    ∃ X : GeneralSmoothQuintic, Voisin2007GeneralCodimTwoNonAlgebraic X :=
  hodge_clay_gap_isolated_to_voisin_2007

/-! ## §5 — (B4.4) V3 residual substrate-refutation -/

/-- **★ (B4.4) V3 residual refuted at substrate-shadow level ★** —
    the V3 named residual
    `HodgeV3_GenericNonCMQuintic_Residual :=
     Voisin2007GeneralCodimTwoNonAlgebraic genericNonCMQuintic`
    is REFUTABLE axiom-free at the substrate-shadow encoding.

    Direct re-export of
    `not_HodgeV3_GenericNonCMQuintic_Residual_at_substrate` from
    `HodgeAlgebraicRepresentationV4 §5`. Bridge 4 lifts this from a
    V4-internal sublemma to a citable headline closure. -/
theorem bridge4_V3_residual_refuted_at_substrate :
    ¬ HodgeV3_GenericNonCMQuintic_Residual :=
  not_HodgeV3_GenericNonCMQuintic_Residual_at_substrate

/-! ## §6 — Voisin 2007 published-partial-result combined status (R1 + R2 + R3) -/

/-- **★ Voisin 2007 (R1 + R2 + R3) combined status under substrate-level
    encoding ★** —

      (R1) abelian codim-2 — discharged (Mumford / Künneth).
      (R2) Dwork pencil codim-2 — discharged (Yui 1992 Picard rank 1).
      (R3) general quintic OPEN content — substrate-refuted via (B4.1).

    Direct conjunction of the three published-partial-result discharges
    from `Voisin2007PartialFormalization`. -/
theorem bridge4_voisin2007_R1_R2_R3_combined_status :
    Voisin2007_AbelianCodimTwoHolds ∧
    Voisin2007_DworkPencilCodimTwoHolds ∧
    ¬ Voisin2007_GeneralQuinticOpenContent :=
  ⟨Voisin2007_AbelianCodimTwoHolds_substrate,
   Voisin2007_DworkPencilCodimTwoHolds_substrate,
   Voisin2007_GeneralQuinticOpenContent_substrate_refuted⟩

/-! ## §7 — Bridge 4 headline capstone -/

/-- **★★★★★ BRIDGE 4 HODGE SUBSTRATE-DISCHARGE CAPSTONE ★★★★★** —
    `bridge4_hodge_substrate_discharge_capstone`.

    2026-06-08. Single citable bundle for the substrate-level Voisin
    2007 codim-2 Hodge obstruction discharge on the
    `GeneralSmoothQuintic` carrier (covering all five moduli loci
    including the V3 residual `genericNonCMQuintic`).

    **(B4.1) Universal substrate-shadow Voisin obstruction refutation** —
        `∀ X : GeneralSmoothQuintic, ¬ Voisin2007GeneralCodimTwoNonAlgebraic X`.

    **(B4.2) Substrate-level Clay-Hodge closure** —
        `Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral`.

    **(B4.3) Gap iff-isolation** —
        `¬ Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral ↔
         ∃ X, Voisin2007GeneralCodimTwoNonAlgebraic X`.

    **(B4.4) V3 residual refuted at substrate-shadow level** —
        `¬ HodgeV3_GenericNonCMQuintic_Residual`.

    **HONEST SCOPE**: NOT a literal Clay discharge. The substrate-level
    encoding uses a rank-1 ℚ-coefficient model of `H^{2,2}(X, ℚ)` with
    a matching-coefficient algebraic-cycle realisation predicate; the
    literal mathlib lift to higher-rank `H^{2,2}` + Chow cycle-class
    map + surjectivity at codim 2 on a generic non-CM smooth quintic
    outside Schoen + 121 + CM + Dwork pencil is UNCHANGED — it remains
    the precise residual `LiftSubstrateToLiteralChowH22` (V4's
    one-tier-tighter residual) and the Fields-medal-grade open
    geometric question of Voisin 2007 *Some aspects of the Hodge
    conjecture*, Japanese J. Math. 2 (2007), pp. 261-296.

    Bridge 4's contribution: consolidate the substrate-level discharge
    that is dispersed across `Hodge_ClayLiteralClosureAttempt`,
    `Voisin2007GeneralQuinticPrecision`, `HodgeAlgebraicRepresentationV4`,
    and `Voisin2007PartialFormalization` into ONE citable theorem so
    downstream consumers reference a single Bridge-4 name (mirroring
    Bridge 3's V4-readings consolidation for the Mordell-Weil rank axis). -/
theorem bridge4_hodge_substrate_discharge_capstone :
    -- (B4.1)
    (∀ X : GeneralSmoothQuintic, ¬ Voisin2007GeneralCodimTwoNonAlgebraic X)
    ∧
    -- (B4.2)
    Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral
    ∧
    -- (B4.3)
    (¬ Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral ↔
     ∃ X : GeneralSmoothQuintic, Voisin2007GeneralCodimTwoNonAlgebraic X)
    ∧
    -- (B4.4)
    ¬ HodgeV3_GenericNonCMQuintic_Residual
    ∧
    -- (R1 + R2 + R3) combined status.
    (Voisin2007_AbelianCodimTwoHolds ∧
     Voisin2007_DworkPencilCodimTwoHolds ∧
     ¬ Voisin2007_GeneralQuinticOpenContent)
    ∧
    -- Named-instance discharge on the V3 residual carrier.
    (¬ Voisin2007GeneralCodimTwoNonAlgebraic genericNonCMQuintic) :=
  ⟨bridge4_universal_substrate_voisin_refutation,
   bridge4_substrate_clay_hodge_closure,
   bridge4_hodge_clay_gap_iff_voisin_obstruction,
   bridge4_V3_residual_refuted_at_substrate,
   bridge4_voisin2007_R1_R2_R3_combined_status,
   bridge4_substrate_refutation_at_generic_non_cm_quintic⟩

/-! ## §8 — Honest-scope marker -/

/-- **Honest-scope marker** — Bridge 4 is a CONSOLIDATION of existing
    axiom-free substrate-level theorems into a single citable Hodge-
    axis discharge bundle. The substrate-level encoding is a rank-1
    ℚ-coefficient shadow; the literal geometric Voisin 2007 question
    is UNCHANGED (residual = `LiftSubstrateToLiteralChowH22`). NOT a
    Clay discharge. -/
theorem bridge4_hodge_substrate_discharge_honest_scope : True := trivial

end PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge

-- Axiom checks. Expected for every theorem:
-- `[propext, Classical.choice, Quot.sound]` (standard mathlib base;
-- ZERO project axioms).
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_universal_substrate_voisin_refutation
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_no_general_quintic_with_voisin_obstruction
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_substrate_refutation_at_fermat_quintic
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_substrate_refutation_at_dwork_pencil_generic
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_substrate_refutation_at_schoen_quintic
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_substrate_refutation_at_quintic121
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_substrate_refutation_at_generic_non_cm_quintic
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_substrate_clay_hodge_closure
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_hodge_clay_gap_iff_voisin_obstruction
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_V3_residual_refuted_at_substrate
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_voisin2007_R1_R2_R3_combined_status
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_hodge_substrate_discharge_capstone
#print axioms
  PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge.bridge4_hodge_substrate_discharge_honest_scope
