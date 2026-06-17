/-
# PF.Referee.BSDSubstrateScopeAccountability

★★★★★ 2026-06-17 — UNASSAILABILITY: BIRCH–SWINNERTON-DYER SCOPE ACCOUNTABILITY ★★★★★

The framework's BSD V5 discharge proves
`Clay_BSD_Standard PF_BSDEncodingV5` axiom-free, but the equality
`algebraicRankV5 E = analyticRankV5 E` is `rfl`-provable by construction:
both projections are defined as the same case-split function
`manuscriptRankV5`. This is the framework's substrate-level encoding of
the BSD content; it is NOT independent computation of the Mordell–Weil
rank and the analytic order at `s = 1`.

This file consolidates the substrate-vs-literal-Clay BSD distinction
into a tighter referee-readable point, parallel to the Hodge, NS, and
YM accountability files.

## What is proven

  `PF_BSD_capstone_yields_Clay_BSD_standardV5 :
     Clay_BSD_Standard PF_BSDEncodingV5`

  Bridge V5 instantiates `StandardBSDEncoding` with:

    * `EllipticCurve  := WeierstrassCurve ℚ`  (mathlib substrate).
    * `algebraicRank  := manuscriptRankV5`
    * `analyticRank   := manuscriptRankV5`

  The Clay form `∀ E, analyticRank E = algebraicRank E` is provable
  by `rfl` since both projections are the same function.

  `manuscriptRankV5 : WeierstrassCurve ℚ → ℕ` is a case-split function
  returning published-discharged rank values for 20 specific curves
  (5 rank-0 CM curves, 13 rank-1 Heegner cohort, E_389a1 rank-2,
  E_rank_three rank-3) and `0` for every other curve.

## What is NOT proven

The literal Clay Birch–Swinnerton-Dyer statement asks: for every
elliptic curve `E` over `ℚ`, does
  ord_{s=1} L(E, s) = rank E(ℚ)
hold, where the left side is computed from the L-function and the right
side is the Mordell–Weil rank of the rational points?

Three structural gaps separate V5 from the literal Clay statement:

  (G1) Algebraic and analytic rank are projected through the SAME
       function —
       `algebraicRankV5 = analyticRankV5 = manuscriptRankV5`. The
       Clay statement asks whether two INDEPENDENTLY DEFINED quantities
       agree; V5 makes them definitionally equal by construction. The
       equality `algebraicRankV5 E = analyticRankV5 E` is `rfl`, not
       a consequence of computing the two sides separately and
       observing agreement.

  (G2) For curves outside the 20-curve case-split set,
       `manuscriptRankV5 E = 0` — which is incorrect for any elliptic
       curve in `WeierstrassCurve ℚ` whose actual Mordell–Weil rank
       is non-zero and which is not one of the 14 rank-≥-1 cataloged
       curves. The Clay equality `0 = 0` holds for such curves
       trivially; the LITERAL rank-equality with the actual rank does
       not.

  (G3) The 20 catalog values are EXTERNAL knowledge encoded as a
       case-split. Sources:
         * E_rank_zero, E_36a1, E_49a1, E_121b1, E_144a1 — Coates–Wiles
           1977 + CM generalisations.
         * E_rank_one + 12 Heegner cohort members
           (37a1, 43a1, 53a1, 61a1, 79a1, 83a1, 89a1, 91a1, 101a1,
           102a1, 106a1, 131a1, 141a1) — Gross–Zagier 1986 +
           Kolyvagin 1990 + Heegner-point cascade.
         * E_389a1 — Bhargava–Skinner–Zhang 2014 + Skinner–Urban.
         * E_rank_three (5077a1) — higher-rank Kolyvagin (encoded,
           speculative).
       Each is a typed substrate-level surfacing of the published
       discharge, not an independent first-principles derivation.

## What this file delivers

  * `PF_substrate_BSD_clay_witness` — the existing axiom-free V5 BSD
    discharge as a single citable export.
  * `PF_substrate_BSD_ranks_share_projection` — typed witness that
    both rank projections are the same function (G1).
  * `PF_substrate_BSD_default_residual_is_zero` — typed witness that
    the default case-split branch returns `0` (G2).
  * `PF_substrate_BSD_catalog_size_is_20` — typed bound on the
    catalog size (G3).
  * `PF_substrate_BSD_scope_capstone` — single citable theorem
    packaging the substrate-level discharge with the three gap markers.

No new mathematical content; V5 BSD discharge unchanged. What is new is
mechanical referee-readability of the rank-projection-shape, default-
zero, and 20-curve-case-split scope at the typed-Prop level.

ZERO project axioms. Kernel axioms only.
-/

import PF.Referee.BSDCapstoneTypedBridgeV5
import PF.Referee.StandardClayStatements
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

namespace PF.Referee.BSDSubstrateScopeAccountability

open PF.Referee.BSDCapstoneTypedBridgeV5
open PrincipiaTractalis
open PrincipiaTractalis.BSDGaloisPairConcordance
open PrincipiaTractalis.BSD_MultiCMRankZeroBatch
open PrincipiaTractalis.BSDRankThreeCurveFramework

/-! ## §1 — V5 substrate witness (what IS proven) -/

/-- **★ The existing V5 BSD substrate discharge, single-citation
    export ★** — `Clay_BSD_Standard PF_BSDEncodingV5` holds axiom-free.

    This is `PF_BSD_capstone_yields_Clay_BSD_standardV5` re-exported
    under the accountability namespace for citability alongside the
    gap markers in §2. -/
theorem PF_substrate_BSD_clay_witness :
    PF.Referee.StandardClayStatements.Clay_BSD_Standard
      PF_BSDEncodingV5 :=
  PF_BSD_capstone_yields_Clay_BSD_standardV5

/-! ## §2 — Substrate-vs-literal-Clay gap markers (what is NOT proven) -/

/-- **(G1) Both rank projections share the same `manuscriptRankV5`
    function.**

    `PF_BSDEncodingV5.algebraicRank = PF_BSDEncodingV5.analyticRank =
     manuscriptRankV5`.

    The Clay equality `analyticRank = algebraicRank` is `rfl`-provable
    on V5 because both sides are the same function — NOT because the
    Mordell–Weil rank and the analytic order at `s = 1` are computed
    independently and observed to agree. -/
def BSD_ranks_share_projection : Prop :=
  PF_BSDEncodingV5.algebraicRank = manuscriptRankV5 ∧
  PF_BSDEncodingV5.analyticRank = manuscriptRankV5 ∧
  PF_BSDEncodingV5.algebraicRank = PF_BSDEncodingV5.analyticRank

theorem BSD_ranks_share_projection_holds :
    BSD_ranks_share_projection :=
  ⟨rfl, rfl, rfl⟩

/-- **(G2) Default case-split branch returns 0.**

    The case-split `manuscriptRankV5` returns 0 for any
    `WeierstrassCurve ℚ` that is not one of the 20 cataloged curves.
    On such curves, the Clay equality reduces to `0 = 0` regardless
    of the curve's actual Mordell–Weil rank or analytic order at
    `s = 1`. -/
def BSD_default_residual_is_zero : Prop :=
  ∀ E : WeierstrassCurve ℚ,
    E ≠ E_rank_zero → E ≠ E_36a1 → E ≠ E_49a1 →
    E ≠ E_121b1 → E ≠ E_144a1 →
    E ≠ E_rank_one →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE53a1.E_53a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE61a1.E_61a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE79a1.E_79a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE83a1.E_83a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE89a1.E_89a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE101a1.E_101a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE102a1.E_102a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE106a1.E_106a1 →
    E ≠ PrincipiaTractalis.BSD_Rank2AttemptE389a1.E_389a1 →
    E ≠ E_rank_three →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE91a1.E_91a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE131a1.E_131a1 →
    E ≠ PrincipiaTractalis.BSD_HeegnerRank1ProofE141a1.E_141a1 →
    manuscriptRankV5 E = 0

theorem BSD_default_residual_is_zero_holds :
    BSD_default_residual_is_zero := by
  intro E h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
  unfold manuscriptRankV5
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

/-- **(G3) Catalog cardinality.**

    The V5 case-split catalogs exactly 20 distinct curves. This Prop
    records the catalog as a typed enumerated list. -/
def BSD_catalog_curves : List (WeierstrassCurve ℚ) :=
  [E_rank_zero, E_36a1, E_49a1, E_121b1, E_144a1,
   E_rank_one,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1.E_43a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE53a1.E_53a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE61a1.E_61a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE79a1.E_79a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE83a1.E_83a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE89a1.E_89a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE101a1.E_101a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE102a1.E_102a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE106a1.E_106a1,
   PrincipiaTractalis.BSD_Rank2AttemptE389a1.E_389a1,
   E_rank_three,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE91a1.E_91a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE131a1.E_131a1,
   PrincipiaTractalis.BSD_HeegnerRank1ProofE141a1.E_141a1]

theorem BSD_catalog_size_is_20 :
    BSD_catalog_curves.length = 20 := by
  unfold BSD_catalog_curves
  rfl

/-! ## §3 — Single referee-readable scope capstone -/

/-- **★★★★★ BSD SUBSTRATE-VS-LITERAL-CLAY SCOPE CAPSTONE ★★★★★** —

    The single citable referee-reading point for the framework's
    Birch–Swinnerton-Dyer claim:

      (A) `Clay_BSD_Standard PF_BSDEncodingV5` holds axiom-free.
      (B) Both rank projections share the same `manuscriptRankV5`
          function; the equality is `rfl` by construction, not by
          independent computation of Mordell–Weil rank and analytic
          order.
      (C) For curves outside the 20-curve catalog,
          `manuscriptRankV5 E = 0`; the Clay equality reduces to
          `0 = 0`, which is correct only when the actual rank is 0.
      (D) The catalog size is 20.

    What this theorem ESTABLISHES (mechanically, at the typed-Prop
    level): the framework's BSD discharge is a substrate-level
    closure on a 20-curve case-split catalog with a default-zero
    residual, NOT an independent computational verification of
    `ord_{s=1} L(E, s) = rank E(ℚ)` for every elliptic curve over ℚ. -/
theorem PF_substrate_BSD_scope_capstone :
    -- (A) Substrate-level Clay_BSD_Standard.
    PF.Referee.StandardClayStatements.Clay_BSD_Standard
      PF_BSDEncodingV5 ∧
    -- (B) Ranks share the same projection function.
    BSD_ranks_share_projection ∧
    -- (C) Default branch returns 0 outside the catalog.
    BSD_default_residual_is_zero ∧
    -- (D) Catalog size is 20.
    (BSD_catalog_curves.length = 20) :=
  ⟨PF_substrate_BSD_clay_witness,
   BSD_ranks_share_projection_holds,
   BSD_default_residual_is_zero_holds,
   BSD_catalog_size_is_20⟩

/-! ## §4 — Honest-scope marker -/

/-- **Honest-scope marker** — this file consolidates the
    substrate-vs-literal-Clay BSD scope distinction into a
    referee-reading point parallel to the Hodge, NS, and YM
    accountability files. The V5 BSD discharge is unchanged; the
    rank-projection identification, default-zero residual, and
    20-curve catalog structure are now mechanically readable at the
    typed-Prop level alongside the discharge itself. -/
theorem PF_substrate_BSD_scope_honest_scope : True := trivial

end PF.Referee.BSDSubstrateScopeAccountability

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PF.Referee.BSDSubstrateScopeAccountability.PF_substrate_BSD_clay_witness
#print axioms
  PF.Referee.BSDSubstrateScopeAccountability.BSD_ranks_share_projection_holds
#print axioms
  PF.Referee.BSDSubstrateScopeAccountability.BSD_default_residual_is_zero_holds
#print axioms
  PF.Referee.BSDSubstrateScopeAccountability.BSD_catalog_size_is_20
#print axioms
  PF.Referee.BSDSubstrateScopeAccountability.PF_substrate_BSD_scope_capstone
#print axioms
  PF.Referee.BSDSubstrateScopeAccountability.PF_substrate_BSD_scope_honest_scope
