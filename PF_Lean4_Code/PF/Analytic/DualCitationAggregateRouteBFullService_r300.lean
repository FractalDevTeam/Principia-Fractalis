/-
# r300: DUAL CITATION AGGREGATE FULL SERVICE — one aggregate input discharges BOTH the substrate-linkage Clay closure AND the Route B mathlib-native second front

★ 2026-08-20 r300 — extends r299's dual-citation aggregate from a
substrate-closure input carrying the Clay-Standard six-axis conjunction
(C'-layer route) to a FULL-SERVICE referee-facing input that also
discharges the r272 Route B mathlib-native RH front (E-layer statements
of r273's extended supreme capstone) from the SAME single input.

## Framework-first position

r273's five-layer extended supreme capstone kept two independent
substrate-closure routes AND a mathlib-native Route B second front on
literal `Complex.riemannZeta`:

- **C route (bulletproof)**: framework's substrate-linkage discharge.
- **E route (Route B)**: mathlib-native second front, previously
  requiring separate Dirichlet 1858 (r271) hypothesis and a certified
  positive Xi witness.

r299 unified the sixteen-variant honest-scope surface into ONE citable
aggregate (C'-layer route). r300 shows that same aggregate ALSO
discharges Route B — the aggregate's Dirichlet 1858 field (r275
refined power-series limit form) promotes to r271's abstract form via
the r275 Abel bridge, and the aggregate's Xi witness field (Platt 2011
= Xi_Positive_At_15 = 0 < Xi 15) specializes the Route B universal at
b := 15.

Consequence: ONE aggregate consumer inhabits ALL SIX layers of the
extended supreme capstone (A, B unconditional; C' via r299 primary
headline; D3 via aggregate's RH anchors; E via r300 bridges).

## What r300 delivers

- `aggregate_provides_dirichlet1858_r271_form` — aggregate → r271
  `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf` via r275
  Abel bridge.

- `aggregate_provides_zeta_half_re_neg` — aggregate →
  `(riemannZeta (1/2 : ℂ)).re < 0` via r272 +
  `aggregate_provides_dirichlet1858_r271_form`.

- `aggregate_provides_route_b_hardy_nonempty_at_15` — aggregate →
  `PositiveOnLineZetaZeroOrdinatesNonempty` via r272 specialized at
  b := 15 using the aggregate's Platt 2011 field
  (Xi_Positive_At_15 = 0 < Xi 15).

- `unified_clay_closure_and_route_b_via_dual_citation_aggregate_r300`
  — THE HEADLINE. From ONE aggregate input, derive the framework's
  Clay-Standard six-axis conjunction AND the Route B mathlib-native
  second front statements simultaneously.

## Reduction chain state at HEAD (after r300)

| Stage | Statement | Discharge |
|---|---|---|
| r299a | sixteen-variant surface → 1 citable aggregate input | 4 leaf projections + 4 route agreements + primary headline |
| r299b | supreme capstone extended v2 with C'-layer aggregate route | six-layer total position |
| **r300** | **aggregate discharges BOTH substrate-linkage Clay closure AND Route B mathlib-native second front from ONE input** | **3 route-B bridges + full-service headline; kernel-only** |

Framework's referee-facing surface at HEAD: ONE citable aggregate
input consumes the entire honest-scope substrate closure PLUS the
mathlib-native second front on literal `Complex.riemannZeta`.

Book anchors: Ch 20 § 20.4, Ch 21 § 4.1-4.2 canonical pair + § 6-7
empirical, Ch 34A § 34A.5. Paper `principia_fractalis_alpha_skeleton_
2026-07-13.pdf` § 6 Corollary 6.3.
-/

import PF.Analytic.UnifiedClayClosureDualCitationAggregate_r299
import PF.RouteBFactAViaNamedResiduals_r272
import PF.Dirichlet1858AbelBridge_r275

namespace PrincipiaTractalis.DualCitationAggregateRouteBFullService

open PrincipiaTractalis
open PrincipiaTractalis.UnifiedClayClosureDualCitationAggregate
open PrincipiaTractalis.UnifiedClayClosureViaDirichlet1858OriginalLectures
open PrincipiaTractalis.Dirichlet1858AbelBridge
open PrincipiaTractalis.DirichletEtaHalfBridge
open PrincipiaTractalis.RouteBFactAViaNamedResiduals
open PrincipiaTractalis.XiRealWitness

/-! ## §1 Aggregate → r271 Dirichlet 1858 abstract form. -/

/-- **`aggregate_provides_dirichlet1858_r271_form`** — the aggregate's
Dirichlet 1858 field promotes to r271's
`Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf` via the r275
Abel bridge.

The aggregate's `dirichlet1858_original_lectures` field is
definitionally equal (Iff.rfl per r298's
`dirichlet1858_original_iff_powerseries_limit`) to r275's
`Dirichlet1858_PowerSeriesLimit_EqualsProductForm`, which r275's
`dirichlet1858_via_abel_and_refined` composes unconditionally to
r271's abstract form. -/
theorem aggregate_provides_dirichlet1858_r271_form
    (h : ClayClosureBundleDualCitationAggregate) :
    Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf :=
  dirichlet1858_via_abel_and_refined h.dirichlet1858_original_lectures

/-! ## §2 Aggregate → (ζ(1/2)).re < 0. -/

/-- **`aggregate_provides_zeta_half_re_neg`** — the aggregate discharges
the r272 Route B sign statement `(riemannZeta (1/2 : ℂ)).re < 0`
directly from its Dirichlet 1858 field. Composes r300's r271-form
bridge with r272's `zeta_half_re_neg_via_dirichlet1858`. -/
theorem aggregate_provides_zeta_half_re_neg
    (h : ClayClosureBundleDualCitationAggregate) :
    (riemannZeta (1/2 : ℂ)).re < 0 :=
  zeta_half_re_neg_via_dirichlet1858 (aggregate_provides_dirichlet1858_r271_form h)

/-! ## §3 Aggregate → Route B RH atomic residual inhabited at b := 15. -/

/-- **`aggregate_provides_route_b_hardy_nonempty_at_15`** — the
aggregate discharges the r272 Route B RH atomic residual
`PositiveOnLineZetaZeroOrdinatesNonempty` by specializing the Route B
universal at b := 15, using the aggregate's Platt 2011 field
(`Platt2011_Rigorous_XiPositiveAt15_Verification := Xi_Positive_At_15
:= 0 < Xi 15`) as the certified positive Xi witness. Composes r300's
r271-form bridge with r272's `route_b_fact_a_via_named_residuals` at
b := 15 with `0 < 15` by `norm_num`. -/
theorem aggregate_provides_route_b_hardy_nonempty_at_15
    (h : ClayClosureBundleDualCitationAggregate) :
    HilbertPolyaPositiveReductionToCountability.PositiveOnLineZetaZeroOrdinatesNonempty :=
  route_b_fact_a_via_named_residuals
    (aggregate_provides_dirichlet1858_r271_form h)
    (by norm_num : (0 : ℝ) < 15)
    h.platt2011_rigorous_verified

/-! ## §4 THE HEADLINE — aggregate discharges Clay closure AND Route B from ONE input. -/

/-- **★★★★★★★★★★★★★★★★★★★★★★★★ (r300) UNIFIED CLAY CLOSURE AND ROUTE B VIA DUAL-CITATION AGGREGATE ★★★★★★★★★★★★★★★★★★★★★★★★** —
from ONE citable aggregate input, derive BOTH:

1. The framework's substrate-linkage Clay-Standard six-axis
   conjunction on PF-substrate encodings (via r299's primary
   headline).

2. The r272 Route B mathlib-native second front on literal
   `Complex.riemannZeta`:
     · `(riemannZeta (1/2 : ℂ)).re < 0` (via r300 § 2 bridge).
     · `PositiveOnLineZetaZeroOrdinatesNonempty` (via r300 § 3 bridge
        at b := 15 with the aggregate's Platt 2011 Xi witness).

The framework's referee-facing surface at HEAD as ONE citable input
consuming the ENTIRE honest-scope substrate closure PLUS the
mathlib-native second front. -/
theorem unified_clay_closure_and_route_b_via_dual_citation_aggregate_r300
    (h : ClayClosureBundleDualCitationAggregate) :
    -- (1) Substrate-linkage Clay-Standard six-axis conjunction.
    (PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard ∧
     PF.Referee.StandardClayStatements.Clay_PvsNP_Standard
       PF.Referee.PNPCapstoneTypedBridge.PF_ComplexityEncoding ∧
     PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard
       PF.NavierStokes.NSPDETypedUpgradeV2.PF_NS3DEncodingV2 ∧
     PF.Referee.StandardClayStatements.Clay_YangMillsMassGap_Standard
       PrincipiaTractalis.YangMills.Bridge5_YM_SubstrateDischarge.PF_YMEncodingBridge5 ∧
     PF.Referee.StandardClayStatements.Clay_BSD_Standard
       PF.Referee.BSDCapstoneTypedBridgeV5.PF_BSDEncodingV5 ∧
     PF.Referee.StandardClayStatements.Clay_Hodge_Standard
       PF.Referee.HodgeCapstoneTypedBridge.PF_HodgeEncoding) ∧
    -- (2) Route B mathlib-native second front.
    (riemannZeta (1/2 : ℂ)).re < 0 ∧
    HilbertPolyaPositiveReductionToCountability.PositiveOnLineZetaZeroOrdinatesNonempty :=
  ⟨unified_clay_closure_via_dual_citation_aggregate_r299 h,
   aggregate_provides_zeta_half_re_neg h,
   aggregate_provides_route_b_hardy_nonempty_at_15 h⟩

/-! ## §5 Axiom checks. -/

#print axioms
  PrincipiaTractalis.DualCitationAggregateRouteBFullService.aggregate_provides_dirichlet1858_r271_form
#print axioms
  PrincipiaTractalis.DualCitationAggregateRouteBFullService.aggregate_provides_zeta_half_re_neg
#print axioms
  PrincipiaTractalis.DualCitationAggregateRouteBFullService.aggregate_provides_route_b_hardy_nonempty_at_15
#print axioms
  PrincipiaTractalis.DualCitationAggregateRouteBFullService.unified_clay_closure_and_route_b_via_dual_citation_aggregate_r300

end PrincipiaTractalis.DualCitationAggregateRouteBFullService
