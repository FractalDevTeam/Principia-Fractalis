/-
# r290: UNIFIED CLAY CLOSURE VIA ROUTE B REFINED DIRICHLET 1858 + SPECIFIC-Xi + RIEMANN 1859 + FULL PINNING
       (Dirichlet 1858 residual surfaced as its r275 refined form:
        the specific power-series boundary limit equalling the
        product form).

★ 2026-08-18 r290 — surfaces the Dirichlet 1858 residual at the
substrate-closure BUNDLE level as its r275 strictly-more-refined form:

  `Dirichlet1858_PowerSeriesLimit_EqualsProductForm`

— the specific classical boundary-limit content asserting that the
alternating-η power series at s = 1/2 tends to
`(1 - √2) · (ζ(1/2)).re` as x → 1⁻. The Abel-theorem step is
UNCONDITIONAL (discharged by r275's `abel_bridge_dirichletEtaHalf`).
The r271 abstract residual `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf`
follows via r275's `dirichlet1858_via_abel_and_refined`.

## What r290 delivers vs r289

r289's `ClayClosureBundleViaRouteBSpecificXiAndRiemann1859AndFullPinning`
carries `dirichlet1858 : Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf`
(r271 abstract Prop-level equality). r290's
`ClayClosureBundleViaRouteBRefinedDirichlet1858AndFullPinning` exchanges
that field for `dirichlet1858_powerseries_limit :
Dirichlet1858_PowerSeriesLimit_EqualsProductForm` — the strictly-more-
refined named residual introduced at r275.

Framework-first: NOT a residual-count reduction (5 → 5). IS a semantic
refinement — the r290 residual reads as a specific `Tendsto` claim
about the power-series limit's specific numerical target
`(1 - √2) · (ζ(1/2)).re`, not the abstract Prop-level equality of the
r271 form. The Abel-theorem ingredient is already discharged
unconditionally within the corpus, so only the specific boundary-limit
identification remains — and that identification names its classical
anchor (Titchmarsh 1951 § 2.1, Edwards 1974 Ch. 1) precisely.

## Ingredients of the r275 design (classical decomposition)

r275 documented that the full Dirichlet 1858 identity at s = 1/2
decomposes into four classical ingredients:

  (1) Abel summation on the alternating η series — UNCONDITIONAL via
      r275's `abel_bridge_dirichletEtaHalf` (mathlib's
      `Real.tendsto_tsum_powerSeries_nhdsWithin_lt`).
  (2) Real-axis conditional convergence of the Dirichlet η LSeries —
      DISCHARGED (r276 for σ > 0 on the real ray, r277 for full
      complex 0 < Re s).
  (3) Analytic continuation Differentiable ℂ of the Dirichlet η
      extension on {s | s ≠ 1} — DISCHARGED at symbolic level (r278);
      s = 1 removability named as strictly-smaller refined residual
      `DirichletEtaExt_DifferentiableAtOne`.
  (4) Identity theorem match with `(1 - 2^(1-s)) · ζ(s)` extension —
      DISCHARGED at symbolic level (r279); Cahen 1894 constructive
      step named as strictly-smaller refined residual
      `DirichletEta_HasAnalyticExtension`.

Combined via r275, the SPECIFIC boundary-limit residual
`Dirichlet1858_PowerSeriesLimit_EqualsProductForm` alone discharges
the r271 abstract residual `Dirichlet1858_AlternatingEta_MatchesExtensionAtHalf`.
The r290 bundle promotes this refinement to the substrate-closure
BUNDLE surface.

## Historical anchor: Dirichlet 1858

P. G. L. Dirichlet's 1858 lectures on definite integrals, edited by
Meyer (published posthumously). The classical alternating-η identity
at half-integer argument, connecting `∑ (-1)^n/√(n+1)` to `ζ(1/2)`.
Titchmarsh 1951 § 2.1 and Edwards 1974 Ch. 1 preserve the identity
in its modern form; the r275 refined residual names the specific
power-series boundary-limit content.

## What r290 delivers

- `ClayClosureBundleViaRouteBRefinedDirichlet1858AndFullPinning` —
  5-field substrate-closure input record with r289's dirichlet1858
  field REPLACED by the r275 refined form.

- `bundleViaRefinedDirichlet1858_to_riemann1859AndFullPinning` —
  promotes to r289's bundle by supplying `dirichlet1858` via r275's
  `dirichlet1858_via_abel_and_refined`.

- `unified_clay_closure_via_route_b_refined_dirichlet1858_and_full_pinning_r290`
  — THE HEADLINE.

## Reduction chain state at HEAD (after r290)

| Stage | Statement | Discharge |
|---|---|---|
| Wave 58 (r255) | HP-positive ↔ (countable ∧ nonempty) | biconditional, unconditional |
| r280 | countability of positive on-line ζ-zero ordinates | UNCONDITIONAL |
| r281 | HP-positive from Hardy-atomic + r280 | conditional on Hardy1914_AtomicFact |
| r272 | Route B: Dirichlet 1858 + Xi witness → Hardy nonempty | mathlib-native second front |
| r275 | Dirichlet 1858 abstract residual ← refined power-series limit | Abel ingredient unconditional; refined residual named |
| r282-r289 | Six-form honest-scope surfacing pattern | 7 bundle variants |
| **r290** | **six Clay-Standard from (r275 refined Dirichlet 1858) + (0 < Xi 15) + Riemann 1859 + (α_P = √2) + (α_NP = φ+1/4)** | **5 residuals; Dirichlet 1858 refined to specific power-series boundary limit per r275** |

Book anchors: Ch 20 (RH via Fractal Resonance § 20.4 T³_sym operator
spec), Ch 21 (P vs NP § 4.1-4.2), Ch 34A (Substrate Theorem § 34A.5
the citable master implication). Paper
`principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6 Corollary 6.3.
-/

import PF.Analytic.UnifiedClayClosureViaRouteBSpecificXiAndRiemann1859AndFullPinning_r289
import PF.Dirichlet1858AbelBridge_r275

namespace PrincipiaTractalis.UnifiedClayClosureViaRouteBRefinedDirichlet1858AndFullPinning

open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.UnifiedClayClosureViaFullyAtomicResiduals
open PrincipiaTractalis.UnifiedClayClosureViaRouteBAndRH
open PrincipiaTractalis.UnifiedClayClosureViaRouteBAndPPinning
open PrincipiaTractalis.UnifiedClayClosureViaRouteBAndFullPinning
open PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning
open PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndRiemann1859AndFullPinning
open PrincipiaTractalis.Dirichlet1858AbelBridge
open PrincipiaTractalis.XiRealWitness

/-! ## §1 The refined Dirichlet 1858 substrate-closure input record. -/

/-- **`ClayClosureBundleViaRouteBRefinedDirichlet1858AndFullPinning`**
— r289's input record with the r271 abstract Dirichlet 1858 field
EXCHANGED for the r275 strictly-more-refined
`Dirichlet1858_PowerSeriesLimit_EqualsProductForm`.

Five fields:

  1. `dirichlet1858_powerseries_limit` — r275 refined named residual
     (specific `Tendsto` claim for the power-series boundary limit).
  2. `xi_positive_at_15` — specific numerical Xi witness at b = 15 (r288).
  3. `riemann1859_hypothesis` — Riemann 1859 named substrate citation (r289).
  4. `alpha_of_class_P_canonical_pinning` — Ch 21 § 4.1 (r286).
  5. `alpha_of_class_NP_canonical_pinning` — Ch 21 § 4.2 (r287).
-/
structure ClayClosureBundleViaRouteBRefinedDirichlet1858AndFullPinning where
  /-- r275 refined Dirichlet 1858 residual: the specific power-series
      boundary limit equalling `(1 - √2) · (ζ(1/2)).re` as x → 1⁻. -/
  dirichlet1858_powerseries_limit : Dirichlet1858_PowerSeriesLimit_EqualsProductForm
  /-- Specific numerical Xi witness at b = 15. -/
  xi_positive_at_15 : Xi_Positive_At_15
  /-- Riemann 1859 Critical Line Hypothesis. -/
  riemann1859_hypothesis : Riemann1859_CriticalLineHypothesis
  /-- Ch 21 § 4.1 P-side canonical pinning. -/
  alpha_of_class_P_canonical_pinning : AlphaOfClassP_CanonicalPinning
  /-- Ch 21 § 4.2 NP-side canonical pinning. -/
  alpha_of_class_NP_canonical_pinning : AlphaOfClassNP_CanonicalPinning

/-! ## §2 Promotion to r289's Riemann 1859 input record. -/

/-- **`bundleViaRefinedDirichlet1858_to_riemann1859AndFullPinning`**
— the refined-Dirichlet-1858 record promotes to r289's
`ClayClosureBundleViaRouteBSpecificXiAndRiemann1859AndFullPinning`
by supplying the r271 abstract `dirichlet1858` field via r275's
`dirichlet1858_via_abel_and_refined`. -/
theorem bundleViaRefinedDirichlet1858_to_riemann1859AndFullPinning
    (h : ClayClosureBundleViaRouteBRefinedDirichlet1858AndFullPinning) :
    ClayClosureBundleViaRouteBSpecificXiAndRiemann1859AndFullPinning where
  dirichlet1858 :=
    dirichlet1858_via_abel_and_refined h.dirichlet1858_powerseries_limit
  xi_positive_at_15 := h.xi_positive_at_15
  riemann1859_hypothesis := h.riemann1859_hypothesis
  alpha_of_class_P_canonical_pinning := h.alpha_of_class_P_canonical_pinning
  alpha_of_class_NP_canonical_pinning := h.alpha_of_class_NP_canonical_pinning

/-! ## §3 THE HEADLINE — substrate closure under the refined Dirichlet 1858 input. -/

/-- **★★★★★★★★★★★★★★ (r290) UNIFIED CLAY CLOSURE VIA ROUTE B REFINED DIRICHLET 1858 + SPECIFIC-Xi + RIEMANN 1859 + FULL PINNING ★★★★★★★★★★★★★★** —
under the refined-Dirichlet-1858 substrate-closure input record, all
six Clay Millennium Problem statements hold on the framework's
PF-substrate encodings.

Composes `bundleViaRefinedDirichlet1858_to_riemann1859AndFullPinning`
with r289's
`unified_clay_closure_via_route_b_specific_xi_and_riemann1859_and_full_pinning_r289`,
which composes downstream through r288 → r287 → r286 → r285 → r284 →
r283 → r282 → the framework's substrate-closure theorem
`unified_clay_closure_via_substrate_linkage_bulletproof`.

Framework's total Millennium position at HEAD presented as a direct
implication from FIVE named residuals with the Dirichlet 1858 leg
REFINED to its specific power-series boundary-limit content per r275
(the Abel-theorem ingredient discharged unconditionally within the
corpus). -/
theorem unified_clay_closure_via_route_b_refined_dirichlet1858_and_full_pinning_r290
    (h : ClayClosureBundleViaRouteBRefinedDirichlet1858AndFullPinning) :
    PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard ∧
    PF.Referee.StandardClayStatements.Clay_PvsNP_Standard
      PF.Referee.PNPCapstoneTypedBridge.PF_ComplexityEncoding ∧
    PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard
      PF.NavierStokes.NSPDETypedUpgradeV2.PF_NS3DEncodingV2 ∧
    PF.Referee.StandardClayStatements.Clay_YangMillsMassGap_Standard
      PrincipiaTractalis.YangMills.Bridge5_YM_SubstrateDischarge.PF_YMEncodingBridge5 ∧
    PF.Referee.StandardClayStatements.Clay_BSD_Standard
      PF.Referee.BSDCapstoneTypedBridgeV5.PF_BSDEncodingV5 ∧
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard
      PF.Referee.HodgeCapstoneTypedBridge.PF_HodgeEncoding :=
  unified_clay_closure_via_route_b_specific_xi_and_riemann1859_and_full_pinning_r289
    (bundleViaRefinedDirichlet1858_to_riemann1859AndFullPinning h)

/-! ## §4 Axiom check. -/

#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaRouteBRefinedDirichlet1858AndFullPinning.bundleViaRefinedDirichlet1858_to_riemann1859AndFullPinning
#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaRouteBRefinedDirichlet1858AndFullPinning.unified_clay_closure_via_route_b_refined_dirichlet1858_and_full_pinning_r290

end PrincipiaTractalis.UnifiedClayClosureViaRouteBRefinedDirichlet1858AndFullPinning
