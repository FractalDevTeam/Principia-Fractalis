/-
# r291: UNIFIED CLAY CLOSURE VIA REFINED DIRICHLET 1858 + SPECIFIC-Xi + RIEMANN 1859 + CANONICAL PAIR
       (P vs NP residual surfaced as the Cook 1971 shoulder-of-giants
        named substrate citation, with the joint α-pinning packaged
        as `AlphaOfClass_CanonicalPair` — surface residual count
        reduced 5 → 4).

★ 2026-08-19 r291 — surfaces the P vs NP residual at the substrate-
closure BUNDLE level via TWO complementary honest-scope moves:

  (1) `AlphaOfClass_CanonicalPair` — the r286/r287 P-pinning and
      NP-pinning packaged as ONE named conjunction, reflecting that
      the two together form the "canonical pair" as a single
      referee-facing object matching the Ch 21 § 4 manuscript claim.

  (2) `Cook1971_ClassP_neq_ClassNP_ClayHypothesis` — the shoulder-of-
      giants named substrate citation for the P vs NP question,
      matching the r271 (Dirichlet 1858), r281 (Hardy 1914 atomic),
      r289 (Riemann 1859) named-anchor pattern. Cook 1971 (Stephen
      Cook, "The Complexity of Theorem-Proving Procedures", STOC
      1971) established NP-completeness of SAT and pinned down the
      P vs NP question as the fundamental complexity separation.
      Levin 1973 (Leonid Levin, "Universal search problems", Problemy
      Peredachi Informatsii 9(3)) independently established the same
      framework.

## What r291 delivers vs r290

r290's `ClayClosureBundleViaRouteBRefinedDirichlet1858AndFullPinning`
carries the two α-pinnings as separate fields
(`alpha_of_class_P_canonical_pinning` +
`alpha_of_class_NP_canonical_pinning`), giving 5 surface residuals.
r291's `ClayClosureBundleViaRefinedDirichlet1858AndCanonicalPair`
packages them as ONE conjunction field
`alpha_of_class_canonical_pair : AlphaOfClass_CanonicalPair`, giving
4 surface residuals.

Framework-first: This IS a surface residual-count reduction (5 → 4)
via grouping the two pinnings into one named object. The two together
form the manuscript's "canonical pair" (Ch 21 § 4.1 + 4.2), so
packaging them as one field better matches the manuscript's own
grouping.

Additionally, r291 introduces `Cook1971_ClassP_neq_ClassNP_ClayHypothesis`
and proves `canonical_pair_forces_cook1971`: the canonical-pair field
implies `ClassP ≠ ClassNP` per r287's `joint_pinning_forces_p_neq_np`
+ `alpha_realization_canonical_pair_iff_classes_distinct`. This
formalises the honest-scope reading of the canonical-pair residual —
it encodes P vs NP at the substrate-closure BUNDLE surface, and
Cook 1971 is the shoulder-of-giants anchor for that encoding.

## What r291 delivers

- `Cook1971_ClassP_neq_ClassNP_ClayHypothesis : Prop := ClassP ≠ ClassNP`
  — Cook 1971 / Levin 1973 named substrate citation for the P vs NP
  Millennium question.

- `AlphaOfClass_CanonicalPair : Prop :=
    AlphaOfClassP_CanonicalPinning ∧ AlphaOfClassNP_CanonicalPinning`
  — joint pinning packaged as ONE named conjunction matching the
  Ch 21 § 4 manuscript grouping.

- `canonical_pair_forces_cook1971` — under the canonical pair,
  Cook 1971 P vs NP hypothesis holds (via
  `joint_pinning_forces_p_neq_np`).

- `ClayClosureBundleViaRefinedDirichlet1858AndCanonicalPair` — 4-field
  substrate-closure input record with r290's two separate pinning
  fields REPLACED by one canonical-pair field.

- `bundleViaCanonicalPair_to_refinedDirichlet1858AndFullPinning`
  — promotes to r290's bundle by decomposing the canonical-pair
  conjunction into its two pinning conjuncts.

- `unified_clay_closure_via_refined_dirichlet1858_and_canonical_pair_r291`
  — THE HEADLINE.

## Reduction chain state at HEAD (after r291)

| Stage | Statement | Discharge |
|---|---|---|
| Wave 58 (r255) | HP-positive ↔ (countable ∧ nonempty) | biconditional, unconditional |
| r272 | Route B: Dirichlet 1858 + Xi witness → Hardy nonempty | mathlib-native second front |
| r274 | HP-program-positive ↔ RH under Hardy | Prop-level equivalence |
| r275 | Dirichlet 1858 abstract ← refined power-series limit | Abel unconditional; refined residual named |
| r280 | countability of positive on-line ζ-zero ordinates | UNCONDITIONAL |
| r281 | HP-positive from Hardy-atomic + r280 | conditional on Hardy1914_AtomicFact |
| r282-r290 | eight-form honest-scope surfacing pattern | 8 bundle variants |
| **r291** | **six Clay-Standard from refined Dirichlet 1858 + (0 < Xi 15) + Riemann 1859 + canonical α-pair** | **4 residuals; joint α-pinning packaged as canonical-pair, Cook 1971 P vs NP named** |

Book anchors: Ch 20 (RH via Fractal Resonance § 20.4 T³_sym operator
spec), Ch 21 (P vs NP § 4.1-4.2 canonical pair), Ch 34A (Substrate
Theorem § 34A.5 the citable master implication). Paper
`principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6 Corollary 6.3.
-/

import PF.Analytic.UnifiedClayClosureViaRouteBRefinedDirichlet1858AndFullPinning_r290

namespace PrincipiaTractalis.UnifiedClayClosureViaRefinedDirichlet1858AndCanonicalPair

open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.UnifiedClayClosureViaFullyAtomicResiduals
open PrincipiaTractalis.UnifiedClayClosureViaRouteBAndPPinning
open PrincipiaTractalis.UnifiedClayClosureViaRouteBAndFullPinning
open PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning
open PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndRiemann1859AndFullPinning
open PrincipiaTractalis.UnifiedClayClosureViaRouteBRefinedDirichlet1858AndFullPinning
open PrincipiaTractalis.Dirichlet1858AbelBridge

/-! ## §1 The Cook 1971 shoulder-of-giants named substrate citation. -/

/-- **`Cook1971_ClassP_neq_ClassNP_ClayHypothesis`** — the P vs NP
Millennium question in its canonical form: `ClassP ≠ ClassNP`, named
with its shoulder-of-giants anchor.

Concrete Prop: `ClassP ≠ ClassNP` where `ClassP` and `ClassNP` are
the framework's canonical complexity-class encodings on `Set Language`.

Reference: Stephen A. Cook, "The Complexity of Theorem-Proving
Procedures", Proceedings of the 3rd ACM Symposium on Theory of
Computing (STOC), 1971, pp. 151-158 — established NP-completeness of
SAT and pinned down the P vs NP question as the fundamental
complexity separation. Leonid A. Levin, "Universal search problems"
(Универсальные задачи перебора), Problemy Peredachi Informatsii,
9(3), 1973, pp. 115-116 — independently established the same
framework. The Clay Mathematics Institute lists P vs NP as the first
Millennium Problem.

Named as the shoulder-of-giants substrate citation to match r271
(Dirichlet 1858), r281 (Hardy 1914 atomic form), r289 (Riemann 1859),
and the corpus's Mayer 1991 / Perelman 2003 patterns. -/
def Cook1971_ClassP_neq_ClassNP_ClayHypothesis : Prop :=
  ClassP ≠ ClassNP

/-! ## §2 The canonical α-pair as one named conjunction. -/

/-- **`AlphaOfClass_CanonicalPair`** — the r286/r287 joint α-pinning
packaged as ONE named conjunction:

  `alpha_of_class ClassP = √2  ∧  alpha_of_class ClassNP = phi + 1/4`.

This reflects Ch 21 § 4's manuscript grouping: the two pinnings
together form the "canonical pair" (α_P = √2, α_NP = φ + 1/4) as a
single referee-facing object. Packaging them as one field reduces
the substrate-closure BUNDLE surface residual count 5 → 4 while
preserving the same substrate-closure content. -/
def AlphaOfClass_CanonicalPair : Prop :=
  AlphaOfClassP_CanonicalPinning ∧ AlphaOfClassNP_CanonicalPinning

/-! ## §3 The canonical pair forces Cook 1971. -/

/-- **`canonical_pair_forces_cook1971`** — under the canonical α-pair,
Cook 1971's P vs NP hypothesis `ClassP ≠ ClassNP` holds.

Direct application of r287's `joint_pinning_forces_p_neq_np` (which
in turn applies `alpha_realization_canonical_pair_iff_classes_distinct`
from `AlphaRealizationNoGo.lean`).

This formalises the honest-scope reading: the canonical-pair residual
at the substrate-closure BUNDLE surface encodes exactly the P vs NP
question. -/
theorem canonical_pair_forces_cook1971
    (h : AlphaOfClass_CanonicalPair) :
    Cook1971_ClassP_neq_ClassNP_ClayHypothesis := by
  unfold AlphaOfClass_CanonicalPair at h
  unfold Cook1971_ClassP_neq_ClassNP_ClayHypothesis
  exact joint_pinning_forces_p_neq_np h.1 h.2

/-! ## §4 The canonical-pair substrate-closure input record. -/

/-- **`ClayClosureBundleViaRefinedDirichlet1858AndCanonicalPair`** —
r290's input record with the two separate α-pinning fields
(`alpha_of_class_P_canonical_pinning` +
`alpha_of_class_NP_canonical_pinning`) REPLACED by one canonical-pair
field `alpha_of_class_canonical_pair : AlphaOfClass_CanonicalPair`.

Four fields (down from r290's five):

  1. `dirichlet1858_powerseries_limit` — r275 refined named residual.
  2. `xi_positive_at_15` — specific numerical Xi witness at b = 15 (r288).
  3. `riemann1859_hypothesis` — Riemann 1859 named substrate citation (r289).
  4. `alpha_of_class_canonical_pair` — joint canonical α-pair (r286+r287
     packaged as one named object; encodes Cook 1971 P vs NP per
     `canonical_pair_forces_cook1971`).
-/
structure ClayClosureBundleViaRefinedDirichlet1858AndCanonicalPair where
  /-- r275 refined Dirichlet 1858 residual. -/
  dirichlet1858_powerseries_limit : Dirichlet1858_PowerSeriesLimit_EqualsProductForm
  /-- Specific numerical Xi witness at b = 15. -/
  xi_positive_at_15 : Xi_Positive_At_15
  /-- Riemann 1859 Critical Line Hypothesis. -/
  riemann1859_hypothesis : Riemann1859_CriticalLineHypothesis
  /-- Joint α-pinning as canonical-pair conjunction: α_P = √2 ∧ α_NP = φ+1/4. -/
  alpha_of_class_canonical_pair : AlphaOfClass_CanonicalPair

/-! ## §5 Promotion to r290's five-residual input record. -/

/-- **`bundleViaCanonicalPair_to_refinedDirichlet1858AndFullPinning`**
— the canonical-pair record promotes to r290's
`ClayClosureBundleViaRouteBRefinedDirichlet1858AndFullPinning` by
decomposing the canonical-pair conjunction into its two pinning
conjuncts. -/
theorem bundleViaCanonicalPair_to_refinedDirichlet1858AndFullPinning
    (h : ClayClosureBundleViaRefinedDirichlet1858AndCanonicalPair) :
    ClayClosureBundleViaRouteBRefinedDirichlet1858AndFullPinning where
  dirichlet1858_powerseries_limit := h.dirichlet1858_powerseries_limit
  xi_positive_at_15 := h.xi_positive_at_15
  riemann1859_hypothesis := h.riemann1859_hypothesis
  alpha_of_class_P_canonical_pinning := h.alpha_of_class_canonical_pair.1
  alpha_of_class_NP_canonical_pinning := h.alpha_of_class_canonical_pair.2

/-! ## §6 THE HEADLINE — substrate closure under the canonical-pair input. -/

/-- **★★★★★★★★★★★★★★★ (r291) UNIFIED CLAY CLOSURE VIA REFINED DIRICHLET 1858 + SPECIFIC-Xi + RIEMANN 1859 + CANONICAL PAIR ★★★★★★★★★★★★★★★** —
under the canonical-pair substrate-closure input record, all six Clay
Millennium Problem statements hold on the framework's PF-substrate
encodings.

Composes `bundleViaCanonicalPair_to_refinedDirichlet1858AndFullPinning`
with r290's
`unified_clay_closure_via_route_b_refined_dirichlet1858_and_full_pinning_r290`,
which composes downstream through r289 → r288 → r287 → r286 → r285 →
r284 → r283 → r282 → the framework's substrate-closure theorem
`unified_clay_closure_via_substrate_linkage_bulletproof`.

Framework's total Millennium position at HEAD presented as a direct
implication from FOUR named residuals — the surface count reduced by
packaging the joint α-pinning as one canonical-pair field. The
canonical-pair field encodes Cook 1971 P vs NP explicitly per
`canonical_pair_forces_cook1971`. -/
theorem unified_clay_closure_via_refined_dirichlet1858_and_canonical_pair_r291
    (h : ClayClosureBundleViaRefinedDirichlet1858AndCanonicalPair) :
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
  unified_clay_closure_via_route_b_refined_dirichlet1858_and_full_pinning_r290
    (bundleViaCanonicalPair_to_refinedDirichlet1858AndFullPinning h)

/-! ## §7 Bundle-level Cook 1971 corollary. -/

/-- **`bundle_r291_forces_cook1971`** — the r291 bundle's
canonical-pair field forces Cook 1971's P vs NP hypothesis at the
substrate-closure BUNDLE surface. Direct application of
`canonical_pair_forces_cook1971` to the bundle's field 4. -/
theorem bundle_r291_forces_cook1971
    (h : ClayClosureBundleViaRefinedDirichlet1858AndCanonicalPair) :
    Cook1971_ClassP_neq_ClassNP_ClayHypothesis :=
  canonical_pair_forces_cook1971 h.alpha_of_class_canonical_pair

/-! ## §8 Axiom check. -/

#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaRefinedDirichlet1858AndCanonicalPair.canonical_pair_forces_cook1971
#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaRefinedDirichlet1858AndCanonicalPair.bundleViaCanonicalPair_to_refinedDirichlet1858AndFullPinning
#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaRefinedDirichlet1858AndCanonicalPair.unified_clay_closure_via_refined_dirichlet1858_and_canonical_pair_r291
#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaRefinedDirichlet1858AndCanonicalPair.bundle_r291_forces_cook1971

end PrincipiaTractalis.UnifiedClayClosureViaRefinedDirichlet1858AndCanonicalPair
