/-
# PF.AlgebraicGeometry.Hodge_Substrate_NamedAnchors_2026_06_19

2026-06-19 — Seven bibliographic citation markers naming the published
sources of the framework's Hodge-axis substrate closure. Rewritten
2026-11-06 to remove the free-discharge pattern (`theorem X_holds :=
trivial` + bundling capstone) that misrepresented the file as proving
seven named theorems when it proved seven `True`s.

## What this file is

Seven `Prop := True` definitions that NAME specific published-mathematics
sources the framework's Hodge-axis substrate closure cites. They are
bibliographic markers, not mathematical content predicates.

  - Hodge 1941 (Cambridge): *The Theory and Applications of Harmonic
    Integrals*. Original source of the Hodge conjecture.
  - Deligne 1971 (Pub. Math. IHES 40:5-58): *Theorie de Hodge II*,
    mixed Hodge structures.
  - Deligne 1968 (Pub. Math. IHES 35:107-126): *Theoreme de Lefschetz
    et criteres de degenerescence de suites spectrales*.
  - Griffiths 1969 (Bull. AMS 75:228-296): *On the periods of certain
    rational integrals and the period map*.
  - Cattani-Deligne-Kaplan 1995 (JAMS 8:483-506): *On the locus of
    Hodge classes*. Algebraicity of Hodge loci.
  - Voisin 2002 (Internat. Math. Res. Notices 20:1057-1075):
    counterexample to the Hodge conjecture extended to Kähler varieties.
  - Voisin 2007 (Cambridge): *Hodge Theory and Complex Algebraic
    Geometry I & II*. Standard reference.

## What was removed on 2026-11-06

The file formerly carried, for each anchor,

  `theorem <lowercase>_anchor_holds : <Anchor> := trivial`

bundled into
  `SevenPublishedHodgeAnchors_Disjunction` + holding theorems,
  `SevenPublishedHodgeAnchors_Conjunction` + holding theorem,
  `hodge_phase1_named_anchors_audit_trail_capstone`.

Every one of those names reduces to `True`. They were free-trivial and
their presence under a name containing "discharge" or "capstone"
misread downstream as "this file discharges seven Hodge theorems". It
does not; it does not need to; and the real Hodge substrate content
lives elsewhere.

## Where the real Hodge content is

  - `PF.AlgebraicGeometry.HodgeAlgebraicRepresentationV2/V3/V4` — the
    framework's typed substrate-level Hodge-class algebraicity Prop.
  - `PF.Hodge_SixSubstrateClassesBundle` — the six-class substrate
    discharge (`HodgeAlgebraicRepresentation` over curve, K3, abelian
    surface, Dwork pencil, CM, and Fermat-quintic branches).
  - `PF.AlgebraicGeometry.Hodge_ClayDischargeAttempt` —
    `PF_HodgeUnifiedEncoding` + `hodge_clay_discharge_capstone`.
  - `PF.AlgebraicGeometry.Bridge4_Hodge_SubstrateDischarge` — the
    single-citation bridge consolidating the above.

## Scope

This file is bibliographic. It makes no mathematical claim beyond the
historical fact that each named paper exists; those facts are not
Lean theorems and should not be encoded as such. The seven `Prop := True`
defs are kept because three Referee master-capstones (
`PrincipiaFractalis_Unified_Substrate_Position_2026_06_19`,
`PrincipiaFractalis_Complete_Substrate_Position_2026_06_19`,
`SixAxisPhase1NamedAnchors_MasterCapstone_2026_06_19`) reference them
by name as literal citation markers. Those capstones remain to be
reviewed in the same way this file was.

## Axiom budget

Zero project axioms. The file now contains no theorems.
-/

namespace PF.AlgebraicGeometry.Hodge_Substrate_NamedAnchors_2026_06_19

/-- **Hodge 1941 citation marker.** Hodge, W.V.D., *The Theory and
    Applications of Harmonic Integrals*, Cambridge University Press,
    1941 (2nd edition 1952). Bibliographic reference; carries no
    mathematical content. -/
def Hodge1941_HarmonicIntegrals_Anchor : Prop := True

/-- **Deligne 1971 citation marker.** Deligne, P., "Théorie de Hodge II.",
    Publ. Math. IHES 40 (1971), 5-58. Bibliographic reference. -/
def Deligne1971_MixedHodgeStructures_Anchor : Prop := True

/-- **Deligne 1968 citation marker.** Deligne, P., "Théorème de Lefschetz
    et critères de dégénérescence de suites spectrales.",
    Publ. Math. IHES 35 (1968), 107-126. Bibliographic reference. -/
def Deligne1968_LefschetzDegeneracy_Anchor : Prop := True

/-- **Griffiths 1969 citation marker.** Griffiths, P.A., "On the periods
    of certain rational integrals.", Bulletin of the AMS 75 (1969),
    228-296. Bibliographic reference. -/
def Griffiths1969_PeriodMap_Anchor : Prop := True

/-- **Cattani-Deligne-Kaplan 1995 citation marker.** Cattani, E.,
    Deligne, P., and Kaplan, A., "On the locus of Hodge classes.",
    Journal of the AMS 8 (1995), 483-506. Bibliographic reference. -/
def CattaniDeligneKaplan1995_HodgeLoci_Anchor : Prop := True

/-- **Voisin 2002 citation marker.** Voisin, C., "A counterexample to
    the Hodge conjecture extended to Kähler varieties.",
    Internat. Math. Res. Notices 20 (2002), 1057-1075. Bibliographic
    reference. -/
def Voisin2002_KahlerCounterexample_Anchor : Prop := True

/-- **Voisin 2007 citation marker.** Voisin, C., *Hodge Theory and
    Complex Algebraic Geometry I & II*, Cambridge University Press,
    2007. Bibliographic reference. -/
def Voisin2007_HodgeComplexAlgebraicGeometry_Anchor : Prop := True

end PF.AlgebraicGeometry.Hodge_Substrate_NamedAnchors_2026_06_19
