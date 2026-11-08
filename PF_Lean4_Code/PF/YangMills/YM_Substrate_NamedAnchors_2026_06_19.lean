/-
# PF.YangMills.YM_Substrate_NamedAnchors_2026_06_19

2026-06-19 — Seven bibliographic citation markers naming the published
sources of the framework's YM-axis substrate closure. Rewritten
2026-11-06 to remove the free-discharge pattern — see Hodge NamedAnchors
cleanup `c98e5b90` for the method and rationale.

## What this file is

Seven `Prop := True` definitions that NAME specific published-mathematics
sources the framework's YM-axis substrate closure cites. They are
bibliographic markers, not mathematical content predicates.

  - Glimm-Jaffe 1981 (Springer-Verlag): functional-integral QFT.
  - Streater-Wightman 1964 (Benjamin / Princeton): Wightman axioms +
    reconstruction theorem.
  - Osterwalder-Schrader 1973 (CMP 31:83-112): Euclidean axioms I.
  - Osterwalder-Schrader 1975 (CMP 42:281-305): Euclidean axioms II.
  - Wilson 1974 (Phys. Rev. D 10:2445): lattice gauge theory,
    area-law confinement.
  - Balaban 1985 (CMP 98:17-51 et seq.): constructive lattice gauge
    theory and continuum limit for SU(N) YM in 4D.
  - Jaffe-Witten 2000 (Clay Math. Inst.): the Clay YM problem.

## What was removed on 2026-11-06

  `theorem <lowercase>_anchor_holds : <Anchor> := trivial` × 7
  `SevenPublishedYMAnchors_Disjunction` + 4 holding theorems
  `SevenPublishedYMAnchors_Conjunction` + holding theorem
  `ym_phase1_named_anchors_audit_trail_capstone`

All type-reduce to `True`. Removed for the same reason as the Hodge /
RH / NS NamedAnchors cleanups.

## Where the real YM content is

  - `PF.YangMills.YM_SubstrateBulletproofClosure` — substrate-level
    closure.
  - `PF.YangMills.YM_FrameworkMillenniumAnswer` — framework's answer
    to Clay YM.
  - `PF.YangMills.YM_OSRPInteractionScaffold`, `PF.YangMills.YangMillsReflectionPositivity*`,
    `PF.YangMills.YM_WightmanReconstructionConcreteWitness` — the
    Osterwalder-Schrader / Wightman reconstruction content as actual
    Lean constructions.
  - r385 `hFubini` DISCHARGED (Wilson RP needs no Fubini hypothesis) —
    see current `YangMills/` tree.

## Scope

Bibliographic. The seven `Prop := True` defs are kept because
externally-referenced master-capstones name them as citation markers.

## Axiom budget

Zero project axioms. The file now contains no theorems.
-/

namespace PF.YangMills.YM_Substrate_NamedAnchors_2026_06_19

/-- **Glimm-Jaffe 1981 citation marker.** Glimm, J. and Jaffe, A.,
    *Quantum Physics: A Functional Integral Point of View*,
    Springer-Verlag, 1981. Bibliographic reference. -/
def GlimmJaffe1981_FunctionalIntegralQFT_Anchor : Prop := True

/-- **Streater-Wightman 1964 citation marker.** Streater, R.F. and
    Wightman, A.S., *PCT, Spin and Statistics, and All That*,
    W.A. Benjamin, 1964 (later Princeton Univ. Press).
    Bibliographic reference. -/
def StreaterWightman1964_WightmanAxioms_Anchor : Prop := True

/-- **Osterwalder-Schrader 1973 citation marker.** Osterwalder, K.
    and Schrader, R., "Axioms for Euclidean Green's functions.",
    Comm. Math. Phys. 31 (1973), 83-112. Bibliographic reference. -/
def OsterwalderSchrader1973_AxiomsI_Anchor : Prop := True

/-- **Osterwalder-Schrader 1975 citation marker.** Osterwalder, K.
    and Schrader, R., "Axioms for Euclidean Green's functions II.",
    Comm. Math. Phys. 42 (1975), 281-305. Bibliographic reference. -/
def OsterwalderSchrader1975_AxiomsII_Anchor : Prop := True

/-- **Wilson 1974 citation marker.** Wilson, K.G., "Confinement of
    quarks.", Phys. Rev. D 10 (1974), 2445-2459.
    Bibliographic reference. -/
def Wilson1974_LatticeGaugeTheory_Anchor : Prop := True

/-- **Balaban 1985 citation marker.** Balaban, T., "Propagators and
    renormalization transformations for lattice gauge theories I, II,
    III.", Comm. Math. Phys. 98 (1985), 17-51; 99 (1985), 75-102;
    99 (1985), 389-434. Bibliographic reference. -/
def Balaban1985_LatticeContinuumLimit_Anchor : Prop := True

/-- **Jaffe-Witten 2000 citation marker.** Jaffe, A. and Witten, E.,
    "Quantum Yang-Mills theory.", Clay Mathematics Institute
    Millennium Prize Problems, 2000. Bibliographic reference. -/
def JaffeWitten2000_ClayYMStatement_Anchor : Prop := True

end PF.YangMills.YM_Substrate_NamedAnchors_2026_06_19
