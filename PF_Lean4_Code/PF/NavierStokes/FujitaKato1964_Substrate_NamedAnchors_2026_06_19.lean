/-
# PF.NavierStokes.FujitaKato1964_Substrate_NamedAnchors_2026_06_19

2026-06-19 — Five bibliographic citation markers naming the published
sources of the framework's NS-axis substrate closure. Rewritten
2026-11-06 to remove the free-discharge pattern — see Hodge NamedAnchors
cleanup `c98e5b90` for the method and rationale.

## What this file is

Five `Prop := True` definitions that NAME specific published-mathematics
sources the framework's NS-axis substrate closure cites. They are
bibliographic markers, not mathematical content predicates.

  - Fujita-Kato 1964 (Arch. Rat. Mech. Anal. 16:269-315): local
    existence for 3D Navier-Stokes IVP in H^{1/2}_σ(ℝ^3).
  - Leray 1934 (Acta Math. 63:193-248): weak solutions for the IVP on
    ℝ^3, global energy inequality, partial regularity.
  - Sobolevskii 1959 (Sov. Math. Dokl. 130:1024-1027): semigroup
    methods for parabolic evolution equations.
  - Beale-Kato-Majda 1984 (Comm. Math. Phys. 94:61-66): blow-up
    criterion via integral control of vorticity supremum.
  - Caffarelli-Kohn-Nirenberg 1982 (Comm. Pure Appl. Math. 35:771-831):
    partial regularity of suitable weak solutions, parabolic Hausdorff
    dimension ≤ 1 for the singular set.

## What was removed on 2026-11-06

  `theorem <lowercase>_anchor_holds : <Anchor> := trivial` × 5
  `FivePublishedNSAnchors_Disjunction` + 5 holding theorems
  `FivePublishedNSAnchors_Conjunction` + holding theorem
  `ns_phase1_named_anchors_audit_trail_capstone`

All type-reduce to `True`. Removed because their names (containing
"discharge", "capstone") misread downstream as proving five named NS
theorems; the real NS content lives elsewhere.

## Where the real NS content is

  - `PF.NavierStokes.NS_SubstrateBulletproofClosure` — substrate-level
    closure.
  - `PF.NavierStokes.NS3D_FullSubstrateNSCapstone` — the full substrate
    NS capstone.
  - `PF.NavierStokes.NS3D_FrameworkMillenniumAnswer` — framework's
    answer to Clay NS.
  - `PF.NavierStokes.NS3D_HeatSemigroup`, `PF.NavierStokes.NS3D_LerayProjector`,
    `PF.NavierStokes.NS3D_StokesOperator` — the Fujita-Kato / Leray /
    Sobolevskii / BKM / CKN content as actual Lean theorems.

## Scope

Bibliographic. The five `Prop := True` defs are kept because
externally-referenced master-capstones name them as citation markers.

## Axiom budget

Zero project axioms. The file now contains no theorems.
-/

namespace PF.NavierStokes.FujitaKato1964_Substrate_NamedAnchors_2026_06_19

/-- **Fujita-Kato 1964 citation marker.** Fujita, H. and Kato, T.,
    "On the Navier-Stokes initial value problem. I.",
    Arch. Rat. Mech. Anal. 16 (1964), 269-315. Bibliographic reference. -/
def FujitaKato1964_LocalExistence_Anchor : Prop := True

/-- **Leray 1934 citation marker.** Leray, J., "Sur le mouvement d'un
    liquide visqueux emplissant l'espace.", Acta Math. 63 (1934),
    193-248. Bibliographic reference. -/
def Leray1934_WeakSolutions_Anchor : Prop := True

/-- **Sobolevskii 1959 citation marker.** Sobolevskii, P.E., "On the
    equations of parabolic type in a Banach space.", Sov. Math. Dokl.
    130 (1959), 1024-1027. Bibliographic reference. -/
def Sobolevskii1959_AnalyticSemigroup_Anchor : Prop := True

/-- **Beale-Kato-Majda 1984 citation marker.** Beale, J.T., Kato, T.,
    and Majda, A., "Remarks on the breakdown of smooth solutions for
    the 3-D Euler equations.", Comm. Math. Phys. 94 (1984), 61-66.
    Bibliographic reference. -/
def BealeKatoMajda1984_BlowUpCriterion_Anchor : Prop := True

/-- **Caffarelli-Kohn-Nirenberg 1982 citation marker.** Caffarelli, L.,
    Kohn, R., and Nirenberg, L., "Partial regularity of suitable weak
    solutions of the Navier-Stokes equations.", Comm. Pure Appl.
    Math. 35 (1982), 771-831. Bibliographic reference. -/
def CaffarelliKohnNirenberg1982_PartialRegularity_Anchor : Prop := True

end PF.NavierStokes.FujitaKato1964_Substrate_NamedAnchors_2026_06_19
