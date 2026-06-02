/-
# PF.Referee.FrontierLedger

**Date**: 2026-06-02
**Status**: pure inventory — zero new proofs, zero hidden content.
**Anchor commit**: ee51039 (Wave 57 master capstone).
**Source roadmap**: `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`.

## Purpose

This module implements step 1 of the referee roadmap's
"Reverse-Engineering Strategy": **Freeze the canonical boundary**. It
catalogs, for each of the six unsolved Clay axes, the corresponding PF
capstone theorem (by exact name), the named open Prop at the analytic
frontier, and whether the capstone is axiom-free at the PF library
level.

**Every entry references an existing theorem or Prop by exact name.**
No new proofs are introduced. No semantic claims are made. This file
exists to make the boundary auditable in a single place.

## What this file is NOT

* Not a proof of any Clay statement.
* Not a discharge of any frontier Prop.
* Not a substitute for the per-axis capstones — it indexes them.
-/

namespace PF.Referee.FrontierLedger

/-- **The six unsolved Clay axes** plus the Perelman anchor (Poincaré).
    Repeated here as a namespace-local enum to keep FrontierLedger
    importable from anywhere without depending on
    `MillenniumReductionSoundness`. -/
inductive ClayAxis
  | Poincare
  | RiemannHypothesis
  | PvsNP
  | NavierStokes
  | YangMills
  | BSD
  | Hodge
  deriving DecidableEq, Repr

/-- Status of the PF capstone for a given axis at HEAD ee51039. -/
inductive CapstoneStatus
  /-- Axiom-free at the PF library level (may still depend on a named
      open Prop or external mathlib content). -/
  | AxiomFreeConditional
  /-- Axiom-free and unconditional within its declared scope (e.g.
      a substrate, finite-dim instance, or numerical bracket). -/
  | AxiomFreeWithinScope
  /-- Already known true by an external mathematician (Perelman). -/
  | ExternalAnchor
  deriving Repr

/-- One entry per Clay axis. All `String` fields are documentation
    only: they name existing Lean theorems and Props at HEAD ee51039
    and supersede nothing. -/
structure FrontierEntry where
  axis : ClayAxis
  /-- The PF capstone theorem by exact Lean name. -/
  capstoneTheorem : String
  /-- The Lean file containing the capstone. -/
  capstoneFile : String
  /-- The named open Prop at the analytic frontier (or `none` if the
      axis is the Perelman anchor). -/
  frontierProp : Option String
  /-- The Lean file containing the frontier Prop. -/
  frontierFile : Option String
  /-- The standard-object bridge that must be supplied for a literal
      Clay-form discharge. From the 2026-06-02 referee roadmap's
      "Current Frontier Ledger" table. -/
  refereeGradeBridge : String
  /-- Status at HEAD ee51039. -/
  status : CapstoneStatus
  deriving Repr

/-- The frontier as of Wave 57 (HEAD ee51039). Each entry cites
    existing Lean files; no entry introduces new content. -/
def frontier : List FrontierEntry :=
  [ { axis := ClayAxis.Poincare
      capstoneTheorem := "PerelmanAnchor"
      capstoneFile := "PF/MillenniumReductionSoundness.lean"
      frontierProp := none
      frontierFile := none
      refereeGradeBridge :=
        "Already discharged externally by Perelman (2003); used in PF only as scaling anchor at alpha = 1."
      status := CapstoneStatus.ExternalAnchor }
  , { axis := ClayAxis.RiemannHypothesis
      capstoneTheorem := "riemann_hypothesis_via_T3_sym_framework"
      capstoneFile := "PF/SpectralBijection.lean (re-exported via PF/Millennium.lean)"
      frontierProp := some "RHSpectralSurjectivityConjecture"
      frontierFile := some "PF/RHSurjectivityConjecture.lean"
      refereeGradeBridge :=
        "Construct the operator/trace formula so zeta zeros are forced spectrum; prove spectral constraint implies Re(s) = 1/2."
      status := CapstoneStatus.AxiomFreeConditional }
  , { axis := ClayAxis.PvsNP
      capstoneTheorem := "P_neq_NP_via_spectral_gap"
      capstoneFile := "PF/P_NP_Complete_Proof.lean"
      frontierProp := some "PolylogEigenvalueConjecture"
      frontierFile := some "PF/PNP_WitnessExistenceScaffold.lean"
      refereeGradeBridge :=
        "Give alpha_of_class standard complexity semantics on languages OR a direct spectral lower-bound. Wave 57 sharpness certificate: this discharge is equivalent to deciding P vs NP."
      status := CapstoneStatus.AxiomFreeConditional }
  , { axis := ClayAxis.NavierStokes
      capstoneTheorem := "NS3D_HsSigmaScaffold (Wave 57)"
      capstoneFile := "PF/NS3D_HsSigmaScaffold.lean"
      frontierProp := some "MathlibSobolevDivFreeAvailable + VortexStretchingPDEBilinearBounded"
      frontierFile := some "PF/NavierStokes3DTorus.lean (Wave 35) + PF/NS3D_HsSigmaScaffold.lean"
      refereeGradeBridge :=
        "Standard critical a priori estimate (BKM, Prodi-Serrin, or critical Sobolev/Besov control) on H^s Schwartz initial data."
      status := CapstoneStatus.AxiomFreeConditional }
  , { axis := ClayAxis.YangMills
      capstoneTheorem := "fractalYMLevel1SpectrumGap_holds (axiom-free, level-1) + YM_OSRPInteractionScaffold (Wave 57, finite-dim closed)"
      capstoneFile := "PF/YangMillsCanonicalConvexKernel.lean + PF/YM_OSRPInteractionScaffold.lean"
      frontierProp := some "fractalYMLevel1LiftsToContinuum (single open) + 4 Wave 47B continuum gaps"
      frontierFile := some "PF/YM_WightmanReconstructionScaffold.lean"
      refereeGradeBridge :=
        "Build the continuum SU(3) Euclidean measure, reflection positivity, Wightman reconstruction, and mass-gap propagation for the standard Clay theory."
      status := CapstoneStatus.AxiomFreeWithinScope }
  , { axis := ClayAxis.BSD
      capstoneTheorem := "bsd_rank_six_universal_concordance + BSD_LSeriesConvergenceScaffold (Wave 57)"
      capstoneFile := "PF/BSDRankFourFiveFrameworks.lean + PF/BSD_LSeriesConvergenceScaffold.lean"
      frontierProp := some "(A3) + (A4): mathlib LSeries.ellipticCurve content + Wiles modularity"
      frontierFile := some "PF/BSD_LSeriesConvergenceScaffold.lean"
      refereeGradeBridge :=
        "Attach the PF rank mechanism to actual elliptic curves, Mordell-Weil rank, analytic rank, modularity, and L-series order of vanishing."
      status := CapstoneStatus.AxiomFreeConditional }
  , { axis := ClayAxis.Hodge
      capstoneTheorem := "hodge_full_dim_one_and_dim_two_capstone + hodge_CY3_complete_via_11_and_22 + hodge_CY4_complete_via_11_22_33 + Hodge_QuinticCYCodim2Scaffold (Wave 57 Dwork pencil)"
      capstoneFile := "PF/HodgeGeneralSurfaceDim2Substrate.lean + PF/HodgeCalabiYau3FoldDim22Substrate.lean + PF/HodgeDim4CY4Substrate.lean + PF/Hodge_QuinticCYCodim2Scaffold.lean"
      frontierProp := some "VoisinObstructionAtCodimTwoCY3 (general smooth quintic, codim >= 2)"
      frontierFile := some "PF/AlgebraicGeometry/CycleClassMapAtCodim2Attempt.lean"
      refereeGradeBridge :=
        "Prove algebraicity of the relevant rational Hodge classes in the standard category (not only in a PF substrate). Wave 57 closes Dwork pencil substrate via classical Lefschetz; general quintic remains the single named open."
      status := CapstoneStatus.AxiomFreeWithinScope }
  ]

/-- Total number of axes catalogued (6 Clay + Poincare anchor = 7). -/
def frontierSize : Nat := frontier.length

/-- Theorem-level guarantee: the ledger contains exactly seven
    entries (six Clay axes plus Poincare). This is an audit invariant,
    not a mathematical claim. -/
theorem frontierSize_eq_seven : frontierSize = 7 := by
  unfold frontierSize frontier
  decide

/-- **Honest scope tag.** This ledger is documentation. It claims no
    discharge of any Clay statement. It exists so that a reader can
    inspect the boundary in a single file. -/
def frontierLedger_isDocumentationOnly : Prop := True

theorem frontierLedger_isDocumentationOnly_holds :
    frontierLedger_isDocumentationOnly := trivial

#check @frontierSize_eq_seven
#check @frontierLedger_isDocumentationOnly_holds

end PF.Referee.FrontierLedger
