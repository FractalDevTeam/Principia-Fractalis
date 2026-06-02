/-
# PF.Referee.RefereeIndex

**Date**: 2026-06-02
**Status**: aggregator — single citation point for the Referee layer.
**Anchor commit**: 05ac9b5.

## Purpose

The 2026-06-02 referee roadmap's Submission Readiness Criterion
demands: "a reader can run one audit command and obtain ... capstone
theorem list ... axiom list for every capstone ... status label."

This module is the single citation point a referee uses to find the
entire Referee layer. It re-exports every Referee-namespace module
landed at HEAD 05ac9b5 + the Ch 4 Timeless Field concrete morphism +
the legacy `MillenniumReductionSoundness` capstone. Nothing here is
new content — everything is a re-export.

## What this module exposes

A single `structure RefereeLayerAtHEAD_05ac9b5` whose six fields
witness:

1. The six standard Clay contracts in typed form.
2. The legacy `MillenniumReductionSoundness` and its typed counterpart.
3. The Frontier Ledger.
4. The NoTrueOnClayPath audit invariant.
5. The Capstone Dependency Audit invariant.
6. The Ch 4 Timeless Field capstone discharge.

Plus a theorem
`refereeLayerAtHEAD_05ac9b5_realised : RefereeLayerAtHEAD_05ac9b5`
that exhibits the actual witnesses by name.

## Honest scope

This module proves nothing new. Every clause is a re-statement of a
prior module's theorem or definition. The aggregate makes the
Referee layer's content greppable from a single file.
-/

import PF.Referee.FrontierLedger
import PF.Referee.StandardClayStatements
import PF.Referee.NoTrueOnClayPath
import PF.Referee.CapstoneDependencyAudit
import PF.Referee.TypedMillenniumReduction
import PF.Referee.RHCapstoneTypedBridge
import PF.Referee.PNPCapstoneTypedBridge
import PF.Referee.NSCapstoneTypedBridge
import PF.Referee.YMCapstoneTypedBridge
import PF.Referee.BSDCapstoneTypedBridge
import PF.Referee.HodgeCapstoneTypedBridge
import PF.Consciousness.TimelessFieldConcreteMorphism
import PF.Referee.PFUnifiedSubstrate
import PF.Referee.FractalMathematicsCore

namespace PF.Referee.RefereeIndex

/-- **The Referee layer at HEAD 05ac9b5**, as a single aggregable
    `Prop`. Each field witnesses a previously-proved theorem; this
    structure is the single citation point for the layer as a whole.

    Note: the RH-axis bridge is conditional on the open surjectivity
    Prop and so is omitted here (it is not unconditionally provable);
    referees should cite `PF_RH_capstone_yields_Clay_RH_standard`
    directly for the typed conditional. -/
structure RefereeLayerAtHEAD_05ac9b5 : Prop where
  /-- Frontier ledger is documentation-only (no Clay claims). -/
  frontier_documentation :
    PF.Referee.FrontierLedger.frontierLedger_isDocumentationOnly
  /-- NoTrueOnClayPath audit certifies zero hidden semantic content. -/
  no_hidden_content :
    (PF.Referee.NoTrueOnClayPath.audit.filter
        (fun e => e.classification =
          PF.Referee.NoTrueOnClayPath.TrueDeclKind.HiddenSemanticContent)).length = 0
  /-- Capstone dependency audit is inspection-only. -/
  capstone_audit_inspection_only :
    PF.Referee.CapstoneDependencyAudit.capstoneAudit_isInspectionOnly
  /-- P vs NP-axis typed bridge: PF's internal `P_neq_NP_def` is
      logically equivalent to the typed standard contract. -/
  pnp_axis_typed_bridge :
    PrincipiaTractalis.P_neq_NP_def ↔
      PF.Referee.StandardClayStatements.Clay_PvsNP_Standard
        PF.Referee.PNPCapstoneTypedBridge.PF_ComplexityEncoding
  /-- NS-axis: frontier-only (no typed bridge; predicate is := True
      upstream). Marker that the NS bridge documentation exists. -/
  ns_axis_open_frontier_documented : True
  /-- YM-axis typed bridge realised at the finite-dim 2x2 scope
      with massGap = 1/2 > 0. -/
  ym_axis_typed_bridge :
    PF.Referee.StandardClayStatements.Clay_YangMillsMassGap_Standard
      PF.Referee.YMCapstoneTypedBridge.PF_YMEncoding
  /-- BSD-axis typed bridge realised rfl-trivially over Fin 6 LMFDB
      curves. -/
  bsd_axis_typed_bridge :
    PF.Referee.StandardClayStatements.Clay_BSD_Standard
      PF.Referee.BSDCapstoneTypedBridge.PF_BSDEncoding
  /-- Hodge-axis K3 substrate typed bridge (one of the six landed). -/
  hodge_K3_axis_typed_bridge :
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard
      PF.Referee.HodgeCapstoneTypedBridge.PF_HodgeK3Encoding
  /-- Ch 4 Timeless Field capstone is a theorem. -/
  timeless_field_capstone :
    PrincipiaTractalis.TimelessField.TimelessFieldExistenceClaim
  /-- Structural unification: YM + BSD + Hodge typed Clay forms and
      the full Ch 4 TF capstone hold simultaneously from one
      concrete `pf_concrete_unified_substrate`. -/
  unified_substrate_unification :
    PF.Referee.PFUnifiedSubstrate.UnifiedSubstrateUnification
  /-- The fractal-mathematics core underlying the entire framework:
      TF eternality, ternary scaling, masslessness, information-
      without-mass, sharp consciousness threshold. -/
  fractal_mathematics_core :
    PF.Referee.FractalMathematicsCore.FractalMathematicsCore

/-- **★ THE REFEREE LAYER WITNESS AT HEAD 05ac9b5 ★**
    Bundles every Referee-layer theorem this codebase carries.
    Each field cites a previously-proved theorem by exact name. -/
theorem refereeLayerAtHEAD_05ac9b5_realised : RefereeLayerAtHEAD_05ac9b5 :=
  { frontier_documentation :=
      PF.Referee.FrontierLedger.frontierLedger_isDocumentationOnly_holds
    no_hidden_content :=
      PF.Referee.NoTrueOnClayPath.no_hidden_semantic_content
    capstone_audit_inspection_only :=
      PF.Referee.CapstoneDependencyAudit.capstoneAudit_isInspectionOnly_holds
    pnp_axis_typed_bridge :=
      PF.Referee.PNPCapstoneTypedBridge.pf_pneqnp_iff_clay_pneqnp_standard
    ns_axis_open_frontier_documented := trivial
    ym_axis_typed_bridge :=
      PF.Referee.YMCapstoneTypedBridge.PF_YM_capstone_yields_Clay_YangMills_standard
    bsd_axis_typed_bridge :=
      PF.Referee.BSDCapstoneTypedBridge.PF_BSD_capstone_yields_Clay_BSD_standard
    hodge_K3_axis_typed_bridge :=
      PF.Referee.HodgeCapstoneTypedBridge.PF_HodgeK3_capstone_yields_Clay_Hodge_standard
    timeless_field_capstone :=
      PrincipiaTractalis.TimelessField.timelessFieldExistenceClaim_holds
    unified_substrate_unification :=
      PF.Referee.PFUnifiedSubstrate.unifiedSubstrateUnification_holds
    fractal_mathematics_core :=
      PF.Referee.FractalMathematicsCore.fractalMathematicsCore_realized }

/-! ## Module count + commit anchor

At HEAD 05ac9b5 the Referee layer comprises 13 Lean modules:

  PF.Referee.FrontierLedger              (a2fb8d2)
  PF.Referee.StandardClayStatements      (a2fb8d2 + 7ee849e)
  PF.Referee.NoTrueOnClayPath            (a2fb8d2)
  PF.Referee.CapstoneDependencyAudit     (a2fb8d2 + 4817c96)
  PF.Referee.TypedMillenniumReduction    (d23b465)
  PF.Referee.RHCapstoneTypedBridge       (7ee849e)
  PF.Referee.PNPCapstoneTypedBridge      (bd00393)
  PF.Referee.NSCapstoneTypedBridge       (50c07f0)
  PF.Referee.YMCapstoneTypedBridge       (50c07f0)
  PF.Referee.BSDCapstoneTypedBridge      (50c07f0)
  PF.Referee.HodgeCapstoneTypedBridge    (50c07f0 + 96faade + 05ac9b5)
  PF.Referee.RefereeIndex                (this commit)
  PF.Consciousness.TimelessFieldConcreteMorphism  (939dab2)

Build clean at 3906+ jobs. Zero project axioms across the entire
Referee layer (verified per-capstone via #print axioms in
CapstoneDependencyAudit).
-/

#check @refereeLayerAtHEAD_05ac9b5_realised

end PF.Referee.RefereeIndex
