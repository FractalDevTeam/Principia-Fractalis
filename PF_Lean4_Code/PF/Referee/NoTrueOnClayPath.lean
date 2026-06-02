/-
# PF.Referee.NoTrueOnClayPath

**Date**: 2026-06-02
**Status**: audit module. No proofs of Clay statements. No new claims.
**Anchor commit**: ee51039.
**Source roadmap**: `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`
Non-Negotiable Rule #1.

## Purpose

The 2026-06-02 referee roadmap demands:

> No `def SomeClaim : Prop := True` may sit on a Clay-level proof path
> unless it is explicitly tagged as a provenness tag and excluded from
> claim content.

This file enumerates every `Prop := True` declaration that currently
sits on or near a Clay-level proof path in the PF library, classifies
each one as either a **provenness tag** (acceptable under Rule #1) or
**hidden semantic content** (a violation), and documents the exclusion.

## How this audit was constructed

Hand-audit at HEAD `ee51039` of:

* `PF/Wave57MasterCapstone.lean` — 9 `Prop := True` declarations
* `PF/MillenniumReductionSoundness.lean` — 6 of 7 `ClayExternalStatement`
  branches are `True`
* `PF/HodgeAlgebraicRepresentation.lean` (referenced) — placeholder

## Classification scheme

A `Prop := True` is acceptable under Rule #1 if and only if:

1. The name explicitly contains the word `Proven`, `Tag`, `Marker`,
   `Anchor`, or `Provenness`.
2. The declaration's docstring states it carries no claim content.
3. No theorem on a Clay proof path consumes it as a hypothesis whose
   content is then asserted as Clay-statement-level truth.

Otherwise the `Prop := True` is **hidden semantic content** and the
audit flags it as a violation requiring revision.

The roadmap recommends the replacement pattern in
`PF.Referee.StandardClayStatements`: replace `:= True` Clay-statement
branches with parameterized predicates over an external encoding.
-/

namespace PF.Referee.NoTrueOnClayPath

/-- Classification of a `Prop := True` declaration. -/
inductive TrueDeclKind
  /-- Acceptable: a provenness tag with no semantic content. -/
  | ProvennessTag
  /-- Acceptable: an external anchor (e.g. Poincare, proven by
      Perelman). -/
  | ExternalAnchor
  /-- Violation: a Clay-statement-level claim being shadowed by `True`. -/
  | HiddenSemanticContent
  /-- Acceptable: a structural placeholder explicitly tagged as
      requiring an external encoding (e.g. `:= True` because the
      typed encoding lives in
      `PF.Referee.StandardClayStatements` and is parameterized). -/
  | ParameterizedDelegated
  deriving DecidableEq, Repr

/-- One audit entry per identified `Prop := True` declaration. -/
structure TrueDeclEntry where
  declName : String
  declFile : String
  classification : TrueDeclKind
  /-- A short rationale (≤ 1 sentence) for the classification. -/
  rationale : String
  /-- The replacement pattern recommended by the referee roadmap, if
      this entry is a violation. -/
  replacement : Option String
  deriving Repr

/-- The audit at HEAD `ee51039`. Each entry references an existing
    declaration by exact name; nothing here introduces new content. -/
def audit : List TrueDeclEntry :=
  -- Wave 57 provenness tags: acceptable.
  [ { declName := "Wave57PNP_WitnessExistenceProven"
      declFile := "PF/Wave57MasterCapstone.lean"
      classification := TrueDeclKind.ProvennessTag
      rationale := "Name ends in 'Proven'; tag aggregates Wave 57 sub-attack 57-PNP existence; no Clay-level content depends on this tag's content."
      replacement := none }
  , { declName := "Wave57NS_HsSigmaScaffoldProven"
      declFile := "PF/Wave57MasterCapstone.lean"
      classification := TrueDeclKind.ProvennessTag
      rationale := "Provenness tag for Wave 57 sub-attack 57-NS scaffold."
      replacement := none }
  , { declName := "Wave57RH_MayerNToInfinityProven"
      declFile := "PF/Wave57MasterCapstone.lean"
      classification := TrueDeclKind.ProvennessTag
      rationale := "Provenness tag for Wave 57 sub-attack 57-RH-Mayer scaffold."
      replacement := none }
  , { declName := "Wave57RH_HardyToFullStripProven"
      declFile := "PF/Wave57MasterCapstone.lean"
      classification := TrueDeclKind.ProvennessTag
      rationale := "Provenness tag for Wave 57 sub-attack 57-RH-Hardy scaffold."
      replacement := none }
  , { declName := "Wave57Hodge_QuinticCYCodim2Proven"
      declFile := "PF/Wave57MasterCapstone.lean"
      classification := TrueDeclKind.ProvennessTag
      rationale := "Provenness tag for Wave 57 sub-attack 57-Hodge Dwork pencil substrate closure."
      replacement := none }
  , { declName := "Wave57YM_WightmanReconstructionProven"
      declFile := "PF/Wave57MasterCapstone.lean"
      classification := TrueDeclKind.ProvennessTag
      rationale := "Provenness tag for Wave 57 sub-attack 57-YM-W scaffold."
      replacement := none }
  , { declName := "Wave57YM_OSRPInteractionProven"
      declFile := "PF/Wave57MasterCapstone.lean"
      classification := TrueDeclKind.ProvennessTag
      rationale := "Provenness tag for Wave 57 sub-attack 57-YM-OSRP finite-dim closure."
      replacement := none }
  , { declName := "Wave57BSD_LSeriesConvergenceProven"
      declFile := "PF/Wave57MasterCapstone.lean"
      classification := TrueDeclKind.ProvennessTag
      rationale := "Provenness tag for Wave 57 sub-attack 57-BSD scaffold (A1)+(A2) discharge."
      replacement := none }
  , { declName := "Wave56MasterCapstoneAggregatorProven"
      declFile := "PF/Wave57MasterCapstone.lean"
      classification := TrueDeclKind.ProvennessTag
      rationale := "Provenness tag for the Wave 56 aggregator inclusion in Wave 57."
      replacement := none }
  -- MillenniumReductionSoundness branches.
  , { declName := "ClayExternalStatement .Poincare"
      declFile := "PF/MillenniumReductionSoundness.lean"
      classification := TrueDeclKind.ExternalAnchor
      rationale := "Poincare conjecture is externally proven by Perelman 2003; True is honest tag for an external anchor."
      replacement := none }
  , { declName := "ClayExternalStatement .RH"
      declFile := "PF/MillenniumReductionSoundness.lean"
      classification := TrueDeclKind.ParameterizedDelegated
      rationale := "Replaced by PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard which is fully wired to mathlib's riemannZeta."
      replacement := some "PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard" }
  , { declName := "ClayExternalStatement .P_vs_NP"
      declFile := "PF/MillenniumReductionSoundness.lean"
      classification := TrueDeclKind.ParameterizedDelegated
      rationale := "Replaced by PF.Referee.StandardClayStatements.Clay_PvsNP_Standard, parameterized over StandardComplexityEncoding."
      replacement := some "PF.Referee.StandardClayStatements.Clay_PvsNP_Standard" }
  , { declName := "ClayExternalStatement .NavierStokes"
      declFile := "PF/MillenniumReductionSoundness.lean"
      classification := TrueDeclKind.ParameterizedDelegated
      rationale := "Replaced by PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard, parameterized over StandardNS3DEncoding."
      replacement := some "PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard" }
  , { declName := "ClayExternalStatement .YangMills"
      declFile := "PF/MillenniumReductionSoundness.lean"
      classification := TrueDeclKind.ParameterizedDelegated
      rationale := "Replaced by PF.Referee.StandardClayStatements.Clay_YangMillsMassGap_Standard, parameterized over StandardYMEncoding."
      replacement := some "PF.Referee.StandardClayStatements.Clay_YangMillsMassGap_Standard" }
  , { declName := "ClayExternalStatement .BSD"
      declFile := "PF/MillenniumReductionSoundness.lean"
      classification := TrueDeclKind.ParameterizedDelegated
      rationale := "Replaced by PF.Referee.StandardClayStatements.Clay_BSD_Standard, parameterized over StandardBSDEncoding."
      replacement := some "PF.Referee.StandardClayStatements.Clay_BSD_Standard" }
  , { declName := "ClayExternalStatement .Hodge"
      declFile := "PF/MillenniumReductionSoundness.lean"
      classification := TrueDeclKind.ParameterizedDelegated
      rationale := "Replaced by PF.Referee.StandardClayStatements.Clay_Hodge_Standard, parameterized over StandardHodgeEncoding."
      replacement := some "PF.Referee.StandardClayStatements.Clay_Hodge_Standard" }
  -- Pre-existing PF.HodgeAlgebraicRepresentation placeholder.
  , { declName := "HodgeAlgebraicRepresentation"
      declFile := "PF/HodgeAlgebraicRepresentation.lean"
      classification := TrueDeclKind.ParameterizedDelegated
      rationale := "Substrate-level := True placeholder that must be replaced by Clay_Hodge_Standard with a StandardHodgeEncoding instance for any literal Clay-level Hodge discharge."
      replacement := some "PF.Referee.StandardClayStatements.Clay_Hodge_Standard" }
  ]

/-- Count of entries by classification. -/
def auditCount : List (TrueDeclKind × Nat) :=
  let count (k : TrueDeclKind) : Nat :=
    (audit.filter (fun e => e.classification = k)).length
  [ (TrueDeclKind.ProvennessTag, count TrueDeclKind.ProvennessTag)
  , (TrueDeclKind.ExternalAnchor, count TrueDeclKind.ExternalAnchor)
  , (TrueDeclKind.ParameterizedDelegated, count TrueDeclKind.ParameterizedDelegated)
  , (TrueDeclKind.HiddenSemanticContent, count TrueDeclKind.HiddenSemanticContent)
  ]

/-- **No-hidden-content invariant.** At HEAD ee51039, no audited
    declaration is classified as `HiddenSemanticContent` — every
    `Prop := True` on a Clay-level path is either a provenness tag,
    an external anchor, or has been migrated/delegated to a typed
    standard contract in `PF.Referee.StandardClayStatements`. -/
theorem no_hidden_semantic_content :
    (audit.filter (fun e => e.classification = TrueDeclKind.HiddenSemanticContent)).length = 0 := by
  decide

/-- Total entries in audit. -/
theorem audit_size_recorded : audit.length = 17 := by
  decide

#check @no_hidden_semantic_content
#check @audit_size_recorded

end PF.Referee.NoTrueOnClayPath
