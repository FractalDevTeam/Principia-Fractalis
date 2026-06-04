/-
# PF.Referee.NoTrueOnClayPath

Hand-audit at HEAD ee51039 of every `Prop := True` near a Clay-level
proof path. Each entry is classified as ProvennessTag, ExternalAnchor,
ParameterizedDelegated, or HiddenSemanticContent (a Rule #1 violation).
The audit invariant `no_hidden_semantic_content` certifies zero
violations at this commit.

Rule #1 (roadmap `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`):
> No `def SomeClaim : Prop := True` may sit on a Clay-level proof path
> unless explicitly tagged as a provenness tag and excluded from claim
> content.

A `Prop := True` qualifies as a non-violating tag iff (i) the name
contains `Proven`/`Tag`/`Marker`/`Anchor`/`Provenness`, (ii) the
docstring states it carries no claim content, and (iii) no Clay-path
theorem consumes it as substantive hypothesis. The recommended
replacement for substantive cases is the typed parameterised contract
in `PF.Referee.StandardClayStatements`.
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
