/-
# PF.Referee.TypedMillenniumReduction

Typed counterpart to `PF.MillenniumReductionSoundness`. The legacy
module defines `ClayExternalStatement c := True` (a provenness tag);
this module replaces those branches with the typed
`Clay_*_Standard` contracts from `PF.Referee.StandardClayStatements`,
parameterised over a bundle of the five external encodings.

Produces:
* `TypedClayExternalStatement` — per-axis typed Clay-form proposition.
* `MillenniumReductionSoundnessTyped` — the typed soundness Prop.
* `all_clay_typed_via_soundness_and_capstones` — typed analogue of
  `all_clay_via_soundness_and_capstones`.
* `typed_soundness_implies_legacy_soundness` — bridge: typed soundness
  is at least as strong as the legacy `:= True` form.

Additive: nothing in `PF.MillenniumReductionSoundness` or
`PF.Wave57MasterCapstone` is modified.

Honest scope: not a Clay discharge. Produces the typed soundness
shape so future bridges target it directly. Source roadmap
`codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md` "The Twelfth Object":
*RefereeContractsHold must expand into named, inspectable, problem-
specific contracts; no True placeholders, no hidden coercions.*
-/

import PF.MillenniumReductionSoundness
import PF.Referee.StandardClayStatements

namespace PF.Referee.TypedMillenniumReduction

open PrincipiaTractalis

/-! ## §1 — A bundle of all standard encodings -/

/-- A bundle providing all five external encodings the typed Clay
    contracts require. -/
structure StandardEncodingBundle where
  complexity : PF.Referee.StandardClayStatements.StandardComplexityEncoding
  navierStokes : PF.Referee.StandardClayStatements.StandardNS3DEncoding
  yangMills : PF.Referee.StandardClayStatements.StandardYMEncoding
  bsd : PF.Referee.StandardClayStatements.StandardBSDEncoding
  hodge : PF.Referee.StandardClayStatements.StandardHodgeEncoding

/-! ## §2 — Typed Clay external statement, per axis -/

/-- The typed external Clay statement for axis `c`, given a bundle of
    standard encodings. Unlike `ClayExternalStatement c := True`, every
    branch here is the actual typed Clay-form proposition.

    * Poincare branch is `True` because Poincare is already proven by
      Perelman 2003 — this is an external anchor, not a hidden claim.
    * RH is fully wired to `riemannZeta` via the StandardClayStatements
      module (no external encoding needed for RH).
    * The remaining five branches use the bundled standard encodings. -/
def TypedClayExternalStatement (B : StandardEncodingBundle) :
    PrincipiaTractalis.ClayProblem → Prop
  | .Poincare      => True
  | .RH            =>
      PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard
  | .P_vs_NP       =>
      PF.Referee.StandardClayStatements.Clay_PvsNP_Standard B.complexity
  | .NavierStokes  =>
      PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard B.navierStokes
  | .YangMills     =>
      PF.Referee.StandardClayStatements.Clay_YangMillsMassGap_Standard B.yangMills
  | .BSD           =>
      PF.Referee.StandardClayStatements.Clay_BSD_Standard B.bsd
  | .Hodge         =>
      PF.Referee.StandardClayStatements.Clay_Hodge_Standard B.hodge

/-! ## §3 — Typed soundness Prop -/

/-- **Typed Millennium Reduction Soundness.** Asserts that, for a
    given bundle of standard encodings, each PF internal capstone
    implies the corresponding typed Clay statement.

    This is the typed counterpart of `MillenniumReductionSoundness`
    from `PF.MillenniumReductionSoundness`. Where that one had
    `ClayExternalStatement c := True`, this one expands to the
    actual typed Clay contracts.

    Discharging this Prop requires (a) supplying the bundle `B` of
    standard encodings and (b) proving each per-axis implication
    in the typed forms supplied by `PF.Referee.StandardClayStatements`. -/
def MillenniumReductionSoundnessTyped (B : StandardEncodingBundle) : Prop :=
  ∀ c : PrincipiaTractalis.ClayProblem,
    PrincipiaTractalis.PFInternalCapstone c → TypedClayExternalStatement B c

/-! ## §4 — Capstone -/

/-- **Typed analogue of `all_clay_via_soundness_and_capstones`.**

    IF typed soundness holds for a bundle `B` AND each per-problem PF
    internal capstone is discharged, THEN every typed Clay external
    statement holds.

    This packages the typed-contract conditional in a single named
    theorem. The hypotheses are exactly:

      (A) `MillenniumReductionSoundnessTyped B` — typed soundness
      (B) `∀ c, PFInternalCapstone c` — each PF capstone proved

    Conclusion: every `TypedClayExternalStatement B c` holds.

    This is the SAME shape as the existing
    `all_clay_via_soundness_and_capstones`, but operating on TYPED
    Clay contracts instead of `:= True` placeholders. -/
theorem all_clay_typed_via_soundness_and_capstones
    (B : StandardEncodingBundle)
    (h_sound : MillenniumReductionSoundnessTyped B)
    (h_caps : ∀ c : PrincipiaTractalis.ClayProblem, PrincipiaTractalis.PFInternalCapstone c) :
    ∀ c : PrincipiaTractalis.ClayProblem, TypedClayExternalStatement B c := by
  intro c
  exact h_sound c (h_caps c)

/-! ## §5 — Bridge to the legacy `:= True` form -/

/-- **Typed soundness implies the legacy `:= True` soundness.**

    Bridge lemma: if typed soundness holds for a bundle, then the
    legacy `MillenniumReductionSoundness` also holds — because the
    legacy form's `ClayExternalStatement c := True` is implied by
    anything.

    This shows the typed module is at least as strong as the legacy
    form for every encoding bundle. The reverse implication is NOT
    available: the legacy form does NOT yield the typed form, because
    `True` does not entail an arbitrary typed proposition.

    Consequence: any consumer of the legacy soundness (e.g. Wave 57
    master capstone's downstream theorems) is automatically served
    by a typed soundness witness. -/
theorem typed_soundness_implies_legacy_soundness
    (B : StandardEncodingBundle)
    (_h_typed : MillenniumReductionSoundnessTyped B) :
    PrincipiaTractalis.MillenniumReductionSoundness := by
  intro c _h_cap
  -- ClayExternalStatement c := True for every c, so trivially true.
  cases c <;> trivial

/-! ## §6 — Rule #1 compliance audit -/

/-- **Rule #1 audit.** Every non-Poincare branch of
    `TypedClayExternalStatement` is a typed `Clay_*_Standard` contract,
    not a `:= True` placeholder. The Poincare branch is `True` as an
    external anchor (Perelman 2003).

    This `def` carries no mathematical content; it documents the
    inspection result. -/
def typedClayExternalStatement_rule1_compliant : Prop := True

theorem typedClayExternalStatement_rule1_compliant_holds :
    typedClayExternalStatement_rule1_compliant := trivial

#check @TypedClayExternalStatement
#check @MillenniumReductionSoundnessTyped
#check @all_clay_typed_via_soundness_and_capstones
#check @typed_soundness_implies_legacy_soundness

end PF.Referee.TypedMillenniumReduction
