/-
# PF.Referee.YMSubstrateScopeAccountability

★★★★★ 2026-06-17 — UNASSAILABILITY: YANG–MILLS SCOPE ACCOUNTABILITY ★★★★★

The framework's Yang–Mills mass-gap discharge satisfies a typed 15-conjunct
`Clay_Standard`-encoded predicate on the SU(2) substrate (mathlib's
`Matrix.specialUnitaryGroup (Fin 2) ℂ`), with a structural mass-gap value
of `3/2`, NOT the literal Clay Yang–Mills statement on an arbitrary
compact simple gauge group with a continuum-limit-derived mass gap.

The honest scope is already partially documented in
`Bridge5_YM_SubstrateDischarge.lean`'s 18-clause `PF_YM_Bridge5_honestScope`
theorem. This file consolidates the substrate-vs-literal-Clay gap as
three named typed Props and provides a single referee-readable scope
capstone parallel to the Hodge and NS accountability files.

## What is proven

  `PF_YM_bridge5_yields_Clay_YangMillsMassGap_substrate :
     Clay_YangMillsMassGap_Standard PF_YMEncodingBridge5`

  Bridge 5 instantiates `StandardYMEncoding` with:

    * GaugeGroup := SU2Type
                   := ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)
    * QYM        := Bridge5SubstrateQYM  (V4 extended with SU(2) +
                                          three published-theorem anchors)
    * satisfiesClayAxioms — 15-conjunct typed property:
        (1)-(12) V4-inherited Bochner–Minlos / inf-dim mass-gap / OS / Wave 55C / Wave 57-YM
        (13)     Glimm–Jaffe 1981 SU(2) typed anchor       (Prop := True)
        (14)     Streater–Wightman 2000 SU(2) typed anchor (Prop := True)
        (15)     Osterwalder–Schrader 1973/75 SU(2) typed anchor (Prop := True)
    * massGap T := T.v4.v3.v2.Δ = 3/2 on the canonical witness.

  All 15 conjuncts and mass-gap positivity are discharged axiom-free.

## What is NOT proven

The literal Clay Yang–Mills statement asks: on `ℝ⁴` with arbitrary
compact simple gauge group `G`, does the quantum Yang–Mills theory
exist (Wightman or OS axioms) with a positive mass gap?

Three structural gaps separate Bridge 5 from the literal Clay statement:

  (G1) Gauge-group class restriction —
       `PF_YMEncodingBridge5.GaugeGroup := SU2Type`. The Clay statement
       quantifies over arbitrary compact simple gauge groups (SU(N) for
       all N ≥ 2, SO(N), Spin(N), Sp(N), the five exceptional groups).
       Bridge 5 closes only the SU(2) instance.

  (G2) Wave 56-pattern typed anchors are `Prop := True` markers —
       `GlimmJaffe_OS_SU2_TypedAnchor`, `StreaterWightman_SU2_TypedAnchor`,
       and `OsterwalderSchrader_SU2_TypedAnchor` are typed-open published-
       theorem anchors at the Wave 56 substrate tier. Each is literally
       `Prop := True` in the framework. They cite specific published
       theorems (Glimm–Jaffe 1981 §6, Streater–Wightman 2000 §3.3,
       Osterwalder–Schrader 1973/75) but do NOT formalise the literal
       continuum content.

  (G3) Mass-gap value is a canonical-witness structural assignment —
       `massGap pfBridge5Witness = 3/2` by definition (the V4/V3/V2
       inheritance chain). This is the framework's structural mass-gap
       parameter, NOT a mass gap derived from a continuum-limit YM
       construction. The literal Clay mass gap is `inf (spec H) > 0`
       on the genuine Hilbert space of the continuum quantum YM theory.

## What this file delivers

  * `PF_substrate_YM_fifteen_conjunct_witness` — the existing axiom-free
    Bridge 5 discharge as a single citable export.
  * `PF_substrate_YM_gauge_group_restriction` — typed witness that the
    encoding's `GaugeGroup` is `SU2Type`, not a universal compact-simple
    quantifier.
  * `PF_substrate_YM_wave56_typed_anchors_are_True_markers` — typed
    witness that the three Wave 56 published-theorem anchors are
    `Prop := True` substrate markers.
  * `PF_substrate_YM_mass_gap_is_structural_witness_value` — typed
    witness that `massGap pfBridge5Witness = 3/2` by canonical-witness
    construction, not by continuum-limit derivation.
  * `PF_substrate_YM_scope_capstone` — single citable theorem packaging
    the three structural gap markers with the substrate-level discharge.

No new mathematical content; Bridge 5's substrate discharge unchanged.
What is new is consolidated mechanical referee-readability of the
substrate-vs-literal-Clay scope distinction at the typed-Prop level.

ZERO project axioms. Kernel axioms only.
-/

import PF.YangMills.Bridge5_YM_SubstrateDischarge
import PF.Referee.StandardClayStatements

namespace PF.Referee.YMSubstrateScopeAccountability

open PrincipiaTractalis.YangMills.Bridge5_YM_SubstrateDischarge

/-! ## §1 — Fifteen-conjunct substrate witness (what IS proven) -/

/-- **★ The existing Bridge 5 YM substrate discharge, single-citation
    export ★** — on the SU(2) gauge-group substrate, the 15-conjunct
    typed `satisfiesClayAxioms` and the mass-gap positivity hold
    axiom-free on the canonical Bridge 5 witness with `Δ = 3/2`.

    This is `PF_YM_bridge5_yields_Clay_YangMillsMassGap_substrate`
    re-exported under the accountability namespace for citability
    alongside the gap markers in §2. -/
theorem PF_substrate_YM_fifteen_conjunct_witness :
    PF.Referee.StandardClayStatements.Clay_YangMillsMassGap_Standard
      PF_YMEncodingBridge5 :=
  PF_YM_bridge5_yields_Clay_YangMillsMassGap_substrate

/-! ## §2 — Substrate-vs-literal-Clay gap markers (what is NOT proven) -/

/-- **(G1) Gauge-group class restriction marker.**

    The encoding's `GaugeGroup` is `SU2Type`
    (= `↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)`), the SU(2) carrier.
    The literal Clay Yang–Mills statement quantifies over an arbitrary
    compact simple gauge group; Bridge 5 closes only the SU(2) instance.

    This Prop is the typed witness of the SU(2) substrate restriction. -/
def YM_gauge_group_is_SU2_substrate : Prop :=
  PF_YMEncodingBridge5.GaugeGroup = SU2Type

theorem YM_gauge_group_is_SU2_substrate_holds :
    YM_gauge_group_is_SU2_substrate := rfl

/-- **(G2) Wave 56-pattern published-theorem anchors are `Prop := True`
    markers.**

    The three SU(2) substrate anchors used as clauses (13)–(15) of
    `satisfiesClayAxioms` are literally `Prop := True` in PF, cited
    against three published theorems:

      * Glimm–Jaffe 1981 §6 OS reconstruction for SU(2) lattice
        gauge theory.
      * Streater–Wightman 2000 §3.3 Wightman axioms for
        SU(2)-equivariant fields.
      * Osterwalder–Schrader 1973/75 axioms for Euclidean Green's
        functions specialised to SU(2).

    Their typed-Prop encoding admits axiom-free discharge by `trivial`;
    the literal continuum content lives outside the framework's
    substrate. -/
def YM_wave56_typed_anchors_are_True_markers : Prop :=
  GlimmJaffe_OS_SU2_TypedAnchor ∧
  StreaterWightman_SU2_TypedAnchor ∧
  OsterwalderSchrader_SU2_TypedAnchor

theorem YM_wave56_typed_anchors_are_True_markers_hold :
    YM_wave56_typed_anchors_are_True_markers :=
  ⟨glimm_jaffe_OS_SU2_typed_anchor_holds,
   streater_wightman_SU2_typed_anchor_holds,
   osterwalder_schrader_SU2_typed_anchor_holds⟩

/-- **(G3) Mass-gap value is a canonical-witness structural assignment.**

    On the canonical Bridge 5 witness, `massGap pfBridge5Witness = 3/2`
    by definition of the V4/V3/V2 inheritance chain (`Δ := 3/2`). This is
    the framework's structural mass-gap parameter (the `α_YM`-derived
    value `α_YM² = 9/4`, hence `α_YM = 3/2`), NOT a mass gap derived
    from a continuum-limit construction of the SU(2) quantum YM theory.

    The literal Clay mass gap is `inf (spec H) > 0` on the Hilbert space
    of the continuum theory. -/
def YM_mass_gap_is_structural_witness_value : Prop :=
  PF_YMEncodingBridge5.massGap pfBridge5Witness = 3 / 2

theorem YM_mass_gap_is_structural_witness_value_holds :
    YM_mass_gap_is_structural_witness_value := rfl

/-! ## §3 — Single referee-readable scope capstone -/

/-- **★★★★★ YM SUBSTRATE-VS-LITERAL-CLAY SCOPE CAPSTONE ★★★★★** —

    The single citable referee-reading point for the framework's
    Yang–Mills mass-gap claim:

      (A) `Clay_YangMillsMassGap_Standard PF_YMEncodingBridge5` holds
          axiom-free (15-conjunct + mass-gap positivity).
      (B) The encoding's `GaugeGroup` is `SU2Type`
          — the SU(2) instance, not an arbitrary compact simple group.
      (C) The three Wave 56-pattern typed anchors
          (Glimm–Jaffe, Streater–Wightman, Osterwalder–Schrader, all SU(2))
          are `Prop := True` markers citing published theorems whose
          literal continuum content lives outside the framework's
          substrate.
      (D) `massGap pfBridge5Witness = 3/2` is a canonical-witness
          structural value (the `α_YM = 3/2` framework parameter),
          NOT a continuum-derived mass gap.

    What this theorem ESTABLISHES (mechanically, at the typed-Prop
    level): the framework's YM mass-gap discharge is the SU(2)
    substrate-level closure with a structural mass-gap parameter, NOT
    the literal Clay statement on arbitrary compact simple gauge groups
    with a continuum-derived mass gap. -/
theorem PF_substrate_YM_scope_capstone :
    -- (A) Substrate-level Clay_YangMillsMassGap_Standard.
    PF.Referee.StandardClayStatements.Clay_YangMillsMassGap_Standard
      PF_YMEncodingBridge5 ∧
    -- (B) SU(2) gauge-group restriction.
    YM_gauge_group_is_SU2_substrate ∧
    -- (C) Wave 56 typed anchors are Prop := True markers.
    YM_wave56_typed_anchors_are_True_markers ∧
    -- (D) Mass gap is a canonical-witness structural value.
    YM_mass_gap_is_structural_witness_value :=
  ⟨PF_substrate_YM_fifteen_conjunct_witness,
   YM_gauge_group_is_SU2_substrate_holds,
   YM_wave56_typed_anchors_are_True_markers_hold,
   YM_mass_gap_is_structural_witness_value_holds⟩

/-! ## §4 — Honest-scope marker -/

/-- **Honest-scope marker** — this file consolidates the
    substrate-vs-literal-Clay YM scope distinction from Bridge 5's
    18-clause `PF_YM_Bridge5_honestScope` into a tighter four-clause
    referee-reading point parallel to the Hodge and NS accountability
    files. The Bridge 5 substrate discharge is unchanged; the
    SU(2) restriction, the Wave 56 typed-anchor pattern, and the
    structural mass-gap-value status are now mechanically readable
    at the typed-Prop level alongside the discharge itself. -/
theorem PF_substrate_YM_scope_honest_scope : True := trivial

end PF.Referee.YMSubstrateScopeAccountability

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PF.Referee.YMSubstrateScopeAccountability.PF_substrate_YM_fifteen_conjunct_witness
#print axioms
  PF.Referee.YMSubstrateScopeAccountability.YM_gauge_group_is_SU2_substrate_holds
#print axioms
  PF.Referee.YMSubstrateScopeAccountability.YM_wave56_typed_anchors_are_True_markers_hold
#print axioms
  PF.Referee.YMSubstrateScopeAccountability.YM_mass_gap_is_structural_witness_value_holds
#print axioms
  PF.Referee.YMSubstrateScopeAccountability.PF_substrate_YM_scope_capstone
#print axioms
  PF.Referee.YMSubstrateScopeAccountability.PF_substrate_YM_scope_honest_scope
