/-
# Clay-axis substrate-position markers: what the three of them carry

**Date**: 2026-11-27 (Legion).

Three declarations in the corpus print `does not depend on any axioms`
in the aggregate build and sit under docstrings that describe
substantive closure on a Clay axis:

```lean
theorem rh_framework_standard_substrate_position : True := trivial
theorem literal_clay_NS_substrate_bridge_substrate_position : True := trivial
theorem cohen2026_pnpSpectral_substrate_position : True := trivial
```

Each name appears in exactly one file — its own — so until this file
nothing in the corpus recorded what they state as against what they
claim. `True` is the correct reading of an all-clean axiom bar here: a
`Prop` mentioning `ℝ` cannot be axiom-free, so "does not depend on any
axioms" on a declaration about spectra, or about Navier-Stokes
solutions, is itself the signal.

The three axes are not in the same condition, and this file keeps them
apart.

## RH — honest already, at the definition site

`clay_riemann_hypothesis_standard_framework_standard` is a real
conditional: it takes `Hardy1914_published_theorem_substrate_citation`
and `Mayer1991_Cohen2025_substrate_HP_program_citation` and concludes
`Clay_RiemannHypothesis_Standard`. The second unfolds to
`HilbertPolyaProgramConjecture_Positive`, whose own docstring in
`PF/Analytic/HilbertPolyaIdentificationBulletproof.lean` reads
"Status: PUBLISHED CONJECTURE; not a theorem. Encoded as a typed
hypothesis", and the discharge's own docstring says its scope is
"overtly hypothesis-conditional". `UnifiedTheoryPremiseAudit_r333` had
already adjudicated that premise.

So nothing on this axis is repaired here. §1 records that the marker is
`True`; §4 pins the two premises to their bodies, so that the word
"citation" in the second one's name cannot be read as a citation of a
theorem.

## NS — the bridge assumes its own conclusion

`Substrate_Forces_Literal_Clay_NS_Bridge` is

    FujitaKato1964_LocalExistence_Anchor →
    Leray1934_WeakSolutions_Anchor →
    Sobolevskii1959_AnalyticSemigroup_Anchor →
    BealeKatoMajda1984_BlowUpCriterion_Anchor →
    CaffarelliKohnNirenberg1982_PartialRegularity_Anchor →
    Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000

and all five named anchors are `def _ : Prop := True`. The predicate is
therefore logically equivalent to Fefferman's statement itself (§2), and
`substrate_to_literal_clay_NS_bridge_conditional`, whose body is its own
hypothesis variable, is the identity on it. The marker above it says
this file "exhibits the substrate's machine-checked closure of the Clay
NS axis on the literal Fefferman 2000 carrier".

The literal statement is not the defect. It is a faithful encoding of
Fefferman's problem over mathlib's `SchwartzMap` carrier on
`EuclideanSpace ℝ (Fin 3)`. The route to it is what carries nothing.

## P-vs-NP — seven anchors, one proposition

All seven `Cohen2026_*_Anchor` are `def _ : Prop := True`, so the
conjunction and the disjunction are each equivalent to `True` (§3), and
anchors about unrelated objects are literally the same proposition:
"the spectral gap Δ is positive" and "42,293 Lean jobs machine-checked"
are interchangeable by `rfl`. That the PNP axis was a vacuity artifact
was already on record from the 2026-11-15 substrate attack (the V2 → V4
pivot). What was missing was the in-kernel statement of it on these
seven anchors and this marker.

## What this file does and does not assert

It asserts no Clay statement and denies none. Every result is an
equivalence, an unfolding, or a hedge. The point is that the emptiness
is machine-checked and cannot drift back into a claim — the discipline
of `NavierStokesCapstoneDisclosure_2026_11_21` and
`ToECapstoneVacuityDisclosure_2026_11_22`. Nothing upstream is renamed,
reworded or deleted.
-/
import PF.Analytic.RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19
import PF.NavierStokes.Fefferman2000_LiteralClayNS3D_Statement_2026_06_19
import PF.TuringEncoding.Cohen2025_PNeqNP_Spectral_NamedAnchors_2026_06_19

set_option autoImplicit false

namespace PF.Referee.ClayAxisSubstratePositionMarkerDisclosure

open PF.Analytic.RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19
open PF.NavierStokes.FujitaKato1964_Substrate_NamedAnchors_2026_06_19
open PF.NavierStokes.Fefferman2000_LiteralClayNS3D_Statement_2026_06_19
open PF.TuringEncoding.Cohen2025_PNeqNP_Spectral_NamedAnchors_2026_06_19

/-! ## §1 — The three markers' types -/

/-- **The RH-axis marker is the canonical proof of `True`.**

    What this theorem records is that it *typechecks*. `= trivial` is
    available for every inhabitant of `True` by proof irrelevance, so
    the content here is the marker's type, not the proof of the
    equation. The same caveat applies to the two that follow. -/
theorem rh_marker_is_True :
    rh_framework_standard_substrate_position = trivial := rfl

/-- **The NS-axis marker is the canonical proof of `True`.** -/
theorem ns_marker_is_True :
    literal_clay_NS_substrate_bridge_substrate_position = trivial := rfl

/-- **The PNP-axis marker is the canonical proof of `True`.** -/
theorem pnp_marker_is_True :
    cohen2026_pnpSpectral_substrate_position = trivial := rfl

/-- **The NS marker is worth nothing toward the literal Clay statement.**

    Anything derivable from a proof of `True` was already derivable
    without it. This is the precise sense in which the marker does not
    exhibit "machine-checked closure of the Clay NS axis": it is not
    that the implication fails, it is that the implication *is* the
    conclusion. Neither side is asserted. -/
theorem ns_marker_adds_nothing :
    (True → Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000)
      ↔ Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000 :=
  ⟨fun h => h trivial, fun h _ => h⟩

/-! ## §2 — The NS bridge is equivalent to Fefferman's statement -/

/-- Each of the five named published-mathematics anchors is `True`. The
    papers they name are real; the propositions carrying their names
    constrain nothing. -/
theorem five_named_anchors_are_each_True :
    (FujitaKato1964_LocalExistence_Anchor ↔ True) ∧
    (Leray1934_WeakSolutions_Anchor ↔ True) ∧
    (Sobolevskii1959_AnalyticSemigroup_Anchor ↔ True) ∧
    (BealeKatoMajda1984_BlowUpCriterion_Anchor ↔ True) ∧
    (CaffarelliKohnNirenberg1982_PartialRegularity_Anchor ↔ True) :=
  ⟨⟨fun _ => trivial, fun _ => trivial⟩,
   ⟨fun _ => trivial, fun _ => trivial⟩,
   ⟨fun _ => trivial, fun _ => trivial⟩,
   ⟨fun _ => trivial, fun _ => trivial⟩,
   ⟨fun _ => trivial, fun _ => trivial⟩⟩

/-- The sharp instrument: two anchors naming different papers about
    different theorems are the *same* proposition. A hypothesis list
    built from them cannot distinguish local existence from partial
    regularity. -/
theorem fujitaKato_anchor_eq_caffarelliKohnNirenberg_anchor :
    FujitaKato1964_LocalExistence_Anchor
      = CaffarelliKohnNirenberg1982_PartialRegularity_Anchor := rfl

/-- **The bridge predicate is Fefferman's statement.**

    Because the five antecedents are each `True`, discharging them is
    free, and `Substrate_Forces_Literal_Clay_NS_Bridge` is logically
    equivalent to the literal Clay Navier-Stokes statement it was meant
    to be a bridge *to*.

    This proves the equivalence, not the statement. Neither side is
    asserted. -/
theorem substrate_forces_bridge_iff_literal_clay :
    Substrate_Forces_Literal_Clay_NS_Bridge
      ↔ Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000 :=
  ⟨fun h => h trivial trivial trivial trivial trivial,
   fun h _ _ _ _ _ => h⟩

/-- **So assuming the bridge is assuming Fefferman's statement.**

    `substrate_to_literal_clay_NS_bridge_conditional` has hypothesis
    `Substrate_Forces_Literal_Clay_NS_Bridge` and conclusion
    `Substrate_Forces_Literal_Clay_NS_Bridge`, and its body is the
    hypothesis variable. Composed with the equivalence above, the
    "substrate-to-literal bridge theorem (conditional)" reads: assume
    the Clay Navier-Stokes statement, conclude the Clay Navier-Stokes
    statement. -/
theorem assuming_the_bridge_is_assuming_fefferman
    (h : Substrate_Forces_Literal_Clay_NS_Bridge) :
    Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000 :=
  substrate_forces_bridge_iff_literal_clay.mp h

/-- And the converse, which is what makes the previous theorem a
    disclosure rather than a result: the bridge hypothesis is not a
    weaker thing that happens to imply the Clay statement, it is
    recoverable *from* the Clay statement, so nothing was transported
    across it. -/
theorem fefferman_gives_back_the_bridge
    (h : Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000) :
    Substrate_Forces_Literal_Clay_NS_Bridge :=
  substrate_forces_bridge_iff_literal_clay.mpr h

/-! ## §3 — The seven PNP anchors are one proposition -/

/-- The seven-anchor conjunction is equivalent to `True`, so
    `seven_cohen2026_pnpSpectral_anchors_conjunction_holds` — proved by
    seven `trivial`s — records nothing about the operator pair
    `(H_P, H_NP)`, about `α_P`, `α_NP`, or about the spectral gap its
    docstring names. -/
theorem seven_pnp_anchors_conjunction_iff_True :
    SevenCohen2026PNPSpectralAnchors_Conjunction ↔ True :=
  ⟨fun _ => trivial,
   fun _ => ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩⟩

/-- The disjunction likewise. A disjunction of `True`s does not become
    informative by being long. -/
theorem seven_pnp_anchors_disjunction_iff_True :
    SevenCohen2026PNPSpectralAnchors_Disjunction ↔ True :=
  ⟨fun _ => trivial, fun _ => Or.inl trivial⟩

/-- The sharp instrument on this axis: "the spectral gap is strictly
    positive" and "42,293 Lean jobs are machine-checked" are the same
    proposition. Two anchors a reader would take to be about mathematics
    and about build provenance respectively are interchangeable by
    `rfl`. -/
theorem spectral_gap_anchor_eq_jobcount_anchor :
    Cohen2026_SpectralGapDeltaPositive_Anchor
      = Cohen2026_Lean42293JobsMachineChecked_Anchor := rfl

/-- The remaining collisions of the same kind, recorded together so that
    the seven-element structure is visibly a one-element structure. -/
theorem all_seven_pnp_anchors_are_one_proposition :
    Cohen2026_PrimeFactorizationEncoding_Anchor
      = Cohen2026_HPAndHNPHamiltonians_Anchor ∧
    Cohen2026_HPAndHNPHamiltonians_Anchor
      = Cohen2026_GroundStateLambdaHP_Anchor ∧
    Cohen2026_GroundStateLambdaHP_Anchor
      = Cohen2026_GroundStateLambdaHNP_Anchor ∧
    Cohen2026_GroundStateLambdaHNP_Anchor
      = Cohen2026_SpectralGapDeltaPositive_Anchor ∧
    Cohen2026_SpectralGapDeltaPositive_Anchor
      = Cohen2026_ThreeBarriersCircumvention_Anchor ∧
    Cohen2026_ThreeBarriersCircumvention_Anchor
      = Cohen2026_Lean42293JobsMachineChecked_Anchor :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §4 — The RH premises, pinned to their bodies -/

/-- `Hardy1914_published_theorem_substrate_citation` is the nonemptiness
    of the set of positive on-line ζ-zero ordinates. Hardy 1914 is a
    genuine published theorem and this is a faithful encoding of it: the
    premise named after a citation really is one. -/
theorem hardy_citation_is_a_nonemptiness :
    Hardy1914_published_theorem_substrate_citation
      ↔ PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability.PositiveOnLineZetaZeroOrdinatesNonempty :=
  ⟨fun h => h, fun h => h⟩

/-- `Mayer1991_Cohen2025_substrate_HP_program_citation` is
    `HilbertPolyaProgramConjecture_Positive`, which its own definition
    site labels "PUBLISHED CONJECTURE; not a theorem".

    The two premises of the RH discharge are therefore not the same kind
    of object, and the shared suffix "substrate citation" flattens that.
    This is recorded, not repaired: the definition site is already
    honest and `UnifiedTheoryPremiseAudit_r333` already adjudicated the
    premise. Nothing here is renamed. -/
theorem hp_program_citation_is_the_open_conjecture :
    Mayer1991_Cohen2025_substrate_HP_program_citation
      ↔ PrincipiaTractalis.HilbertPolyaIdentificationBulletproof.HilbertPolyaProgramConjecture_Positive :=
  ⟨fun h => h, fun h => h⟩

/-- The discharge needs both premises. Re-exported here so that a reader
    who arrives at the `True` marker of §1 is pointed at the conditional
    that does the work, rather than away from it. -/
theorem rh_discharge_needs_both_premises
    (hHardy : Hardy1914_published_theorem_substrate_citation)
    (hHP : Mayer1991_Cohen2025_substrate_HP_program_citation) :
    PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard :=
  clay_riemann_hypothesis_standard_framework_standard hHardy hHP

/-! ## §5 — The non-claims, stated -/

/-- Nothing above decides the Clay Navier-Stokes problem in either
    direction. Recorded as a hedge so that the disclosure cannot be
    misread as a refutation: either the literal statement holds, or the
    bridge hypothesis is unavailable — and this file does not say
    which. -/
theorem no_verdict_on_literal_clay_NS :
    Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000 ∨
      ¬ Substrate_Forces_Literal_Clay_NS_Bridge := by
  by_cases hc : Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000
  · exact Or.inl hc
  · exact Or.inr (fun hb => hc (substrate_forces_bridge_iff_literal_clay.mp hb))

end PF.Referee.ClayAxisSubstratePositionMarkerDisclosure
