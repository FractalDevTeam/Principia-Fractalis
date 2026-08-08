/-
# r216: what the Principia Fractalis Substrate Theorem actually says.

★ 2026-08-08 r216 — an ADDITIVE, kernel-visible disclosure. Nothing is deleted,
weakened, renamed, or edited. Every declaration cited below is imported by
exact name and left exactly as it stands. The point is to put the logical
content of the flagship theorem IN THE KERNEL, so that it cannot drift back
out of the prose. ★

## What this file is

`PF/Referee/PrincipiaFractalisSubstrateTheorem.lean` states, at `:392-394`:

    theorem PrincipiaFractalisSubstrateTheorem :
        PFSubstrateAntecedents → PFSubstrateConsequences := by
      intro _h_antecedents -- ★ antecedent DISCARDED
      exact { ... }

and then, at `:481-483`:

    theorem PrincipiaFractalisSubstrateConsequences_holds_unconditionally :
        PFSubstrateConsequences :=
      PrincipiaFractalisSubstrateTheorem pfSubstrateAntecedents_realised

The antecedent is discarded (note the underscore in `_h_antecedents`), and the
conclusion is independently provable. `A → C` with `C` independently provable
carries **no information about `A`**. It is not a derivation of `C` from `A`.

This file proves that, in the kernel:

* §1 — *any* proposition whatsoever implies `PFSubstrateConsequences`. The
  specific content of `PFSubstrateAntecedents` plays no role.
* §2 — the flagship implication is derivable from its own conclusion. A
  derivation would run the other way.
* §3 — the converse is not established, and both sides are independently
  inhabited.
* §4 — field-level disclosures for the three fields where a cheap, true
  statement is available (C7, C17, C20/A5).
* §5 — what is *not* in dispute: the record contains genuine analysis, and it
  contains **zero** `Prop := True` fields.

## What does NOT follow

* `ch34A_substrate_theorem.tex:632` — "the substrate antecedents (A1)--(A5)
  ... **determine** the twenty-five consequences (C1)--(C25)". The Lean
  theorem does not establish determination in any deductive sense; §1 below
  shows the antecedents are interchangeable with `2 + 2 = 4`.
* `ch34A:684-696` — "A referee who accepts the implication form has accepted
  both that the substrate exists and that it determines the consequences.
  The framework's headline is **both**." Accepting the implication form
  commits a referee to nothing beyond accepting the unconditional form, since
  §2 below derives the implication from the unconditional form alone.

## This is a prose problem, not concealment

The Lean file already says all of this, in its own docstring, at `:374-377`:

  > **The Lean implication is therefore vacuously true**: it does not derive
  > the consequences FROM the antecedents in any deductive sense; it merely
  > records that both are inhabitable in the same file.

and at `:391` the source comment on the discarded hypothesis reads
"★ antecedent DISCARDED". The Lean layer is candid; the chapter gloss is not.
The ledger should record this as a headline/prose defect in ch34A, **not** as
concealment in the formalisation. The same file's own
`PrincipiaFractalisSubstrateTheoremHonestScope` record (`:496-516`) states the
"substrate DETERMINES the consequences" claim explicitly as a *claim*
(field S3), tagged `True`, i.e. as documentation rather than as content.

## What WOULD constitute a real derivation

A proof of at least one consequence `Cᵢ` that genuinely uses an antecedent:
a term whose elaboration *fails* when the antecedent hypothesis is removed
from the context. Concretely, the test is that

    theorem Ci_from_substrate (h : PFSubstrateAntecedents) : Cᵢ := <term>

does **not** typecheck as

    theorem Ci_unconditional : Cᵢ := <term>

with `h` deleted. No such consequence exists in the current corpus:
`PrincipiaFractalisSubstrateConsequences_holds_unconditionally` exhibits all
25 fields with the antecedent absent. §4 records the one place where the
antecedent is *syntactically* consumed (C7 via A3, C20 via A5 — projection
out of the record), and notes that even there the dependence is uninformative
because the projected conclusion is separately `rfl`-true or tautologous.

## What this file does NOT touch

The operator-algebra substrate results of r102--r113 are real, unconditional
mathematics and are entirely unaffected by anything here:

* `PF/SubstrateCompletionFaithful.lean:328` — `UHF_trace_faithful`
* `PF/SubstrateCompletionFaithful.lean:367` —
  `substrate_completion_simple_unconditional`

Those are theorems about a UHF completion, they consume real hypotheses, and
no claim in this file weakens them. The defect disclosed here is confined to
the ch34A *meta*-theorem's logical form and its chapter gloss.

## Cross-references

* `codex/AUDIT_RESPONSE_2026-08-06.md` §4.2 — the full 25-field
  classification (1 zero-witness existential, 7 definitional/tautologous,
  5 restricted-carrier, ~6 content-bearing, 6 re-packaging bundles) and the
  A5/C20 double-count finding.
* `PF/NavierStokesTypedContent_r215.lean` — the C4 (Navier--Stokes) field is
  already disclosed there in full and is NOT redone here. Summary of that
  result, for orientation only: the typed predicate `NS_Solution` contains no
  time derivative, no convective term, no pressure, no Laplacian and no
  viscosity; the C4 existential is witnessed by the zero field at the zero
  datum (`NS_via_substrate_existential_witnessed_by_zero`, r215 `:399`).

## Verification discipline

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True` field, no
existential introduced by this file. Every theorem below is closed and its
axiom set is printed in §6; all are ⊆ `[propext, Classical.choice, Quot.sound]`.
Import line for this stone:

    import PF.SubstrateTheoremContent_r216
-/

import PF.Referee.PrincipiaFractalisSubstrateTheorem

namespace PrincipiaTractalis.SubstrateTheoremContent

open PF.Referee.PrincipiaFractalisSubstrateTheorem

/-! ## §1 — The core disclosure: the antecedents do no work

`PFSubstrateConsequences` is provable outright
(`PrincipiaFractalisSubstrateConsequences_holds_unconditionally`,
`PrincipiaFractalisSubstrateTheorem.lean:481-483`). Therefore *every*
proposition implies it, and the flagship implication's antecedent is
interchangeable with any other proposition without loss.
-/

/-- **The consequences follow from any hypothesis whatsoever.**

    The flagship theorem `PrincipiaFractalisSubstrateTheorem` has the form
    `PFSubstrateAntecedents → PFSubstrateConsequences`. This theorem shows
    that the specific choice of `PFSubstrateAntecedents` plays **no role**:
    substituting any proposition `P` — `True`, `1 = 1`, an unrelated
    arithmetic identity, a statement about knot theory — yields an equally
    valid theorem, by the same one-line proof.

    Consequently the implication form cannot be evidence that the substrate
    antecedents *determine* the consequences, and the gloss at
    `ch34A_substrate_theorem.tex:632` ("(A1)--(A5) ... determine the
    twenty-five consequences (C1)--(C25)") does not follow from it. -/
theorem consequences_hold_under_any_hypothesis (P : Prop) :
    P → PFSubstrateConsequences :=
  fun _ => PrincipiaFractalisSubstrateConsequences_holds_unconditionally

/-- **Concrete instance of §1 with an unrelated hypothesis.**

    `2 + 2 = 4` bears no relation to the Timeless Field substrate, the
    α-rigidity skeleton, the Perelman anchor, the IBM 9-way hardware run, or
    the 143-problem dataset. It nonetheless implies all twenty-five
    consequences, by exactly the proof that `PFSubstrateAntecedents` does.

    This is the sharpest available statement of what the implication form
    conveys about the substrate: nothing. -/
theorem consequences_hold_under_an_unrelated_hypothesis :
    (2 : ℕ) + 2 = 4 → PFSubstrateConsequences :=
  consequences_hold_under_any_hypothesis _

/-- **Instance of §1 with the weakest possible hypothesis.**

    `True` is implied by every proposition, so this is the strongest of the
    §1 instances: it entails all the others, including the flagship
    implication itself (see §2). -/
theorem consequences_hold_under_True :
    True → PFSubstrateConsequences :=
  consequences_hold_under_any_hypothesis _

/-! ## §2 — The implication is derivable from its own conclusion

A derivation would run from the antecedents to the consequences. This runs
from the consequences to the implication. That direction is what makes the
implication vacuous: it is not evidence about `PFSubstrateAntecedents`, it is
a restatement of `PFSubstrateConsequences` with a discarded argument bolted
on.
-/

/-- **The flagship implication follows from its own conclusion.**

    Given `PFSubstrateConsequences`, the implication
    `PFSubstrateAntecedents → PFSubstrateConsequences` is immediate by
    discarding the hypothesis. This is precisely how
    `PrincipiaFractalisSubstrateTheorem` is proved at
    `PrincipiaFractalisSubstrateTheorem.lean:392-394` (`intro
    _h_antecedents`), and it is why the implication carries no information
    that the unconditional form does not already carry.

    A *derivation* would run the other way: it would exhibit a proof term
    that consumes a component of `PFSubstrateAntecedents` in an essential
    way, and that fails to elaborate when the hypothesis is removed. See the
    header, "What WOULD constitute a real derivation".

    Corollary for referees: accepting the implication form commits one to
    nothing beyond accepting the unconditional form. The claim at
    `ch34A:684-696` that a referee accepting the implication form "has
    accepted both that the substrate exists and that it determines the
    consequences" does not follow. -/
theorem substrate_implication_from_conclusion :
    PFSubstrateConsequences → (PFSubstrateAntecedents → PFSubstrateConsequences) :=
  fun hC _ => hC

/-! ## §3 — The converse is not established

**Nothing in the Principia Fractalis corpus proves**

    PFSubstrateConsequences → PFSubstrateAntecedents

*in a way that carries information*, and nothing in the corpus establishes
any nontrivial dependence of `C1`--`C25` on `A1`--`A5`. There is no theorem
here asserting the converse as a substantive result, because there is none to
assert, and a fake theorem in that slot would repeat in the other direction
exactly the error this file corrects.

What *is* true, and provable, is weaker and different: both sides are
independently inhabited. `PFSubstrateAntecedents` is proved outright by
`pfSubstrateAntecedents_realised` (`PrincipiaFractalisSubstrateTheorem.lean:117`),
and `PFSubstrateConsequences` is proved outright by
`PrincipiaFractalisSubstrateConsequences_holds_unconditionally` (`:481`).
Two independently provable propositions imply each other trivially, in both
directions, by discarding the hypothesis — which is exactly the situation the
Lean file's own docstring describes at `:374-377`: *"it merely records that
both are inhabitable in the same file."*
-/

/-- **The substrate antecedents are provable outright.**

    A re-export of `pfSubstrateAntecedents_realised`
    (`PrincipiaFractalisSubstrateTheorem.lean:117`), recorded here so that
    §3's point stands in the kernel: `PFSubstrateAntecedents` needs no
    hypothesis at all. It is not an assumption of the framework in the Lean
    layer; it is a proved proposition. -/
theorem substrate_antecedents_hold_unconditionally : PFSubstrateAntecedents :=
  pfSubstrateAntecedents_realised

/-- **The "converse" also holds, by discarding its hypothesis — and therefore
    also carries no information.**

    Read the name literally. This is **not** a derivation of the substrate
    antecedents from the consequences. It is the observation that, both sides
    being independently provable, the implication typechecks in *both*
    directions by the same vacuous move, so neither direction is evidence
    about the other side.

    Do not cite this as "the consequences imply the substrate". What it shows
    is that direction-of-implication statements between two provable
    propositions are empty. -/
theorem converse_implication_holds_by_discarding_its_hypothesis :
    PFSubstrateConsequences → PFSubstrateAntecedents :=
  fun _ => pfSubstrateAntecedents_realised

/-! ## §4 — Field-level disclosures

Only the fields where a cheap, true, kernel-checkable statement is available
are treated here. The full field-by-field classification of all twenty-five
consequences is in `codex/AUDIT_RESPONSE_2026-08-06.md` §4.2.

* **C4 (Navier--Stokes)** — already disclosed in
  `PF/NavierStokesTypedContent_r215.lean`; not redone here. Its existential
  is witnessed by the zero field at the zero datum and the predicate contains
  no PDE (see header).
* **C7** — definitional; treated below.
* **C17** — arithmetic; treated below.
* **C20 / A5** — true by construction of the dataset; treated below. Note
  this proposition appears as substrate antecedent **A5** *and* as consequence
  **C20**, so the same tautology is counted on both sides of the implication.
* Remaining fields — see the audit response; no claim is made about them here.
-/

/-- **C7 is a definitional unfolding, not a derived fact.**

    Consequence C7 (`Poincare_via_Perelman`,
    `PrincipiaFractalisSubstrateTheorem.lean:190-191`) is
    `α_Poincare = 1`. At `PF/CrossMillenniumSharedInvariants.lean:64` the
    definition reads

        noncomputable def α_Poincare : ℝ := 1

    so the field is closed by `rfl`. It records the numeral chosen in the
    definition. It is **not** a statement about Ricci flow, about Perelman's
    2002--2003 proof, or about the Poincaré conjecture, and nothing in the
    Lean layer connects it to any of those. The docstring's citation of
    "Perelman 2002--2003" is provenance for the choice of numeral, not
    content that the kernel checks. -/
theorem C7_alpha_Poincare_eq_one_is_definitional :
    PrincipiaTractalis.CrossMillenniumSharedInvariants.α_Poincare = 1 :=
  rfl

/-- **The one place the antecedent is syntactically consumed — and why it is
    still uninformative.**

    Antecedent A3 (`perelmanAlphaPoincareEqOne`, `:99-100`) and consequence
    C7 (`Poincare_via_Perelman`, `:190-191`) are the *same proposition*
    `α_Poincare = 1`. So C7 can be obtained by projecting A3 out of the
    antecedent record, and this proof term genuinely mentions `h` — it would
    not elaborate with `h` deleted.

    That is not a derivation in any useful sense. The conclusion is
    separately `rfl`-true (`C7_alpha_Poincare_eq_one_is_definitional` above),
    so the dependence on `h` conveys nothing: A3 is C7, restated on the other
    side of the arrow. Recorded here because the header's test for a real
    derivation ("does not typecheck when the antecedent is removed") is
    satisfiable by this trivial route, and the ledger should not be
    surprised by it later. -/
theorem C7_from_A3_by_projection (h : PFSubstrateAntecedents) :
    PrincipiaTractalis.CrossMillenniumSharedInvariants.α_Poincare = 1 :=
  h.perelmanAlphaPoincareEqOne

/-- **C17 is arithmetic and carries no geometric content.**

    Consequence C17 (`brst_H2_eq_78_eq_E6`,
    `PrincipiaFractalisSubstrateTheorem.lean:286`) is the natural-number
    identity `(78 : ℕ) = 48 + 26 + 4`. `norm_num` closes it.

    The field's name and docstring speak of "BRST H² = 78 = dim E_6". The
    Lean statement contains **no BRST complex**, no cohomology group, no
    differential, no gauge algebra, and no `E₆`. It is a sum of three
    numerals. It is true, and it is not evidence for any statement about
    BRST cohomology or about the dimension of `E₆`; those readings live
    entirely in the docstring. -/
theorem C17_brst_78_is_arithmetic : (78 : ℕ) = 48 + 26 + 4 := by
  norm_num

/-- **The 143-problem dataset is two hardcoded records, replicated.**

    `PF/Empirical/HundredFortyThreeProblems.lean:127-142` builds the dataset
    as

        the143Problems = List.replicate 72 (canonicalEntry .P)
                      ++ List.replicate 71 (canonicalEntry .NP)

    and this equation is closed by `rfl`. There are exactly two distinct
    entries in the list. -/
theorem the143Problems_is_two_replicated_records :
    PrincipiaTractalis.Empirical.the143Problems =
      List.replicate 72
          (PrincipiaTractalis.Empirical.canonicalEntry
            PrincipiaTractalis.Empirical.ProblemClass.P) ++
        List.replicate 71
          (PrincipiaTractalis.Empirical.canonicalEntry
            PrincipiaTractalis.Empirical.ProblemClass.NP) :=
  rfl

/-- **A5 = C20 is true by construction of the dataset.**

    `canonicalEntry c` sets `alphaMeasured := canonicalAlpha c`
    (`HundredFortyThreeProblems.lean:127`). Every entry of `the143Problems`
    is `canonicalEntry .P` or `canonicalEntry .NP`
    (`the143Problems_is_two_replicated_records` above). So every entry's
    measured α equals `canonicalAlpha` of its own class **by definition**,
    and the "universal fractal coherence" claim `α ∈ {√2, φ + 1/4}` is a
    schema-consistency check, not a measurement.

    This proposition is used **twice** in the flagship theorem: as substrate
    antecedent **A5** (`hundred43ProblemCoherence`, `:107-111`) and as
    consequence **C20** (`hundred43_problem_universal_coherence`, `:296-300`).
    The same tautology therefore appears on both sides of the implication.

    The corpus itself already says this: `HundredFortyThreeProblems.lean:190`
    carries the note "this theorem is a TAUTOLOGY over 143 copies of two
    hardcoded records ... **This theorem is NOT empirical evidence** of
    anything." Recorded here so the substrate-theorem layer carries it too. -/
theorem A5_C20_every_entry_alpha_is_its_class_canonical :
    ∀ p ∈ PrincipiaTractalis.Empirical.the143Problems,
      p.alphaMeasured =
        PrincipiaTractalis.Empirical.canonicalAlpha p.classLabel :=
  PrincipiaTractalis.Empirical.every_problem_is_fractally_coherent

/-- **C20 is A5, projected.**

    Like C7/A3 (above), consequence C20 is obtained by projecting antecedent
    A5 out of the record. The two field types are the same proposition, so
    this proof term mentions `h`; and again the dependence is uninformative,
    because the conclusion is a construction tautology
    (`A5_C20_every_entry_alpha_is_its_class_canonical`). -/
theorem C20_from_A5_by_projection (h : PFSubstrateAntecedents) :
    ∀ p ∈ PrincipiaTractalis.Empirical.the143Problems,
      p.alphaMeasured = Real.sqrt 2 ∨
      p.alphaMeasured = PrincipiaTractalis.phi + 1/4 :=
  h.hundred43ProblemCoherence

/-! ## §5 — What is NOT in dispute

A correction that overstates its own reach is the same error in the other
direction. Three things must be said plainly.

**(a) `PFSubstrateConsequences` has ZERO `Prop := True` fields.** All
twenty-five fields carry substantive propositions — equations between reals,
inequalities, universally quantified implications, and named structures. The
`True`-valued fields in that file belong to the *adjacent* record
`PrincipiaFractalisSubstrateTheoremHonestScope`
(`PrincipiaFractalisSubstrateTheorem.lean:496-516`), whose four fields
`substrate_level_machine_verified`, `consequences_compose_existing_landings`,
`framework_claim_is_substrate_determines_consequences` and
`not_literal_Clay_discharge_substrate_level_only` are each `: True` and are
explicitly documentation tags, discharged by `⟨trivial, trivial, trivial,
trivial⟩` at `:518-520`. An earlier audit conflated the two records and
attributed the `True` fields to `PFSubstrateConsequences`. That was wrong,
and this record carries the correction.

**(b) The consequences record contains real mathematics.** C15
(`phi_iit_lower_bound`, `:270-275`) is genuine analysis, discharged in
`PF/Consciousness/QuantumClassicalDecoherenceThreshold.lean:186` by an
honest exp/log argument. §5 below projects it out of the record, which is
itself a proof that the field is not `True`: a `True`-valued field could not
supply this conclusion.

**(c) The defect is in the implication's *form* and in the chapter's gloss,
not in the individual landings.** Many fields are definitional or
tautologous (§4), several are restricted-carrier, and roughly six are
content-bearing — see `codex/AUDIT_RESPONSE_2026-08-06.md` §4.2 for the
count. "The antecedents do no work" is a statement about the arrow, not a
verdict on every field behind it.
-/

/-- **The consequences record carries real analysis, not tags.**

    Projecting field C15 (`phi_iit_lower_bound`) out of
    `PFSubstrateConsequences` yields a genuine analytic statement: if the
    framework's `ch_2 = 19/20` threshold is met by `1 - exp(-Φ/2)`, then
    `Φ ≥ 2·log 20`. Its underlying proof
    (`QuantumClassicalDecoherenceThreshold.phi_iit_lower_bound_at_threshold`,
    `:186-207`) is an exp/log monotonicity argument with no tautology in it.

    This theorem also *witnesses* claim (a) above for at least one field: a
    field of type `True` could not have supplied this conclusion, so C15 is
    demonstrably not a `True` tag. -/
theorem consequences_contain_real_analysis (h : PFSubstrateConsequences) :
    ∀ Phi : ℝ,
      (19 : ℝ) / 20 ≤ 1 - Real.exp (-Phi / 2) →
        2 * Real.log 20 ≤ Phi :=
  h.phi_iit_lower_bound

/-- **The C15 bound, unconditionally.**

    The same analytic content, with no hypothesis, straight from the
    unconditional record. Not every field of `PFSubstrateConsequences` is
    hollow; this one is real, and it is stated here so that a reader of this
    disclosure file sees the fair side without leaving the file. -/
theorem phi_iit_lower_bound_holds :
    ∀ Phi : ℝ,
      (19 : ℝ) / 20 ≤ 1 - Real.exp (-Phi / 2) →
        2 * Real.log 20 ≤ Phi :=
  PrincipiaFractalisSubstrateConsequences_holds_unconditionally.phi_iit_lower_bound

/-! ## §6 — Axiom audit

Every theorem in this file, with its axiom set. All must be
⊆ `[propext, Classical.choice, Quot.sound]`. No `sorry`, no `native_decide`,
no `axiom` declared here.
-/

-- §1
#print axioms consequences_hold_under_any_hypothesis
#print axioms consequences_hold_under_an_unrelated_hypothesis
#print axioms consequences_hold_under_True

-- §2
#print axioms substrate_implication_from_conclusion

-- §3
#print axioms substrate_antecedents_hold_unconditionally
#print axioms converse_implication_holds_by_discarding_its_hypothesis

-- §4
#print axioms C7_alpha_Poincare_eq_one_is_definitional
#print axioms C7_from_A3_by_projection
#print axioms C17_brst_78_is_arithmetic
#print axioms the143Problems_is_two_replicated_records
#print axioms A5_C20_every_entry_alpha_is_its_class_canonical
#print axioms C20_from_A5_by_projection

-- §5
#print axioms consequences_contain_real_analysis
#print axioms phi_iit_lower_bound_holds

end PrincipiaTractalis.SubstrateTheoremContent
