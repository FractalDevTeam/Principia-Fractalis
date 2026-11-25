/-
# Typed-Prop vacuity disclosure — Andrews–Curtis carrier and the GI citation Props

Author: Pablo Cohen
Date: November 25, 2026

Two modules in the corpus define `Prop := True` declarations that carry no
disclosure of their own emptiness anywhere in their text. Every other such
declaration in the corpus says so in its own docstring; these two did not. This
file says so IN THE KERNEL rather than leaving a referee to discover it.

ADDITIVE ONLY. Nothing is weakened, renamed, or removed. Every theorem the two
modules prove, they still prove.

## 1. `PF/NumberTheory/AndrewsCurtisFrameworkAttack.lean`

The carrier is

    structure BalancedPresentation where
      rank : ℕ
      rank_pos : rank ≥ 1

and that is the whole of it: **the carrier records no relators.** The
Andrews–Curtis conjecture is a statement about relator tuples and the moves that
act on them, so the carrier is blind to precisely the data the conjecture is
about. `BalancedPresentation`'s own docstring is honest — it says "Symbolic
carrier" — but two declarations downstream of it are not:

* `PresentsTrivialGroup (_p) : Prop := True` is documented as "the
  presentation's normal closure equals the whole free group on `rank`
  generators". It states nothing of the kind; it is constantly `True`, so it
  holds of every presentation, including presentations of nontrivial groups.
* `AndrewsCurtisConjecture` is documented as the conjecture in "**literal**,
  typed form". It is not literal. With the hypothesis constantly `True` and the
  conclusion `∃ moveCount : ℕ, moveCount ≥ 0` — satisfied by `0` — the encoded
  statement is PROVABLE, and `andrewsCurtisConjecture_as_encoded_is_provable`
  below proves it in four tokens.

**Nothing is withdrawn by this disclosure.** No theorem in that module claims
`AndrewsCurtisConjecture`; it is defined and never inhabited, and the capstone
`structure AndrewsCurtisFrameworkAttack` has no field of that type. Its fields
are the α-identities, the three concrete witnesses, the substrate match, and the
two typed named results. So the defect is an overstated *definition*, not a
claimed solution — which is why the repair is to state what the definition says,
not to retract a result.

**Removal condition (RULE 4).** This scaffold comes down when
`BalancedPresentation` is replaced by a carrier that records relators, which is
writable at the current pin: mathlib has `FreeGroup` (12 files) and
`PresentedGroup (rels : Set (FreeGroup α))` in
`Mathlib/GroupTheory/PresentedGroup.lean:34`. A faithful carrier is a pair
`(n : ℕ, rels : Fin n → FreeGroup (Fin n))`; `PresentsTrivialGroup` becomes
`Subsingleton (PresentedGroup (Set.range rels))`; and the AC moves become an
explicitly generated relation on such tuples. Until that exists, the three
declarations above are symbolic shape only, and this file is what says so.

The sharp instrument is `balancedPresentation_determined_by_rank`: two
presentations of the same rank are *equal* in this encoding. So
`⟨x | x⟩` and `⟨x | x²⟩` — the first presenting the trivial group, the second
ℤ/2 — are the same object here, and `PresentsTrivialGroup` holds of it. That is
the precise sense in which the hypothesis is not the Andrews–Curtis hypothesis.

**Status of removal condition (1): the hypothesis side is DISCHARGED.**
`PF/NumberTheory/AndrewsCurtisFaithfulCarrier_2026_11_25.lean` builds the
faithful carrier — `rels : Fin rank → FreeGroup (Fin rank)` — and defines
`PresentsTrivialGroupFaithful p := Subsingleton (PresentedGroup (Set.range
p.rels))`. It proves the trivial presentation presents the trivial group at
EVERY rank, proves `⟨x | x²⟩` does not, and proves that the old carrier's
`forget` identifies exactly those two presentations BY `rfl`. So the ⟨x | x⟩ /
⟨x | x²⟩ sentence above is now a theorem rather than a remark. What remains of
condition (1) is the conclusion side: the AC-move relation and its invariants.
Until that lands, no declaration in either file is an Andrews–Curtis conjecture
of any form, and none is named as one.

## 2. `PF/Empirical/ProblemClassTriClass_2026_06_22.lean`

Three declarations name published-and-proven results and carry none of their
content:

* `Babai2016_quasi_poly_GI_citation : Prop := ∃ c : ℝ, c > 0 ∧ True`
* `Schoning1988_low_hierarchy_GI_citation : Prop := True`
* `GoldwasserSipser1986_GI_in_coNP_citation : Prop := True`

The named results are real (Babai 2016 as corrected by Helfgott 2017; Schöning
1988, JCSS 37:312–323; Goldwasser–Sipser, STOC 1986). The Props are not those
results. `schoning_eq_goldwasserSipser` below is the sharpest demonstration
available: two citations of two different papers are *the same Prop by `rfl`*,
which no bibliographic content could survive.

These three are inert — nothing in the corpus consumes them as a hypothesis, and
no module imported that file before this one. They are bibliography, and this
file names them as bibliography.

**Removal condition (RULE 4).** These become content-bearing only once there is
a model of computation to state them against. Mathlib has no complexity class,
no time-bounded computation predicate, and no Arthur–Merlin protocol, so a
faithful encoding is NOT writable at this pin — unlike §1. Until one exists the
honest status is "named, not formalized", and the three Props must never be
cited as evidence for the tri-class assignment. The CSV's `peak_alpha = 1.41`
measurement stands or falls on its own, with no support from these Props.
-/

import Mathlib.Tactic
import PF.NumberTheory.AndrewsCurtisFrameworkAttack
import PF.Empirical.ProblemClassTriClass_2026_06_22

set_option autoImplicit false

namespace PF.Referee.TypedPropVacuityDisclosure

open PF.NumberTheory.AndrewsCurtisFrameworkAttack
open PF.Empirical.TriClass

/-! ## §1 — Andrews–Curtis: the carrier is relator-blind -/

/-- The carrier records no relators, so a `BalancedPresentation` is determined by
its rank alone. Two presentations of equal rank are *equal* in this encoding —
`⟨x | x⟩` and `⟨x | x²⟩` among them. -/
theorem balancedPresentation_determined_by_rank
    (p q : BalancedPresentation) (h : p.rank = q.rank) : p = q := by
  obtain ⟨r, hr⟩ := p
  obtain ⟨s, hs⟩ := q
  have h' : r = s := h
  subst h'
  rfl

/-- `PresentsTrivialGroup` is constantly `True`: it holds of every presentation,
not only of presentations of the trivial group. -/
theorem presentsTrivialGroup_is_vacuous (p : BalancedPresentation) :
    PresentsTrivialGroup p ↔ True :=
  Iff.rfl

/-- `ACEquivalentToTrivial` is satisfied by `moveCount = 0`, so it too is
equivalent to `True` and records no AC-move sequence. -/
theorem acEquivalentToTrivial_is_vacuous (p : BalancedPresentation) :
    ACEquivalentToTrivial p ↔ True :=
  iff_true_intro ⟨0, Nat.zero_le 0⟩

/-- **The sharp fact.** `AndrewsCurtisConjecture` as encoded is PROVABLE. A
statement provable in four tokens is not the open Andrews–Curtis conjecture, and
this theorem is the proof that it is not. -/
theorem andrewsCurtisConjecture_as_encoded_is_provable :
    AndrewsCurtisConjecture :=
  fun _p _h => ⟨0, Nat.zero_le 0⟩

/-- Equivalently: the encoded conjecture carries no content. -/
theorem andrewsCurtisConjecture_as_encoded_is_vacuous :
    AndrewsCurtisConjecture ↔ True :=
  iff_true_intro andrewsCurtisConjecture_as_encoded_is_provable

/-- The hypothesis and the conclusion of the encoded conjecture are the same
Prop, for every presentation — the implication it states is between
indistinguishable sides. -/
theorem andrewsCurtis_hypothesis_iff_conclusion (p : BalancedPresentation) :
    PresentsTrivialGroup p ↔ ACEquivalentToTrivial p :=
  (presentsTrivialGroup_is_vacuous p).trans
    (acEquivalentToTrivial_is_vacuous p).symm

/-! ## §2 — The graph-isomorphism citation Props -/

/-- Babai 2016's citation Prop is satisfied by `c = 1` and carries none of the
`n^O((log n)^2)` content its docstring describes. -/
theorem babai2016_citation_is_vacuous :
    Babai2016_quasi_poly_GI_citation ↔ True :=
  iff_true_intro ⟨1, by norm_num, trivial⟩

/-- Schöning 1988's citation Prop is `True`. -/
theorem schoning1988_citation_is_vacuous :
    Schoning1988_low_hierarchy_GI_citation ↔ True :=
  Iff.rfl

/-- Goldwasser–Sipser 1986's citation Prop is `True`. -/
theorem goldwasserSipser1986_citation_is_vacuous :
    GoldwasserSipser1986_GI_in_coNP_citation ↔ True :=
  Iff.rfl

/-- **The sharpest instrument.** Two citations of two different papers — a
low-hierarchy theorem and an Arthur–Merlin protocol — are the *same Prop by
`rfl`*. No bibliographic content survives that identification. -/
theorem schoning_eq_goldwasserSipser :
    Schoning1988_low_hierarchy_GI_citation
      = GoldwasserSipser1986_GI_in_coNP_citation :=
  rfl

/-! ## §3 — The disclosure, bundled

Wired by inferred type (`def` + `And.intro`), never by transcribing statements
into field types. -/

def typedPropVacuityDisclosureBundle :=
  And.intro andrewsCurtisConjecture_as_encoded_is_vacuous
    (And.intro babai2016_citation_is_vacuous
      (And.intro schoning1988_citation_is_vacuous
        (And.intro goldwasserSipser1986_citation_is_vacuous
          schoning_eq_goldwasserSipser)))

end PF.Referee.TypedPropVacuityDisclosure
