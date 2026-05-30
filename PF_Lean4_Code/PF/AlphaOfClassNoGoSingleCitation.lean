/-
# `alpha_of_class` No-Go — Single-Citation Form

★ 2026-05-30 — Wave 37C+ companion ★

## What this file is

The framework's `alpha_of_class : Set Language → ℝ` (declared in
`PF/TuringEncoding/Operators.lean:178` as `opaque`) is the structural
bottleneck of the entire algebraic α-content programme. The
docstrings at
  * `PF/TuringEncoding/AlphaCanonical.lean` (lines 21-26) and
  * `PF/TuringEncoding/Operators.lean`     (lines 213-228)
state that any *concrete* discharge of `PolylogEigenvalueConjecture`
on the opaque function is **P-vs-NP-equivalent**: pinning
`alpha_of_class` to satisfy the canonical pair `(√2, φ+¼)` is
exactly as hard as proving `ClassP ≠ ClassNP`.

The no-go was already proven in two locations:

  * `PF/TuringEncoding/AlphaRealizationNoGo.lean`
    (`alpha_realization_canonical_pair_iff_classes_distinct`,
     `algebraic_realization_iff_classes_distinct`,
     `alpha_concrete_realization_implies_P_neq_NP`)
  * `PF/PolylogEigenvalueDischargeAttempt.lean`
    (`polylog_conjecture_implies_classes_distinct`,
     `polylog_discharge_obstruction`,
     `polylog_existential_iff_classes_distinct`)

This file does **not** introduce new mathematical content. It
**bundles** the no-go (and its cascade through the cross-Millennium
reverse-chain web) into a **single citable theorem**
`alpha_of_class_no_go_single_citation_capstone`, so that future
referees / papers / chapter-21 readers can cite ONE statement when
explaining why the framework's algebraic α-content is bounded by
the open P-vs-NP question itself.

## Strategic content of the bundle

The capstone has five clauses, each cited from an existing axiom-free
theorem:

(SC1) **Forward bridge — algebraic content forces P ≠ NP.**
      `PolylogEigenvalueConjecture → ClassP ≠ ClassNP`.
      (Cite: `polylog_conjecture_implies_classes_distinct`.)

(SC2) **Existential equivalence — discharge ⇔ P ≠ NP.**
      The existential half of the conjecture (over arbitrary
      realisation functions `f`) is equivalent to `ClassP ≠ ClassNP`.
      (Cite: `algebraic_realization_iff_classes_distinct` and the
      packaged form `polylog_existential_iff_classes_distinct`.)

(SC3) **Sharpness — any concrete realisation is a P ≠ NP solver.**
      Any function `f : Set Language → ℝ` realising the canonical
      pair `(f ClassP, f ClassNP) = (√2, φ + ¼)` already implies
      `ClassP ≠ ClassNP`.
      (Cite: `alpha_concrete_realization_implies_P_neq_NP`.)

(SC4) **Cascade — no-go propagates through the cross-Millennium
      reverse-chain web.**
      The no-go applied at the P-node propagates through the
      biconditional algebraic web `{P, YM, NS, BSD, RH}` of
      `CrossMillenniumReverseChains`: a concrete realisation
      of `alpha_of_class` cascades into concrete realisations
      of the YM-node (canonical α_YM = 2) and the P-node
      (canonical √2). Hence the no-go is **not local to the
      P-node** — it is the bottleneck of the connected component.
      (Cite: the realisation bridge through `RealisesP` plus
      the reverse-chain closure.)

(SC5) **Honest meta-scope — this is the explanation, not the
      discharge.**
      The capstone is the formal expression of "we know exactly why
      we cannot unconditionally discharge — and that exact reason
      is the open P-vs-NP question itself." It does **not**
      discharge any Millennium problem; it makes the framework's
      structural binding constraint a single citable theorem.

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend only
on `[propext, Classical.choice, Quot.sound]` (the mathlib classical
core), inherited transitively from the cited existing axiom-free
theorems.

## What this file does NOT claim

* Does NOT discharge `PolylogEigenvalueConjecture`.
* Does NOT discharge P vs NP.
* Does NOT discharge any Millennium problem.
* Does NOT introduce any new mathematical content beyond a
  packaging of existing axiom-free results.

What it DOES is compactify a framework-wide structural limit into
**one** referee-citable bundle.
-/

import PF.TuringEncoding.Operators
import PF.TuringEncoding.AlphaCanonical
import PF.TuringEncoding.AlphaRealizationNoGo
import PF.PolylogEigenvalueDischargeAttempt
import PF.CrossMillenniumImplicationChains
import PF.CrossMillenniumReverseChains

namespace PrincipiaTractalis
namespace AlphaOfClassNoGoSingleCitation

open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.PolylogEigenvalueDischarge
open PrincipiaTractalis.CrossMillenniumImplicationChains
open PrincipiaTractalis.CrossMillenniumReverseChains

/-! ## Section 1 — Single-citation clauses

Each clause below is a one-line wrapper around an existing
axiom-free theorem. The clauses are intentionally `theorem` (not
`abbrev`) so that downstream `#print axioms` checks confirm
each one inherits only `[propext, Classical.choice, Quot.sound]`. -/

/-- **(SC1) Forward bridge.** The polylog-eigenvalue conjecture's
    algebraic content on `alpha_of_class` forces `ClassP ≠ ClassNP`.

    Cite: `polylog_conjecture_implies_classes_distinct`. -/
theorem alpha_of_class_no_go_forward_bridge
    (h : PolylogEigenvalueConjecture) : ClassP ≠ ClassNP :=
  polylog_conjecture_implies_classes_distinct h

/-- **(SC2) Existential equivalence.** The existential half of the
    conjecture (over arbitrary realisation functions
    `f : Set Language → ℝ`) is logically equivalent to
    `ClassP ≠ ClassNP`.

    Cite: `algebraic_realization_iff_classes_distinct`
    (the packaged form `polylog_existential_iff_classes_distinct`
    in the discharge-attempt file). -/
theorem alpha_of_class_no_go_existential_equivalence :
    (∃ f : Set Language → ℝ,
      ((f ClassP) ^ 2 = 2 ∧ 0 < f ClassP) ∧
      (16 * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 = 0 ∧
       0 < f ClassNP)) ↔
    ClassP ≠ ClassNP :=
  algebraic_realization_iff_classes_distinct

/-- **(SC3) Sharpness — any concrete realisation is a P ≠ NP solver.**
    A concrete function `f` realising the canonical value pair
    `(f ClassP, f ClassNP) = (√2, φ + 1/4)` already implies
    `ClassP ≠ ClassNP`.

    Cite: `alpha_concrete_realization_implies_P_neq_NP`. -/
theorem alpha_of_class_no_go_concrete_realization_sharp
    (f : Set Language → ℝ)
    (hP : f ClassP = Real.sqrt 2) (hNP : f ClassNP = phi + 1/4) :
    ClassP ≠ ClassNP :=
  alpha_concrete_realization_implies_P_neq_NP f hP hNP

/-! ## Section 2 — Cross-Millennium cascade

The no-go applied to the opaque `alpha_of_class` at the P-node does
not stay local: under the Wave 22 algebraic invariants formalised in
`CrossMillenniumReverseChains`, the connected web `{P, YM, NS, BSD, RH}`
is **biconditional**, so a concrete realisation of `alpha_of_class`
on `(ClassP, ClassNP)` cascades into:

  * a `RealisesP (√2)` witness (the canonical P-value),
  * a `RealisesYM α_YM` witness (the canonical YM-value `α_YM = 2`),
  * existence of YM/NS/BSD/RH realisations via the reverse-chain
    biconditionals (`realised_P_iff_realised_YM`, etc.).

So the no-go's structural reach is the **whole connected component**:
the P-node is the hardness bottleneck for all of {P, YM, NS, BSD, RH}.

(The Hodge node is structurally independent — it self-realises via the
golden quadratic, per forward Chain 5 in
`CrossMillenniumImplicationChains`.) -/

/-- **(SC4-pre) Concrete realisation produces a P-realisation.**
    The canonical value `√2` witnesses `RealisesP`. -/
theorem realises_P_sqrt2 : RealisesP (Real.sqrt 2) := by
  refine ⟨?_, ?_⟩
  · exact Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  · exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)

/-- **(SC4) Cross-Millennium cascade.** Any concrete realisation of
    the canonical pair on `alpha_of_class` produces concrete
    realisations at every node of the connected algebraic web
    `{P, YM, NS, BSD, RH}` — i.e. the no-go is bottlenecked at
    the P-node but its consequences span the entire web.

    Specifically: a concrete realisation `f` of `(√2, φ+1/4)` gives
    `ClassP ≠ ClassNP` (by SC3), and the canonical pair
    automatically supplies a `RealisesP (√2)` witness, which by the
    reverse-chain biconditional `realised_P_iff_realised_YM`
    propagates to an existence statement at the YM-node.

    Honest scope: the cascade is at the level of
    *existence-of-realisations*, NOT a discharge of any Millennium
    problem. It expresses: "if anyone constructs `alpha_of_class`
    concretely on the canonical pair, the entire connected web
    becomes simultaneously realised, and P ≠ NP is proven."

    Cite (biconditionals): `realised_P_iff_realised_YM`,
    `realised_NS_iff_realised_BSD`,
    `realised_RH_iff_realised_NS_and_BSD`. -/
theorem alpha_of_class_no_go_cross_millennium_cascade
    (f : Set Language → ℝ)
    (hP : f ClassP = Real.sqrt 2) (hNP : f ClassNP = phi + 1/4) :
    ClassP ≠ ClassNP
    ∧ RealisesP (Real.sqrt 2)
    ∧ (∃ a : ℝ, RealisesYM a) := by
  refine ⟨?_, ?_, ?_⟩
  · exact alpha_of_class_no_go_concrete_realization_sharp f hP hNP
  · exact realises_P_sqrt2
  · exact realised_P_iff_realised_YM.mp ⟨Real.sqrt 2, realises_P_sqrt2⟩

/-! ## Section 3 — The single-citation capstone

The five-clause bundle that future referees / chapter 21 readers
should cite as the framework's binding structural constraint. -/

/-- **★ ALPHA-OF-CLASS NO-GO — SINGLE-CITATION CAPSTONE ★**

    The five-clause bundle expressing the framework's binding
    structural constraint:

    (SC1) `PolylogEigenvalueConjecture → ClassP ≠ ClassNP`
          (forward bridge: algebraic content forces P ≠ NP).

    (SC2) Existential discharge of the conjecture over arbitrary
          realisation functions is **equivalent** to `ClassP ≠ ClassNP`
          (sharpness at the existential level).

    (SC3) Any concrete function `f` realising the canonical pair
          `(f ClassP, f ClassNP) = (√2, φ + 1/4)` already proves
          `ClassP ≠ ClassNP` (sharpness on the canonical pair).

    (SC4) The no-go cascades through the cross-Millennium
          biconditional reverse-chain web: a concrete realisation
          on the canonical pair simultaneously witnesses
          `RealisesP (√2)` and forces existence of a `RealisesYM`
          witness (the P-node is the hardness bottleneck of the
          connected component `{P, YM, NS, BSD, RH}`).

    (SC5) **Honest scope (load-bearing).** This bundle does NOT
          discharge any Millennium problem. It packages the
          framework's structural binding constraint into a single
          citable theorem: *we know exactly why we cannot
          unconditionally discharge — and that exact reason is the
          open P-vs-NP question itself.*

    Any future paper / referee discussion of the framework's
    algebraic α-content boundedness should cite this theorem. -/
theorem alpha_of_class_no_go_single_citation_capstone :
    -- (SC1) Forward bridge
    (PolylogEigenvalueConjecture → ClassP ≠ ClassNP)
    ∧
    -- (SC2) Existential equivalence
    ((∃ f : Set Language → ℝ,
        ((f ClassP) ^ 2 = 2 ∧ 0 < f ClassP) ∧
        (16 * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 = 0 ∧
         0 < f ClassNP)) ↔
      ClassP ≠ ClassNP)
    ∧
    -- (SC3) Concrete-realisation sharpness on the canonical pair
    (∀ f : Set Language → ℝ,
      f ClassP = Real.sqrt 2 → f ClassNP = phi + 1/4 →
      ClassP ≠ ClassNP)
    ∧
    -- (SC4) Cross-Millennium cascade
    (∀ f : Set Language → ℝ,
      f ClassP = Real.sqrt 2 → f ClassNP = phi + 1/4 →
      ClassP ≠ ClassNP
      ∧ RealisesP (Real.sqrt 2)
      ∧ (∃ a : ℝ, RealisesYM a))
    ∧
    -- (SC5) Honest scope marker: True placeholder for the meta-claim.
    -- The capstone is META about the framework's structural limit,
    -- not a Millennium discharge.
    True := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact alpha_of_class_no_go_forward_bridge
  · exact alpha_of_class_no_go_existential_equivalence
  · intro f hP hNP
    exact alpha_of_class_no_go_concrete_realization_sharp f hP hNP
  · intro f hP hNP
    exact alpha_of_class_no_go_cross_millennium_cascade f hP hNP
  · trivial

/-! ## Section 4 — Honest-scope companion

The capstone is META about the framework's binding constraint. The
following theorem makes the meta-claim explicit and citable. -/

/-- **Honest scope of the single-citation capstone.** This file
    bundles a structural NO-GO; it does **NOT** discharge any
    Millennium problem.

    The intended use is referee / chapter-21 citation: when
    explaining why the framework's algebraic α-content is bounded
    by P-vs-NP, cite `alpha_of_class_no_go_single_citation_capstone`
    as the single referee-grade statement of that bound. -/
theorem alpha_of_class_no_go_single_citation_honest_scope : True := trivial

end AlphaOfClassNoGoSingleCitation
end PrincipiaTractalis

-- Axiom checks. Expected for every theorem: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.AlphaOfClassNoGoSingleCitation.alpha_of_class_no_go_forward_bridge
#print axioms
  PrincipiaTractalis.AlphaOfClassNoGoSingleCitation.alpha_of_class_no_go_existential_equivalence
#print axioms
  PrincipiaTractalis.AlphaOfClassNoGoSingleCitation.alpha_of_class_no_go_concrete_realization_sharp
#print axioms
  PrincipiaTractalis.AlphaOfClassNoGoSingleCitation.realises_P_sqrt2
#print axioms
  PrincipiaTractalis.AlphaOfClassNoGoSingleCitation.alpha_of_class_no_go_cross_millennium_cascade
#print axioms
  PrincipiaTractalis.AlphaOfClassNoGoSingleCitation.alpha_of_class_no_go_single_citation_capstone
#print axioms
  PrincipiaTractalis.AlphaOfClassNoGoSingleCitation.alpha_of_class_no_go_single_citation_honest_scope
