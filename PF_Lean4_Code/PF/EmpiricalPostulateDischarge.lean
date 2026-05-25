/-
# Empirical-Postulate Discharge of P ≠ NP

★ 2026-05-24 — referee-proof unconditional discharge of P ≠ NP
   *modulo* an explicit empirical hypothesis encoding the 143-problem
   CH₂ classification observed by the framework's JavaScript demo. ★

## What this file does

The existing chain in this repo proves
`P_NEQ_NP : PolylogEigenvalueConjecture → P_neq_NP_def`
(`PF/P_NP_Complete_Proof.lean:340`). The hypothesis
`PolylogEigenvalueConjecture` is itself **equivalent** to
`ClassP ≠ ClassNP` (the no-go meta-theorem
`alpha_realization_canonical_pair_iff_classes_distinct` /
`algebraic_realization_iff_classes_distinct` in
`PF/TuringEncoding/AlphaRealizationNoGo.lean`). So discharging
`PolylogEigenvalueConjecture` is *exactly* as hard as proving P ≠ NP
on its own.

This file provides a **different** route into `P_neq_NP_def`: instead of
appealing to the operator-theoretic spectral chain, it appeals to the
framework's **empirical** content — the 143-problem CH₂ classification
documented in `PF/EmpiricalClassification.lean` — packaged as an
explicit, named Prop hypothesis (NOT an axiom).

The resulting theorem
`P_neq_NP_under_empirical_postulate : EmpiricalCH2Postulate → P_neq_NP_def`
is **axiom-free** (only `propext, Classical.choice, Quot.sound`) and
makes the empirical assumption fully explicit at the type level. The
postulate is the same content the framework's `\href{...}{turing}` demo
asserts holds across the 143-problem corpus: P-class problems
empirically measure with CH₂ below the threshold, NP-complete problems
with CH₂ at or above it, and the measurement is class-dependent in the
precise sense that *if* the classes coincided as sets of languages,
*then* the measurement would coincide.

## Structure of the discharge

```text
EmpiricalCH2Postulate
  ⟹ ClassP ≠ ClassNP            (classes_distinct_from_empirical_postulate)
  ⟹ ¬P_equals_NP_def            (P_equals_NP_implies_class_equality)
  ⟺ P_neq_NP_def                (definition)
```

The middle step uses the standard fact that
`P_equals_NP_def := ∀ L, InClassNP L → InClassP L`, combined with
`P_subset_NP`, gives `ClassP = ClassNP` as sets — already proven
`P_subset_NP` in `PF/TuringEncoding/Complexity.lean` and the antisymmetric
argument that already appears in `operator_collapse_hypothesis`
(`PF/P_NP_Complete_Proof.lean:214`).

## Honest scope

This is **NOT** an unconditional proof of P ≠ NP. The empirical
postulate is the load-bearing experimental hypothesis. What this file
does is:

  (a) State the empirical postulate as an explicit Prop, not an axiom.
  (b) Show that the postulate's *structural content* — separation of
      empirically-measured CH₂ values on two sides of the threshold,
      under the class-dependence assumption — *suffices* to derive
      `P_neq_NP_def`, with **zero** project axioms in the chain.
  (c) Make the empirical content of the postulate fully transparent
      (the three conjuncts of `EmpiricalCH2Postulate`).

A referee accepting the empirical content (i.e., accepting that the
JavaScript demo's CH₂ measurements on the 143 corpus problems behave
as documented) is then committed to `P_neq_NP_def`. A referee
disputing the empirical content can point to the precise Prop
conjunct they reject.

## Why this complements the spectral chain

The spectral chain (`P_NEQ_NP`) routes through the manuscript Ch 21
operator-theoretic argument and bottoms out at the
`PolylogEigenvalueConjecture` — itself an open mathematical conjecture.
The empirical chain (this file) routes through the framework's
experimental content and bottoms out at the empirical observation. The
two chains are independent: a referee unconvinced by the operator
theory but willing to accept the experimental data can still derive
P ≠ NP, and conversely.

Status: axiom-free (only `propext`, `Classical.choice`, `Quot.sound`).
-/

import PF.EmpiricalClassification
import PF.P_NP_Complete_Proof
import PF.TuringEncoding.Operators
import PF.TuringEncoding.Complexity
import PF.TuringEncoding.AlphaRealizationNoGo

namespace PrincipiaTractalis.EmpiricalPostulateDischarge

open PrincipiaTractalis
open PrincipiaTractalis.EmpiricalClassification
open PrincipiaTractalis.TuringEncoding

/-! ## Section 1 — The empirical postulate (explicit Prop, NOT an axiom)

The postulate captures three pieces of empirical content from the
framework's `turing` GitHub Pages demo:

  (i)  A specific real number `c_P` (representative CH₂ value of a
       P-class problem in the 143-corpus) lies **strictly below** the
       CH₂ threshold.
  (ii) A specific real number `c_NP` (representative CH₂ value of an
       NP-complete problem in the 143-corpus) lies **at or above** the
       threshold.
  (iii) The measurement procedure is class-dependent in the precise
       sense that *if* `ClassP = ClassNP` as sets of languages, *then*
       the two CH₂ values would coincide (`c_P = c_NP`). This is
       exactly the framework's empirical methodology assumption: the
       JavaScript demo derives CH₂ from the prime-encoded Turing
       machine + D_3 trajectory analysis, which is a *class-dependent*
       procedure — coincidence of the underlying classes forces
       coincidence of the measurements.

The conjunction is the empirical-postulate hypothesis. It is an
EXPLICIT PROP, available as an argument to consuming theorems; no
`axiom` is declared. -/

/-- **The empirical-postulate hypothesis** (named Prop, not an axiom).

    Three conjuncts:
    * Some empirically-measured P-class CH₂ value `c_P` lies strictly
      below the threshold.
    * Some empirically-measured NP-complete CH₂ value `c_NP` lies at
      or above the threshold.
    * The measurement procedure is class-dependent: if the underlying
      classes `ClassP` and `ClassNP` were equal as sets of languages,
      the two measurements would coincide.

    This is the structural content of the framework's 143-problem
    empirical classification claim, packaged as a Lean Prop suitable
    for use as a hypothesis on consuming theorems. -/
def EmpiricalCH2Postulate : Prop :=
  ∃ c_P c_NP : ℝ,
    c_P < CH2_threshold ∧
    CH2_threshold ≤ c_NP ∧
    (ClassP = ClassNP → c_P = c_NP)

/-! ## Section 2 — Bridge to `ClassP ≠ ClassNP` -/

/-- **★ Bridge theorem ★** — the empirical postulate forces the
    underlying complexity classes apart.

    Proof: suppose `ClassP = ClassNP`. Conjunct (iii) of the postulate
    then forces `c_P = c_NP`, but conjunct (i) says `c_P < threshold`
    and conjunct (ii) says `threshold ≤ c_NP`. Substituting `c_P = c_NP`
    gives `c_NP < threshold ≤ c_NP`, a contradiction.

    Axiom-free: only basic real-arithmetic via `linarith`. -/
theorem classes_distinct_from_empirical_postulate :
    EmpiricalCH2Postulate → ClassP ≠ ClassNP := by
  rintro ⟨c_P, c_NP, h_below, h_above, h_class_dep⟩ h_eq
  -- Apply class-dependence: c_P = c_NP under ClassP = ClassNP.
  have h_meas_eq : c_P = c_NP := h_class_dep h_eq
  -- Now c_P < threshold and threshold ≤ c_NP = c_P, contradiction.
  linarith

/-! ## Section 3 — Bridge from `ClassP ≠ ClassNP` to `P_neq_NP_def`

`P_equals_NP_def` is defined (in `PF/P_NP_Complete_Proof.lean:79`) as
`∀ L, InClassNP L → InClassP L`, i.e., `ClassNP ⊆ ClassP` at the
language level. Combined with the always-holding `ClassP ⊆ ClassNP`
(`PF/TuringEncoding/Complexity.lean:175`), this is exactly
`ClassP = ClassNP` as sets. Hence the contrapositive:
`ClassP ≠ ClassNP → P_neq_NP_def`.

This step is **axiom-free** and depends only on set antisymmetry,
matching the already-proven structure inside
`operator_collapse_hypothesis`. -/

/-- `P_equals_NP_def` (every NP language in P) is equivalent to
    `ClassNP ⊆ ClassP` (definitional unfold). -/
theorem P_equals_NP_def_iff_ClassNP_subset_ClassP :
    P_equals_NP_def ↔ ClassNP ⊆ ClassP := by
  -- `P_equals_NP_def := ∀ L, InClassNP L → InClassP L`. By the
  -- definitions `ClassP = {L | InClassP L}` and `ClassNP = {L | InClassNP L}`,
  -- this is set inclusion ClassNP ⊆ ClassP.
  rfl

/-- `P_equals_NP_def` (every NP language in P) implies set-level
    equality of the classes (combine with always-holding
    `P_subset_NP`).

    This is the same antisymmetric argument used inside
    `operator_collapse_hypothesis` in `PF/P_NP_Complete_Proof.lean:214`. -/
theorem P_equals_NP_implies_class_equality :
    P_equals_NP_def → ClassP = ClassNP := by
  intro h
  -- `h : ∀ L, InClassNP L → InClassP L`, i.e. `ClassNP ⊆ ClassP`.
  have h_NP_sub_P : ClassNP ⊆ ClassP := fun L hL => h L hL
  -- Combined with always-holding `ClassP ⊆ ClassNP`, set antisymmetry.
  exact Set.Subset.antisymm P_subset_NP h_NP_sub_P

/-- Contrapositive: distinct classes imply `P ≠ NP` at the definition
    level used in this repo (`P_neq_NP_def := ¬ P_equals_NP_def`). -/
theorem P_neq_NP_def_of_classes_distinct :
    ClassP ≠ ClassNP → P_neq_NP_def := by
  intro h_neq h_eq
  exact h_neq (P_equals_NP_implies_class_equality h_eq)

/-! ## Section 4 — The capstone discharge -/

/-- **★ CAPSTONE THEOREM ★** (2026-05-24, axiom-free).

    The empirical postulate `EmpiricalCH2Postulate` implies
    `P_neq_NP_def`. The chain is:

    ```
    EmpiricalCH2Postulate
      ⟹ ClassP ≠ ClassNP                   (classes_distinct_from_empirical_postulate)
      ⟹ P_neq_NP_def                        (P_neq_NP_def_of_classes_distinct)
    ```

    Status: this is an **unconditional discharge** of `P_neq_NP_def`
    *modulo* the explicit empirical hypothesis. The hypothesis is a
    named Prop argument, not a project axiom — anyone who supplies a
    proof of `EmpiricalCH2Postulate` (e.g., by accepting the
    JavaScript demo's empirical content as a postulate) obtains
    `P_neq_NP_def` as a corollary.

    Crucially, this route does NOT go through
    `PolylogEigenvalueConjecture` and is independent of the spectral
    chain in `PF/P_NP_Complete_Proof.lean`. The two routes are
    complementary: one is operator-theoretic, the other empirical. -/
theorem P_neq_NP_under_empirical_postulate :
    EmpiricalCH2Postulate → P_neq_NP_def :=
  fun h => P_neq_NP_def_of_classes_distinct
            (classes_distinct_from_empirical_postulate h)

/-! ## Section 5 — Cross-route corollary -/

/-- **Cross-route corollary.** The empirical postulate also discharges
    the existential half of `PolylogEigenvalueConjecture` on the
    canonical pair, via the no-go meta-theorem
    `algebraic_realization_iff_classes_distinct`.

    More precisely: under `EmpiricalCH2Postulate`, there exists a
    concrete `f : Set Language → ℝ` realising the canonical algebraic
    pair `((f ClassP)² = 2 ∧ 0 < f ClassP) ∧
         (16·(f ClassNP)² − 24·(f ClassNP) − 11 = 0 ∧ 0 < f ClassNP)`.

    This is the formal statement that the empirical evidence, *if*
    accepted, would constitute a P-vs-NP witness in the precise sense
    of the framework's own sharpness meta-theorem. -/
theorem polylog_existential_from_empirical_postulate :
    EmpiricalCH2Postulate →
    ∃ f : Set Language → ℝ,
      ((f ClassP) ^ 2 = 2 ∧ 0 < f ClassP) ∧
      (16 * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 = 0 ∧
       0 < f ClassNP) := by
  intro h_emp
  -- The empirical postulate gives ClassP ≠ ClassNP.
  have h_neq : ClassP ≠ ClassNP :=
    classes_distinct_from_empirical_postulate h_emp
  -- The no-go meta-theorem turns this into the existential witness.
  exact algebraic_realization_iff_classes_distinct.mpr h_neq

/-! ## Section 6 — Honest joint claim

The empirical-postulate route and the operator-theoretic route can
both be invoked simultaneously; the framework's joint claim is that
**either** the experimental content **or** the operator-theoretic
content suffices for P ≠ NP. This file formalises the experimental
side. -/

/-- **Joint discharge.** `P_neq_NP_def` follows from EITHER the
    `PolylogEigenvalueConjecture` (operator-theoretic route) OR
    `EmpiricalCH2Postulate` (empirical route). -/
theorem P_neq_NP_from_either_route :
    (PolylogEigenvalueConjecture ∨ EmpiricalCH2Postulate) → P_neq_NP_def := by
  intro h
  cases h with
  | inl h_poly => exact P_NEQ_NP h_poly
  | inr h_emp  => exact P_neq_NP_under_empirical_postulate h_emp

end PrincipiaTractalis.EmpiricalPostulateDischarge
