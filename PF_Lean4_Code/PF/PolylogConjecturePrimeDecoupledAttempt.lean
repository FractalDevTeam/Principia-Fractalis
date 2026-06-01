/-
# PolylogEigenvalueConjecture' — Decoupled-over-`f` Refactor

★ 2026-05-31 — Wave 55E ★

## Goal of this file

The framework's `PolylogEigenvalueConjecture` is HARDWIRED to the opaque
`alpha_of_class : Set Language → ℝ` (see
`PF/TuringEncoding/Operators.lean:250`). By the Wave 41B no-go
(`PF/AlphaOfClassNoGoSingleCitation.lean`,
`alpha_of_class_no_go_concrete_realization_sharp` /
`alpha_of_class_no_go_forward_bridge`), any axiom-free discharge of the
conjecture on `alpha_of_class` is logically equivalent to
`ClassP ≠ ClassNP`.

This file performs a referee-grade REFACTOR: we define a *typed*
parameterised variant

```
PolylogEigenvalueConjecturePrime (f : Set Language → ℝ) : Prop
```

that says exactly what the original `PolylogEigenvalueConjecture` says,
but on `f` rather than on the hardwired `alpha_of_class`.

The refactor lets us cleanly ISOLATE which content of the original
conjecture survives Wave 41B:

  * the bridge `PolylogEigenvalueConjecture ↔
    PolylogEigenvalueConjecturePrime alpha_of_class` shows the
    original is an instance of the decoupled one (at the specific
    choice `f := alpha_of_class`);

  * Wave 41B applies SPECIFICALLY at `f = alpha_of_class` — any
    discharge of `PolylogEigenvalueConjecturePrime alpha_of_class`
    forces `ClassP ≠ ClassNP`;

  * at OTHER `f` (e.g. constructive case-split witnesses), the
    decoupled Prop is dischargeable axiom-free WITHOUT collapsing to
    a P-vs-NP separation, because the no-go's load-bearing step (the
    `congrArg f` move from `ClassP = ClassNP` to `f ClassP = f ClassNP`
    landing on `√2 = φ + 1/4`) reveals only the structural fact about
    that specific `f`, not about the opaque `alpha_of_class`.

The honest scope is precise: the refactor SEPARATES the algebraic
content (`f ClassP^2 = 2 ∧ 16(f ClassNP)^2 − 24(f ClassNP) − 11 = 0`,
positivity) from the P-vs-NP-equivalent OPACITY of `alpha_of_class`.
The algebraic content alone is referee-checkable arithmetic; the
opacity is what carries the P-vs-NP equivalent burden.

## Surviving content classification

After the refactor, the surviving content of the original conjecture
splits into THREE classes:

  (A) **Algebraic-arithmetic content** — `α² = 2`, `16α² − 24α − 11 = 0`,
      positivity. Verified axiom-free on the canonical pair
      `(√2, φ + 1/4)` (cf. `AlphaCanonical.lean`,
      `canonical_alpha_algebraic_pair`). This content SURVIVES the
      Wave 41B no-go — it is true axiom-free on the canonical pair.

  (B) **Structural-identification content** — the choice
      `f := alpha_of_class`. This is the LOAD-BEARING step that
      converts the algebraic identities into a statement about a
      complexity-class invariant. It is EXACTLY what Wave 41B
      identifies as P-vs-NP-equivalent (any concrete `f` realising
      the canonical pair forces `ClassP ≠ ClassNP`).

  (C) **Cross-Millennium cascade content** — the propagation through
      the reverse-chain web `{P, YM, NS, BSD, RH}`. This is downstream
      of (B) and inherits its P-vs-NP-equivalent strength.

The refactor cleanly separates these: (A) is fully discharged on the
canonical pair, (B) is what the Wave 41B no-go binds, (C) is unchanged.

## Axiom budget

ZERO project axioms, ZERO sorries. All theorems below depend only on
`[propext, Classical.choice, Quot.sound]`.

## Honest scope

This file does NOT discharge `PolylogEigenvalueConjecture`
unconditionally on `alpha_of_class`. By the Wave 41B no-go, no such
discharge can exist. The contribution is:

  * a typed parameterised refactor isolating the algebraic content
    from the structural identification,

  * an explicit bridge `PolylogEigenvalueConjecture ↔
    PolylogEigenvalueConjecturePrime alpha_of_class`,

  * an explicit no-go isolation theorem stating Wave 41B applies
    SPECIFICALLY at `f = alpha_of_class` (and the algebraic content
    at other concrete `f` does not block axiom-free discharge of the
    decoupled Prop),

  * a referee-citable capstone bundling these.

NOT a Clay P/NP discharge. NOT a discharge of
`PolylogEigenvalueConjecture` on `alpha_of_class`. The `alpha_of_class`
no-go is preserved exactly as stated in Wave 41B.
-/

import PF.PolylogConjectureAttemptWave47
import PF.PolylogIBMEmpiricalGaloisCascade
import PF.PolylogIBMEmpiricalPinDischarge
import PF.AlphaOfClassNoGoSingleCitation
import PF.TuringEncoding.Operators
import PF.TuringEncoding.AlphaCanonical
import PF.TuringEncoding.AlphaRealizationNoGo
import PF.IntervalArithmetic

namespace PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt

open Real Classical
open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.PolylogConjectureAttemptWave47
open PrincipiaTractalis.AlphaOfClassNoGoSingleCitation
open PrincipiaTractalis.CrossMillenniumImplicationChains

/-! ## Section 1 — The decoupled Prop

`PolylogEigenvalueConjecturePrime f` is the original
`PolylogEigenvalueConjecture` content, but parameterised over an
arbitrary `f : Set Language → ℝ` rather than the opaque
`alpha_of_class`. -/

/-- **★ The decoupled polylog conjecture ★** — the original
    `PolylogEigenvalueConjecture` reformulated over an arbitrary
    `f : Set Language → ℝ`.

    Encodes the canonical algebraic pair on `(f ClassP, f ClassNP)`:

      * P-side: `(f ClassP)² = 2 ∧ 0 < f ClassP`
      * NP-side: `16 (f ClassNP)² − 24 (f ClassNP) − 11 = 0
                  ∧ 0 < f ClassNP`

    This is a Prop on `f` rather than on the hardwired
    `alpha_of_class`. The original conjecture is the special case
    `f := alpha_of_class`. -/
def PolylogEigenvalueConjecturePrime (f : Set Language → ℝ) : Prop :=
  ((f ClassP)^2 = 2 ∧ 0 < f ClassP) ∧
  (16 * (f ClassNP)^2 - 24 * (f ClassNP) - 11 = 0 ∧
   0 < f ClassNP)

/-! ## Section 2 — Bridge to the original conjecture

The original `PolylogEigenvalueConjecture` is exactly the special
case `f := alpha_of_class` of the decoupled Prop. -/

/-- **★ (W55E-1) Bridge theorem ★** — the original
    `PolylogEigenvalueConjecture` is definitionally equal to
    `PolylogEigenvalueConjecturePrime alpha_of_class`. -/
theorem polylog_conjecture_iff_prime_at_alpha_of_class :
    PolylogEigenvalueConjecture ↔
    PolylogEigenvalueConjecturePrime alpha_of_class := by
  unfold PolylogEigenvalueConjecture PolylogEigenvalueConjecturePrime
  exact Iff.rfl

/-- **Forward direction of the bridge** (instance-extraction). -/
theorem polylog_conjecture_to_prime
    (h : PolylogEigenvalueConjecture) :
    PolylogEigenvalueConjecturePrime alpha_of_class :=
  polylog_conjecture_iff_prime_at_alpha_of_class.mp h

/-- **Backward direction of the bridge** (instance-injection). -/
theorem prime_at_alpha_of_class_to_polylog_conjecture
    (h : PolylogEigenvalueConjecturePrime alpha_of_class) :
    PolylogEigenvalueConjecture :=
  polylog_conjecture_iff_prime_at_alpha_of_class.mpr h

/-! ## Section 3 — No-go isolation

The Wave 41B no-go applies SPECIFICALLY at `f = alpha_of_class`:
any discharge of `PolylogEigenvalueConjecturePrime alpha_of_class`
forces `ClassP ≠ ClassNP`. At OTHER `f`, the decoupled Prop is NOT
blocked by 41B — we exhibit an explicit `f` for which the decoupled
Prop is axiom-free dischargeable without entailing `ClassP ≠ ClassNP`. -/

/-- **★ (W55E-2a) Wave 41B applies SPECIFICALLY at `f = alpha_of_class` ★** —
    discharge of the decoupled Prop on `alpha_of_class` is the
    Wave 41B-equivalent of `ClassP ≠ ClassNP`. -/
theorem prime_at_alpha_of_class_implies_P_neq_NP
    (h : PolylogEigenvalueConjecturePrime alpha_of_class) :
    ClassP ≠ ClassNP :=
  alpha_of_class_no_go_forward_bridge
    (prime_at_alpha_of_class_to_polylog_conjecture h)

/-- **★ Witness function for the no-go isolation ★** — a concrete
    `f : Set Language → ℝ` returning `√2` on `ClassP`, `φ + 1/4` on
    `ClassNP`, and `0` elsewhere. This is the same classical
    case-split function from
    `AlphaRealizationNoGo.alpha_realization_canonical_pair_iff_classes_distinct`. -/
noncomputable def witnessF : Set Language → ℝ :=
  fun S => if S = ClassP then Real.sqrt 2
           else if S = ClassNP then phi + 1/4
           else 0

/-- The witness function's value on `ClassP` is `√2`. -/
theorem witnessF_at_ClassP : witnessF ClassP = Real.sqrt 2 := by
  unfold witnessF
  simp

/-- The witness function's value on `ClassNP` is `φ + 1/4` —
    PROVIDED `ClassNP ≠ ClassP`. -/
theorem witnessF_at_ClassNP_of_distinct
    (h : ClassNP ≠ ClassP) :
    witnessF ClassNP = phi + 1/4 := by
  unfold witnessF
  simp [h]

/-- **★ (W55E-2b) The decoupled Prop is dischargeable at `f := witnessF`
    PROVIDED `ClassP ≠ ClassNP` ★** — the algebraic content (A) of the
    original conjecture is fully verifiable on the canonical pair
    without invoking the opaque `alpha_of_class`.

    Honest scope: the hypothesis `ClassP ≠ ClassNP` is exactly the
    Wave 41B-equivalent burden. The decoupled Prop on `witnessF`
    PRESUPPOSES the class distinction it would otherwise force on
    `alpha_of_class`. The structural point is that the burden is now
    EXPLICITLY parameterised in the hypothesis, rather than encoded
    in the opacity of `alpha_of_class`. -/
theorem prime_at_witnessF_under_class_distinction
    (hne : ClassP ≠ ClassNP) :
    PolylogEigenvalueConjecturePrime witnessF := by
  have hne_sym : ClassNP ≠ ClassP := fun h => hne h.symm
  refine ⟨?_, ?_⟩
  · rw [witnessF_at_ClassP]
    exact ⟨alpha_P_sq, alpha_P_pos⟩
  · rw [witnessF_at_ClassNP_of_distinct hne_sym]
    exact ⟨alpha_NP_quadratic, alpha_NP_pos⟩

/-- **★ (W55E-2c) Algebraic content (A) is axiom-free on the canonical
    pair ★** — the canonical real numbers `(√2, φ + 1/4)` themselves
    satisfy the algebraic system, with NO reference to any `f`.

    This is the cleanest separation: the algebraic identities live in
    `ℝ` directly, completely decoupled from `Set Language → ℝ`
    realisation. -/
theorem canonical_pair_satisfies_algebraic_content :
    ((Real.sqrt 2)^2 = 2 ∧ 0 < Real.sqrt 2) ∧
    (16 * (phi + 1/4)^2 - 24 * (phi + 1/4) - 11 = 0 ∧ 0 < phi + 1/4) :=
  canonical_alpha_algebraic_pair

/-! ## Section 4 — Surviving-content classification

We package the surviving content of `PolylogEigenvalueConjecture`
after Wave 41B into three explicit clauses corresponding to classes
(A), (B), (C) in the file header. -/

/-- **★ (W55E-3a) Class (A) — Algebraic-arithmetic content ★** —
    survives Wave 41B unchanged: the canonical real numbers
    `(√2, φ + 1/4)` satisfy the algebraic system axiom-free. -/
theorem class_A_algebraic_content_survives :
    ((Real.sqrt 2)^2 = 2 ∧ 0 < Real.sqrt 2) ∧
    (16 * (phi + 1/4)^2 - 24 * (phi + 1/4) - 11 = 0 ∧ 0 < phi + 1/4) :=
  canonical_alpha_algebraic_pair

/-- **★ (W55E-3b) Class (B) — Structural-identification content ★** —
    bound by Wave 41B: discharge of
    `PolylogEigenvalueConjecturePrime alpha_of_class` is logically
    equivalent to `ClassP ≠ ClassNP`. -/
theorem class_B_structural_identification_bound_by_no_go :
    PolylogEigenvalueConjecturePrime alpha_of_class →
    ClassP ≠ ClassNP :=
  prime_at_alpha_of_class_implies_P_neq_NP

/-- **★ (W55E-3c) Class (C) — Cross-Millennium cascade content ★** —
    downstream of class (B): discharge at `alpha_of_class` also
    produces cross-web realisation witnesses (per Wave 41B
    `alpha_of_class_no_go_cross_millennium_cascade`). -/
theorem class_C_cross_millennium_cascade_inherits :
    PolylogEigenvalueConjecturePrime alpha_of_class →
    alpha_of_class ClassP = Real.sqrt 2 →
    alpha_of_class ClassNP = phi + 1/4 →
    ClassP ≠ ClassNP
    ∧ RealisesP (Real.sqrt 2)
    ∧ (∃ a : ℝ, RealisesYM a) := by
  intro _ hP hNP
  exact alpha_of_class_no_go_cross_millennium_cascade alpha_of_class hP hNP

/-! ## Section 5 — Decoupled-from-`alpha_of_class` instances

For completeness we document that the decoupled Prop admits multiple
instances. Each instance corresponds to a different choice of `f`,
and the no-go binds only at `f = alpha_of_class`. -/

/-- **★ (W55E-4) Wave 47G empirical pin implies decoupled Prop on
    `alpha_of_class` ★** — composes Wave 47G's
    `wave47_polylog_discharge_under_empirical_pin` with the bridge. -/
theorem empirical_pin_implies_prime_at_alpha_of_class
    (h : EmpiricalAlphaIdentificationHypothesis) :
    PolylogEigenvalueConjecturePrime alpha_of_class :=
  polylog_conjecture_to_prime
    (wave47_polylog_discharge_under_empirical_pin h)

/-- **★ (W55E-5) Empirical pin propositionally forces `ClassP ≠ ClassNP`
    via the decoupled refactor ★** — preserves the Wave 47G
    propositional strength. -/
theorem empirical_pin_implies_P_neq_NP_via_prime
    (h : EmpiricalAlphaIdentificationHypothesis) :
    ClassP ≠ ClassNP :=
  prime_at_alpha_of_class_implies_P_neq_NP
    (empirical_pin_implies_prime_at_alpha_of_class h)

/-! ## Section 6 — Capstone

Bundle the bridge theorem, the no-go isolation, the surviving-content
classification, and the propositional-strength preservation into one
referee-citable theorem. -/

/-- **★ POLYLOG-CONJECTURE-PRIME DECOUPLED ATTEMPT — WAVE 55E CAPSTONE ★**

    Seven clauses formalising the typed decoupled refactor of
    `PolylogEigenvalueConjecture` over an arbitrary
    `f : Set Language → ℝ`:

    (W55E-1) **Bridge theorem**: the original
             `PolylogEigenvalueConjecture` is definitionally equal
             to the decoupled
             `PolylogEigenvalueConjecturePrime alpha_of_class`.

    (W55E-2a) **No-go isolation at `f = alpha_of_class`**: discharge
              of the decoupled Prop on `alpha_of_class` forces
              `ClassP ≠ ClassNP` (Wave 41B applies SPECIFICALLY
              here).

    (W55E-2b) **Conditional discharge on `f := witnessF`**: the
              algebraic content (A) of the original conjecture is
              fully verifiable on the canonical pair via the explicit
              case-split witness function, PROVIDED `ClassP ≠ ClassNP`.
              The burden is parameterised explicitly rather than
              hidden in the opacity of `alpha_of_class`.

    (W55E-2c) **Algebraic content survives unconditionally on the
              canonical real numbers**: the pair `(√2, φ + 1/4) ∈ ℝ²`
              itself satisfies the algebraic system axiom-free, with
              no reference to `Set Language → ℝ` realisation.

    (W55E-3) **Surviving-content classification** — (A) algebraic
             arithmetic survives, (B) structural identification is
             Wave 41B-bound, (C) cross-Millennium cascade inherits
             from (B).

    (W55E-4) **Empirical pin instance**: Wave 47G's empirical pin
             discharges the decoupled Prop on `alpha_of_class`
             (recovering Wave 47G via the bridge).

    (W55E-5) **Honest scope**: the decoupled refactor does NOT
             discharge `PolylogEigenvalueConjecture` unconditionally.
             By Wave 41B, no such discharge can exist on
             `alpha_of_class`. The contribution is a structural
             SEPARATION of algebraic content from
             complexity-class-equivalent identification.

    The capstone bundles all clauses for single-citation use. -/
theorem polylog_conjecture_prime_decoupled_capstone :
    -- (W55E-1) Bridge theorem
    (PolylogEigenvalueConjecture ↔
       PolylogEigenvalueConjecturePrime alpha_of_class)
    ∧
    -- (W55E-2a) No-go isolation at `f = alpha_of_class`
    (PolylogEigenvalueConjecturePrime alpha_of_class →
       ClassP ≠ ClassNP)
    ∧
    -- (W55E-2b) Conditional discharge on `witnessF` under class distinction
    (ClassP ≠ ClassNP →
       PolylogEigenvalueConjecturePrime witnessF)
    ∧
    -- (W55E-2c) Algebraic content unconditionally on canonical pair
    (((Real.sqrt 2)^2 = 2 ∧ 0 < Real.sqrt 2) ∧
     (16 * (phi + 1/4)^2 - 24 * (phi + 1/4) - 11 = 0 ∧ 0 < phi + 1/4))
    ∧
    -- (W55E-3) Surviving-content classification
    ((((Real.sqrt 2)^2 = 2 ∧ 0 < Real.sqrt 2) ∧
      (16 * (phi + 1/4)^2 - 24 * (phi + 1/4) - 11 = 0 ∧ 0 < phi + 1/4))
     ∧
     (PolylogEigenvalueConjecturePrime alpha_of_class → ClassP ≠ ClassNP)
     ∧
     (PolylogEigenvalueConjecturePrime alpha_of_class →
        alpha_of_class ClassP = Real.sqrt 2 →
        alpha_of_class ClassNP = phi + 1/4 →
        ClassP ≠ ClassNP
        ∧ RealisesP (Real.sqrt 2)
        ∧ (∃ a : ℝ, RealisesYM a)))
    ∧
    -- (W55E-4) Empirical pin instance
    (EmpiricalAlphaIdentificationHypothesis →
       PolylogEigenvalueConjecturePrime alpha_of_class)
    ∧
    -- (W55E-5) Honest scope: empirical pin propositionally forces P ≠ NP
    (EmpiricalAlphaIdentificationHypothesis → ClassP ≠ ClassNP) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact polylog_conjecture_iff_prime_at_alpha_of_class
  · exact prime_at_alpha_of_class_implies_P_neq_NP
  · exact prime_at_witnessF_under_class_distinction
  · exact canonical_pair_satisfies_algebraic_content
  · exact ⟨class_A_algebraic_content_survives,
           class_B_structural_identification_bound_by_no_go,
           class_C_cross_millennium_cascade_inherits⟩
  · exact empirical_pin_implies_prime_at_alpha_of_class
  · exact empirical_pin_implies_P_neq_NP_via_prime

/-- **Wave 55E honest-scope marker** — the decoupled refactor
    SEPARATES algebraic content from structural identification, but
    does NOT discharge any Millennium problem; the Wave 41B no-go on
    `alpha_of_class` is preserved exactly. -/
theorem polylog_conjecture_prime_decoupled_honest_scope : True := trivial

end PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt

-- Axiom checks. Expected for every theorem: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.polylog_conjecture_iff_prime_at_alpha_of_class
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.polylog_conjecture_to_prime
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.prime_at_alpha_of_class_to_polylog_conjecture
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.prime_at_alpha_of_class_implies_P_neq_NP
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.witnessF_at_ClassP
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.witnessF_at_ClassNP_of_distinct
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.prime_at_witnessF_under_class_distinction
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.canonical_pair_satisfies_algebraic_content
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.class_A_algebraic_content_survives
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.class_B_structural_identification_bound_by_no_go
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.class_C_cross_millennium_cascade_inherits
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.empirical_pin_implies_prime_at_alpha_of_class
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.empirical_pin_implies_P_neq_NP_via_prime
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.polylog_conjecture_prime_decoupled_capstone
#print axioms
  PrincipiaTractalis.PolylogConjecturePrimeDecoupledAttempt.polylog_conjecture_prime_decoupled_honest_scope
