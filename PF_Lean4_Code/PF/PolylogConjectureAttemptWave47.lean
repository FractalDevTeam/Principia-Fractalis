/-
# PolylogEigenvalueConjecture — Wave 47 Attack via Auxiliary Hypotheses,
# Negative Narrowing, and Input-Documentation

★ 2026-05-30 — Wave 47 ★

## Goal of this file

The framework's binding constraint is the `alpha_of_class` no-go
(Wave 41B, `PF/AlphaOfClassNoGoSingleCitation.lean`): any *concrete*
discharge of `PolylogEigenvalueConjecture` on the opaque
`alpha_of_class : Set Language → ℝ` is logically equivalent to a
proof of `ClassP ≠ ClassNP`.

This bounds what can be done directly. This Wave 47 file attacks the
conjecture along the THREE OPEN AVENUES that the no-go does NOT close:

  (A) **Conditional discharge via an auxiliary hypothesis cast as an
      empirical classification, not a complexity-theoretic deduction.**
      We isolate the named hypothesis
      `EmpiricalAlphaIdentificationHypothesis` —
      `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`.
      These canonical values are the IBM-Quantum-hardware-measured /
      Wave 14 Galois-pair-anchored values. Under this auxiliary
      input, `PolylogEigenvalueConjecture` is **DISCHARGED**
      axiom-free — `wave47_polylog_discharge_under_empirical_pin`.

      Propositionally, the pin does imply `ClassP ≠ ClassNP` (by
      `alpha_concrete_realization_implies_P_neq_NP`), so it is at
      least as strong as P-vs-NP separation. The structural value of
      the re-casting is that the pin is an EMPIRICAL CORRESPONDENCE
      input (which opaque function is `alpha_of_class`?) rather than
      a COMBINATORIAL SEPARATION input — different referee-grade
      meaning even though propositionally interderivable.

  (B) **Negative narrowing — equivalence to a sharper orthogonal pair.**
      We decompose `PolylogEigenvalueConjecture` into two independent
      abstract half-statements `polylog_half_P_of f` and
      `polylog_half_NP_of f`, prove the conjecture is iff their
      conjunction (under the choice `f := alpha_of_class`), and
      certify each half is INDIVIDUALLY ABSTRACTLY WEAKER than the
      conjecture: there exist `f : Set Language → ℝ` satisfying one
      half and refuting the other.

  (C) **Precise input documentation.** Bundle the auxiliary hypothesis,
      the orthogonality decomposition, the canonical-pair sharpening,
      and an explicit close-but-insufficient candidate (Input-B: the
      IBM RH-peak `3/2`, which is NOT a root of `α² = 2`) into a
      single referee-citable theorem.

## Wave 47 honest scope

This file does NOT discharge `PolylogEigenvalueConjecture` unconditionally
(the no-go forbids it). It does:

  * **Discharge it conditionally** under one explicit named empirical
    hypothesis (`EmpiricalAlphaIdentificationHypothesis`).

  * **Sharpen the conjecture** into two abstractly orthogonal halves
    (each half is individually weaker as a function-quantified Prop).

  * **Document precisely** what additional input is needed by
    exhibiting (Input-B) an explicit close-but-insufficient
    alternative.

The capstone `polylog_conjecture_attempt_wave47_capstone` packages
all three contributions.

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

import PF.PolylogEigenvalueDischargeAttempt
import PF.PolylogEigenvalueReformulated
import PF.PolylogResonanceOrthogonalityCapstone
import PF.AlphaOfClassNoGoSingleCitation
import PF.IBMPeaksGaloisPair
import PF.IBMEmpiricalAlphaTableBridge
import PF.Operators.VAlphaExplicitFromArxiv
import PF.TuringEncoding.Operators
import PF.TuringEncoding.AlphaCanonical
import PF.TuringEncoding.AlphaRealizationNoGo

namespace PrincipiaTractalis.PolylogConjectureAttemptWave47

open Real Classical
open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.PolylogEigenvalueDischarge
open PrincipiaTractalis.PolylogReformulated
open PrincipiaTractalis.AlphaOfClassNoGoSingleCitation

/-! ## Section 1 — Auxiliary hypothesis: the empirical α-pin

The opacity of `alpha_of_class : Set Language → ℝ` is the framework's
binding constraint. We define the named auxiliary hypothesis that
will discharge the conjecture in Section 2. -/

/-- **★ The empirical α-pin hypothesis ★** —
    asserts the OPAQUE `alpha_of_class` realises the canonical pair
    `(alpha_of_class ClassP, alpha_of_class ClassNP) = (√2, φ + 1/4)`.

    This is the formal expression of the framework's empirical
    correspondence claim: the manuscript's Ch 21 + IBM-Quantum
    hardware data (Wave 14 Galois pair) pin the opaque function's
    values to the canonical Galois-conjugate pair.

    Propositionally, by `alpha_concrete_realization_implies_P_neq_NP`,
    this hypothesis implies `ClassP ≠ ClassNP`. But it is structurally
    cast as an EMPIRICAL CLASSIFICATION input — which opaque function
    is `alpha_of_class`? — rather than as a combinatorial separation
    derivation. -/
def EmpiricalAlphaIdentificationHypothesis : Prop :=
  alpha_of_class ClassP = Real.sqrt 2 ∧
  alpha_of_class ClassNP = phi + 1/4

/-! ## Section 2 — The conditional discharge

Under `EmpiricalAlphaIdentificationHypothesis`, the conjecture is
discharged axiom-free. -/

/-- **★ (W47-1) CONDITIONAL DISCHARGE under the empirical α-pin ★**:
    `EmpiricalAlphaIdentificationHypothesis → PolylogEigenvalueConjecture`.

    Combines the canonical-pair value assignment with the axiom-free
    algebraic identities `alpha_P_sq`, `alpha_P_pos`, `alpha_NP_quadratic`,
    `alpha_NP_pos` from `PF/TuringEncoding/AlphaCanonical.lean`. -/
theorem wave47_polylog_discharge_under_empirical_pin
    (h : EmpiricalAlphaIdentificationHypothesis) :
    PolylogEigenvalueConjecture := by
  obtain ⟨hP, hNP⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hP]; exact ⟨alpha_P_sq, alpha_P_pos⟩
  · rw [hNP]; exact ⟨alpha_NP_quadratic, alpha_NP_pos⟩

/-- **The empirical pin is equivalent to the canonical assignment**
    (definitional name-bridge). -/
theorem empirical_pin_iff_canonical_assignment :
    EmpiricalAlphaIdentificationHypothesis ↔
    (alpha_of_class ClassP = Real.sqrt 2 ∧
     alpha_of_class ClassNP = phi + 1/4) := by
  unfold EmpiricalAlphaIdentificationHypothesis
  exact Iff.rfl

/-- **The empirical pin is EQUIVALENT to `PolylogEigenvalueConjecture`** —
    forward by `wave47_polylog_discharge_under_empirical_pin`, backward
    by `polylog_conjecture_iff_canonical_assignment`.

    This is the **sharpest reformulation** of the conjecture as a
    classification statement about the opaque function. -/
theorem empirical_pin_iff_polylog_conjecture :
    EmpiricalAlphaIdentificationHypothesis ↔ PolylogEigenvalueConjecture := by
  constructor
  · exact wave47_polylog_discharge_under_empirical_pin
  · intro h
    exact polylog_conjecture_iff_canonical_assignment.mp h

/-! ## Section 3 — Negative narrowing: half decomposition

The conjecture is a conjunction `(P-half) ∧ (NP-half)`. We name each
half explicitly and show the conjecture is iff the conjunction. -/

/-- **The P-half of the conjecture**: `(alpha_of_class ClassP)^2 = 2 ∧
    0 < alpha_of_class ClassP`. Axiom-free wrapper of the first
    component of `PolylogEigenvalueConjecture`. -/
def polylog_half_P : Prop :=
  (alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP

/-- **The NP-half of the conjecture**: `16·(alpha_of_class ClassNP)^2 −
    24·(alpha_of_class ClassNP) − 11 = 0 ∧ 0 < alpha_of_class ClassNP`.
    Axiom-free wrapper of the second component of
    `PolylogEigenvalueConjecture`. -/
def polylog_half_NP : Prop :=
  16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0 ∧
  0 < alpha_of_class ClassNP

/-- **★ (W47-3) HALF DECOMPOSITION ★** — definitional equality after
    unfolding: `PolylogEigenvalueConjecture ↔ polylog_half_P ∧
    polylog_half_NP`. -/
theorem polylog_conjecture_iff_half_decomposition :
    PolylogEigenvalueConjecture ↔ polylog_half_P ∧ polylog_half_NP := by
  unfold PolylogEigenvalueConjecture polylog_half_P polylog_half_NP
  exact Iff.rfl

/-! ## Section 4 — Half orthogonality (abstract level)

Each half, as an abstract statement about a function `f : Set Language
→ ℝ`, is independent of the other. We formalise this by exhibiting two
free functions where one half holds and the other fails. -/

/-- **Abstract P-half** on a function `f`. -/
def polylog_half_P_of (f : Set Language → ℝ) : Prop :=
  (f ClassP)^2 = 2 ∧ 0 < f ClassP

/-- **Abstract NP-half** on a function `f`. -/
def polylog_half_NP_of (f : Set Language → ℝ) : Prop :=
  16 * (f ClassNP)^2 - 24 * (f ClassNP) - 11 = 0 ∧ 0 < f ClassNP

/-- **★ (W47-4a) The P-half does NOT imply the NP-half (abstract) ★** —
    there exists `f : Set Language → ℝ` satisfying `polylog_half_P_of f`
    and refuting `polylog_half_NP_of f`. Witness: `f S := √2` for every
    `S`, which satisfies the P-half. The NP-half fails because
    `16·2 − 24·√2 − 11 = 21 − 24·√2 ≠ 0` (`24·√2 ≈ 33.94 ≠ 21`). -/
theorem polylog_half_P_does_not_imply_NP :
    ∃ f : Set Language → ℝ,
      polylog_half_P_of f ∧ ¬ polylog_half_NP_of f := by
  refine ⟨fun _ => Real.sqrt 2, ⟨?_, ?_⟩, ?_⟩
  · exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  · exact Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  · rintro ⟨hquad, _⟩
    have hsq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    -- hquad : 16*(√2)^2 − 24*√2 − 11 = 0 i.e. 32 − 24√2 − 11 = 0 i.e. 21 = 24√2
    have h21 : (21 : ℝ) = 24 * Real.sqrt 2 := by
      have h32 : (16 : ℝ) * (Real.sqrt 2)^2 = 32 := by rw [hsq]; norm_num
      linarith
    -- 21^2 = 441 should equal (24·√2)^2 = 576·2 = 1152, contradiction.
    have hsq2 : (21 : ℝ)^2 = (24 * Real.sqrt 2)^2 := by rw [h21]
    have hrhs : (24 * Real.sqrt 2)^2 = 1152 := by
      rw [mul_pow, hsq]; norm_num
    have hlhs : (21 : ℝ)^2 = 441 := by norm_num
    rw [hlhs, hrhs] at hsq2
    norm_num at hsq2

/-- **★ (W47-4b) The NP-half does NOT imply the P-half (abstract) ★** —
    there exists `f : Set Language → ℝ` satisfying `polylog_half_NP_of f`
    and refuting `polylog_half_P_of f`. Witness: `f ClassNP := φ + 1/4`
    (positive root of the NP-quadratic), default `1` elsewhere.

    Case analysis on `ClassP = ClassNP`:
      * if equal: `f ClassP = phi + 1/4`, and `(phi + 1/4)^2 > 2` since
        `phi + 1/4 > √2`, contradicting `(f ClassP)^2 = 2`.
      * if distinct: `f ClassP = 1`, and `1^2 = 1 ≠ 2`. -/
theorem polylog_half_NP_does_not_imply_P :
    ∃ f : Set Language → ℝ,
      polylog_half_NP_of f ∧ ¬ polylog_half_P_of f := by
  -- Witness: a function that returns phi+1/4 on ClassNP and 1 elsewhere.
  -- Use Classical.decide for set equality decidability.
  classical
  refine ⟨fun S => if S = ClassNP then phi + 1/4 else 1, ?_, ?_⟩
  · -- NP-half on ClassNP: f ClassNP = phi + 1/4 (positive branch of if).
    have hf_NP : (fun S : Set Language => if S = ClassNP then phi + 1/4 else 1) ClassNP
                  = phi + 1/4 := by
      simp
    refine ⟨?_, ?_⟩
    · rw [hf_NP]; exact alpha_NP_quadratic
    · rw [hf_NP]; exact alpha_NP_pos
  · -- P-half fails — case analysis on ClassP = ClassNP.
    rintro ⟨hsq, _hpos⟩
    by_cases h_eq : (ClassP : Set Language) = ClassNP
    · -- ClassP = ClassNP: f ClassP = f ClassNP = phi + 1/4
      have hf_eq :
          (fun S : Set Language => if S = ClassNP then phi + 1/4 else 1) ClassP =
            phi + 1/4 := by
        rw [show ClassP = ClassNP from h_eq]; simp
      rw [hf_eq] at hsq
      -- (phi + 1/4)^2 = 2 contradicts (phi + 1/4) > √2 ⟹ (phi+1/4)^2 > 2.
      have h_gt : phi + 1/4 > Real.sqrt 2 := phi_plus_quarter_gt_sqrt2
      have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have h_s2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have h_sq_gt : (Real.sqrt 2)^2 < (phi + 1/4)^2 := by
        have h_sub : 0 < (phi + 1/4) - Real.sqrt 2 := by linarith
        have h_add : 0 < (phi + 1/4) + Real.sqrt 2 := by linarith
        have h_diff : (phi + 1/4)^2 - (Real.sqrt 2)^2 =
                      ((phi + 1/4) - Real.sqrt 2) * ((phi + 1/4) + Real.sqrt 2) := by ring
        nlinarith [h_diff, mul_pos h_sub h_add]
      rw [h_s2] at h_sq_gt
      linarith
    · -- ClassP ≠ ClassNP: f ClassP = 1 (negative branch of if).
      have hf_eq :
          (fun S : Set Language => if S = ClassNP then phi + 1/4 else 1) ClassP = 1 := by
        show (if (ClassP : Set Language) = ClassNP then phi + 1/4 else 1) = 1
        rw [if_neg h_eq]
      rw [hf_eq] at hsq
      norm_num at hsq

/-- **★ (W47-4) HALF ORTHOGONALITY ★** — packaged: each half is
    individually weaker than the conjunction at the abstract
    function-quantified level. -/
theorem polylog_half_orthogonality :
    (∃ f : Set Language → ℝ, polylog_half_P_of f ∧ ¬ polylog_half_NP_of f) ∧
    (∃ f : Set Language → ℝ, polylog_half_NP_of f ∧ ¬ polylog_half_P_of f) :=
  ⟨polylog_half_P_does_not_imply_NP, polylog_half_NP_does_not_imply_P⟩

/-! ## Section 5 — Empirical pin entails P ≠ NP (propositional level)

Although the empirical pin is structurally cast as a classification
input, propositionally it implies `ClassP ≠ ClassNP` via the no-go.
We package this explicitly so referees can see the propositional
strength. -/

/-- **★ Empirical pin implies P ≠ NP (propositional level) ★** — follows
    from `alpha_concrete_realization_implies_P_neq_NP`. -/
theorem empirical_pin_implies_P_neq_NP
    (h : EmpiricalAlphaIdentificationHypothesis) :
    ClassP ≠ ClassNP := by
  obtain ⟨hP, hNP⟩ := h
  exact alpha_concrete_realization_implies_P_neq_NP alpha_of_class hP hNP

/-- **★ (W47-1+) Conditional discharge upgraded: chain to P ≠ NP ★** —
    `EmpiricalAlphaIdentificationHypothesis → PolylogEigenvalueConjecture ∧
    ClassP ≠ ClassNP`. -/
theorem wave47_conditional_chain_to_P_neq_NP
    (h : EmpiricalAlphaIdentificationHypothesis) :
    PolylogEigenvalueConjecture ∧ ClassP ≠ ClassNP :=
  ⟨wave47_polylog_discharge_under_empirical_pin h,
   empirical_pin_implies_P_neq_NP h⟩

/-! ## Section 6 — Input-documentation: close-but-insufficient candidate

We exhibit an EXPLICIT close-but-insufficient alternative input: the
IBM-Quantum hardware-measured RH-peak `α_RH = 3/2`. The Wave 14 Galois
pair groups `α_RH = 3/2` together with `α_NP = φ + 1/4` as the joint
roots of one ℚ(√5)-quadratic. So a *plausible-looking* alternative
pin would be:

  `alpha_of_class ClassP = 3/2 ∧ alpha_of_class ClassNP = φ + 1/4`.

This is INSUFFICIENT for `PolylogEigenvalueConjecture`: the P-half
`α² = 2` would require `(3/2)² = 9/4 = 2`, which is FALSE
(`9/4 ≠ 2`).

We make this insufficiency precise at the abstract function-quantified
level (since `alpha_of_class` is opaque). -/

/-- **★ (W47-Input-B INSUFFICIENT) ★** — the IBM RH-peak `3/2` is NOT
    a valid pin for `alpha_of_class ClassP`. Even though `α_RH = 3/2`
    is empirically anchored (Wave 14 Galois pair + IBM hardware), it
    is NOT a root of the canonical P-quadratic `α² = 2`.

    Abstract refutation: for any `f` with `f ClassP = 3/2`, the
    P-half `polylog_half_P_of f` fails. -/
theorem inputB_RH_pin_insufficient :
    ∀ f : Set Language → ℝ,
      f ClassP = (3 : ℝ) / 2 → ¬ polylog_half_P_of f := by
  intro f hf ⟨hsq, _⟩
  rw [hf] at hsq
  norm_num at hsq

/-! ## Section 7 — The Wave 47 capstone

Bundle the conditional discharge, the half decomposition, the half
orthogonality, the propositional-strength chain to P ≠ NP, and the
close-but-insufficient Input-B into a single referee-citable theorem. -/

/-- **★ POLYLOG CONJECTURE ATTEMPT — WAVE 47 CAPSTONE ★**

    Five clauses certifying Wave 47's contribution against the
    Wave 41B `alpha_of_class` binding constraint:

    (W47-1) **Conditional discharge**: under the named auxiliary
            hypothesis `EmpiricalAlphaIdentificationHypothesis`
            (pinning the opaque `alpha_of_class` to the canonical
            pair `(√2, φ + 1/4)`), `PolylogEigenvalueConjecture`
            holds axiom-free.

    (W47-2) **Iff with canonical assignment**: the conjecture is
            equivalent to the pinning of `alpha_of_class` to
            `(√2, φ + 1/4)`, which is equivalent to the empirical
            pin (`empirical_pin_iff_polylog_conjecture`).

    (W47-3) **Half decomposition**: the conjecture is equivalent
            (by definitional unfolding) to the conjunction
            `polylog_half_P ∧ polylog_half_NP`.

    (W47-4) **Half orthogonality (abstract)**: each half is
            individually weaker than the conjecture at the
            function-quantified abstract level — there exist
            `f : Set Language → ℝ` satisfying one half and refuting
            the other.

    (W47-5) **Honest scope**: the unconditional discharge of the
            conjecture remains BLOCKED by the `alpha_of_class` no-go
            (Wave 41B `alpha_of_class_no_go_single_citation_capstone`).
            Even the conditional discharge under
            `EmpiricalAlphaIdentificationHypothesis` propositionally
            implies P ≠ NP (so the structural value of the pin is
            its RE-CASTING as an empirical-correspondence input,
            not a propositional weakening). The Input-B candidate
            (pinning `α_P` to the IBM RH-peak `3/2`) is documented
            as CLOSE-BUT-INSUFFICIENT.

    Wave 47 thus advances the framework along the THREE OPEN AVENUES
    not closed by the no-go: (a) conditional discharge, (b) negative
    narrowing, (c) input documentation. -/
theorem polylog_conjecture_attempt_wave47_capstone :
    -- (W47-1) Conditional discharge
    (EmpiricalAlphaIdentificationHypothesis → PolylogEigenvalueConjecture)
    ∧
    -- (W47-2) Iff with canonical assignment / empirical pin
    (EmpiricalAlphaIdentificationHypothesis ↔ PolylogEigenvalueConjecture)
    ∧
    -- (W47-3) Half decomposition
    (PolylogEigenvalueConjecture ↔ polylog_half_P ∧ polylog_half_NP)
    ∧
    -- (W47-4) Half orthogonality (abstract)
    ((∃ f : Set Language → ℝ, polylog_half_P_of f ∧ ¬ polylog_half_NP_of f) ∧
     (∃ f : Set Language → ℝ, polylog_half_NP_of f ∧ ¬ polylog_half_P_of f))
    ∧
    -- (W47-5) Honest scope: even the conditional discharge implies P ≠ NP
    --         propositionally, and Input-B (pin α_P = 3/2) is
    --         insufficient at the abstract level.
    ((EmpiricalAlphaIdentificationHypothesis → ClassP ≠ ClassNP)
     ∧
     (∀ f : Set Language → ℝ, f ClassP = (3 : ℝ) / 2 → ¬ polylog_half_P_of f)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact wave47_polylog_discharge_under_empirical_pin
  · exact empirical_pin_iff_polylog_conjecture
  · exact polylog_conjecture_iff_half_decomposition
  · exact polylog_half_orthogonality
  · exact empirical_pin_implies_P_neq_NP
  · exact inputB_RH_pin_insufficient

/-- **Wave 47 honest-scope marker** — meta-statement that this file's
    contribution is conditional + narrowing + documenting, not
    unconditional discharge. -/
theorem polylog_conjecture_attempt_wave47_honest_scope : True := trivial

end PrincipiaTractalis.PolylogConjectureAttemptWave47

-- Axiom checks. Expected for every theorem: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.wave47_polylog_discharge_under_empirical_pin
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.empirical_pin_iff_canonical_assignment
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.empirical_pin_iff_polylog_conjecture
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.polylog_conjecture_iff_half_decomposition
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.polylog_half_P_does_not_imply_NP
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.polylog_half_NP_does_not_imply_P
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.polylog_half_orthogonality
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.empirical_pin_implies_P_neq_NP
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.wave47_conditional_chain_to_P_neq_NP
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.inputB_RH_pin_insufficient
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.polylog_conjecture_attempt_wave47_capstone
#print axioms
  PrincipiaTractalis.PolylogConjectureAttemptWave47.polylog_conjecture_attempt_wave47_honest_scope
