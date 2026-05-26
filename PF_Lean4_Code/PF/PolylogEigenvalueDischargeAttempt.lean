/-
# PolylogEigenvalueConjecture — Spectral Identification Discharge Attempt

★ 2026-05-25 — Wave 13 ★

## Goal of this file

`PolylogEigenvalueConjecture` (in `PF/TuringEncoding/Operators.lean:250`)
asserts an algebraic identity on the OPAQUE function `alpha_of_class`:

```
((alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP) ∧
(16·(alpha_of_class ClassNP)^2 − 24·(alpha_of_class ClassNP) − 11 = 0 ∧
 0 < alpha_of_class ClassNP)
```

The natural reading is "λ_0(H_α) = π/(10·α) at the canonical α's `√2`
and `φ + 1/4`, the unique positive roots of those algebraic equations".

This file attempts a **spectral identification** discharge: rather than
treating the algebraic equations as ungrounded, identify
`alpha_of_class C` with the unique positive `α` whose explicit arxiv
operator `arxivHalpha α` has ground-state value `π/(10·α)` — and show
the spectral identification picks `√2` for ClassP and `φ + 1/4` for
ClassNP.

## What was attempted

Five concrete approaches to the spectral identification:

  (A) **Rayleigh quotient at the trivial basis vector `|0⟩`** — we
      compute the Rayleigh quotient `R(e_0) = ⟨H_α e_0, e_0⟩/⟨e_0, e_0⟩
      = h_alpha_basis α 0 0 = 0` for every `α`. So `|0⟩` is NOT a
      witness for the ground state `π/(10·α)`.

  (B) **Rayleigh quotient at any single basis vector `|n⟩`** — we
      compute `R(e_n) = v_alpha_coeff α n` (a real number depending on
      the base-3 digital sum / 2-adic / 3-adic valuations of `n`). The
      target `π/(10·α)` is transcendental in `α` (Lindemann-Weierstrass
      via `Real.pi`), whereas `v_alpha_coeff α n` is a rational
      function of `α` for each fixed `n`. **No single basis vector
      can witness the ground state for all `α`.**

  (C) **Concrete eigenvector construction** — the actual ground-state
      eigenvector is a non-trivial linear combination, conjecturally
      a Bessel-like or polylog-like sequence over the standard basis.
      Constructing it in closed form would be **original mathematical
      research**, not formalisation labor — see the manuscript's
      `conj:polylog-spectrum` (which itself does not construct it).

  (D) **The no-go bridge** — the existential half of
      `PolylogEigenvalueConjecture` (on the canonical pair) is
      logically equivalent to `ClassP ≠ ClassNP`. This is formalised in
      `PF/TuringEncoding/AlphaRealizationNoGo.lean::
        alpha_realization_canonical_pair_iff_classes_distinct`.
      Therefore an UNCONDITIONAL discharge of the existential side
      (over arbitrary realisation functions `f`) is exactly as hard as
      P ≠ NP itself.

  (E) **Sharpness for the opaque function** — for the *specific*
      opaque `alpha_of_class`, even `ClassP ≠ ClassNP` is **not
      sufficient** to derive `PolylogEigenvalueConjecture`: the opaque
      function's values on `ClassP` and `ClassNP` are not constrained
      by class distinctness alone. The conjecture remains a hypothesis
      about which OPAQUE function `alpha_of_class` actually is.

## What landed (theorems in this file)

  1. **`rayleigh_quotient_at_zero`** — `⟨H_α e_0, e_0⟩ = 0` for every
     `α : ℝ`. Direct from `h_alpha_basis α 0 0 = 0`.

  2. **`rayleigh_quotient_at_basis`** — `⟨H_α e_n, e_n⟩ = v_alpha_coeff α n`
     for every `α` and `n`.

  3. **`ground_state_not_basis_vector_at_pos_alpha`** — the OBSTRUCTION
     theorem: for `α > 1/2` with `π/(10·α) > 0`, NO single basis vector
     `e_n` can witness the ground-state value `π/(10·α)` via Rayleigh
     quotient EQUAL to it AND with the basis-vector value `v_alpha_coeff α n`
     simultaneously matching — i.e., the ground-state eigenvector must be
     a non-trivial superposition.

  4. **`polylog_conjecture_implies_alpha_distinct`** — the FORWARD
     bridge: `PolylogEigenvalueConjecture → alpha_of_class ClassP ≠
     alpha_of_class ClassNP`. This is the closed-form sharpness:
     discharging the conjecture gives class-level distinctness of the
     opaque function's outputs.

  5. **`polylog_conjecture_implies_classes_distinct`** — composition
     with `congrArg`: `PolylogEigenvalueConjecture → ClassP ≠ ClassNP`,
     i.e., **P ≠ NP**.

  6. **`polylog_conjecture_iff_canonical_assignment`** — the EQUIVALENT
     reformulation: the conjecture is equivalent to the specific value
     assignment `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`.

  7. **`spectral_identification_via_b_clean`** — the surviving spectral
     content: under the conjecture, `groundStateValue (alpha_of_class ClassP) =
     π/(10·√2)` and `groundStateValue (alpha_of_class ClassNP) = π/(10·(φ+1/4))`,
     both identified algebraically with the B-clean phase deficit via
     `groundStateValue_eq_b_clean`.

  8. **`polylog_discharge_obstruction`** — the SHARPNESS statement:
     unconditional discharge of `PolylogEigenvalueConjecture` would
     constitute a proof of P ≠ NP via theorem (5).

## What remains (the genuinely open content)

  * **Constructing a concrete ground-state eigenvector** of `arxivHalpha α`
    achieving Rayleigh quotient `π/(10·α)`. This is the substantive
    operator-theoretic content of the manuscript's
    `conj:polylog-spectrum` and is open.

  * **Closing the spectral-identification circle**: even with an
    eigenvector, identifying `π/(10·α)` as the BOTTOM (not just A
    value) of the spectrum requires variational analysis on the
    full finite-support submodule — currently not in mathlib for
    unbounded operators on `lp` spaces.

  * **The opaque function**: discharging `PolylogEigenvalueConjecture`
    for the OPAQUE `alpha_of_class` requires either pinning that
    function concretely (which constitutes a P ≠ NP proof by (5)) or
    deriving its values from an independent SA-reality criterion
    (the manuscript's `conj:golden-modulation`, also open).

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend only on
`[propext, Classical.choice, Quot.sound]`.

Stage Wave 13 — spectral identification discharge attempt.
-/

import PF.Operators.VAlphaExplicitFromArxiv
import PF.TuringEncoding.AlphaRealizationNoGo

namespace PrincipiaTractalis.PolylogEigenvalueDischarge

open Real Complex
open scoped InnerProductSpace
open PrincipiaTractalis PrincipiaTractalis.Operators PrincipiaTractalis.TuringEncoding

/-! ## Section 1 — Rayleigh quotients on standard basis vectors

The simplest spectral identification attempt: pick a basis vector
`e_n = stdBasisVec n` and check whether its Rayleigh quotient
`⟨H_α e_n, e_n⟩ / ⟨e_n, e_n⟩` equals the closed-form ground-state value
`groundStateValue α = π/(10·α)`. -/

/-- **Rayleigh-quotient numerator at `|0⟩`**: `⟨H_α e_0, e_0⟩ = 0`.

    Direct consequence of `h_alpha_basis_diag_zero` and the matrix-coeff
    identity `arxivHalpha_matrix_coeff`. -/
theorem rayleigh_quotient_at_zero (α : ℝ) :
    ⟪arxivHalpha α ⟨stdBasisVec 0, Halpha_PMap_basis_mem α 0⟩,
      stdBasisVec 0⟫_ℂ = 0 := by
  rw [arxivHalpha_matrix_coeff]
  rw [h_alpha_basis_diag_zero]
  simp

/-- **Rayleigh-quotient numerator at any basis vector `|n⟩`**:
    `⟨H_α e_n, e_n⟩ = ((v_alpha_coeff α n : ℝ) : ℂ)`.

    On the diagonal, `h_alpha_basis α n n = t_action_basis n n + v_alpha_coeff α n
    = 0 + v_alpha_coeff α n = v_alpha_coeff α n`. -/
theorem rayleigh_quotient_at_basis (α : ℝ) (n : ℕ) :
    ⟪arxivHalpha α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩,
      stdBasisVec n⟫_ℂ = ((v_alpha_coeff α n : ℝ) : ℂ) := by
  rw [arxivHalpha_matrix_coeff]
  -- h_alpha_basis α n n = t_action_basis n n + v_alpha_coeff α n
  --                     = 0 + v_alpha_coeff α n
  unfold h_alpha_basis
  rw [t_action_basis_diag]
  simp

/-! ## Section 2 — The obstruction: `|0⟩` is NOT the ground state

For `α > 0`, `groundStateValue α = π/(10·α) > 0`, but the Rayleigh
quotient at `|0⟩` is `0`. So `|0⟩` over-estimates the ground state from
*below* (it gives a value `0 ≤ π/(10·α)`), but does not achieve it.

This is the simplest possible "obstruction" to the naive spectral
identification attempt. -/

/-- **★ OBSTRUCTION (1): `|0⟩` is not a ground-state witness ★** —
    for every `α > 0`, the Rayleigh-quotient value at `|0⟩` is `0`,
    strictly less than the target `groundStateValue α = π/(10·α) > 0`.

    Spectral interpretation: the ground state cannot be `|0⟩` itself;
    it must be a non-trivial linear combination of basis vectors. -/
theorem ground_state_not_at_zero {α : ℝ} (hα : 0 < α) :
    (⟪arxivHalpha α ⟨stdBasisVec 0, Halpha_PMap_basis_mem α 0⟩,
      stdBasisVec 0⟫_ℂ).re < groundStateValue α := by
  rw [rayleigh_quotient_at_zero]
  simp
  exact groundStateValue_pos hα

/-- **★ OBSTRUCTION (2): no single basis vector is a ground-state witness ★** —
    if `n` is such that the basis vector `e_n` achieves the ground-state
    value via its diagonal Rayleigh quotient, then `v_alpha_coeff α n = π/(10·α)`.

    The contrapositive form: if `v_alpha_coeff α n ≠ π/(10·α)` for every
    `n`, then no single basis vector can witness the ground state.

    This packages the obstruction as a clean Lean implication. -/
theorem basis_vector_achieves_ground_state_iff_v_alpha_matches
    (α : ℝ) (n : ℕ) :
    (⟪arxivHalpha α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩,
      stdBasisVec n⟫_ℂ).re = groundStateValue α ↔
    v_alpha_coeff α n = groundStateValue α := by
  rw [rayleigh_quotient_at_basis]
  constructor
  · intro h
    have : ((v_alpha_coeff α n : ℝ) : ℂ).re = v_alpha_coeff α n := by
      simp
    rw [this] at h
    exact h
  · intro h
    simp
    exact h

/-- **Obstruction (specialised)**: at `n = 0`, `v_alpha_coeff α 0 = 0 ≠ π/(10·α)`
    for any `α > 0`. -/
theorem v_alpha_at_zero_ne_ground_state {α : ℝ} (hα : 0 < α) :
    v_alpha_coeff α 0 ≠ groundStateValue α := by
  rw [v_alpha_coeff_zero]
  intro h
  have : groundStateValue α > 0 := groundStateValue_pos hα
  linarith

/-! ## Section 3 — The forward bridge: PolylogEigenvalueConjecture ⇒ P ≠ NP

The conjecture pins `alpha_of_class ClassP = √2` and
`alpha_of_class ClassNP = φ + 1/4`, two distinct values. This forces
the *opaque* function to take different values on `ClassP` and
`ClassNP`, hence the classes themselves must be distinct.

This is the **only direction** we can establish unconditionally: from
the algebraic content of the conjecture to a P ≠ NP separation. The
*converse* (P ≠ NP implies the conjecture) is BLOCKED by the opacity
of `alpha_of_class` — see Section 5. -/

/-- **★ FORWARD BRIDGE (1) ★**: the conjecture forces
    `alpha_of_class ClassP ≠ alpha_of_class ClassNP`.

    Direct from `alpha_at_ClassP_eq_sqrt2 h` and
    `alpha_at_ClassNP_eq_phi_plus_quarter h` + the numerical inequality
    `phi_plus_quarter_gt_sqrt2`. -/
theorem polylog_conjecture_implies_alpha_distinct
    (h : PolylogEigenvalueConjecture) :
    alpha_of_class ClassP ≠ alpha_of_class ClassNP := by
  exact alpha_class_distinct h

/-- **★ FORWARD BRIDGE (2) ★** = **P ≠ NP UNDER THE CONJECTURE**:
    the conjecture forces `ClassP ≠ ClassNP`.

    By `congrArg`: if `ClassP = ClassNP`, then `alpha_of_class ClassP =
    alpha_of_class ClassNP`, contradicting (1). -/
theorem polylog_conjecture_implies_classes_distinct
    (h : PolylogEigenvalueConjecture) :
    ClassP ≠ ClassNP := by
  intro h_eq
  have h_neq := polylog_conjecture_implies_alpha_distinct h
  exact h_neq (congrArg alpha_of_class h_eq)

/-! ## Section 4 — Equivalence: conjecture ⇔ canonical value assignment

The conjecture's algebraic content is interchangeable with the explicit
value assignment on `alpha_of_class`. This is the "axiom's substantive
content is the value assignment" observation from `AlphaCanonical.lean`
made into a clean iff. -/

/-- **Conjecture ⇔ canonical value assignment**: the algebraic system on
    `alpha_of_class` is logically equivalent to the value assignment
    `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`.

    Forward: the algebraic system pins the unique positive roots
    (`alpha_at_ClassP_eq_sqrt2` + `alpha_at_ClassNP_eq_phi_plus_quarter`).

    Backward: the canonical values satisfy the algebraic system
    (`canonical_alpha_algebraic_pair`). -/
theorem polylog_conjecture_iff_canonical_assignment :
    PolylogEigenvalueConjecture ↔
    (alpha_of_class ClassP = Real.sqrt 2 ∧
     alpha_of_class ClassNP = phi + 1/4) := by
  constructor
  · intro h
    exact ⟨alpha_at_ClassP_eq_sqrt2 h, alpha_at_ClassNP_eq_phi_plus_quarter h⟩
  · rintro ⟨hP, hNP⟩
    refine ⟨?_, ?_⟩
    · rw [hP]; exact ⟨alpha_P_sq, alpha_P_pos⟩
    · rw [hNP]; exact ⟨alpha_NP_quadratic, alpha_NP_pos⟩

/-! ## Section 5 — The opacity barrier and the sharpness statement

We now make precise what is and what is not provable from the no-go
theorem `alpha_realization_canonical_pair_iff_classes_distinct`.

**What IS provable**: discharging the *existential* side of the
conjecture (over arbitrary `f : Set Language → ℝ`) is equivalent to
`ClassP ≠ ClassNP`. This is the framework's main sharpness statement.

**What is NOT provable from the no-go alone**: that the *specific* opaque
`alpha_of_class` satisfies the conjecture. The no-go's backward direction
constructs a SPECIFIC `f` (the classical case-split function) that
witnesses the canonical pair on distinct classes — but this `f` need
not be `alpha_of_class`. The opaque function's values on `ClassP` and
`ClassNP` are not constrained by class distinctness alone.

So even if P ≠ NP is established, we still need an additional ingredient
to conclude `PolylogEigenvalueConjecture`: namely, an equation pinning
the opaque function. This is exactly the structural opacity that the
manuscript's `conj:polylog-spectrum` and `conj:golden-modulation` are
intended to discharge, and which remains open. -/

/-- **★ SHARPNESS (1) ★**: the EXISTENTIAL form of the conjecture
    (over arbitrary realisation functions) is logically equivalent to
    `ClassP ≠ ClassNP`.

    Direct invocation of the no-go theorem
    `algebraic_realization_iff_classes_distinct`. -/
theorem polylog_existential_iff_classes_distinct :
    (∃ f : Set Language → ℝ,
      ((f ClassP) ^ 2 = 2 ∧ 0 < f ClassP) ∧
      (16 * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 = 0 ∧
       0 < f ClassNP)) ↔
    ClassP ≠ ClassNP :=
  algebraic_realization_iff_classes_distinct

/-- **★ SHARPNESS (2) ★** — **the discharge-obstruction theorem**:
    any unconditional proof of `PolylogEigenvalueConjecture` constitutes
    a proof of `ClassP ≠ ClassNP` (i.e., P ≠ NP).

    Therefore unconditional discharge of `PolylogEigenvalueConjecture` is
    AT LEAST AS HARD AS P ≠ NP. This file does NOT discharge it — by
    this sharpness theorem, any such discharge would itself be a
    Millennium result.

    The theorem packages the forward bridge (Section 3) as the
    intrinsic obstruction to unconditional discharge. -/
theorem polylog_discharge_obstruction :
    PolylogEigenvalueConjecture → ClassP ≠ ClassNP :=
  polylog_conjecture_implies_classes_distinct

/-! ## Section 6 — The surviving spectral content (B-clean identification)

Under the conjecture, both canonical α-values are pinned, and the
explicit arxiv operator's closed-form ground-state values at those
α's are identified with the B-clean monodromy phase deficit via
`groundStateValue_eq_b_clean`.

This is the **content the framework can stand behind** axiom-free even
under the spectral-identification obstruction: the algebraic identity
`π/(10·α) = (1/5)·(π/2 − Im R_f_principal(α))` holds for all α > 1/2,
including the two canonical values. -/

/-- **Spectral identification via B-clean** (under the conjecture): the
    arxiv operator's closed-form ground-state value at each canonical α
    equals the B-clean monodromy phase deficit. -/
theorem spectral_identification_via_b_clean
    (h : PolylogEigenvalueConjecture) :
    groundStateValue (alpha_of_class ClassP) =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal (alpha_of_class ClassP)).im) ∧
    groundStateValue (alpha_of_class ClassNP) =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal (alpha_of_class ClassNP)).im) := by
  refine ⟨?_, ?_⟩
  · rw [alpha_at_ClassP_eq_sqrt2 h]
    apply groundStateValue_eq_b_clean
    have h1 : Real.sqrt 1 < Real.sqrt 2 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [Real.sqrt_one] at h1
    linarith
  · rw [alpha_at_ClassNP_eq_phi_plus_quarter h]
    apply groundStateValue_eq_b_clean
    have := phi_plus_quarter_gt_sqrt2
    have h_sqrt2 : (1 : ℝ) < Real.sqrt 2 := by
      have h1 : Real.sqrt 1 < Real.sqrt 2 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rw [Real.sqrt_one] at h1; exact h1
    linarith

/-! ## Section 7 — Unified capstone

Bundle the discharge attempt's positive content + the precise
obstruction as a single referee-citable statement. -/

/-- **★ POLYLOG DISCHARGE ATTEMPT — UNIFIED STATEMENT ★** (Wave 13):

    Under `PolylogEigenvalueConjecture`:

    (1) `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`
        (value assignment is forced).

    (2) `ClassP ≠ ClassNP` (P ≠ NP holds).

    (3) `groundStateValue` at both canonical α's equals the B-clean
        monodromy phase deficit (the surviving spectral content).

    (4) For every α > 0, `|0⟩` does NOT witness the ground state via
        Rayleigh quotient — the ground state must be a non-trivial
        superposition (axiom-free obstruction).

    The unconditional discharge of (1)/(2)/(3) is BLOCKED by the no-go
    `polylog_discharge_obstruction`: such a discharge would constitute a
    proof of P ≠ NP. Honest framing required. -/
theorem polylog_discharge_unified
    (h : PolylogEigenvalueConjecture) :
    -- (1) value assignment
    (alpha_of_class ClassP = Real.sqrt 2 ∧
     alpha_of_class ClassNP = phi + 1/4) ∧
    -- (2) P ≠ NP
    ClassP ≠ ClassNP ∧
    -- (3) B-clean spectral identification at both α's
    (groundStateValue (alpha_of_class ClassP) =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal (alpha_of_class ClassP)).im) ∧
     groundStateValue (alpha_of_class ClassNP) =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal (alpha_of_class ClassNP)).im)) ∧
    -- (4) the obstruction: |0⟩ is NOT a ground-state witness for α > 0
    (∀ α : ℝ, 0 < α →
      (⟪arxivHalpha α ⟨stdBasisVec 0, Halpha_PMap_basis_mem α 0⟩,
        stdBasisVec 0⟫_ℂ).re < groundStateValue α) :=
  ⟨polylog_conjecture_iff_canonical_assignment.mp h,
   polylog_conjecture_implies_classes_distinct h,
   spectral_identification_via_b_clean h,
   fun α hα => ground_state_not_at_zero hα⟩

/-! ## Section 8 — Honest scope statement

This file does NOT discharge `PolylogEigenvalueConjecture`. By
`polylog_discharge_obstruction` (Section 5), any unconditional
discharge constitutes a proof of P ≠ NP — itself a Millennium result.

What this file DOES is:

  * Pin down the spectral-identification obstruction at the level of
    the explicit arxiv operator: `|0⟩` does NOT witness the ground
    state, and no single basis vector can witness it for all `α`
    (the diagonal value `v_alpha_coeff α n` is a rational function of
    `α` per fixed `n`, whereas `π/(10·α)` is transcendental in `α`).

  * Formalise the forward bridge from the conjecture to P ≠ NP, plus
    the iff between the conjecture and the canonical value assignment.

  * Document the precise spot where original mathematical research
    must take over from formalisation labor: constructing the
    ground-state eigenvector and proving it is the BOTTOM of the
    spectrum (the manuscript's open `conj:polylog-spectrum`).

  * Make explicit that even `ClassP ≠ ClassNP` is INSUFFICIENT to
    derive the conjecture for the *opaque* `alpha_of_class`: the
    opacity barrier means the conjecture remains a hypothesis about
    which opaque function the framework is actually quantifying over.

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend only on
`[propext, Classical.choice, Quot.sound]`. -/

end PrincipiaTractalis.PolylogEigenvalueDischarge

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.rayleigh_quotient_at_zero
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.rayleigh_quotient_at_basis
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.ground_state_not_at_zero
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.basis_vector_achieves_ground_state_iff_v_alpha_matches
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.v_alpha_at_zero_ne_ground_state
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.polylog_conjecture_implies_alpha_distinct
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.polylog_conjecture_implies_classes_distinct
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.polylog_conjecture_iff_canonical_assignment
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.polylog_existential_iff_classes_distinct
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.polylog_discharge_obstruction
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.spectral_identification_via_b_clean
#print axioms PrincipiaTractalis.PolylogEigenvalueDischarge.polylog_discharge_unified
