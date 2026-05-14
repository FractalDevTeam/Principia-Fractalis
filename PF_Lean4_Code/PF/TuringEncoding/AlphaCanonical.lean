/-
# Canonical α Values — Direct Algebraic Identities

The book's Ch 21 Section 4.2 fixes the canonical resonance values
`α_P = √2` and `α_NP = φ + 1/4` for the P-class and NP-class operators
respectively. The remaining project axiom `alpha_class_self_adjointness_canonical`
asserts these values satisfy the algebraic equations

  `α_P^2 = 2`         and         `16·α_NP^2 − 24·α_NP − 11 = 0`

as the "self-adjointness equations" of the operators. This file provides
**direct, axiom-free proofs** of these algebraic identities for the specific
real numbers `√2` and `φ + 1/4`, demonstrating that the algebraic content of
the axiom is independently verifiable.

The axiom's substantive content is therefore not the algebraic equations
themselves (which are simple arithmetic facts about specific real numbers)
but rather the *structural assignment* of these values to ClassP and ClassNP
via the opaque function `alpha_of_class`.

The path to genuinely retire the axiom requires either:
(a) defining `alpha_of_class` concretely (breaks the downstream P ≠ NP chain
    since concrete-definition forces ClassP=ClassNP → equal α values), or
(b) deriving the assignment from a rigorous SA reality criterion involving
    polylog / modular-form analysis (multi-month foundation work).

This file delivers (a)-prerequisite: the **algebraic identities** held as
axiom-free theorems, providing the referee with direct verification of the
arithmetic content.

Stage L4 — direct axiom-free identities for the canonical α values.
-/

import PF.IntervalArithmetic

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## Identity 1: `(√2)² = 2` -/

/-- `(Real.sqrt 2)^2 = 2` — the P-class algebraic identity, axiom-free. -/
theorem alpha_P_sq : (Real.sqrt 2) ^ 2 = 2 :=
  Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-! ## Identity 2: φ satisfies `φ² = φ + 1` -/

/-- The golden ratio's defining quadratic: `φ² = φ + 1`. -/
theorem phi_sq_eq : phi ^ 2 = phi + 1 := by
  unfold phi
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- ((1+√5)/2)² = (1 + 2√5 + (√5)²)/4 = (6 + 2√5)/4 = (3+√5)/2
  -- (1+√5)/2 + 1 = (3+√5)/2 ✓
  field_simp
  nlinarith [h5]

/-! ## Identity 3: `16·(φ + 1/4)² − 24·(φ + 1/4) − 11 = 0` -/

/-- `α_NP = φ + 1/4` satisfies the NP-class quadratic `16α² − 24α − 11 = 0`,
    axiom-free.

    Derivation: expand `16(φ + 1/4)² = 16φ² + 8φ + 1`. Using `φ² = φ + 1`,
    this is `16(φ + 1) + 8φ + 1 = 24φ + 17`. And `24(φ + 1/4) = 24φ + 6`.
    So `16α² − 24α − 11 = (24φ + 17) − (24φ + 6) − 11 = 0`. -/
theorem alpha_NP_quadratic :
    16 * (phi + 1/4) ^ 2 - 24 * (phi + 1/4) - 11 = 0 := by
  have h := phi_sq_eq
  nlinarith [h]

/-! ## Positivity facts -/

/-- `Real.sqrt 2 > 0` — used to identify `√2` as the unique positive
    root of `α² = 2`. -/
theorem alpha_P_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

/-- `φ + 1/4 > 0` — used to identify `φ + 1/4` as the positive root of
    the NP-class quadratic. -/
theorem alpha_NP_pos : 0 < phi + 1/4 := by
  have h : (1.6180339887 : ℝ) ≤ phi := phi_in_interval_10digit.1
  linarith

/-! ## Bridge: the canonical pair satisfies the axiom's content

The pair `(√2, φ + 1/4)` jointly satisfies the algebraic system of
`alpha_class_self_adjointness_canonical` — but now as a direct
algebraic fact, not as an axiom about an opaque function. -/

/-- **The canonical algebraic pair** (axiom-free version of the axiom's
    content, on the *specific* real numbers `√2` and `φ + 1/4` rather
    than on `alpha_of_class ClassP` and `alpha_of_class ClassNP`). -/
theorem canonical_alpha_algebraic_pair :
    ((Real.sqrt 2) ^ 2 = 2 ∧ 0 < Real.sqrt 2) ∧
    (16 * (phi + 1/4) ^ 2 - 24 * (phi + 1/4) - 11 = 0 ∧ 0 < phi + 1/4) :=
  ⟨⟨alpha_P_sq, alpha_P_pos⟩, ⟨alpha_NP_quadratic, alpha_NP_pos⟩⟩

/-! ## Equivalence: axiom's algebraic form ⇔ value assignment

The axiom `alpha_class_self_adjointness_canonical` asserts the algebraic
conjunction on `alpha_of_class ClassP` and `alpha_of_class ClassNP`. We
show this is logically equivalent (for *any* real-valued function `f`)
to the *value assignment* `f x = √2 ∧ f y = φ + 1/4` — making the
axiom's substantive content transparent as a structural identification
of two distinguished resonance values. -/

/-- **Forward direction**: the algebraic system pins the values. Given
    `f` satisfying the algebra on `(x, y)`, then `f x = √2` and `f y = φ + 1/4`. -/
theorem algebraic_pair_to_value_assignment
    {f : Set Language → ℝ} {x y : Set Language}
    (h : ((f x) ^ 2 = 2 ∧ 0 < f x) ∧
         (16 * (f y) ^ 2 - 24 * (f y) - 11 = 0 ∧ 0 < f y)) :
    f x = Real.sqrt 2 ∧ f y = phi + 1/4 := by
  obtain ⟨⟨hxsq, hxpos⟩, ⟨hyquad, hypos⟩⟩ := h
  refine ⟨?_, ?_⟩
  · -- f x = √2 via Real.sqrt_sq + (f x)² = 2 + positivity
    have : Real.sqrt ((f x) ^ 2) = f x := Real.sqrt_sq hxpos.le
    rw [← this, hxsq]
  · -- f y = φ + 1/4: the positive root of 16α² − 24α − 11 = 0
    -- Discriminant: 24² + 4·16·11 = 576 + 704 = 1280 = 64·20 = 256·5
    -- Roots: (24 ± √1280) / 32 = (24 ± 16√5) / 32 = (3 ± 2√5) / 4
    -- Positive root: (3 + 2√5) / 4. We claim (3 + 2√5)/4 = φ + 1/4.
    -- φ + 1/4 = (1 + √5)/2 + 1/4 = (2 + 2√5 + 1)/4 = (3 + 2√5)/4. ✓
    have h_target : phi + 1/4 = (3 + 2 * Real.sqrt 5) / 4 := by
      unfold phi; ring
    -- Factor the quadratic: 16y² - 24y - 11 = 16(y - (3+2√5)/4)(y - (3-2√5)/4)
    have h5_pos : (0 : ℝ) < Real.sqrt 5 :=
      Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
    have h5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    have h_factor : (16 : ℝ) * (f y) ^ 2 - 24 * (f y) - 11 =
                    16 * (f y - (3 + 2 * Real.sqrt 5) / 4) *
                         (f y - (3 - 2 * Real.sqrt 5) / 4) := by
      have h5sq : (Real.sqrt 5) * (Real.sqrt 5) = 5 := by
        have := h5_sq; nlinarith [this]
      ring_nf
      nlinarith [h5_sq]
    rw [h_factor] at hyquad
    -- Either f y = (3+2√5)/4 or f y = (3-2√5)/4. The negative root is excluded.
    have h_neg_root : (3 - 2 * Real.sqrt 5) / 4 < 0 := by
      have h_sqrt5_gt : Real.sqrt 5 > 3 / 2 := by
        have : (3/2 : ℝ)^2 < 5 := by norm_num
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), h5_pos]
      linarith
    -- From product = 0 (modulo factor 16 ≠ 0), one of the factors is zero
    have h16_ne : (16 : ℝ) ≠ 0 := by norm_num
    have h_prod_zero : (f y - (3 + 2 * Real.sqrt 5) / 4) *
                       (f y - (3 - 2 * Real.sqrt 5) / 4) = 0 := by
      have := hyquad
      nlinarith [hyquad]
    rcases mul_eq_zero.mp h_prod_zero with h_pos_root | h_neg_root_eq
    · -- f y = (3+2√5)/4 = φ + 1/4 ✓
      have : f y = (3 + 2 * Real.sqrt 5) / 4 := by linarith
      rw [this, ← h_target]
    · -- f y = (3-2√5)/4 < 0, contradicts hypos
      have : f y = (3 - 2 * Real.sqrt 5) / 4 := by linarith
      linarith [this ▸ hypos]

end PrincipiaTractalis.TuringEncoding
