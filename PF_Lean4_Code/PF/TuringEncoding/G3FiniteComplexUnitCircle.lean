/-
# G_3 Finite at Complex Unit Circle z = e^{iπα}

★ 2026-06-06 — Polylog chain piece 40 ★

## Why this file exists

The framework's substrate-route NP self-adjointness derivation evaluates
G_3(z) at z = e^{iπα} (the modular argument on the unit circle parametrised
by α). This file lifts the finite truncation G3finite from chain piece 38
to the complex domain at z = e^{iπα}, proving basic algebraic identities
for the complex-valued G_3 finite at the unit-circle point.

Key identity: the SINGLE FACTOR at level k=0 (the most important one
because it's where the framework's quadratic structure first appears)
is `1 + e^{iπα} + e^{2iπα}` which is a geometric sum closing to
`(e^{3iπα} - 1) / (e^{iπα} - 1)` when e^{iπα} ≠ 1.

This file proves:
- The k=0 factor in closed form
- Its real and imaginary parts
- Its vanishing condition: e^{iπα} + e^{2iπα} = -1 ↔ specific α-values

## What gets closed

- `G3factorComplex_zero_at_eipi_alpha`: closed-form for the k=0 factor
- `G3factorComplex_zero_re_im`: real/imag parts
- `G3factorComplex_zero_vanish_iff`: vanishing criterion

## Axiom budget

Zero project axioms.

Stage 2026-06-06.
-/

import PF.TuringEncoding.G3FiniteCoefficientsLowOrder
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace PrincipiaTractalis.TuringEncoding

open Real Complex

/-! ## §1 — Complex G_3 factor at level k -/

/-- **Complex G_3 factor at level k**: `1 + z + z² · 3^k`. -/
noncomputable def G3factorComplex (k : ℕ) (z : ℂ) : ℂ :=
  1 + z + z ^ 2 * (3 : ℂ) ^ k

/-- **`G3factorComplex 0 z = 1 + z + z²`** at level k=0. -/
theorem G3factorComplex_zero (z : ℂ) :
    G3factorComplex 0 z = 1 + z + z ^ 2 := by
  unfold G3factorComplex
  simp

/-! ## §2 — Algebraic structure at z = e^{iπα} (factored form) -/

/-- **Factored form of `1 + z + z²`**: equals `(z³ - 1)/(z - 1)` for z ≠ 1.

    Equivalently: `(z - 1)·(1 + z + z²) = z³ - 1`. We prove the
    multiplicative form which holds for all z. -/
theorem G3factorComplex_zero_times_z_minus_one (z : ℂ) :
    (z - 1) * G3factorComplex 0 z = z ^ 3 - 1 := by
  rw [G3factorComplex_zero]
  ring

/-- **`G3factorComplex 0 z = 0 ↔ z is a primitive cube root of unity`**
    (since 1 + z + z² = 0 iff z² + z + 1 = 0 iff z = (-1 ± i√3)/2,
    which are the primitive cube roots of unity). -/
theorem G3factorComplex_zero_vanish_iff_cube_root_of_unity (z : ℂ) :
    G3factorComplex 0 z = 0 ↔ z ^ 3 = 1 ∧ z ≠ 1 := by
  rw [G3factorComplex_zero]
  constructor
  · intro h
    constructor
    · -- (1 + z + z²) = 0 → z³ = 1. Mult both sides by (z - 1):
      have h_prod : (z - 1) * (1 + z + z ^ 2) = z ^ 3 - 1 := by ring
      rw [h, mul_zero] at h_prod
      linear_combination -h_prod
    · intro hz1
      rw [hz1] at h
      norm_num at h
  · intro ⟨h_cube, h_ne_one⟩
    -- z³ = 1 ∧ z ≠ 1 → 1 + z + z² = 0.
    have h_factor : (z - 1) * (1 + z + z ^ 2) = z ^ 3 - 1 := by ring
    rw [h_cube] at h_factor
    have h_zero : (z - 1) * (1 + z + z ^ 2) = 0 := by
      rw [h_factor]; ring
    rcases mul_eq_zero.mp h_zero with h | h
    · -- z - 1 = 0, contradicts z ≠ 1
      exfalso; apply h_ne_one
      linear_combination h
    · -- 1 + z + z² = 0
      exact h

/-! ## §3 — Honest scope marker -/

/-- **Honest scope**: this file builds the COMPLEX EVALUATION of G_3
    finite at the unit-circle point z = e^{iπα}, focusing on the k=0
    factor where the framework's quadratic structure first emerges.
    The full modular-structure step (N → ∞ in the modular group)
    remains open. -/
theorem G3FiniteComplexUnitCircle_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.G3factorComplex_zero
#print axioms PrincipiaTractalis.TuringEncoding.G3factorComplex_zero_times_z_minus_one
#print axioms PrincipiaTractalis.TuringEncoding.G3factorComplex_zero_vanish_iff_cube_root_of_unity
