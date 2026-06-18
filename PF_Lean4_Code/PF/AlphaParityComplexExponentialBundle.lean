/-
# PF.AlphaParityComplexExponentialBundle

★★★★ 2026-06-17 — FUN: parity of α-axes under `exp(2π·i·x)` exhibits
the algebraic-integer-vs-half-integer-vs-integer structure of the
framework's rational Clay axes.

## Parity identities

  exp(2π·i·α_RH) = −1                 (half-integer α_RH = 3/2)
  exp(2π·i·α_YM) = 1                  (integer α_YM = 2)
  exp(2π·i·α_Poincaré) = 1            (integer α_Poincaré = 1)
  exp(2π·i·α_P²) = 1                  (since α_P² = α_YM)

The framework's rational Clay axes split into integer (α_Poincaré, α_YM)
and half-integer (α_RH) classes under the `e^(2πi·x)` parity map. The
algebraic-irrational axes (α_P, α_NP, α_Hodge) do not factor as
clean half-integer or integer combinations of π.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace PrincipiaTractalis
namespace AlphaParityComplexExponentialBundle

open Real Complex
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — exp(2π·i·α_RH) = −1 (half-integer parity) -/

/-- **★★★ `exp(2π·i·α_RH) = −1` ★★★** — α_RH = 3/2 is a half-integer,
    so 2π·α_RH = 3π gives the canonical Euler half-rotation. -/
theorem exp_two_pi_i_α_RH_eq_neg_one :
    Complex.exp (2 * Real.pi * α_RH * Complex.I) = -1 := by
  have h_rewrite : (2 * (Real.pi : ℂ) * (α_RH : ℂ) * Complex.I) =
                   ((3 : ℂ) * Real.pi * Complex.I) := by
    unfold α_RH
    push_cast
    ring
  rw [h_rewrite]
  -- exp(3πi) = exp(2πi + πi) = exp(2πi) · exp(πi) = 1 · (-1) = -1
  have h_split : ((3 : ℂ) * Real.pi * Complex.I) =
                 (2 * Real.pi * Complex.I + Real.pi * Complex.I) := by ring
  rw [h_split, Complex.exp_add, Complex.exp_two_pi_mul_I, Complex.exp_pi_mul_I]
  ring

/-! ## §2 — exp(2π·i·α_YM) = 1 (integer parity) -/

/-- **★★★ `exp(2π·i·α_YM) = 1` ★★★** — α_YM = 2 is an integer, so
    2π·α_YM = 4π gives a full multiple of 2π. -/
theorem exp_two_pi_i_α_YM_eq_one :
    Complex.exp (2 * Real.pi * α_YM * Complex.I) = 1 := by
  have h_rewrite : (2 * (Real.pi : ℂ) * (α_YM : ℂ) * Complex.I) =
                   (2 * Real.pi * Complex.I + 2 * Real.pi * Complex.I) := by
    unfold α_YM
    push_cast
    ring
  rw [h_rewrite, Complex.exp_add, Complex.exp_two_pi_mul_I]
  ring

/-! ## §3 — exp(2π·i·α_Poincaré) = 1 -/

/-- **`exp(2π·i·α_Poincaré) = 1`** — α_Poincaré = 1 gives the canonical
    Euler full-rotation. -/
theorem exp_two_pi_i_α_Poincare_eq_one :
    Complex.exp (2 * Real.pi * α_Poincare * Complex.I) = 1 := by
  have h_rewrite : (2 * (Real.pi : ℂ) * (α_Poincare : ℂ) * Complex.I) =
                   (2 * Real.pi * Complex.I) := by
    unfold α_Poincare
    push_cast
    ring
  rw [h_rewrite, Complex.exp_two_pi_mul_I]

/-! ## §4 — exp(2π·i·α_P²) = 1 -/

/-- **`exp(2π·i·α_P²) = 1`** — since α_P² = α_YM = 2 (an integer). -/
theorem exp_two_pi_i_α_P_sq_eq_one :
    Complex.exp (2 * Real.pi * α_P ^ 2 * Complex.I) = 1 := by
  have h_p_sq : α_P ^ 2 = α_YM := α_P_sq_eq_α_YM
  have h_rewrite : (2 * (Real.pi : ℂ) * ((α_P : ℂ) ^ 2) * Complex.I) =
                   (2 * Real.pi * (α_YM : ℂ) * Complex.I) := by
    push_cast
    rw [show ((α_P : ℂ) ^ 2 : ℂ) = ((α_P ^ 2 : ℝ) : ℂ) by push_cast; ring]
    rw [show ((α_P ^ 2 : ℝ) : ℂ) = ((α_YM : ℝ) : ℂ) by rw [h_p_sq]]
  rw [h_rewrite, exp_two_pi_i_α_YM_eq_one]

/-! ## §5 — Bundle capstone -/

/-- **★★★★ THE α-AXIS PARITY COMPLEX-EXPONENTIAL CAPSTONE ★★★★** —
    four identities exhibiting the integer-vs-half-integer split of
    the framework's rational Clay axes under `e^(2πi·x)`:

      exp(2π·i·α_RH) = −1            (half-integer, α_RH = 3/2)
      exp(2π·i·α_YM) = 1             (integer, α_YM = 2)
      exp(2π·i·α_Poincaré) = 1       (integer, α_Poincaré = 1)
      exp(2π·i·α_P²) = 1             (since α_P² = α_YM)

    The framework's rational Clay axes split cleanly into the
    Pontryagin-dual classes of the complex unit circle. -/
theorem α_parity_complex_exponential_capstone :
    Complex.exp (2 * Real.pi * α_RH * Complex.I) = -1 ∧
    Complex.exp (2 * Real.pi * α_YM * Complex.I) = 1 ∧
    Complex.exp (2 * Real.pi * α_Poincare * Complex.I) = 1 ∧
    Complex.exp (2 * Real.pi * α_P ^ 2 * Complex.I) = 1 :=
  ⟨exp_two_pi_i_α_RH_eq_neg_one,
   exp_two_pi_i_α_YM_eq_one,
   exp_two_pi_i_α_Poincare_eq_one,
   exp_two_pi_i_α_P_sq_eq_one⟩

end AlphaParityComplexExponentialBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaParityComplexExponentialBundle.exp_two_pi_i_α_RH_eq_neg_one
#print axioms PrincipiaTractalis.AlphaParityComplexExponentialBundle.exp_two_pi_i_α_YM_eq_one
#print axioms PrincipiaTractalis.AlphaParityComplexExponentialBundle.exp_two_pi_i_α_Poincare_eq_one
#print axioms PrincipiaTractalis.AlphaParityComplexExponentialBundle.exp_two_pi_i_α_P_sq_eq_one
#print axioms PrincipiaTractalis.AlphaParityComplexExponentialBundle.α_parity_complex_exponential_capstone
