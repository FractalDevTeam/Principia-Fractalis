/-
# PF.AlphaComplexUnitAlgebraBundle

★★★★ 2026-06-17 — FUN: identities for the complex unit `i` and `1+i`
in framework form.

## Headline

  i² = −α_Poincaré
  i⁴ = α_Poincaré
  (1 + i)² = α_YM · i
  ‖1 + i‖² = α_YM        (so ‖1 + i‖ = α_P)

The complex imaginary unit and 1+i — the basic Gaussian-integer building
blocks — anchor to α_Poincaré (unity) and α_YM (= 2 = magnitude squared
of 1+i).

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace PrincipiaTractalis
namespace AlphaComplexUnitAlgebraBundle

open Complex
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — i² = −α_Poincaré -/

/-- **`i² = −α_Poincaré`** — defining property of i. -/
theorem I_sq_eq_neg_α_Poincare :
    Complex.I ^ 2 = -(α_Poincare : ℂ) := by
  rw [Complex.I_sq]
  unfold α_Poincare
  push_cast
  ring

/-! ## §2 — i⁴ = α_Poincaré -/

/-- **`i⁴ = α_Poincaré`** — fourth-power identity. -/
theorem I_pow_four_eq_α_Poincare :
    Complex.I ^ 4 = (α_Poincare : ℂ) := by
  have h : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
  rw [h, Complex.I_sq]
  unfold α_Poincare
  push_cast
  ring

/-! ## §3 — (1 + i)² = α_YM · i -/

/-- **★★★ `(1 + i)² = α_YM · i` ★★★** — the canonical Gaussian-integer
    square equals 2i in framework form. -/
theorem one_add_I_sq_eq_α_YM_mul_I :
    (1 + Complex.I) ^ 2 = (α_YM : ℂ) * Complex.I := by
  have h_expand : (1 + Complex.I) ^ 2 = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
  rw [h_expand, Complex.I_sq]
  unfold α_YM
  push_cast
  ring

/-! ## §4 — ‖1 + i‖² = α_YM -/

/-- **`‖1 + i‖² = α_YM`** — squared modulus of 1+i equals 2. -/
theorem normSq_one_add_I_eq_α_YM :
    Complex.normSq (1 + Complex.I) = α_YM := by
  simp [Complex.normSq_apply]
  unfold α_YM
  ring

/-! ## §5 — Bundle capstone -/

/-- **★★★★ THE α-AXIS COMPLEX-UNIT-ALGEBRA BUNDLE CAPSTONE ★★★★** —
    four identities exhibiting basic Gaussian-integer algebra in
    framework form:

      i² = −α_Poincaré                       (defining property)
      i⁴ = α_Poincaré                         (fourth-power identity)
      (1 + i)² = α_YM · i                     (Gaussian-integer squared)
      ‖1 + i‖² = α_YM                          (modulus squared)

    The complex imaginary unit and 1+i anchor to α_Poincaré (unity)
    and α_YM (= 2 = both (1+i)² rotation factor and squared modulus). -/
theorem α_complex_unit_algebra_bundle_capstone :
    Complex.I ^ 2 = -(α_Poincare : ℂ) ∧
    Complex.I ^ 4 = (α_Poincare : ℂ) ∧
    (1 + Complex.I) ^ 2 = (α_YM : ℂ) * Complex.I ∧
    Complex.normSq (1 + Complex.I) = α_YM :=
  ⟨I_sq_eq_neg_α_Poincare,
   I_pow_four_eq_α_Poincare,
   one_add_I_sq_eq_α_YM_mul_I,
   normSq_one_add_I_eq_α_YM⟩

end AlphaComplexUnitAlgebraBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaComplexUnitAlgebraBundle.I_sq_eq_neg_α_Poincare
#print axioms PrincipiaTractalis.AlphaComplexUnitAlgebraBundle.I_pow_four_eq_α_Poincare
#print axioms PrincipiaTractalis.AlphaComplexUnitAlgebraBundle.one_add_I_sq_eq_α_YM_mul_I
#print axioms PrincipiaTractalis.AlphaComplexUnitAlgebraBundle.normSq_one_add_I_eq_α_YM
#print axioms PrincipiaTractalis.AlphaComplexUnitAlgebraBundle.α_complex_unit_algebra_bundle_capstone
