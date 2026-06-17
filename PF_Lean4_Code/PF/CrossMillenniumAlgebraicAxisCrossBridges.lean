/-
# PF.CrossMillenniumAlgebraicAxisCrossBridges

★ 2026-06-17 — Two clean closed-form cross-axis bridges between the
two algebraic Clay α-axes (α_P = √2, α_NP = φ + 1/4) and α_Hodge = φ.

## Identities

  (A) `α_NP * α_P = (4·α_Hodge + 1) · α_P / 4`
      Equivalently `α_NP · α_P = √2 · (4φ + 1) / 4`.

      Derivation:
        α_NP · α_P = (φ + 1/4) · √2
                   = φ·√2 + √2/4
                   = (4φ + 1)·√2 / 4
                   = (4·α_Hodge + 1)·α_P / 4.

  (B) `α_NP / α_P = (4·α_Hodge + 1) · α_P / 8`
      Equivalently `α_NP / α_P = √2 · (4φ + 1) / 8`.

      Derivation: (A) divided by 2 via 1/α_P = α_P/2.

Both identities exhibit `4·α_Hodge + 1 = 4φ + 1` as the structural
coefficient relating the two algebraic Clay axes (P, NP) to α_Hodge.
Numerically `4φ + 1 ≈ 7.4721`, giving `α_NP·α_P ≈ 2.6420` and
`α_NP/α_P ≈ 1.3210` matching `(φ + 1/4)·√2` and `(φ + 1/4)/√2`.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PrincipiaTractalis
namespace CrossMillenniumAlgebraicAxisCrossBridges

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — The product identity -/

/-- **`α_NP · α_P = (4·α_Hodge + 1) · α_P / 4`** — the product of the
    two algebraic Clay α-axes factors through `4·α_Hodge + 1` and α_P.

    Equivalently `α_NP · α_P = √2 · (4φ + 1) / 4`. -/
theorem α_NP_mul_α_P_closed_form :
    α_NP * α_P = (4 * α_Hodge + 1) * α_P / 4 := by
  unfold α_NP α_P α_Hodge phi
  ring

/-- **Numerical witness for (A)** — `α_NP · α_P = √2 · (4φ + 1) / 4`
    in the literal `(φ + 1/4)·√2` evaluation. -/
theorem α_NP_mul_α_P_literal :
    α_NP * α_P = Real.sqrt 2 * (4 * α_Hodge + 1) / 4 := by
  rw [α_NP_mul_α_P_closed_form]
  unfold α_P
  ring

/-! ## §2 — The ratio identity -/

/-- **`α_NP / α_P = (4·α_Hodge + 1) · α_P / 8`** — the ratio of the two
    algebraic Clay α-axes factors through `4·α_Hodge + 1` and α_P,
    with a factor of 1/8.

    Derivation: `α_NP / α_P = α_NP · (1/α_P) = α_NP · (α_P/2)` by
    `inv_α_P_eq_α_P_div_two`, then apply (A). -/
theorem α_NP_div_α_P_closed_form :
    α_NP / α_P = (4 * α_Hodge + 1) * α_P / 8 := by
  unfold α_NP α_P α_Hodge phi
  have h_sqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  have h_sqrt_two_pos : Real.sqrt 2 > 0 :=
    Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  field_simp
  nlinarith [h_sqrt_two_sq, h_sqrt_two_pos]

/-- **Numerical witness for (B)** — `α_NP / α_P = √2 · (4φ + 1) / 8`
    in the literal evaluation. -/
theorem α_NP_div_α_P_literal :
    α_NP / α_P = Real.sqrt 2 * (4 * α_Hodge + 1) / 8 := by
  rw [α_NP_div_α_P_closed_form]
  unfold α_P
  ring

/-! ## §3 — Product/ratio capstone -/

/-- **★ Algebraic-axis cross-bridge capstone ★** — both the product
    and the ratio of α_NP and α_P factor through `(4·α_Hodge + 1)·α_P`,
    with the product = .../4 and the ratio = .../8. The factor-of-2
    relating the two is exactly `α_P² = 2`. -/
theorem α_NP_α_P_cross_bridge_capstone :
    α_NP * α_P = (4 * α_Hodge + 1) * α_P / 4 ∧
    α_NP / α_P = (4 * α_Hodge + 1) * α_P / 8 ∧
    α_NP * α_P = 2 * (α_NP / α_P) :=
  ⟨α_NP_mul_α_P_closed_form,
   α_NP_div_α_P_closed_form,
   by rw [α_NP_mul_α_P_closed_form, α_NP_div_α_P_closed_form]; ring⟩

end CrossMillenniumAlgebraicAxisCrossBridges
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.CrossMillenniumAlgebraicAxisCrossBridges.α_NP_mul_α_P_closed_form
#print axioms
  PrincipiaTractalis.CrossMillenniumAlgebraicAxisCrossBridges.α_NP_div_α_P_closed_form
#print axioms
  PrincipiaTractalis.CrossMillenniumAlgebraicAxisCrossBridges.α_NP_α_P_cross_bridge_capstone
