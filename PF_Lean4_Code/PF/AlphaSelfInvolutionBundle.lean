/-
# PF.AlphaSelfInvolutionBundle

★★★★ 2026-06-17 — FUN: each α-axis under the involution `x ↦ x·(x − 1)`
lands on a clean framework constant. The map `x ↦ x² − x` exhibits each
axis's structural signature.

## Self-involution identities

  α_Hodge · (α_Hodge − 1) = α_Poincaré                (golden, → 1)
  α_YM · (α_YM − 1) = α_YM                             (silver fixed point)
  α_P · (α_P − 1) = α_YM − α_P                         (P-class diagonal)
  α_RH · (α_RH − 1) = 3/4 = α_BSD/π                   (existing — rational decomposition)

The golden axis under the involution lands EXACTLY on α_Poincaré = 1.
The Yang-Mills axis is a FIXED POINT of the involution (since α_YM − 1
= α_Poincaré = 1, we have α_YM · 1 = α_YM).

## Inverse-power sum identity

  1/α_Hodge + 1/α_Hodge² = α_Poincaré

The sum of the first two negative powers of the golden axis equals one.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaSelfInvolutionBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_Hodge · (α_Hodge − 1) = α_Poincaré -/

/-- **★★★ `α_Hodge · (α_Hodge − 1) = α_Poincaré` ★★★** — the golden axis
    under the involution x↦x(x−1) lands on α_Poincaré = 1. -/
theorem α_Hodge_mul_α_Hodge_sub_one_eq_α_Poincare :
    α_Hodge * (α_Hodge - 1) = α_Poincare := by
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  unfold α_Poincare
  nlinarith [h_sq]

/-! ## §2 — 1/α_Hodge + 1/α_Hodge² = α_Poincaré -/

/-- **★★★ `1/α_Hodge + 1/α_Hodge² = α_Poincaré` ★★★** — sum of the
    first two negative powers of α_Hodge equals one. -/
theorem inv_α_Hodge_plus_inv_α_Hodge_sq_eq_α_Poincare :
    1 / α_Hodge + 1 / α_Hodge ^ 2 = α_Poincare := by
  have h_pos : 0 < α_Hodge := by
    unfold α_Hodge phi
    have : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
    linarith
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  have h_pow_pos : 0 < α_Hodge ^ 2 := pow_pos h_pos 2
  unfold α_Poincare
  field_simp
  nlinarith [h_sq, h_pos]

/-! ## §3 — α_YM · (α_YM − 1) = α_YM (silver fixed point) -/

/-- **`α_YM · (α_YM − 1) = α_YM`** — α_YM = 2 is a fixed point of the
    involution x↦x(x−1) (since α_YM − 1 = 1, multiplication is identity). -/
theorem α_YM_mul_α_YM_sub_one_eq_α_YM :
    α_YM * (α_YM - 1) = α_YM := by
  unfold α_YM
  norm_num

/-! ## §4 — α_P · (α_P − 1) = α_YM − α_P -/

/-- **`α_P · (α_P − 1) = α_YM − α_P`** — P-class under the involution
    yields the YM-deficit (= 2 − √2). -/
theorem α_P_mul_α_P_sub_one_eq_α_YM_sub_α_P :
    α_P * (α_P - 1) = α_YM - α_P := by
  have h_p_sq : α_P ^ 2 = α_YM := α_P_sq_eq_α_YM
  nlinarith [h_p_sq]

/-! ## §5 — Bundle capstone -/

/-- **★★★★ THE α-AXIS SELF-INVOLUTION BUNDLE CAPSTONE ★★★★** —
    four identities exhibiting how each α-axis behaves under the
    involution `x ↦ x·(x − 1) = x² − x`:

      α_Hodge · (α_Hodge − 1) = α_Poincaré          (golden, → 1)
      1/α_Hodge + 1/α_Hodge² = α_Poincaré           (negative-power sum)
      α_YM · (α_YM − 1) = α_YM                       (silver fixed point)
      α_P · (α_P − 1) = α_YM − α_P                   (P-class diagonal)

    α_Hodge maps to α_Poincaré; α_YM is the fixed point; α_P relates
    to α_YM via the involution. -/
theorem α_self_involution_bundle_capstone :
    α_Hodge * (α_Hodge - 1) = α_Poincare ∧
    1 / α_Hodge + 1 / α_Hodge ^ 2 = α_Poincare ∧
    α_YM * (α_YM - 1) = α_YM ∧
    α_P * (α_P - 1) = α_YM - α_P :=
  ⟨α_Hodge_mul_α_Hodge_sub_one_eq_α_Poincare,
   inv_α_Hodge_plus_inv_α_Hodge_sq_eq_α_Poincare,
   α_YM_mul_α_YM_sub_one_eq_α_YM,
   α_P_mul_α_P_sub_one_eq_α_YM_sub_α_P⟩

end AlphaSelfInvolutionBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaSelfInvolutionBundle.α_Hodge_mul_α_Hodge_sub_one_eq_α_Poincare
#print axioms PrincipiaTractalis.AlphaSelfInvolutionBundle.inv_α_Hodge_plus_inv_α_Hodge_sq_eq_α_Poincare
#print axioms PrincipiaTractalis.AlphaSelfInvolutionBundle.α_YM_mul_α_YM_sub_one_eq_α_YM
#print axioms PrincipiaTractalis.AlphaSelfInvolutionBundle.α_P_mul_α_P_sub_one_eq_α_YM_sub_α_P
#print axioms PrincipiaTractalis.AlphaSelfInvolutionBundle.α_self_involution_bundle_capstone
