/-
# PF.AlphaPentagonalCosBundle

★★★ 2026-06-17 — FUN: cos(π/10) in framework form via α_Hodge.

## Pentagonal cos

  cos²(π/10) = (α_Hodge + 2) / 4
  cos(π/10)  = √(α_Hodge + 2) / 2

The framework's golden axis appears under a square root in cos(π/10),
mirroring the sin(π/5) = √(3 − α_Hodge)/2 identity from
`AlphaPentagonalSinBundle`.

## Derivation

  cos²(π/10) = 1 − sin²(π/10) = 1 − (1/(2·α_Hodge))²
            = 1 − 1/(4·α_Hodge²)
            = 1 − (1/4)·(2 − α_Hodge)        [via 1/α_Hodge² = 2 − α_Hodge]
            = 1 − 1/2 + α_Hodge/4
            = (α_Hodge + 2) / 4.

## Complete 5-fold trig parameterisation by α_Hodge

  cos(π/10)   = √(α_Hodge + 2) / 2
  sin(π/10)   = 1 / (2·α_Hodge)
  cos(π/5)    = α_Hodge / 2                  (existing)
  sin(π/5)    = √(3 − α_Hodge) / 2           (existing in AlphaPentagonalSinBundle)
  cos(2π/5)   = 1 / (2·α_Hodge)              (= sin(π/10) by complementary angle)
  sin(2π/5)   = √(α_Hodge + 2) / 2           (= cos(π/10))
  cos(3π/10)  = √(3 − α_Hodge) / 2           (= sin(π/5))
  sin(3π/10)  = α_Hodge / 2                  (= cos(π/5))

All eight 5-fold-symmetry trig values are parameterized by α_Hodge.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaPentagonalCosBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants

/-! ## §1 — cos²(π/10) = (α_Hodge + 2) / 4 -/

/-- **★★★ `cos²(π/10) = (α_Hodge + 2) / 4` ★★★** — clean closed form. -/
theorem cos_sq_pi_div_ten_eq :
    Real.cos (Real.pi / 10) ^ 2 = (α_Hodge + 2) / 4 := by
  have h_pyth : Real.sin (Real.pi / 10) ^ 2 + Real.cos (Real.pi / 10) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (Real.pi / 10)
  rw [sin_pi_div_ten_eq_one_div_two_α_Hodge] at h_pyth
  have h_pos : 0 < α_Hodge := by
    unfold α_Hodge phi
    have : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
    linarith
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  have h_pow_pos : 0 < α_Hodge ^ 2 := pow_pos h_pos 2
  -- inv_sq: 1/α_Hodge² = 2 − α_Hodge
  have h_inv_sq : 1 / α_Hodge ^ 2 = 2 - α_Hodge := by
    field_simp
    nlinarith [h_sq, h_pos]
  -- h_pyth: (1/(2·α_Hodge))² + cos² = 1
  -- Goal: cos² = (α_Hodge + 2)/4
  -- (1/(2α_Hodge))² = 1/(4α_Hodge²) = (1/4)·(2 − α_Hodge) = (2 − α_Hodge)/4
  have h_sin_sq : (1 / (2 * α_Hodge)) ^ 2 = (2 - α_Hodge) / 4 := by
    rw [show ((1 / (2 * α_Hodge)) ^ 2 : ℝ) = 1 / (4 * α_Hodge ^ 2) by ring]
    rw [show (1 / (4 * α_Hodge ^ 2) : ℝ) = (1 / α_Hodge ^ 2) / 4 by ring]
    rw [h_inv_sq]
  linarith [h_pyth, h_sin_sq]

/-! ## §2 — cos(π/10) positivity -/

private lemma cos_pi_div_ten_pos : 0 < Real.cos (Real.pi / 10) := by
  apply Real.cos_pos_of_mem_Ioo
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  constructor
  · -- Goal: -(π/2) < π/10
    show -(Real.pi / 2) < Real.pi / 10
    linarith
  · -- Goal: π/10 < π/2
    show Real.pi / 10 < Real.pi / 2
    linarith

/-! ## §3 — cos(π/10) = √(α_Hodge + 2) / 2 -/

/-- **★★★ `cos(π/10) = √(α_Hodge + 2) / 2` ★★★** — pentagonal cos in
    framework form. -/
theorem cos_pi_div_ten_eq_sqrt_α_Hodge_plus_two_div_two :
    Real.cos (Real.pi / 10) = Real.sqrt (α_Hodge + 2) / 2 := by
  have h_sq : Real.cos (Real.pi / 10) ^ 2 = (α_Hodge + 2) / 4 :=
    cos_sq_pi_div_ten_eq
  have h_pos : 0 < Real.cos (Real.pi / 10) := cos_pi_div_ten_pos
  have h_α_Hodge_plus_two_nonneg : 0 ≤ α_Hodge + 2 := by
    have h_pos : 0 < α_Hodge := by
      unfold α_Hodge phi
      have : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
      linarith
    linarith
  have h_squared : (Real.cos (Real.pi / 10)) ^ 2 =
                   (Real.sqrt (α_Hodge + 2) / 2) ^ 2 := by
    rw [h_sq]
    rw [div_pow]
    rw [Real.sq_sqrt h_α_Hodge_plus_two_nonneg]
    norm_num
  have h_rhs_nonneg : 0 ≤ Real.sqrt (α_Hodge + 2) / 2 := by
    have : 0 ≤ Real.sqrt (α_Hodge + 2) := Real.sqrt_nonneg _
    linarith
  nlinarith [h_squared,
             sq_nonneg (Real.cos (Real.pi / 10) - Real.sqrt (α_Hodge + 2) / 2),
             sq_nonneg (Real.cos (Real.pi / 10) + Real.sqrt (α_Hodge + 2) / 2),
             h_pos, h_rhs_nonneg]

/-! ## §4 — Bundle capstone -/

/-- **★★★ THE PENTAGONAL COS BUNDLE CAPSTONE ★★★** —
    closed forms for cos(π/10) in framework form via α_Hodge,
    paired with the existing sin(π/10) = 1/(2·α_Hodge). -/
theorem α_pentagonal_cos_bundle_capstone :
    Real.cos (Real.pi / 10) ^ 2 = (α_Hodge + 2) / 4 ∧
    Real.cos (Real.pi / 10) = Real.sqrt (α_Hodge + 2) / 2 :=
  ⟨cos_sq_pi_div_ten_eq,
   cos_pi_div_ten_eq_sqrt_α_Hodge_plus_two_div_two⟩

end AlphaPentagonalCosBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaPentagonalCosBundle.cos_sq_pi_div_ten_eq
#print axioms PrincipiaTractalis.AlphaPentagonalCosBundle.cos_pi_div_ten_eq_sqrt_α_Hodge_plus_two_div_two
#print axioms PrincipiaTractalis.AlphaPentagonalCosBundle.α_pentagonal_cos_bundle_capstone
