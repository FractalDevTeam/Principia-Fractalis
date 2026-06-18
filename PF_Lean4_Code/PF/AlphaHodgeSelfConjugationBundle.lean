/-
# PF.AlphaHodgeSelfConjugationBundle

★★★ 2026-06-17 — FUN: golden self-conjugation identities under
x ↔ 1/x. Beautiful clean closed forms.

## Identities

  α_Hodge + 1/α_Hodge   = √5
  α_Hodge − 1/α_Hodge   = α_Poincaré        (= 1)
  α_Hodge² + 1/α_Hodge² = 3
  α_Hodge² − 1/α_Hodge² = √5
  α_Hodge³ + 1/α_Hodge³ = 2·√5
  α_Hodge³ − 1/α_Hodge³ = 2·α_YM (= 4)

Symmetric / antisymmetric combinations of α_Hodge^k and 1/α_Hodge^k
collapse to rationals or rational multiples of √5 via the golden
substrate equation.

The framework's α_Poincaré (= 1) appears as `α_Hodge − 1/α_Hodge`,
and α_YM·2 (= 4) appears as `α_Hodge³ + 1/α_Hodge³`.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaHodgeSelfConjugationBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants

/-! ## §1 — Auxiliary positivity -/

private lemma α_Hodge_pos : 0 < α_Hodge := by
  unfold α_Hodge phi
  have : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  linarith

private lemma α_Hodge_ne_zero : α_Hodge ≠ 0 := ne_of_gt α_Hodge_pos

/-! ## §2 — Rank-1 self-conjugation -/

/-- **`α_Hodge + 1/α_Hodge = √5`** — clean closed form. -/
theorem α_Hodge_add_inv_α_Hodge_eq_sqrt_five :
    α_Hodge + 1 / α_Hodge = Real.sqrt 5 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  unfold α_Hodge phi
  have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  field_simp
  nlinarith [h_sqrt5_sq, h_sqrt5_pos]

/-- **`α_Hodge − 1/α_Hodge = α_Poincaré`** — the framework's Perelman
    anchor emerges as the antisymmetric self-conjugation. -/
theorem α_Hodge_sub_inv_α_Hodge_eq_α_Poincare :
    α_Hodge - 1 / α_Hodge = α_Poincare := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  unfold α_Poincare
  field_simp
  nlinarith [h_sq, h_pos]

/-! ## §3 — Rank-2 self-conjugation -/

/-- **`α_Hodge² + 1/α_Hodge² = 3`** — clean rational closed form. -/
theorem α_Hodge_sq_add_inv_α_Hodge_sq_eq_three :
    α_Hodge ^ 2 + 1 / α_Hodge ^ 2 = 3 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  have h_pow_pos : 0 < α_Hodge ^ 2 := pow_pos h_pos 2
  field_simp
  nlinarith [h_sq, h_pos]

/-- **`α_Hodge² − 1/α_Hodge² = √5`** — the SAME √5 as
    α_Hodge + 1/α_Hodge. Beautiful self-conjugation symmetry. -/
theorem α_Hodge_sq_sub_inv_α_Hodge_sq_eq_sqrt_five :
    α_Hodge ^ 2 - 1 / α_Hodge ^ 2 = Real.sqrt 5 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  have h_pow_pos : 0 < α_Hodge ^ 2 := pow_pos h_pos 2
  unfold α_Hodge phi
  have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  field_simp
  nlinarith [h_sqrt5_sq, h_sqrt5_pos]

/-! ## §4 — Rank-3 self-conjugation -/

/-- **`α_Hodge³ + 1/α_Hodge³ = 2·√5`** — symmetric rank-3 is
    Fibonacci-irrational (cosh-side, F_3 = 2 with √5). -/
theorem α_Hodge_cubed_add_inv_α_Hodge_cubed_eq_two_sqrt_five :
    α_Hodge ^ 3 + 1 / α_Hodge ^ 3 = 2 * Real.sqrt 5 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos
  have h_cubed : α_Hodge ^ 3 = 2 * α_Hodge + 1 := α_Hodge_cubed
  -- Prove inv via product = 1
  have h_inv_cubed : 1 / α_Hodge ^ 3 = 2 * α_Hodge - 3 := by
    have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
    have h_fourth : α_Hodge ^ 4 = 3 * α_Hodge + 2 := α_Hodge_fourth
    have h_prod : (2 * α_Hodge - 3) * α_Hodge ^ 3 = 1 := by
      have h_step : (2 * α_Hodge - 3) * α_Hodge ^ 3 = 2 * α_Hodge ^ 4 - 3 * α_Hodge ^ 3 := by ring
      rw [h_step, h_fourth, h_cubed]; ring
    have h_pow_pos : 0 < α_Hodge ^ 3 := pow_pos h_pos 3
    field_simp
    linarith [h_prod]
  rw [h_inv_cubed, h_cubed]
  -- Goal: (2·α_Hodge + 1) + (2·α_Hodge - 3) = 2·√5
  -- = 4·α_Hodge - 2 = 2·(2·α_Hodge - 1) = 2·√5 (via 2α_Hodge - 1 = √5)
  unfold α_Hodge phi
  have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  ring

/-- **`α_Hodge³ − 1/α_Hodge³ = 2·α_YM`** — antisymmetric rank-3 is
    Lucas-rational (sinh-side, L_3 = 4 = 2·α_YM). -/
theorem α_Hodge_cubed_sub_inv_α_Hodge_cubed_eq_two_α_YM :
    α_Hodge ^ 3 - 1 / α_Hodge ^ 3 = 2 * α_YM := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos
  have h_cubed : α_Hodge ^ 3 = 2 * α_Hodge + 1 := α_Hodge_cubed
  have h_inv_cubed : 1 / α_Hodge ^ 3 = 2 * α_Hodge - 3 := by
    have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
    have h_fourth : α_Hodge ^ 4 = 3 * α_Hodge + 2 := α_Hodge_fourth
    have h_prod : (2 * α_Hodge - 3) * α_Hodge ^ 3 = 1 := by
      have h_step : (2 * α_Hodge - 3) * α_Hodge ^ 3 = 2 * α_Hodge ^ 4 - 3 * α_Hodge ^ 3 := by ring
      rw [h_step, h_fourth, h_cubed]; ring
    have h_pow_pos : 0 < α_Hodge ^ 3 := pow_pos h_pos 3
    field_simp
    linarith [h_prod]
  rw [h_inv_cubed, h_cubed]
  unfold α_YM
  ring

/-! ## §5 — Bundle capstone -/

/-- **★★★★ THE GOLDEN SELF-CONJUGATION BUNDLE ★★★★** —
    six clean closed forms for α_Hodge^k ± 1/α_Hodge^k at k = 1, 2, 3.
    The Lucas-rational identities give α_Poincaré (= 1) and 2·α_YM
    (= 4); the Fibonacci-irrational identities give √5 and 2·√5.

    Pattern:
      Symmetric:    α_Hodge^k + 1/α_Hodge^k = L_k/(common pattern)
      Antisymmetric: α_Hodge^k − 1/α_Hodge^k = F_k·√5/(common pattern)

    At rank 1: + = √5, − = 1   (L_1=1, F_1=1)
    At rank 2: + = 3, − = √5    (L_2=3, F_2=1)
    At rank 3: + = 4, − = 2√5   (L_3=4, F_3=2) -/
theorem α_Hodge_self_conjugation_bundle_capstone :
    α_Hodge + 1 / α_Hodge = Real.sqrt 5 ∧
    α_Hodge - 1 / α_Hodge = α_Poincare ∧
    α_Hodge ^ 2 + 1 / α_Hodge ^ 2 = 3 ∧
    α_Hodge ^ 2 - 1 / α_Hodge ^ 2 = Real.sqrt 5 ∧
    α_Hodge ^ 3 + 1 / α_Hodge ^ 3 = 2 * Real.sqrt 5 ∧
    α_Hodge ^ 3 - 1 / α_Hodge ^ 3 = 2 * α_YM :=
  ⟨α_Hodge_add_inv_α_Hodge_eq_sqrt_five,
   α_Hodge_sub_inv_α_Hodge_eq_α_Poincare,
   α_Hodge_sq_add_inv_α_Hodge_sq_eq_three,
   α_Hodge_sq_sub_inv_α_Hodge_sq_eq_sqrt_five,
   α_Hodge_cubed_add_inv_α_Hodge_cubed_eq_two_sqrt_five,
   α_Hodge_cubed_sub_inv_α_Hodge_cubed_eq_two_α_YM⟩

end AlphaHodgeSelfConjugationBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaHodgeSelfConjugationBundle.α_Hodge_add_inv_α_Hodge_eq_sqrt_five
#print axioms PrincipiaTractalis.AlphaHodgeSelfConjugationBundle.α_Hodge_sub_inv_α_Hodge_eq_α_Poincare
#print axioms PrincipiaTractalis.AlphaHodgeSelfConjugationBundle.α_Hodge_sq_add_inv_α_Hodge_sq_eq_three
#print axioms PrincipiaTractalis.AlphaHodgeSelfConjugationBundle.α_Hodge_cubed_add_inv_α_Hodge_cubed_eq_two_sqrt_five
#print axioms PrincipiaTractalis.AlphaHodgeSelfConjugationBundle.α_Hodge_cubed_sub_inv_α_Hodge_cubed_eq_two_α_YM
#print axioms
  PrincipiaTractalis.AlphaHodgeSelfConjugationBundle.α_Hodge_self_conjugation_bundle_capstone
