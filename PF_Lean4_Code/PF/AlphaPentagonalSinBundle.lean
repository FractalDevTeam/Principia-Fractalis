/-
# PF.AlphaPentagonalSinBundle

★★★ 2026-06-17 — FUN: sin(π/5) in framework form via α_Hodge.

## Pentagonal sin

  sin(π/5) = √(3 − α_Hodge) / 2

The framework's golden axis appears in the pentagonal sin under the
square root.

## Derivation

  sin²(π/5) = 1 − cos²(π/5) = 1 − (α_Hodge/2)²
            = 1 − α_Hodge²/4
            = 1 − (α_Hodge + 1)/4         [α_Hodge² = α_Hodge + 1]
            = (4 − α_Hodge − 1)/4
            = (3 − α_Hodge)/4.

So sin(π/5) = √(3 − α_Hodge)/2 (positive branch since π/5 ∈ (0, π)).

## Pentagonal circumradius

For a regular pentagon with side 1, the circumradius is `1/(2·sin(π/5))`
= `1/√(3 − α_Hodge)` in framework form.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaPentagonalSinBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants

/-! ## §1 — sin²(π/5) = (3 − α_Hodge) / 4 -/

/-- **`sin²(π/5) = (3 − α_Hodge) / 4`** — squared form. -/
theorem sin_sq_pi_div_five_eq :
    Real.sin (Real.pi / 5) ^ 2 = (3 - α_Hodge) / 4 := by
  have h_pyth : Real.sin (Real.pi / 5) ^ 2 + Real.cos (Real.pi / 5) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (Real.pi / 5)
  rw [cos_pi_div_five_eq_α_Hodge_div_two] at h_pyth
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  nlinarith [h_pyth, h_sq]

/-! ## §2 — sin(π/5) positivity -/

private lemma sin_pi_div_five_pos : 0 < Real.sin (Real.pi / 5) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · have h_pi_pos : 0 < Real.pi := Real.pi_pos
    positivity
  · have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h : Real.pi / 5 < Real.pi := by linarith
    exact h

/-! ## §3 — sin(π/5) = √(3 − α_Hodge) / 2 -/

/-- **★★★ `sin(π/5) = √(3 − α_Hodge) / 2` ★★★** — pentagonal sin in
    framework form. -/
theorem sin_pi_div_five_eq_sqrt_three_sub_α_Hodge_div_two :
    Real.sin (Real.pi / 5) = Real.sqrt (3 - α_Hodge) / 2 := by
  have h_sq : Real.sin (Real.pi / 5) ^ 2 = (3 - α_Hodge) / 4 :=
    sin_sq_pi_div_five_eq
  have h_pos : 0 < Real.sin (Real.pi / 5) := sin_pi_div_five_pos
  have h_three_minus_α_Hodge_pos : 0 ≤ 3 - α_Hodge := by
    have h_α_Hodge_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
    -- α_Hodge < 2 since α_Hodge² = α_Hodge + 1 < 4 if α_Hodge < 2
    -- α_Hodge = (1+√5)/2, √5 < 3, so α_Hodge < 2
    unfold α_Hodge phi
    have h_sqrt5_lt : Real.sqrt 5 < 3 := by
      have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 :=
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
        Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
      nlinarith [h_sqrt5_sq, h_sqrt5_pos]
    linarith
  -- Take square root
  have h_squared : (Real.sin (Real.pi / 5)) ^ 2 =
                   (Real.sqrt (3 - α_Hodge) / 2) ^ 2 := by
    rw [h_sq]
    rw [div_pow]
    rw [Real.sq_sqrt h_three_minus_α_Hodge_pos]
    norm_num
  have h_rhs_nonneg : 0 ≤ Real.sqrt (3 - α_Hodge) / 2 := by
    have : 0 ≤ Real.sqrt (3 - α_Hodge) := Real.sqrt_nonneg _
    linarith
  -- Both sides positive, squares equal → equal
  nlinarith [h_squared, sq_nonneg (Real.sin (Real.pi / 5) - Real.sqrt (3 - α_Hodge) / 2),
             sq_nonneg (Real.sin (Real.pi / 5) + Real.sqrt (3 - α_Hodge) / 2),
             h_pos, h_rhs_nonneg]

/-! ## §4 — Bundle capstone -/

/-- **★★★ THE PENTAGONAL SIN BUNDLE CAPSTONE ★★★** —
    sin(π/5) closed forms in framework form via α_Hodge. -/
theorem α_pentagonal_sin_bundle_capstone :
    Real.sin (Real.pi / 5) ^ 2 = (3 - α_Hodge) / 4 ∧
    Real.sin (Real.pi / 5) = Real.sqrt (3 - α_Hodge) / 2 :=
  ⟨sin_sq_pi_div_five_eq,
   sin_pi_div_five_eq_sqrt_three_sub_α_Hodge_div_two⟩

end AlphaPentagonalSinBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaPentagonalSinBundle.sin_sq_pi_div_five_eq
#print axioms PrincipiaTractalis.AlphaPentagonalSinBundle.sin_pi_div_five_eq_sqrt_three_sub_α_Hodge_div_two
#print axioms PrincipiaTractalis.AlphaPentagonalSinBundle.α_pentagonal_sin_bundle_capstone
