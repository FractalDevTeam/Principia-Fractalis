/-
# PF.AlphaDifferenceOfSquaresBundle

★ 2026-06-17 — Five clean difference-of-squares identities between the
algebraic and rational α-axes, all closing inside ℚ + ℚ·α_Hodge or ℚ.

## Identities

  α_Hodge² − α_P²  = α_Hodge − 1
  α_NP²    − α_Hodge² = (1/2)·α_Hodge + 1/16
  α_NP²    − α_P²     = (3/2)·α_Hodge − 15/16
  α_NP²    − α_RH²    = (3/2)·α_Hodge − 19/16
  α_NP²    − α_YM²    = (3/2)·α_Hodge − 47/16

Each follows from the closed-form squares
α_Hodge² = α_Hodge + 1, α_P² = 2, α_NP² = (3/2)·α_Hodge + 17/16,
α_RH² = 9/4, α_YM² = 4.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaDifferenceOfSquaresBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants

/-! ## §1 — Difference-of-squares identities -/

/-- **`α_Hodge² − α_P² = α_Hodge − 1`** — algebraic difference inside
    ℚ + ℚ·α_Hodge. -/
theorem α_Hodge_sq_sub_α_P_sq : α_Hodge ^ 2 - α_P ^ 2 = α_Hodge - 1 := by
  rw [α_Hodge_sq_eq_self_plus_one]
  have h_P_sq : α_P ^ 2 = 2 := by
    rw [α_P_sq_eq_α_YM]; unfold α_YM; norm_num
  rw [h_P_sq]
  ring

/-- **`α_NP² − α_Hodge² = (1/2)·α_Hodge + 1/16`**. -/
theorem α_NP_sq_sub_α_Hodge_sq :
    α_NP ^ 2 - α_Hodge ^ 2 = (1/2) * α_Hodge + 1/16 := by
  rw [α_NP_sq, α_Hodge_sq_eq_self_plus_one]
  ring

/-- **`α_NP² − α_P² = (3/2)·α_Hodge − 15/16`**. -/
theorem α_NP_sq_sub_α_P_sq :
    α_NP ^ 2 - α_P ^ 2 = (3/2) * α_Hodge - 15/16 := by
  rw [α_NP_sq]
  have h_P_sq : α_P ^ 2 = 2 := by
    rw [α_P_sq_eq_α_YM]; unfold α_YM; norm_num
  rw [h_P_sq]
  ring

/-- **`α_NP² − α_RH² = (3/2)·α_Hodge − 19/16`**. -/
theorem α_NP_sq_sub_α_RH_sq :
    α_NP ^ 2 - α_RH ^ 2 = (3/2) * α_Hodge - 19/16 := by
  rw [α_NP_sq, α_RH_sq_eq_nine_fourths]
  ring

/-- **`α_NP² − α_YM² = (3/2)·α_Hodge − 47/16`**. -/
theorem α_NP_sq_sub_α_YM_sq :
    α_NP ^ 2 - α_YM ^ 2 = (3/2) * α_Hodge - 47/16 := by
  rw [α_NP_sq]
  have h_YM_sq : α_YM ^ 2 = 4 := by unfold α_YM; norm_num
  rw [h_YM_sq]
  ring

/-! ## §2 — Bundle capstone -/

/-- **★ α-axis difference-of-squares bundle ★** — five clean closed
    forms inside ℚ + ℚ·α_Hodge for the squared differences between
    the algebraic and rational Clay axes. -/
theorem α_difference_of_squares_bundle_capstone :
    α_Hodge ^ 2 - α_P ^ 2 = α_Hodge - 1 ∧
    α_NP ^ 2 - α_Hodge ^ 2 = (1/2) * α_Hodge + 1/16 ∧
    α_NP ^ 2 - α_P ^ 2 = (3/2) * α_Hodge - 15/16 ∧
    α_NP ^ 2 - α_RH ^ 2 = (3/2) * α_Hodge - 19/16 ∧
    α_NP ^ 2 - α_YM ^ 2 = (3/2) * α_Hodge - 47/16 :=
  ⟨α_Hodge_sq_sub_α_P_sq,
   α_NP_sq_sub_α_Hodge_sq,
   α_NP_sq_sub_α_P_sq,
   α_NP_sq_sub_α_RH_sq,
   α_NP_sq_sub_α_YM_sq⟩

end AlphaDifferenceOfSquaresBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaDifferenceOfSquaresBundle.α_Hodge_sq_sub_α_P_sq
#print axioms PrincipiaTractalis.AlphaDifferenceOfSquaresBundle.α_NP_sq_sub_α_Hodge_sq
#print axioms PrincipiaTractalis.AlphaDifferenceOfSquaresBundle.α_NP_sq_sub_α_P_sq
#print axioms PrincipiaTractalis.AlphaDifferenceOfSquaresBundle.α_NP_sq_sub_α_RH_sq
#print axioms PrincipiaTractalis.AlphaDifferenceOfSquaresBundle.α_NP_sq_sub_α_YM_sq
#print axioms
  PrincipiaTractalis.AlphaDifferenceOfSquaresBundle.α_difference_of_squares_bundle_capstone
