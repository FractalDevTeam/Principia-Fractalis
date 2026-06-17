/-
# PF.AlphaHodgeHyperbolicLadderRanks6And7

★ 2026-06-17 — Extend the α_Hodge hyperbolic ladder to ranks 6 and 7,
confirming the Lucas/Fibonacci pattern continues.

## Closed forms

  cosh(6·log α_Hodge) = 9          (= L_6/2)
  sinh(6·log α_Hodge) = 4·√5       (= F_6·√5/2)
  cosh(7·log α_Hodge) = 13·√5/2    (= F_7·√5/2)
  sinh(7·log α_Hodge) = 29/2       (= L_7/2)

## Derivation pattern (uniform)

  α_Hodge^6 = 8·α_Hodge + 5      (Fibonacci F_6=8, F_5=5)
  α_Hodge^7 = 13·α_Hodge + 8     (Fibonacci F_7=13, F_6=8)
  1/α_Hodge^6 = 13 − 8·α_Hodge
  1/α_Hodge^7 = 13·α_Hodge − 21

Then cosh/sinh = (α_Hodge^n ± 1/α_Hodge^n)/2 collapses to the
Lucas-or-Fibonacci form.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaHodgeHyperbolicLadderRanks6And7

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants

/-! ## §1 — Auxiliaries -/

private lemma α_Hodge_pos_local : 0 < α_Hodge := by
  unfold α_Hodge phi
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  linarith

private lemma inv_α_Hodge_sixth : 1 / α_Hodge ^ 6 = 13 - 8 * α_Hodge := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_pow_pos : 0 < α_Hodge ^ 6 := pow_pos h_pos 6
  have h_sixth : α_Hodge ^ 6 = 8 * α_Hodge + 5 := α_Hodge_sixth
  have h_seventh : α_Hodge ^ 7 = 13 * α_Hodge + 8 := α_Hodge_seventh
  -- (13 − 8·α_Hodge) · α_Hodge^6 = 13·α_Hodge^6 − 8·α_Hodge^7
  --                              = 13·(8·α_Hodge + 5) − 8·(13·α_Hodge + 8)
  --                              = 104·α_Hodge + 65 − 104·α_Hodge − 64 = 1
  have h_prod : (13 - 8 * α_Hodge) * α_Hodge ^ 6 = 1 := by
    have h_step : (13 - 8 * α_Hodge) * α_Hodge ^ 6
                = 13 * α_Hodge ^ 6 - 8 * α_Hodge ^ 7 := by ring
    rw [h_step, h_sixth, h_seventh]; ring
  field_simp
  linarith [h_prod]

private lemma inv_α_Hodge_seventh : 1 / α_Hodge ^ 7 = 13 * α_Hodge - 21 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_pow_pos : 0 < α_Hodge ^ 7 := pow_pos h_pos 7
  have h_seventh : α_Hodge ^ 7 = 13 * α_Hodge + 8 := α_Hodge_seventh
  have h_eighth : α_Hodge ^ 8 = 21 * α_Hodge + 13 := α_Hodge_eighth
  have h_prod : (13 * α_Hodge - 21) * α_Hodge ^ 7 = 1 := by
    have h_step : (13 * α_Hodge - 21) * α_Hodge ^ 7
                = 13 * α_Hodge ^ 8 - 21 * α_Hodge ^ 7 := by ring
    rw [h_step, h_eighth, h_seventh]; ring
  field_simp
  linarith [h_prod]

/-! ## §2 — Rank 6 -/

/-- **`cosh(6·log α_Hodge) = 9`** — Lucas ladder rank 6 (L_6 = 18). -/
theorem cosh_six_log_α_Hodge_eq_nine :
    Real.cosh (6 * Real.log α_Hodge) = 9 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_log_eq : 6 * Real.log α_Hodge = Real.log (α_Hodge ^ 6) := by
    rw [Real.log_pow]; ring
  rw [h_log_eq]
  have h_pow_pos : 0 < α_Hodge ^ 6 := pow_pos h_pos 6
  rw [Real.cosh_log h_pow_pos]
  rw [show ((α_Hodge ^ 6)⁻¹ : ℝ) = 1 / α_Hodge ^ 6 from (one_div _).symm]
  rw [inv_α_Hodge_sixth, α_Hodge_sixth]
  ring

/-- **`sinh(6·log α_Hodge) = 4·√5`** — Fibonacci ladder rank 6 (F_6 = 8). -/
theorem sinh_six_log_α_Hodge_eq_four_sqrt_five :
    Real.sinh (6 * Real.log α_Hodge) = 4 * Real.sqrt 5 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_log_eq : 6 * Real.log α_Hodge = Real.log (α_Hodge ^ 6) := by
    rw [Real.log_pow]; ring
  rw [h_log_eq]
  have h_pow_pos : 0 < α_Hodge ^ 6 := pow_pos h_pos 6
  rw [Real.sinh_log h_pow_pos]
  rw [show ((α_Hodge ^ 6)⁻¹ : ℝ) = 1 / α_Hodge ^ 6 from (one_div _).symm]
  rw [inv_α_Hodge_sixth, α_Hodge_sixth]
  unfold α_Hodge phi
  ring

/-! ## §3 — Rank 7 -/

/-- **`cosh(7·log α_Hodge) = 13·√5/2`** — Fibonacci ladder rank 7 (F_7 = 13). -/
theorem cosh_seven_log_α_Hodge_eq_thirteen_sqrt_five_halves :
    Real.cosh (7 * Real.log α_Hodge) = 13 * Real.sqrt 5 / 2 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_log_eq : 7 * Real.log α_Hodge = Real.log (α_Hodge ^ 7) := by
    rw [Real.log_pow]; ring
  rw [h_log_eq]
  have h_pow_pos : 0 < α_Hodge ^ 7 := pow_pos h_pos 7
  rw [Real.cosh_log h_pow_pos]
  rw [show ((α_Hodge ^ 7)⁻¹ : ℝ) = 1 / α_Hodge ^ 7 from (one_div _).symm]
  rw [inv_α_Hodge_seventh, α_Hodge_seventh]
  unfold α_Hodge phi
  ring

/-- **`sinh(7·log α_Hodge) = 29/2`** — Lucas ladder rank 7 (L_7 = 29). -/
theorem sinh_seven_log_α_Hodge_eq_twenty_nine_halves :
    Real.sinh (7 * Real.log α_Hodge) = 29/2 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_log_eq : 7 * Real.log α_Hodge = Real.log (α_Hodge ^ 7) := by
    rw [Real.log_pow]; ring
  rw [h_log_eq]
  have h_pow_pos : 0 < α_Hodge ^ 7 := pow_pos h_pos 7
  rw [Real.sinh_log h_pow_pos]
  rw [show ((α_Hodge ^ 7)⁻¹ : ℝ) = 1 / α_Hodge ^ 7 from (one_div _).symm]
  rw [inv_α_Hodge_seventh, α_Hodge_seventh]
  ring

/-! ## §4 — Rank 6-7 capstone -/

/-- **★★★ α_Hodge hyperbolic ladder ranks 6 and 7 ★★★** — four
    closed forms extending the ladder, two Lucas (rational) and
    two Fibonacci (irrational, ·√5/2). -/
theorem α_Hodge_hyperbolic_ladder_ranks_6_7_capstone :
    Real.cosh (6 * Real.log α_Hodge) = 9 ∧
    Real.sinh (6 * Real.log α_Hodge) = 4 * Real.sqrt 5 ∧
    Real.cosh (7 * Real.log α_Hodge) = 13 * Real.sqrt 5 / 2 ∧
    Real.sinh (7 * Real.log α_Hodge) = 29/2 :=
  ⟨cosh_six_log_α_Hodge_eq_nine,
   sinh_six_log_α_Hodge_eq_four_sqrt_five,
   cosh_seven_log_α_Hodge_eq_thirteen_sqrt_five_halves,
   sinh_seven_log_α_Hodge_eq_twenty_nine_halves⟩

end AlphaHodgeHyperbolicLadderRanks6And7
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.AlphaHodgeHyperbolicLadderRanks6And7.cosh_six_log_α_Hodge_eq_nine
#print axioms
  PrincipiaTractalis.AlphaHodgeHyperbolicLadderRanks6And7.sinh_six_log_α_Hodge_eq_four_sqrt_five
#print axioms
  PrincipiaTractalis.AlphaHodgeHyperbolicLadderRanks6And7.cosh_seven_log_α_Hodge_eq_thirteen_sqrt_five_halves
#print axioms
  PrincipiaTractalis.AlphaHodgeHyperbolicLadderRanks6And7.sinh_seven_log_α_Hodge_eq_twenty_nine_halves
#print axioms
  PrincipiaTractalis.AlphaHodgeHyperbolicLadderRanks6And7.α_Hodge_hyperbolic_ladder_ranks_6_7_capstone
