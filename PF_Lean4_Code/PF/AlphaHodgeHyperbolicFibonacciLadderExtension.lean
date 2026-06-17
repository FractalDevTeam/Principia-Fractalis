/-
# PF.AlphaHodgeHyperbolicFibonacciLadderExtension

★★★★ 2026-06-17 — The Fibonacci half of the α_Hodge hyperbolic ladder.

## The complete α_Hodge hyperbolic ladder pattern

  cosh(2k · log α_Hodge)     = L_{2k} / 2              (rational, Lucas)
  sinh((2k+1) · log α_Hodge) = L_{2k+1} / 2            (rational, Lucas)
  cosh((2k+1) · log α_Hodge) = F_{2k+1} · √5 / 2       (irrational, Fibonacci)
  sinh(2k · log α_Hodge)     = F_{2k} · √5 / 2          (irrational, Fibonacci)

The Lucas half (rational) provides bridges to the rational Clay axes
α_RH = 3/2 = L_2/2 and α_YM = 2 = L_3/2; the Fibonacci half (irrational,
proportional to √5) provides the dual bridges.

## This file's additions (Fibonacci half, ranks 4 and 5)

  sinh(4 · log α_Hodge) = 3·√5 / 2   (= F_4 · √5/2)
  cosh(5 · log α_Hodge) = 5·√5 / 2   (= F_5 · √5/2)

Together with the existing cosh(log α_Hodge) = √5/2 = F_1·√5/2 and
cosh(3·log α_Hodge) = √5 = F_3·√5/2 (the latter proven in
`AlphaHodgeHyperbolicLadderBridges`), the Fibonacci ladder is
established for ranks 1, 3, 4, 5.

## Derivation pattern

For any positive integer n:
  cosh(n · log α_Hodge) = (α_Hodge^n + 1/α_Hodge^n) / 2
  sinh(n · log α_Hodge) = (α_Hodge^n − 1/α_Hodge^n) / 2

Using α_Hodge^n = F_n·α_Hodge + F_{n-1} (Fibonacci closed form), the
sum/difference patterns collapse to Lucas (for even k cosh or odd k sinh)
or Fibonacci·√5/2 (for odd k cosh or even k sinh).

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import PF.AlphaHodgeHyperbolicLadderBridges
import PF.AlphaHodgeHyperbolicLucasLadderExtension

namespace PrincipiaTractalis
namespace AlphaHodgeHyperbolicFibonacciLadderExtension

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants

/-! ## §1 — Auxiliaries -/

private lemma α_Hodge_pos_local : 0 < α_Hodge := by
  unfold α_Hodge phi
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  linarith

private lemma inv_α_Hodge_fourth : 1 / α_Hodge ^ 4 = 5 - 3 * α_Hodge := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  have h_pow_pos : 0 < α_Hodge ^ 4 := pow_pos h_pos 4
  field_simp
  nlinarith [h_sq, h_pos]

private lemma inv_α_Hodge_fifth : 1 / α_Hodge ^ 5 = 5 * α_Hodge - 8 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_pow_pos : 0 < α_Hodge ^ 5 := pow_pos h_pos 5
  have h_fifth : α_Hodge ^ 5 = 5 * α_Hodge + 3 := α_Hodge_fifth
  have h_sixth : α_Hodge ^ 6 = 8 * α_Hodge + 5 := α_Hodge_sixth
  have h_prod : (5 * α_Hodge - 8) * α_Hodge ^ 5 = 1 := by
    have h_six : (5 * α_Hodge - 8) * α_Hodge ^ 5 = 5 * α_Hodge ^ 6 - 8 * α_Hodge ^ 5 := by
      ring
    rw [h_six, h_fifth, h_sixth]; ring
  field_simp
  linarith [h_prod]

/-! ## §2 — sinh(4·log α_Hodge) = 3·√5/2 = F_4·√5/2 -/

/-- **`sinh(4·log α_Hodge) = 3·√5/2`** — Fibonacci ladder rank 4. -/
theorem sinh_four_log_α_Hodge_eq_three_sqrt_five_halves :
    Real.sinh (4 * Real.log α_Hodge) = 3 * Real.sqrt 5 / 2 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_log_eq : 4 * Real.log α_Hodge = Real.log (α_Hodge ^ 4) := by
    rw [Real.log_pow]; ring
  rw [h_log_eq]
  have h_pow_pos : 0 < α_Hodge ^ 4 := pow_pos h_pos 4
  rw [Real.sinh_log h_pow_pos]
  rw [show ((α_Hodge ^ 4)⁻¹ : ℝ) = 1 / α_Hodge ^ 4 from (one_div _).symm]
  rw [inv_α_Hodge_fourth, α_Hodge_fourth]
  -- Goal: ((3·α_Hodge + 2) − (5 − 3·α_Hodge))/2 = 3·√5/2
  -- = (6·α_Hodge − 3)/2 = 3·(2·α_Hodge − 1)/2 = 3·√5/2
  unfold α_Hodge phi
  ring

/-! ## §3 — cosh(5·log α_Hodge) = 5·√5/2 = F_5·√5/2 -/

/-- **`cosh(5·log α_Hodge) = 5·√5/2`** — Fibonacci ladder rank 5. -/
theorem cosh_five_log_α_Hodge_eq_five_sqrt_five_halves :
    Real.cosh (5 * Real.log α_Hodge) = 5 * Real.sqrt 5 / 2 := by
  have h_pos : 0 < α_Hodge := α_Hodge_pos_local
  have h_log_eq : 5 * Real.log α_Hodge = Real.log (α_Hodge ^ 5) := by
    rw [Real.log_pow]; ring
  rw [h_log_eq]
  have h_pow_pos : 0 < α_Hodge ^ 5 := pow_pos h_pos 5
  rw [Real.cosh_log h_pow_pos]
  rw [show ((α_Hodge ^ 5)⁻¹ : ℝ) = 1 / α_Hodge ^ 5 from (one_div _).symm]
  rw [inv_α_Hodge_fifth, α_Hodge_fifth]
  unfold α_Hodge phi
  ring

/-! ## §4 — Fibonacci ladder capstone -/

/-- **★★★ Fibonacci ladder ranks 4, 5 capstone ★★★** — the irrational
    (Fibonacci·√5/2) half of the α_Hodge hyperbolic ladder at ranks 4
    and 5. -/
theorem α_Hodge_hyperbolic_fibonacci_ladder_capstone :
    Real.sinh (4 * Real.log α_Hodge) = 3 * Real.sqrt 5 / 2 ∧
    Real.cosh (5 * Real.log α_Hodge) = 5 * Real.sqrt 5 / 2 :=
  ⟨sinh_four_log_α_Hodge_eq_three_sqrt_five_halves,
   cosh_five_log_α_Hodge_eq_five_sqrt_five_halves⟩

end AlphaHodgeHyperbolicFibonacciLadderExtension
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.AlphaHodgeHyperbolicFibonacciLadderExtension.sinh_four_log_α_Hodge_eq_three_sqrt_five_halves
#print axioms
  PrincipiaTractalis.AlphaHodgeHyperbolicFibonacciLadderExtension.cosh_five_log_α_Hodge_eq_five_sqrt_five_halves
#print axioms
  PrincipiaTractalis.AlphaHodgeHyperbolicFibonacciLadderExtension.α_Hodge_hyperbolic_fibonacci_ladder_capstone
