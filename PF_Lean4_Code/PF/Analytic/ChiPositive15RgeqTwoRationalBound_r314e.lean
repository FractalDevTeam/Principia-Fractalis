/-
# r314e: Rationalize `exp(-4π) < 1/234256` via Taylor `exp(π) > 22`
#       → `|R_geq_2| < 1/10^6` explicit rational bound

★ 2026-08-22 r314e — rationalization of r314d's symbolic bound
`|R_geq_2| ≤ exp(-4π)/(2π·(1-exp(-4π)))` into a fully rational bound
`|R_geq_2| < 1/10^6`, directly consumable by r313's chain-closer.

## Route

- `Real.pi_gt_d2 : 3.14 < π` (mathlib).
- `exp(π) > exp(3.14)` via `Real.exp_lt_exp.mpr`.
- `exp(3.14) ≥ ∑ k ∈ range 8, (3.14)^k / k!` via `Real.sum_le_exp_of_nonneg`.
- Compute Taylor sum through k = 7: `∑ = 22.7449...` > 22.
- Hence `exp(π) > 22`.
- `exp(4·π) = exp(π)^4 > 22^4 = 234256` via `Real.exp_nat_mul` + `pow_lt_pow_left`.
- `exp(-4·π) = 1/exp(4·π) < 1/234256` via `Real.exp_neg`.
- Chain via r314d: `|R_geq_2| ≤ exp(-4π)/(2π·(1-exp(-4π))) < (1/234256)/(2π·(1-1/234256))`.
  Numerically: `(1/234256)/(2π·(1 - 1/234256)) ≈ 4.269e-6/(6.283 · 0.99999573) ≈ 6.79e-7 < 10^(-6)` ✓.

## Framework-first status (per MASTER DIRECTIVE)

Concludes the r314-series certified remainder theorem. Delivers the rational
bound needed by r313's Xi_Positive_At_15_from_J_1_and_R_geq_2_bounds bridge.

Standing rules absolute: no `sorry`, no `native_decide`, no floating-point-as-proof,
no hidden oracle, no assumed transcendental enclosure. Every ingredient is a
mathlib primitive.

## What r314e delivers

- `exp_314_ge_taylor_sum` : `exp(3.14) ≥ ∑ k ∈ range 8, (3.14)^k / k!`.
- `taylor_sum_gt_twenty_two` : `(∑ k ∈ range 8, (3.14)^k / k!) > 22` (norm_num).
- `exp_pi_gt_twenty_two` : `exp(π) > 22`.
- `exp_four_pi_gt_234256` : `exp(4π) > 234256`.
- `exp_neg_four_pi_lt_reciprocal` : `exp(-4π) < 1/234256`.
- `abs_R_geq_2_lt_one_millionth` : `|R_geq_2| < 1/10^6`. **THE r314e CORE**.

## r315 direction

Certified `J_1 > L` via `t = log y` substitution transforming to
`2·∫_0^∞ exp(-π·e^t) · e^(t/4) · cos((15/2) t) dt`. Rational cutoff `T`,
rigorous exp/cos Taylor bounds on `[0, T]`, tail bound on `[T, ∞)`,
sum to certified rational `L` with `4/901 + 10^(-6) < L`.

## r316 direction

Apply r313's `Xi_Positive_At_15_from_J_1_and_R_geq_2_bounds` with r315's `L`
and r314e's `E = 1/10^6`. Requires `4/901 < L - 1/10^6` provable. Only then
does `Xi_Positive_At_15` become DISCHARGED.

Book anchors: Ch 20 § 20.4, Ch 34A § 34A.5.
-/

import PF.Analytic.ChiPositive15RgeqTwoSymbolicBound_r314d
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential

namespace PrincipiaTractalis.ChiPositive15RgeqTwoRationalBound

open Real
open PrincipiaTractalis.ChiPositive15ThetaTruncation
open PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm
open PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound

/-! ## §1 Taylor lower bound for `exp(3.14)`. -/

/-- **`exp_314_ge_taylor_sum`** — `exp(3.14) ≥ ∑ k ∈ Finset.range 8, (3.14)^k / k!`. -/
theorem exp_314_ge_taylor_sum :
    (∑ k ∈ Finset.range 8, (3.14 : ℝ)^k / k.factorial) ≤ Real.exp 3.14 :=
  Real.sum_le_exp_of_nonneg (by norm_num) 8

/-- **`taylor_sum_gt_twenty_two`** — the Taylor sum through k = 7 evaluates
above 22 for x = 3.14: `∑ k ∈ range 8, (3.14)^k / k! > 22`.

Explicit rational arithmetic:
- k=0: 1
- k=1: 3.14
- k=2: (3.14)²/2 = 9.8596/2 = 4.9298
- k=3: (3.14)³/6 = 30.959144/6 = 5.15985733...
- k=4: (3.14)⁴/24 = 97.211712/24 = 4.05048800
- k=5: (3.14)⁵/120 = 305.244775/120 = 2.54370645...
- k=6: (3.14)⁶/720 = 958.469...
- k=7: (3.14)⁷/5040 = ...
Sum > 22.7 > 22.

Proof by `norm_num`. -/
theorem taylor_sum_gt_twenty_two :
    (22 : ℝ) < ∑ k ∈ Finset.range 8, (3.14 : ℝ)^k / k.factorial := by
  simp [Finset.sum_range_succ, Nat.factorial]
  norm_num

/-! ## §2 `exp(π) > 22`. -/

/-- **`exp_pi_gt_twenty_two`** — `exp(π) > 22`. -/
theorem exp_pi_gt_twenty_two : (22 : ℝ) < Real.exp Real.pi := by
  have h_pi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h_exp_mono : Real.exp 3.14 ≤ Real.exp Real.pi := Real.exp_le_exp.mpr h_pi_gt.le
  have h_taylor : (22 : ℝ) < Real.exp 3.14 :=
    lt_of_lt_of_le taylor_sum_gt_twenty_two exp_314_ge_taylor_sum
  linarith

/-! ## §3 `exp(4π) > 234256`. -/

/-- **`exp_four_pi_gt_234256`** — `exp(4·π) > 234256` (where `22^4 = 234256`). -/
theorem exp_four_pi_gt_234256 : (234256 : ℝ) < Real.exp (4 * Real.pi) := by
  have h_exp_pow : Real.exp (4 * Real.pi) = Real.exp Real.pi ^ 4 := by
    rw [show (4 : ℝ) * Real.pi = ((4 : ℕ) : ℝ) * Real.pi from by norm_num,
        Real.exp_nat_mul]
  rw [h_exp_pow]
  have h_pow : (22 : ℝ)^4 < Real.exp Real.pi ^ 4 := by
    apply pow_lt_pow_left₀ exp_pi_gt_twenty_two (by norm_num) (by norm_num)
  have h_calc : (22 : ℝ)^4 = 234256 := by norm_num
  linarith

/-! ## §4 `exp(-4π) < 1/234256`. -/

/-- **`exp_neg_four_pi_lt_reciprocal`** — `exp(-(4·π)) < 1/234256`. -/
theorem exp_neg_four_pi_lt_reciprocal :
    Real.exp (-(4 * Real.pi)) < 1 / 234256 := by
  rw [Real.exp_neg]
  rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 234256)]
  have : (1 / 234256 : ℝ)⁻¹ = 234256 := by norm_num
  rw [this]
  exact exp_four_pi_gt_234256

/-! ## §5 Numerical chain: bound the RHS of r314d's inequality. -/

/-- **`symbolic_bound_lt_one_millionth`** —

  `exp(-(4·π)) / (2π · (1 - exp(-(4·π)))) < 1/10^6`.

Route: `exp(-4π) < 1/234256`, so numerator `< 1/234256`. Denominator:
`(1 - exp(-4π)) > 1 - 1/234256 = 234255/234256`, and `2π > 2·3.14 = 6.28`.
So denominator `> 6.28 · 234255/234256 > 6.279...`. Then
`bound < (1/234256) / 6.279... = 1/(234256 · 6.279...) < 1/1.47·10^6 < 1/10^6` ✓. -/
theorem symbolic_bound_lt_one_millionth :
    Real.exp (-(4 * Real.pi)) / (2 * Real.pi * (1 - Real.exp (-(4 * Real.pi))))
      < 1 / 10^6 := by
  have h_exp_lt : Real.exp (-(4 * Real.pi)) < 1 / 234256 := exp_neg_four_pi_lt_reciprocal
  have h_exp_nn : 0 ≤ Real.exp (-(4 * Real.pi)) := (Real.exp_pos _).le
  have h_exp_lt_one : Real.exp (-(4 * Real.pi)) < 1 :=
    lt_trans h_exp_lt (by norm_num)
  have h_pi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Denominator: 2π · (1 - exp(-4π))
  -- Lower bound: 2 · 3.14 · (1 - 1/234256) = 6.28 · (234255/234256)
  have h_one_sub_gt : 1 - Real.exp (-(4 * Real.pi)) > 1 - 1/234256 := by linarith
  have h_one_sub_pos : 0 < 1 - Real.exp (-(4 * Real.pi)) := by linarith
  have h_two_pi_gt : (2 : ℝ) * Real.pi > 2 * 3.14 := by linarith
  have h_two_pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have h_denom_pos : (0 : ℝ) < 2 * Real.pi * (1 - Real.exp (-(4 * Real.pi))) :=
    mul_pos h_two_pi_pos h_one_sub_pos
  -- Bound: exp(-4π) / denom < (1/234256) / (2·3.14 · (1 - 1/234256))
  --      = (1/234256) / (6.28 · (234255/234256))
  --      = 234256 / (234256 · 6.28 · 234255)
  --      = 1 / (6.28 · 234255)
  --      = 1 / 1471121.4
  --      < 1 / 10^6 ✓
  have h_denom_lb : (0 : ℝ) < 2 * 3.14 * (1 - 1/234256) := by norm_num
  have h_denom_gt : 2 * 3.14 * (1 - 1/234256) < 2 * Real.pi * (1 - Real.exp (-(4 * Real.pi))) := by
    apply mul_lt_mul' h_two_pi_gt.le h_one_sub_gt (by norm_num) h_two_pi_pos
  -- Now: exp(-4π)/denom < (1/234256) / (2·3.14 · (1 - 1/234256))
  calc Real.exp (-(4 * Real.pi)) / (2 * Real.pi * (1 - Real.exp (-(4 * Real.pi))))
      ≤ (1 / 234256 : ℝ) / (2 * Real.pi * (1 - Real.exp (-(4 * Real.pi)))) := by
        exact div_le_div_of_nonneg_right h_exp_lt.le h_denom_pos.le |>.trans (le_refl _)
    _ < (1 / 234256 : ℝ) / (2 * 3.14 * (1 - 1/234256)) := by
        apply div_lt_div_of_pos_left (by norm_num) h_denom_lb h_denom_gt
    _ < 1 / 10^6 := by norm_num

/-! ## §6 THE r314e CORE RATIONAL BOUND. -/

/-- **`abs_R_geq_2_lt_one_millionth`** — THE r314e CORE RATIONAL BOUND:

  `|R_geq_2| < 1/10^6`.

Combines r314d's `abs_R_geq_2_le_symbolic_bound` (`|R_geq_2| ≤ exp(-4π)/(2π·(1-exp(-4π)))`)
with §5's `symbolic_bound_lt_one_millionth`. Directly consumable by r313's
`Xi_Positive_At_15_from_J_1_and_R_geq_2_bounds` with `E = 1/10^6`. -/
theorem abs_R_geq_2_lt_one_millionth : |R_geq_2| < 1 / 10^6 :=
  lt_of_le_of_lt abs_R_geq_2_le_symbolic_bound symbolic_bound_lt_one_millionth

/-! ## §7 Axiom checks. -/

#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoRationalBound.exp_314_ge_taylor_sum
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoRationalBound.taylor_sum_gt_twenty_two
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoRationalBound.exp_pi_gt_twenty_two
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoRationalBound.exp_four_pi_gt_234256
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoRationalBound.exp_neg_four_pi_lt_reciprocal
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoRationalBound.symbolic_bound_lt_one_millionth
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoRationalBound.abs_R_geq_2_lt_one_millionth

end PrincipiaTractalis.ChiPositive15RgeqTwoRationalBound
