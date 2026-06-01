/-
# Ch 11 Anomaly Cancellation Refutation (Wave 55-Ch11)

## Manuscript claims

`Principia_Fractalis_master_folder_rev2/chapters/ch11_geometric_unity.tex`
lines 140-205 contain two numerical claims that both attempt to derive
the consciousness threshold `ch_2 = 0.95`:

### Thm 11.5 `anomaly_cancel` (line 169)
Closed form supplied:
  `ch_2 = (4π)^7 · 10^7 / (8174 · 10^14) ≈ 0.95 Φ_0`
with the normalisation `Φ_0 = 1`.

Actual numerical value (Wolfram-style, 80-digit):
  `(4π)^7 ≈ 4.9518 × 10^7`
  `(4π)^7 · 10^7 / (8174 · 10^14) ≈ 6.054 × 10⁻⁴`
NOT `0.95`. Off by a factor of `≈ 1570`.

### Prop 11.6 `rqg_mean` (line 200)
Closed form supplied:
  `⟨|Ψ_RQG|²⟩ = √(5/(π+5)) ≈ 0.95`

Actual numerical value:
  `√(5/(π+5)) = √(5/8.1416) ≈ 0.7837`
NOT `0.95`.

The chapter argues (line 205) that `ch_2 = 0.95` is "twice determined".
Both determinations are arithmetically false.

## What this file proves (axiom-free)

1. `anomaly_cancel_predicted_value_ne_0_95` —
   `(4π)^7 · 10^7 / (8174 · 10^14) ≠ 95/100`.

   Strategy: bracket the predicted value below `1/1000`, and observe
   that `95/100 > 1/1000`, so the two cannot be equal.

2. `prop_11_6_psi_rqg_sq_ne_0_95` —
   `Real.sqrt (5/(Real.pi + 5)) ≠ 95/100`.

   Strategy: if equality held, squaring would give
   `5/(π+5) = (95/100)² = 9025/10000`.
   But `5/(π+5) < 9025/10000` since `π > 3.14` implies
   `9025·π > 9025·3.14 = 28338.5 > 4875 = 50000 - 45125`.

3. `anomaly_cancel_predicted_value_upper_bracket` and
   `prop_11_6_psi_rqg_sq_upper_bracket` — auxiliary brackets giving
   sharp upper bounds on the actual values.

4. `Ch11AnomalyCancellationRefutation_capstone` — bundles all four.

## Honest scope

This refutes TWO specific manuscript numerical claims (Ch 11 Thm 11.5
+ Prop 11.6) at axiom-free level. It does NOT discharge any Clay
problem. The structural claim that `ch_2 = 0.95` has OTHER derivations
in the framework (Ch 6 Chern-Weil, Ch 31 ch₂↔Φ bridge) which are
untouched by this file. What is touched is the specific Ch 11
"twice determined" argument on lines 140-205 — both legs of which
fail their stated numerical close.

## Pattern

Identical refutation pattern to Wave 55-R_f's
`R_f_one_two_ne_manuscript_value` in `PF/RfIntegerAlphaDichotomy.lean`
(commit 496193c): existing axiom-free Lean theorems + `norm_num` +
strict bracket transitivity.

Stage L7 — Wave 55-Ch11 manuscript refutation.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds

namespace PrincipiaTractalis.Ch11Refutation

open Real

/-! ## §1 — Thm 11.5 `anomaly_cancel` numerical refutation -/

/-- The closed-form value that Ch 11 line 169 equates to `0.95`. -/
noncomputable def anomaly_cancel_predicted : ℝ :=
  (4 * Real.pi) ^ 7 * 10 ^ 7 / (8174 * 10 ^ 14)

/-- **Upper bracket on the predicted anomaly-cancellation value**.

    We prove `(4π)^7 · 10^7 / (8174 · 10^14) < 1/1000`.

    Strategy:
    * `Real.pi < 3.141593` (mathlib `Real.pi_lt_d6`).
    * Therefore `4·π < 12.566372`, both nonnegative.
    * Monotonicity of `(·)^7` on nonneg reals gives
      `(4·π)^7 ≤ 12.566372^7`.
    * `norm_num` closes the rational inequality
      `12.566372^7 · 10^7 < (8174 · 10^14) / 1000`. -/
theorem anomaly_cancel_predicted_value_upper_bracket :
    anomaly_cancel_predicted < (1 / 1000 : ℝ) := by
  unfold anomaly_cancel_predicted
  have h_pi_ub : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- 4·π is positive and bounded above by 4·3.141593 = 12.566372.
  have h_4pi_pos : (0 : ℝ) < 4 * Real.pi := by linarith
  have h_4pi_ub : 4 * Real.pi < (12.566372 : ℝ) := by linarith
  -- (4π)^7 ≤ 12.566372^7 by monotonicity on nonneg reals.
  have h_4pi_nn : (0 : ℝ) ≤ 4 * Real.pi := le_of_lt h_4pi_pos
  have h_4pi_ub_le : 4 * Real.pi ≤ (12.566372 : ℝ) := le_of_lt h_4pi_ub
  have h_pow_ub : (4 * Real.pi) ^ 7 ≤ (12.566372 : ℝ) ^ 7 :=
    pow_le_pow_left₀ h_4pi_nn h_4pi_ub_le 7
  -- Denominator strictly positive.
  have h_denom_pos : (0 : ℝ) < 8174 * 10 ^ 14 := by norm_num
  -- Reduce to: (4π)^7 · 10^7 < (8174 · 10^14) / 1000.
  rw [div_lt_iff₀ h_denom_pos]
  -- It is enough that 12.566372^7 · 10^7 < (8174 · 10^14) · (1/1000).
  have h_inner : (12.566372 : ℝ) ^ 7 * 10 ^ 7 < 8174 * 10 ^ 14 * (1 / 1000) := by
    norm_num
  have h_lhs_le :
      (4 * Real.pi) ^ 7 * 10 ^ 7 ≤ (12.566372 : ℝ) ^ 7 * 10 ^ 7 :=
    mul_le_mul_of_nonneg_right h_pow_ub (by norm_num : (0 : ℝ) ≤ 10 ^ 7)
  linarith

/-- **★ Ch 11 Thm 11.5 numerical refutation ★**.

    The manuscript-supplied closed form
    `(4π)^7 · 10^7 / (8174 · 10^14)` does NOT equal `95/100`.

    Proof: the LHS is `< 1/1000`, but `95/100 = 0.95 > 1/1000`, so they
    must differ. -/
theorem anomaly_cancel_predicted_value_ne_0_95 :
    anomaly_cancel_predicted ≠ (95 / 100 : ℝ) := by
  intro h_eq
  have h_ub := anomaly_cancel_predicted_value_upper_bracket
  rw [h_eq] at h_ub
  -- Now h_ub : 95/100 < 1/1000, which is numerically false.
  norm_num at h_ub

/-! ## §2 — Prop 11.6 `rqg_mean` Gaussian-integration refutation -/

/-- The closed-form value that Ch 11 line 200 equates to `0.95`. -/
noncomputable def prop_11_6_psi_rqg_sq : ℝ := Real.sqrt (5 / (Real.pi + 5))

/-- **Upper bracket on `5/(π+5)`**: strictly less than `(95/100)²`.

    From `Real.pi > 3.141592`, we get `π + 5 > 8.141592`, hence
    `5/(π+5) < 5/8.141592 < 0.62 < 0.9025 = (95/100)²`. -/
theorem prop_11_6_inner_lt_squared_target :
    5 / (Real.pi + 5) < (95 / 100 : ℝ) ^ 2 := by
  have h_pi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  -- Therefore π + 5 > 8.141592 > 0.
  have h_denom_pos : (0 : ℝ) < Real.pi + 5 := by linarith
  have h_denom_lo : (8.141592 : ℝ) < Real.pi + 5 := by linarith
  -- 5 / (π+5) < 5 / 8.141592 (division reversal on positive denominators).
  have h_ratio_ub : 5 / (Real.pi + 5) < 5 / (8.141592 : ℝ) := by
    apply div_lt_div_of_pos_left
    · norm_num
    · norm_num
    · exact h_denom_lo
  -- 5 / 8.141592 < (95/100)^2 = 9025/10000 = 0.9025  — purely numerical.
  have h_num : (5 / 8.141592 : ℝ) < (95 / 100 : ℝ) ^ 2 := by norm_num
  exact lt_trans h_ratio_ub h_num

/-- **Upper bracket on `√(5/(π+5))`**: strictly less than `95/100`.

    Strategy: since both `Real.sqrt (5/(π+5))` and `95/100` are nonneg,
    and `(95/100)² > 5/(π+5)` by `prop_11_6_inner_lt_squared_target`,
    monotonicity of `sqrt` on nonneg reals gives the strict bound. -/
theorem prop_11_6_psi_rqg_sq_upper_bracket :
    prop_11_6_psi_rqg_sq < (95 / 100 : ℝ) := by
  unfold prop_11_6_psi_rqg_sq
  have h_target_nn : (0 : ℝ) ≤ 95 / 100 := by norm_num
  -- sqrt is strictly monotone on nonneg reals; use the sqrt < a equivalence.
  rw [show (95 / 100 : ℝ) = Real.sqrt ((95 / 100 : ℝ) ^ 2) from
        (Real.sqrt_sq h_target_nn).symm]
  apply Real.sqrt_lt_sqrt
  · -- 0 ≤ 5/(π+5)
    have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    have h_denom_pos : (0 : ℝ) < Real.pi + 5 := by linarith
    exact div_nonneg (by norm_num) (le_of_lt h_denom_pos)
  · exact prop_11_6_inner_lt_squared_target

/-- **★ Ch 11 Prop 11.6 numerical refutation ★**.

    The Gaussian-integration closed form `√(5/(π+5))` does NOT equal
    `95/100`.

    Proof: the LHS is strictly less than `95/100`. -/
theorem prop_11_6_psi_rqg_sq_ne_0_95 :
    prop_11_6_psi_rqg_sq ≠ (95 / 100 : ℝ) := by
  intro h_eq
  have h_ub := prop_11_6_psi_rqg_sq_upper_bracket
  rw [h_eq] at h_ub
  exact lt_irrefl _ h_ub

/-! ## §3 — Capstone -/

/-- **★ Capstone: Ch 11 anomaly-cancellation + RQG-mean BOTH refuted ★**.

    Conjoins:
    1. `(4π)^7 · 10^7 / (8174 · 10^14) < 1/1000`
       (`anomaly_cancel_predicted_value_upper_bracket`).
    2. `(4π)^7 · 10^7 / (8174 · 10^14) ≠ 95/100`
       (`anomaly_cancel_predicted_value_ne_0_95`).
    3. `√(5/(π+5)) < 95/100`
       (`prop_11_6_psi_rqg_sq_upper_bracket`).
    4. `√(5/(π+5)) ≠ 95/100`
       (`prop_11_6_psi_rqg_sq_ne_0_95`).

    The manuscript's "twice determined" argument (line 205) collapses:
    BOTH determinations fail. The framework's structural ch_2 = 0.95
    claim must rest on OTHER derivations (Ch 6 Chern-Weil, Ch 31
    ch₂↔Φ bridge), not the Ch 11 leg. -/
theorem Ch11AnomalyCancellationRefutation_capstone :
    anomaly_cancel_predicted < (1 / 1000 : ℝ) ∧
    anomaly_cancel_predicted ≠ (95 / 100 : ℝ) ∧
    prop_11_6_psi_rqg_sq < (95 / 100 : ℝ) ∧
    prop_11_6_psi_rqg_sq ≠ (95 / 100 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact anomaly_cancel_predicted_value_upper_bracket
  · exact anomaly_cancel_predicted_value_ne_0_95
  · exact prop_11_6_psi_rqg_sq_upper_bracket
  · exact prop_11_6_psi_rqg_sq_ne_0_95

end PrincipiaTractalis.Ch11Refutation
