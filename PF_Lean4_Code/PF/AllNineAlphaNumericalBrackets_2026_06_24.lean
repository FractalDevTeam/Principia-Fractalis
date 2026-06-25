/-
# PF.AllNineAlphaNumericalBrackets_2026_06_24

★★★★★★★★ 2026-06-24 — uniform 4-decimal numerical brackets on all nine
substrate-class α values themselves (the column-2 entries of Table 1 of
the paper).

Closed forms exist in `PF/FrameworkApplicationCapstone.lean`. This file
provides uniform 4-decimal kernel-only brackets where the α value is
irrational, and exact rational equalities where the α value is rational.

## What this adds

  ✓ 4-decimal brackets on the four irrational α values:
        α_P     = √2          ∈ (1.4142, 1.4143)
        α_NP    = φ + 1/4     ∈ (1.8680, 1.8681)
        α_Hodge = φ           ∈ (1.6180, 1.6181)
        α_QG    = √(2π)       ∈ (2.5066, 2.5067)
  ✓ Brackets on the three π-involving α values:
        α_BSD   = 3π/4        ∈ (2.3561, 2.3562)
        α_NS    = 3π/2        ∈ (4.7123, 4.7124)
        (and α_Poincaré = 1, α_RH = 3/2, α_YM = 2 are exact rationals)
  ✓ Bundled all-nine α brackets capstone

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.FrameworkApplicationCapstone
import PF.IntervalArithmetic

namespace PrincipiaTractalis.AllNineAlphaNumericalBrackets

open Real PrincipiaTractalis PrincipiaTractalis.Capstone

/-! ## §1 — Exact rationals (no irrationality involved) -/

/-- `α_Poincaré = 1` exact. -/
theorem alpha_Poincare_exact : alpha_Poincare = 1 := rfl

/-- `α_RH = 3/2` exact. -/
theorem alpha_RH_exact : alpha_RH = 3 / 2 := rfl

/-- `α_YM = 2` exact. -/
theorem alpha_YM_exact : alpha_YM = 2 := rfl

/-! ## §2 — Numerical 4-decimal brackets via `IntervalArithmetic` -/

/-- `α_P = √2 ∈ (1.4142, 1.4143)`. -/
theorem alpha_P_bracket :
    (1.4142 : ℝ) < alpha_P ∧ alpha_P < (1.4143 : ℝ) := by
  unfold alpha_P
  have hlo := sqrt2_in_interval_10digit.1
  have hhi := sqrt2_in_interval_10digit.2
  refine ⟨?_, ?_⟩ <;> linarith

/-- `α_NP = φ + 1/4 ∈ (1.8680, 1.8681)`. -/
theorem alpha_NP_bracket :
    (1.8680 : ℝ) < alpha_NP ∧ alpha_NP < (1.8681 : ℝ) := by
  unfold alpha_NP
  have hlo := phi_in_interval_10digit.1
  have hhi := phi_in_interval_10digit.2
  unfold phi at hlo hhi
  refine ⟨?_, ?_⟩ <;> linarith

/-- `α_Hodge = φ ∈ (1.6180, 1.6181)`. -/
theorem alpha_Hodge_bracket :
    (1.6180 : ℝ) < alpha_Hodge ∧ alpha_Hodge < (1.6181 : ℝ) := by
  unfold alpha_Hodge
  have hlo := phi_in_interval_10digit.1
  have hhi := phi_in_interval_10digit.2
  unfold phi at hlo hhi
  refine ⟨?_, ?_⟩ <;> linarith

/-- `α_BSD = 3π/4 ∈ (2.3561, 2.3562)`. -/
theorem alpha_BSD_bracket :
    (2.3561 : ℝ) < alpha_BSD ∧ alpha_BSD < (2.3562 : ℝ) := by
  unfold alpha_BSD
  have hlo := Real.pi_gt_d6
  have hhi := Real.pi_lt_d6
  refine ⟨?_, ?_⟩ <;> linarith

/-- `α_NS = 3π/2 ∈ (4.7123, 4.7124)`. -/
theorem alpha_NS_bracket :
    (4.7123 : ℝ) < alpha_NS ∧ alpha_NS < (4.7124 : ℝ) := by
  unfold alpha_NS
  have hlo := Real.pi_gt_d6
  have hhi := Real.pi_lt_d6
  refine ⟨?_, ?_⟩ <;> linarith

/-- `α_QG = √(2π) ∈ (2.5066, 2.5067)`.

    Proof: `(2.5066)² = 6.28304356 < 2π` (since 2π > 6.28318 from `Real.pi_gt_d6`)
    and `2π < 2·3.14160 = 6.28320 < 2.5067² = 6.28354489`. -/
theorem alpha_QG_bracket :
    (2.5066 : ℝ) < alpha_QG ∧ alpha_QG < (2.5067 : ℝ) := by
  unfold alpha_QG
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have h2pi_lo : (6.28318 : ℝ) < 2 * Real.pi := by linarith
  have h2pi_hi : 2 * Real.pi < (6.28320 : ℝ) := by linarith
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  refine ⟨?_, ?_⟩
  · -- 2.5066 < √(2π)
    -- show (2.5066)² < 2π
    have h_sq : (2.5066 : ℝ) ^ 2 < 2 * Real.pi := by
      have : (2.5066 : ℝ) ^ 2 = 6.28304356 := by norm_num
      linarith
    have h_pos : (0 : ℝ) ≤ 2.5066 := by norm_num
    exact (Real.lt_sqrt h_pos).mpr h_sq
  · -- √(2π) < 2.5067
    -- show 2π < 2.5067²
    have h_sq : 2 * Real.pi < (2.5067 : ℝ) ^ 2 := by
      have : (2.5067 : ℝ) ^ 2 = 6.28354489 := by norm_num
      linarith
    have h_pos : (0 : ℝ) < 2.5067 := by norm_num
    exact (Real.sqrt_lt' h_pos).mpr h_sq

/-! ## §3 — All-nine bundled bracket capstone -/

/-- **★★★★★★★★ THE ALL-NINE-α BRACKET CAPSTONE ★★★★★★★★** —
    every substrate-class α value has either an exact rational equality
    or a kernel-only 4-decimal numerical bracket.

    Conjunction of three exact rationals + six 4-decimal brackets.

    Zero project axioms. -/
theorem all_nine_alpha_brackets_capstone :
    -- Three exact rationals
    (alpha_Poincare = 1) ∧
    (alpha_RH = 3 / 2) ∧
    (alpha_YM = 2) ∧
    -- Six 4-decimal brackets
    ((1.4142 : ℝ) < alpha_P ∧ alpha_P < (1.4143 : ℝ)) ∧
    ((1.8680 : ℝ) < alpha_NP ∧ alpha_NP < (1.8681 : ℝ)) ∧
    ((1.6180 : ℝ) < alpha_Hodge ∧ alpha_Hodge < (1.6181 : ℝ)) ∧
    ((2.3561 : ℝ) < alpha_BSD ∧ alpha_BSD < (2.3562 : ℝ)) ∧
    ((4.7123 : ℝ) < alpha_NS ∧ alpha_NS < (4.7124 : ℝ)) ∧
    ((2.5066 : ℝ) < alpha_QG ∧ alpha_QG < (2.5067 : ℝ)) :=
  ⟨alpha_Poincare_exact,
   alpha_RH_exact,
   alpha_YM_exact,
   alpha_P_bracket,
   alpha_NP_bracket,
   alpha_Hodge_bracket,
   alpha_BSD_bracket,
   alpha_NS_bracket,
   alpha_QG_bracket⟩

end PrincipiaTractalis.AllNineAlphaNumericalBrackets

-- ★ Axiom check ★
#print axioms
  PrincipiaTractalis.AllNineAlphaNumericalBrackets.all_nine_alpha_brackets_capstone
