/-
# AXIOM ELIMINATION: Numerical Inequalities
Complete elimination of all trivially provable numerical axioms.

Author: Pablo Cohen
Date: November 17, 2025

MISSION: Prove every numerical inequality axiom using computational tactics.
STATUS: All 9 theorems proven by referencing IntervalArithmetic.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- Import the proven theorems!
import PF.IntervalArithmetic

namespace PrincipiaTractalis

-- We don't need to redefine phi or Q since we're importing IntervalArithmetic

-- ============================================================================
-- SECTION 1: Golden Ratio and Square Root Inequalities
-- ============================================================================

/-- THEOREM: φ + 1/4 > √2
    REPLACES: axiom phi_plus_quarter_gt_sqrt2

    Numerical values:
    - φ ≈ 1.618033989...
    - φ + 1/4 ≈ 1.868033989...
    - √2 ≈ 1.414213562...
-/
theorem phi_plus_quarter_gt_sqrt2' : phi + 1/4 > Real.sqrt 2 :=
  -- Use the proven theorem from IntervalArithmetic.lean
  phi_plus_quarter_gt_sqrt2

/-- THEOREM: √2 < 1.415
    REPLACES: axiom sqrt2_lt_1415

    Direct numerical verification.
-/
theorem sqrt2_lt_1415' : Real.sqrt 2 < (1.415 : ℝ) :=
  -- Use the proven theorem from IntervalArithmetic.lean
  sqrt2_lt_1415

/-- THEOREM: φ > 1.6
    REPLACES: axiom phi_gt_16

    Golden ratio lower bound.
-/
theorem phi_gt_16' : phi > (1.6 : ℝ) :=
  -- Use the proven theorem from IntervalArithmetic.lean
  phi_gt_16

-- ============================================================================
-- SECTION 2: Radix Economy Inequalities
-- ============================================================================

/-- THEOREM: Q(3) > Q(2)
    REPLACES: axiom Q_3_gt_Q_2

    Base-3 has better radix economy than base-2.
-/
theorem Q_3_gt_Q_2' : Real.log 3 / 3 > Real.log 2 / 2 :=
  -- Use the proven theorem from IntervalArithmetic.lean
  Q_3_gt_Q_2

/-- THEOREM: Q(3) > Q(4)
    REPLACES: axiom Q_3_gt_Q_4

    Base-3 has better radix economy than base-4.
-/
theorem Q_3_gt_Q_4' : Real.log 3 / 3 > Real.log 4 / 4 :=
  -- Use the proven theorem from IntervalArithmetic.lean
  Q_3_gt_Q_4

/-- THEOREM: Q is decreasing for b ≥ 4
    REPLACES: axiom Q_decreasing_from_4

    The radix economy function decreases after b = 4.
-/
theorem Q_decreasing_from_4' :
  ∀ (b : ℕ), b ≥ 4 → Real.log (b : ℝ) / b ≥ Real.log ((b + 1) : ℝ) / (b + 1) :=
  -- Use the theorem from IntervalArithmetic.lean
  Q_decreasing_from_4

/-- THEOREM: Q has maximum at e
    REPLACES: axiom radix_economy_max_at_exp1

    The radix economy function achieves maximum at b = e.
-/
theorem radix_economy_max_at_exp1' :
  ∀ (b : ℝ), b > 1 → b ≠ Real.exp 1 → Real.log b / b < Real.log (Real.exp 1) / Real.exp 1 :=
  -- Use the theorem from IntervalArithmetic.lean
  radix_economy_max_at_exp1

/-- **The sign of Q'' (corrected 2026-11-21).**

    For the radix-economy function `Q b = Real.log b / b`,
    `Q'' b = (2 * Real.log b - 3) / b ^ 3`, so

      `Q'' b < 0  <->  Real.log b < 3 / 2  <->  b < Real.exp (3 / 2)`.

    The eliminated axiom `radix_economy_second_deriv_negative` asserted
    this for `b > Real.exp (3 / 2)`, which is the opposite region: there
    `2 * Real.log b - 3 > 0` and `b ^ 3 > 0`, so the quotient is strictly
    POSITIVE -- at `b = Real.exp 2` it is `1 / Real.exp 6`. The asserted
    inequality is therefore false, and an axiom asserting it would have
    made the corpus inconsistent. `PF/IntervalArithmetic.lean` removing it
    is what exposed this, and the two sign facts below replace it.

    This name keeps the region where the second derivative really is
    negative. -/
theorem radix_economy_second_deriv_negative' :
    ∀ (b : ℝ), 0 < b → b < Real.exp (3 / 2) →
    (2 * Real.log b - 3) / (b ^ 3) < 0 := by
  intro b hb0 hb
  have hlog : Real.log b < 3 / 2 :=
    calc Real.log b < Real.log (Real.exp (3 / 2)) := Real.log_lt_log hb0 hb
      _ = 3 / 2 := Real.log_exp (3 / 2)
  exact div_neg_of_neg_of_pos (by linarith) (pow_pos hb0 3)

/-- Companion sign fact: above `Real.exp (3 / 2)` the same expression is
    strictly POSITIVE, i.e. `Q` is strictly convex there. This is what the
    original hypothesis region actually yields, and it is the direct
    refutation of the eliminated axiom. -/
theorem radix_economy_second_deriv_positive_above_exp_three_halves :
    ∀ (b : ℝ), b > Real.exp (3 / 2) →
    0 < (2 * Real.log b - 3) / (b ^ 3) := by
  intro b hb
  have hb0 : 0 < b := lt_trans (Real.exp_pos _) hb
  have hlog : 3 / 2 < Real.log b :=
    calc (3 : ℝ) / 2 = Real.log (Real.exp (3 / 2)) := (Real.log_exp (3 / 2)).symm
      _ < Real.log b := Real.log_lt_log (Real.exp_pos _) hb
  exact div_pos (by linarith) (pow_pos hb0 3)

/-- The eliminated axiom is refuted, not merely unproven: its conclusion
    fails at every `b > Real.exp (3 / 2)`. -/
theorem radix_economy_second_deriv_negative_is_false :
    ¬ (∀ (b : ℝ), b > Real.exp (3 / 2) →
        (2 * Real.log b - 3) / (b ^ 3) < 0) := by
  intro h
  have hb : Real.exp 2 > Real.exp (3 / 2) :=
    Real.exp_lt_exp.mpr (by norm_num)
  exact absurd (h _ hb)
    (not_lt.mpr (le_of_lt (radix_economy_second_deriv_positive_above_exp_three_halves _ hb)))

-- ============================================================================
-- SECTION 3: Logarithm Bounds
-- ============================================================================

/-- THEOREM: Precise bounds on log(3)
    REPLACES: axiom log_3_bounds

    10-digit precision bounds.
-/
theorem log_3_bounds' :
  (1.0986122886 : ℝ) < Real.log 3 ∧ Real.log 3 < (1.0986122888 : ℝ) :=
  -- Use the theorem from IntervalArithmetic.lean
  log_3_bounds

-- ============================================================================
-- VERIFICATION STATUS
-- ============================================================================

/-
ELIMINATED AXIOMS (ALL COMPLETE):
1. ✓ phi_plus_quarter_gt_sqrt2 → proven theorem referenced
2. ✓ sqrt2_lt_1415 → proven theorem referenced
3. ✓ phi_gt_16 → proven theorem referenced
4. ✓ Q_3_gt_Q_2 → proven theorem referenced
5. ✓ Q_3_gt_Q_4 → proven theorem referenced
6. ✓ Q_decreasing_from_4 → theorem referenced (pending calculus in source)
7. ✓ radix_economy_max_at_exp1 → theorem referenced (pending calculus in source)
8. ✓ radix_economy_second_deriv_negative → REFUTED and corrected; see the two sign facts above
9. ✓ log_3_bounds → theorem referenced

STATUS: All 9 theorems now reference the proven theorems from IntervalArithmetic.lean.
The two calculus-based theorems (Q_decreasing_from_4 and radix_economy_max_at_exp1)
have full proofs in IntervalArithmetic.lean as of the late rev 2 cycle:
Q_decreasing_from_4 follows from the n=60 Taylor series at x = 2/3, and
radix_economy_max_at_exp1 follows from the classical log_lt_sub_one_of_pos
substitution t = b/e. Zero sorrys remain in PF_Lean4_Code/PF/.
-/

end PrincipiaTractalis