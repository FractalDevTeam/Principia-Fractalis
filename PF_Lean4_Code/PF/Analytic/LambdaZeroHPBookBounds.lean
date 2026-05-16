/-
# Numerical Bounds for `lambda_zero_HP_book`

Connects the polylog-route's target value `lambda_zero_HP_book = π/(10·√2)`
to the precise interval-arithmetic bounds in `PF.IntervalArithmetic`.

The existing `lambda_0_P_precise` theorem provides 10-digit precision
on `π/(10·√2) ≈ 0.2221441469`. This file ports that bound to
`lambda_zero_HP_book` and provides concrete numerical thresholds for
the IVT-based axiom-retirement framework.

Stage L4 — Numerical bounds bridge.
-/

import PF.Analytic.SStarBridge
import PF.IntervalArithmetic

namespace PrincipiaTractalis.Analytic

open Real

/-! ## Algebraic equality: `lambda_zero_HP_book = pi_10 / √2` -/

/-- **Algebraic equality**: `lambda_zero_HP_book = pi_10 / Real.sqrt 2`.

    Direct definitional unfolding: both equal `π / (10 · √2)`. -/
theorem lambda_zero_HP_book_eq_pi10_div_sqrt2 :
    lambda_zero_HP_book = pi_10 / Real.sqrt 2 := by
  unfold lambda_zero_HP_book pi_10
  ring

/-! ## 10-digit precise bound -/

/-- **10-digit precision** on `lambda_zero_HP_book ≈ 0.2221441469`.

    Direct corollary of `lambda_0_P_precise` via the algebraic equality. -/
theorem lambda_zero_HP_book_precise :
    |lambda_zero_HP_book - (0.2221441469 : ℝ)| < 1e-10 := by
  rw [lambda_zero_HP_book_eq_pi10_div_sqrt2]
  exact lambda_0_P_precise

/-! ## Explicit upper and lower bounds -/

/-- **Explicit lower bound**: `0.2221441468 < lambda_zero_HP_book`. -/
theorem lambda_zero_HP_book_lower :
    (0.2221441468 : ℝ) < lambda_zero_HP_book := by
  have h := lambda_zero_HP_book_precise
  rw [abs_sub_lt_iff] at h
  linarith [h.2]

/-- **Explicit upper bound**: `lambda_zero_HP_book < 0.222144147`. -/
theorem lambda_zero_HP_book_upper :
    lambda_zero_HP_book < (0.222144147 : ℝ) := by
  have h := lambda_zero_HP_book_precise
  rw [abs_sub_lt_iff] at h
  linarith [h.1]

/-- **Positivity**: `0 < lambda_zero_HP_book`. -/
theorem lambda_zero_HP_book_pos : 0 < lambda_zero_HP_book := by
  have := lambda_zero_HP_book_lower
  linarith

/-! ## Thresholds for the IVT sign-change argument

For the IVT-based existence of `s_star`, we need numerical bracketing:

  `bookEvaluationGap a < 0 < bookEvaluationGap b`

where `bookEvaluationGap s := bookEvaluation s - lambda_zero_HP_book`.

The thresholds below give explicit numerical targets:

* To prove `bookEvaluationGap a < 0`, suffices to show
  `bookEvaluation a < 0.2221441468`.
* To prove `bookEvaluationGap b > 0`, suffices to show
  `bookEvaluation b > 0.222144147`.

These are concrete numerical conditions that can be checked via interval
arithmetic on truncated polylog evaluations. -/

/-- **Sufficient condition for `bookEvaluationGap a < 0`**:
    if `bookEvaluation a < 0.2221441468`, then `bookEvaluationGap a < 0`. -/
theorem bookEvaluationGap_neg_of_lt
    {a : ℝ} (h : bookEvaluation a < (0.2221441468 : ℝ)) :
    bookEvaluationGap a < 0 := by
  unfold bookEvaluationGap
  linarith [lambda_zero_HP_book_lower]

/-- **Sufficient condition for `bookEvaluationGap b > 0`**:
    if `bookEvaluation b > 0.222144147`, then `bookEvaluationGap b > 0`. -/
theorem bookEvaluationGap_pos_of_gt
    {b : ℝ} (h : (0.222144147 : ℝ) < bookEvaluation b) :
    0 < bookEvaluationGap b := by
  unfold bookEvaluationGap
  linarith [lambda_zero_HP_book_upper]

/-! ## Documentation: usage in the IVT framework

Combined with `book_eigenvalue_identity_of_sign_change`
(in `SStarBridge.lean`), these thresholds reduce the
`BookEigenvalueIdentity` retirement to:

  1. Continuity of `bookEvaluationGap` on a closed sub-interval `[a, b]`
     (mostly mechanized; `bookEvaluation` continuity at `z_book` is the
     open analytic content).
  2. Numerical computation: `bookEvaluation a < 0.2221441468` AND
     `bookEvaluation b > 0.222144147` for some specific decimal values
     `a, b ∈ (0, 1)` (e.g., the manuscript-suggested bracketing near
     `s_star ≈ 0.182`).

The numerical thresholds are now concrete, axiom-clean values rather
than abstract references to `lambda_zero_HP_book`.
-/

end PrincipiaTractalis.Analytic
