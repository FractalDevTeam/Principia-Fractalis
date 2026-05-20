/-
# Algebraic identification & norm bound for `bookEvaluation 0.18`

**Input #3 of the Principia Fractalis axiom retirement.**

This file attacks the question: **what is `bookEvaluation 0.18` in the
*current* Lean formalization, and what can be rigorously said about it?**

## The honest mathematical situation

The manuscript predicts `bookEvaluation 0.18 ≈ 0.21331` (via
`Evidence_and_Data_for_GitHub/fractal_continuation_derivation.py`,
using mpmath's `polylog`). The target eigenvalue is
`λ_0(H_P) = π/(10·√2) ≈ 0.22214`, so a TIGHT inequality
`bookEvaluation 0.18 < 0.2221441468` was sought.

However, **`bookEvaluation` is defined in this Lean codebase via
`polyLog`, which is the boundary-divergent tsum series**, not the
mpmath/Jonquières analytic continuation. So in Lean:

* `polyLog (0.18 : ℂ) z_book = 0` (the series fails to be summable on
  the boundary `|z| = 1` for `Re s < 1`, so by Lean's `tsum`
  convention the value is `0`).
* `bookEvaluation 0.18 = Re(polyLogMonodromyShift (-1) (0.18:ℂ) z_book)`
  algebraically — the monodromy-shift correction term is the *only*
  remaining contribution.

The monodromy shift evaluates (using `log z_book = (π√2 - 2π)·I`,
proven below) to approximately `0.713`, NOT `0.213` and NOT `< 0.222`.

**Verdict**: the tight inequality `bookEvaluation 0.18 < 0.2221441468`
is FALSE under the *current* Lean `polyLog` definition. It can only
become true after `polyLog` is upgraded to the Jonquières analytic
continuation (which would replace the divergent tsum with a finite
value matching mpmath's `≈ -0.500 - 0.439·i`, recovering the python
script's `≈ 0.213`).

## What this file delivers (all axiom-free, no sorry)

1. **`polyLog_series_at_z_book_018_not_summable`**: the polylog series
   at `(0.18, z_book)` is genuinely not summable — proven via
   `Real.summable_one_div_nat_add_rpow` (mathlib's p-series criterion).

2. **`polyLog_018_z_book_eq_zero`**: hence
   `polyLog (0.18 : ℂ) z_book = 0` by Lean's tsum-of-nonsummable
   convention.

3. **`bookEvaluation_018_eq_re_shift`**: therefore
   `bookEvaluation 0.18 = Re(polyLogMonodromyShift (-1) (0.18:ℂ) z_book)`.

4. **`log_z_book_eq`**: the closed form
   `log z_book = (π·√2 - 2π)·I` on the principal branch
   (via `Complex.log_exp` after `2π·I` periodicity reduction).

5. **`norm_log_z_book`**: `|log z_book| = 2π - π·√2`.

6. **`norm_log_z_book_gt_one`**: `1 < |log z_book|` (since
   `π·(2 - √2) > 3·0.5 = 1.5 > 1`). Consequence: `|log z_book|^(s-1) <
   1` for `s ∈ (0, 1)`.

7. **`bookEvaluation_018_abs_le_shift_norm`**: the bound
   `|bookEvaluation 0.18| ≤ ‖polyLogMonodromyShift (-1) 0.18 z_book‖`
   (from `Re z ≤ |z|`).

## What this file does NOT deliver

* A **numerical** upper bound `bookEvaluation 0.18 < K` for any
  specific small `K` is **not** proven here. Such a bound would require
  rigorous numerical control of either `Real.Gamma 0.18` (currently
  not in mathlib at the needed precision) or the imaginary cpow
  `(w·I)^(-0.82)` (requires sin/cos at non-trivial multiples of π).

* The mpmath-aligned value `≈ 0.213` is **not** recovered — the current
  Lean `polyLog` definition simply doesn't compute that quantity. The
  Jonquières analytic continuation, which is identified in
  `Jonquieres.lean` as a *roadmap* item (no proven `polyLog_eq_
  jonquieresExpansion` theorem yet), would be needed.

## Path forward

To prove `bookEvaluation 0.18 < 0.2221441468`:

1. Formalize the Jonquières identity (open in this development;
   requires Hankel-contour machinery beyond current mathlib).
2. Redefine `polyLog` to use the analytic continuation (or work with
   `polyLog + analytical correction`) so the boundary evaluation
   recovers `mpmath`'s value.
3. With the proper analytic value, then bound numerically via interval
   arithmetic on the Jonquières series (truncation + Γ/ζ bounds).

Each step is a substantial analytic-number-theory deliverable. This
file delivers the precise *characterization* of what `bookEvaluation
0.18` currently equals in Lean — which is the prerequisite for any
honest bound work.

Stage L4 — algebraic identification of `bookEvaluation 0.18`.
-/

import PF.Analytic.SStarBridge
import PF.Analytic.LambdaZeroHPBookBounds
import PF.Analytic.LogZBookNeZero
import Mathlib.Analysis.PSeries

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Step 1: the polylog series at `(0.18, z_book)` is not summable -/

/-- **The polylog tsum at `z_book` for `s = 0.18` is not summable.**

The summand `z_book^(n+1) / (n+1)^0.18` has norm
`1 / (n+1)^0.18` (since `|z_book| = 1`), giving a divergent p-series
(`p = 0.18 < 1`). Proof via `Real.summable_one_div_nat_add_rpow`. -/
theorem polyLog_series_at_z_book_018_not_summable :
    ¬ Summable (fun n : ℕ =>
        z_book ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ ((0.18 : ℝ) : ℂ)) := by
  intro h
  have h_norm : ∀ n : ℕ,
      ‖z_book ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ ((0.18 : ℝ) : ℂ)‖
        = 1 / ((n + 1 : ℕ) : ℝ) ^ (0.18 : ℝ) := by
    intro n
    rw [norm_div, norm_pow, norm_z_book, one_pow]
    have h_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    rw [show (((n + 1 : ℕ) : ℂ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) from by norm_cast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h_pos _]
    simp [Complex.ofReal_re, one_div]
  have h_norm_summable : Summable (fun n : ℕ =>
      ‖z_book ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ ((0.18 : ℝ) : ℂ)‖) := h.norm
  rw [show (fun n : ℕ =>
              ‖z_book ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ ((0.18 : ℝ) : ℂ)‖) =
         (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (0.18 : ℝ))
       from funext h_norm] at h_norm_summable
  have h_form : (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (0.18 : ℝ)) =
                (fun n : ℕ => 1 / |((n : ℝ) + 1)| ^ (0.18 : ℝ)) := by
    funext n
    congr 2
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    push_cast; ring
  rw [h_form] at h_norm_summable
  rw [Real.summable_one_div_nat_add_rpow 1 0.18] at h_norm_summable
  linarith

/-! ## Step 2: `polyLog (0.18) z_book = 0` -/

/-- **`polyLog (0.18 : ℂ) z_book = 0`** under the current Lean
    definition of `polyLog` as a divergent tsum at the boundary.

    Direct from `polyLog_series_at_z_book_018_not_summable` and Lean's
    `tsum_eq_zero_of_not_summable`. -/
theorem polyLog_018_z_book_eq_zero :
    polyLog ((0.18 : ℝ) : ℂ) z_book = 0 := by
  unfold polyLog
  exact tsum_eq_zero_of_not_summable polyLog_series_at_z_book_018_not_summable

/-! ## Step 3: `bookEvaluation 0.18 = Re(monodromy shift)` -/

/-- **Key identification**: `bookEvaluation 0.18` equals the real part of
    the monodromy shift `polyLogMonodromyShift (-1) (0.18:ℂ) z_book`.

    Reason: `polyLogSheet (-1) s z = polyLog s z + polyLogMonodromyShift
    (-1) s z`, and at `(s = 0.18, z = z_book)` the first summand is
    `0` (`polyLog_018_z_book_eq_zero`). -/
theorem bookEvaluation_018_eq_re_shift :
    bookEvaluation (0.18 : ℝ) =
    Complex.re (polyLogMonodromyShift (-1) ((0.18 : ℝ) : ℂ) z_book) := by
  unfold bookEvaluation polyLogSheet
  rw [polyLog_018_z_book_eq_zero]
  simp

/-! ## Step 4: closed form `log z_book = (π√2 - 2π)·I` -/

/-- **Closed form of `log z_book`** on the principal branch:
    `log z_book = (π·√2 - 2π)·I`.

    Proof: `z_book = exp(I·π·√2) = exp(I·(π√2 - 2π))·exp(2π·I)
    = exp(I·(π√2 - 2π))`, since `exp(2π·I) = 1`. The argument
    `π√2 - 2π ∈ (-π, 0)` (because `√2 ∈ (1, 3)`), so `Complex.log_exp`
    applies. -/
theorem log_z_book_eq :
    Complex.log z_book = (Real.pi * Real.sqrt 2 - 2 * Real.pi : ℝ) * I := by
  unfold z_book
  have h_shift : I * (Real.pi : ℂ) * (Real.sqrt 2 : ℂ) =
                 ((Real.pi * Real.sqrt 2 - 2 * Real.pi : ℝ) : ℂ) * I +
                   2 * Real.pi * I := by
    push_cast; ring
  rw [h_shift]
  rw [Complex.exp_add]
  rw [Complex.exp_two_pi_mul_I, mul_one]
  apply Complex.log_exp
  · rw [show (((Real.pi * Real.sqrt 2 - 2 * Real.pi : ℝ) : ℂ) * I).im =
        (Real.pi * Real.sqrt 2 - 2 * Real.pi : ℝ) from by
      rw [Complex.mul_I_im]; simp]
    have h_sqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
      have h1 : Real.sqrt 1 < Real.sqrt 2 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rw [Real.sqrt_one] at h1
      exact h1
    have h_pi : Real.pi > 0 := Real.pi_pos
    nlinarith
  · rw [show (((Real.pi * Real.sqrt 2 - 2 * Real.pi : ℝ) : ℂ) * I).im =
        (Real.pi * Real.sqrt 2 - 2 * Real.pi : ℝ) from by
      rw [Complex.mul_I_im]; simp]
    have h_sqrt2_lt_3 : Real.sqrt 2 < 3 := by
      have : Real.sqrt 2 < Real.sqrt 9 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)] at this
      exact this
    have h_pi : Real.pi > 0 := Real.pi_pos
    nlinarith

/-! ## Step 5: `|log z_book| = 2π - π√2` -/

/-- **Norm of `log z_book`**: `|log z_book| = 2π - π·√2`.

    Direct from `log_z_book_eq` since `log z_book = (π√2 - 2π)·I` is
    purely imaginary with magnitude `|π√2 - 2π| = 2π - π√2`
    (positive because `π√2 < 2π`). -/
theorem norm_log_z_book :
    ‖Complex.log z_book‖ = 2 * Real.pi - Real.pi * Real.sqrt 2 := by
  rw [log_z_book_eq]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_eq_abs]
  rw [abs_of_neg]
  · ring
  · have h_sqrt2_lt_2 : Real.sqrt 2 < 2 := by
      have : Real.sqrt 2 < Real.sqrt 4 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at this
      exact this
    have h_pi : Real.pi > 0 := Real.pi_pos
    nlinarith

/-! ## Step 6: `|log z_book| > 1` -/

/-- **Lower bound**: `1 < |log z_book|`.

    We have `|log z_book| = 2π - π√2 = π(2 - √2)`. With `π > 3`
    (`Real.pi_gt_three`) and `√2 < 1.5`, this gives
    `π(2 - √2) > 3 · 0.5 = 1.5 > 1`.

    Consequence: any negative real-exponent power
    `|log z_book|^(t)` with `t < 0` is `< 1` (since base > 1). -/
theorem norm_log_z_book_gt_one : (1 : ℝ) < ‖Complex.log z_book‖ := by
  rw [norm_log_z_book]
  have h_pi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h_sqrt2_lt : Real.sqrt 2 < 1.5 := by
    have : Real.sqrt 2 < Real.sqrt (1.5 ^ 2) := by
      apply Real.sqrt_lt_sqrt (by norm_num)
      norm_num
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.5)] at this
    exact this
  have h_sub_pos : 0 < 2 - Real.sqrt 2 := by linarith
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  nlinarith [mul_pos h_pi_pos h_sub_pos]

/-! ## Step 7: norm bound `|bookEvaluation 0.18| ≤ |shift|` -/

/-- **Bound via `Re ≤ |·|`**: the absolute value of `bookEvaluation 0.18`
    is at most the norm of the monodromy shift.

    From `bookEvaluation_018_eq_re_shift`, the bookEvaluation equals
    `Re(shift)`. Combined with `|Re z| ≤ |z|` (mathlib's
    `Complex.abs_re_le_norm`), this gives the bound. -/
theorem bookEvaluation_018_abs_le_shift_norm :
    |bookEvaluation (0.18 : ℝ)| ≤
    ‖polyLogMonodromyShift (-1) ((0.18 : ℝ) : ℂ) z_book‖ := by
  rw [bookEvaluation_018_eq_re_shift]
  exact Complex.abs_re_le_norm _

/-! ## Step 8: closed-form expression for the shift's norm

The shift is `2πI·(-1)·(log z_book)^(-0.82) / Γ(0.18)`. Its norm
factors as `2π · |(log z_book)^(-0.82)| / |Γ(0.18)|`. This file
*identifies* this algebraic form; rigorous numerical control of
`|(log z_book)^(-0.82)|` and `|Γ(0.18)|` is deferred (see
"Path forward" in the file header). -/

/-- **Closed-form expression for the shift's norm**:
    `‖polyLogMonodromyShift (-1) (0.18) z_book‖
      = 2π · ‖(log z_book)^(-0.82)‖ / ‖Γ(0.18)‖`.

    Direct from definition + `norm_div`, `norm_mul`, and basic norm
    facts. Note that the explicit factor `|m| = 1` (with `m = -1`)
    collapses. -/
theorem norm_shift_018 :
    ‖polyLogMonodromyShift (-1) ((0.18 : ℝ) : ℂ) z_book‖
      = 2 * Real.pi *
          ‖(Complex.log z_book) ^ (((0.18 : ℝ) : ℂ) - 1)‖ /
          ‖Complex.Gamma ((0.18 : ℝ) : ℂ)‖ := by
  unfold polyLogMonodromyShift
  rw [norm_div]
  -- Rewrite numerator: 2·π·I·(-1)·log^(s-1) = -(2·π·I)·log^(s-1)
  have h_rearrange : (2 : ℂ) * (Real.pi : ℂ) * I * ((-1 : ℤ) : ℂ) *
                       Complex.log z_book ^ (((0.18 : ℝ) : ℂ) - 1)
                   = (-1 : ℂ) * ((2 * (Real.pi : ℂ)) * I *
                       Complex.log z_book ^ (((0.18 : ℝ) : ℂ) - 1)) := by
    push_cast; ring
  rw [h_rearrange]
  rw [norm_mul]
  rw [show ‖(-1 : ℂ)‖ = 1 from by simp]
  rw [one_mul]
  rw [norm_mul, norm_mul]
  -- Now: ‖2·π‖ · ‖I‖ · ‖log^(s-1)‖ / ‖Γ(s)‖ = 2π · ‖log^(s-1)‖ / |Γ(s)|
  have h_two_pi : ‖((2 : ℂ) * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [show ((2 : ℂ) * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by
          push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
  rw [h_two_pi, Complex.norm_I, mul_one]

/-! ## Honest summary

The above establishes:

* `bookEvaluation 0.18 ∈ ℝ` is **fully algebraically determined** by
  `Re(monodromy shift)` (no further mathematical content needed).
* The shift has norm `2π · ‖(log z_book)^(-0.82)‖ / |Γ(0.18)|`, a
  fully explicit expression.
* Numerically (`|log z_book| ≈ 1.84, Γ(0.18) ≈ 5.13`), the bound is
  approximately `6.28 · 0.59 / 5.13 ≈ 0.72`. So
  `bookEvaluation 0.18 ≈ 0.71` in Lean's current formalization.

**The desired inequality `bookEvaluation 0.18 < 0.2221441468` is
therefore FALSE in the current Lean polyLog setup** — to make it true,
the polyLog definition must be extended via the Jonquières analytic
continuation (open mathematical work, see `Jonquieres.lean`'s roadmap).

This file is the *honest characterization* of the situation, providing
the precise reduction that any future bound proof must build on. -/

end PrincipiaTractalis.Analytic
