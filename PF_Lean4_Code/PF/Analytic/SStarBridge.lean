/-
# Numerical Bridge: `s_star` Existence via IVT

The bridge from the polylog-route Hankel identity (now fully mechanized
in the 17-module chain) to the manuscript's specific eigenvalue identity:

  `Re[polyLogSheet (-1) s_star · z_book] = π/(10√2)`

where `z_book = e^(iπ√2)` and `s_star ≈ 0.182049937912121` is the
numerical solution from `fractal_continuation_derivation.py`.

**Strategy**: define the evaluation function

  `bookEvaluation s := Re[polyLogSheet (-1) s z_book]`,

view it as a real function of `s ∈ (0, 1)`, and use **IVT** to prove
existence of `s_star`:
* `bookEvaluation` is continuous on `(0, 1)` (analytic in `s`).
* Given numerical bracketing: `bookEvaluation a < π/(10√2) < bookEvaluation b`
  for some `0 < a < b < 1`, IVT gives `s_star ∈ (a, b)` with
  `bookEvaluation s_star = π/(10√2)`.

This file:
* Defines `bookEvaluation` as the real-part evaluation.
* Defines `bookEvaluationGap s := bookEvaluation s − π/(10√2)`.
* Provides an **IVT-based existence framework**: given continuity and
  a sign-change in `bookEvaluationGap` on `(0, 1)`, derives
  `BookEigenvalueIdentity`.
* Documents the remaining numerical work (verifying the sign change at
  specific decimal values).

Stage L4 — `s_star` existence bridge.
-/

import PF.Analytic.EigenvalueIdentity

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Definitions -/

/-- **Book's evaluation function**: `s ↦ Re[polyLogSheet (-1) s z_book]`,
    viewed as a real function on `(0, 1)`. -/
noncomputable def bookEvaluation (s : ℝ) : ℝ :=
  Complex.re (polyLogSheet (-1) (s : ℂ) z_book)

/-- **Evaluation gap**: `bookEvaluation s − π/(10√2)`. A root of this
    function in `(0, 1)` gives the manuscript's `s_star`. -/
noncomputable def bookEvaluationGap (s : ℝ) : ℝ :=
  bookEvaluation s - lambda_zero_HP_book

/-! ## Trivial fact: `BookEigenvalueIdentity` iff `bookEvaluationGap` has a root in `(0, 1)` -/

/-- **Reduction to root-finding**: `BookEigenvalueIdentity` is equivalent
    to the existence of `s_star ∈ (0, 1)` with `bookEvaluationGap s_star = 0`. -/
theorem BookEigenvalueIdentity_iff_gap_zero :
    BookEigenvalueIdentity ↔
    ∃ s_star : ℝ, 0 < s_star ∧ s_star < 1 ∧ bookEvaluationGap s_star = 0 := by
  unfold BookEigenvalueIdentity bookEvaluationGap bookEvaluation
  constructor
  · rintro ⟨s, h_pos, h_lt, h_eq⟩
    exact ⟨s, h_pos, h_lt, by rw [h_eq]; ring⟩
  · rintro ⟨s, h_pos, h_lt, h_eq⟩
    refine ⟨s, h_pos, h_lt, ?_⟩
    linarith

/-! ## IVT-based existence framework -/

/-- **IVT-based existence schema**: if `bookEvaluationGap` is continuous on
    a closed sub-interval `[a, b] ⊂ (0, 1)` and changes sign (negative at
    `a`, positive at `b`), then there exists `s_star ∈ (a, b)` with
    `bookEvaluationGap s_star = 0`, i.e., `BookEigenvalueIdentity` holds.

    This reduces the manuscript's transcendental-equation claim to:
    1. Continuity of `bookEvaluation` (analytical content).
    2. Sign-change verification at specific values
       (e.g., `bookEvaluationGap 0.18 < 0 < bookEvaluationGap 0.19`,
       a numerical content). -/
theorem book_eigenvalue_identity_of_sign_change
    {a b : ℝ} (h_a_pos : 0 < a) (h_b_lt : b < 1) (h_a_lt_b : a < b)
    (h_cont : ContinuousOn bookEvaluationGap (Set.Icc a b))
    (h_a_neg : bookEvaluationGap a < 0)
    (h_b_pos : 0 < bookEvaluationGap b) :
    BookEigenvalueIdentity := by
  rw [BookEigenvalueIdentity_iff_gap_zero]
  obtain ⟨s_star, h_s_in, h_s_eq⟩ :=
    intermediate_value_Ioo h_a_lt_b.le h_cont
      ⟨h_a_neg, h_b_pos⟩
  exact ⟨s_star,
         lt_of_lt_of_le h_a_pos h_s_in.1.le,
         lt_of_le_of_lt h_s_in.2.le h_b_lt,
         h_s_eq⟩

/-- **Symmetric variant**: sign change with `gap a > 0` and `gap b < 0`. -/
theorem book_eigenvalue_identity_of_sign_change_rev
    {a b : ℝ} (h_a_pos : 0 < a) (h_b_lt : b < 1) (h_a_lt_b : a < b)
    (h_cont : ContinuousOn bookEvaluationGap (Set.Icc a b))
    (h_a_pos_gap : 0 < bookEvaluationGap a)
    (h_b_neg : bookEvaluationGap b < 0) :
    BookEigenvalueIdentity := by
  rw [BookEigenvalueIdentity_iff_gap_zero]
  -- Apply intermediate_value_Ioo' for descending direction
  obtain ⟨s_star, h_s_in, h_s_eq⟩ :=
    intermediate_value_Ioo' h_a_lt_b.le h_cont
      ⟨h_b_neg, h_a_pos_gap⟩
  exact ⟨s_star,
         lt_of_lt_of_le h_a_pos h_s_in.1.le,
         lt_of_le_of_lt h_s_in.2.le h_b_lt,
         h_s_eq⟩

/-! ## Documentation: remaining numerical work

The manuscript's `fractal_continuation_derivation.py` gives
`s_star ≈ 0.182049937912121`. To rigorously establish
`BookEigenvalueIdentity` in Lean via this framework, the remaining
work is:

**Step 1 (analytic content)**: prove
  `ContinuousOn bookEvaluationGap (Set.Icc a b)`
on some `[a, b] ⊂ (0, 1)` containing `0.182`. This follows from:
* Continuity of `Complex.re` (immediate).
* Continuity of `polyLogSheet (-1) (·) z_book` in the first argument
  (the `s` variable).
* `polyLogSheet (-1) s z = polyLog s z + polyLogMonodromyShift (-1) s z`,
  so we need:
  - `s ↦ polyLog s z` continuous (analytic in s for fixed z with
    appropriate properties — well-defined on the principal sheet).
  - `s ↦ polyLogMonodromyShift (-1) s z` continuous (involves
    `s ↦ (log z)^(s-1) / Γ(s)`, both continuous for s in the
    appropriate range).

**Step 2 (numerical content)**: verify
  `bookEvaluationGap 0.18 < 0` and `bookEvaluationGap 0.19 > 0`
(or similar bracketing values close to `s_star ≈ 0.182`). This requires
either:
* Interval arithmetic on the polylog series (truncation + bounds).
* The manuscript's specific analytical chain (Hankel-route + Jonquières
  + numerical convergence).

With the 17-module polylog-route Hankel chain mechanized, Step 1 reduces
to standard continuity assembly (no new analytic content). Step 2 is the
**genuinely numerical input** — a finite computation that can be done
either via mathlib's interval-arithmetic infrastructure or via an
external trusted numerical verification cited in the manuscript.

The framework here (`book_eigenvalue_identity_of_sign_change`) provides
the rigorous bridge from the numerical input to the manuscript's claim.
-/

end PrincipiaTractalis.Analytic
