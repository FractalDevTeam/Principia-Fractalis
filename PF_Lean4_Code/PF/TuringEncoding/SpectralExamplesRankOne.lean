/-
# Spectral Examples — Rank-1 Kernel

★ 2026-06-06 — Polylog chain piece 17 ★

## Why this file exists

A rank-1 kernel at N=2 has the form `V(x_i, x_j) = f(x_i) · f(x_j)` for
some `f`. The matrix is then `M = v · vᵀ` where `v = (f(x_0), f(x_1))`.
Eigenvalues: `λ_+ = ‖v‖² = f(x_0)² + f(x_1)²`, `λ_- = 0`.

## What gets closed

- `discriminant_rank_one_case`: Δ = (f(x_0)² + f(x_1)²)²
- `lambdaPlus_rank_one`: λ_+ = f(x_0)² + f(x_1)²
- `lambdaMinus_rank_one`: λ_- = 0
- `spectral_gap_rank_one_eq_sum_sq`: gap = f(x_0)² + f(x_1)²

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.SpectralExamplesConstant

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — Rank-1 kernel at N=2 -/

/-- **For a rank-1 kernel** V(x, y) = f(x)·f(y), the determinant is zero
    (rows linearly dependent). -/
theorem determinant_rank_one_case (f : ℝ → ℝ) (x_0 x_1 : ℝ) :
    (fun x y => f x * f y) x_0 x_0 * (fun x y => f x * f y) x_1 x_1 -
    ((fun x y => f x * f y) x_0 x_1) ^ 2 = 0 := by
  show (f x_0 * f x_0) * (f x_1 * f x_1) - (f x_0 * f x_1) ^ 2 = 0
  ring

/-- **The discriminant for a rank-1 kernel** at N=2:
    `Δ = (f(x_0)² + f(x_1)²)²` (since `(a + c)² − 0 = (a + c)²`). -/
theorem discriminant_rank_one_case (f : ℝ → ℝ) (x_0 x_1 : ℝ) :
    ((fun x y => f x * f y) x_0 x_0 + (fun x y => f x * f y) x_1 x_1) ^ 2 -
    4 * ((fun x y => f x * f y) x_0 x_0 * (fun x y => f x * f y) x_1 x_1 -
         ((fun x y => f x * f y) x_0 x_1) ^ 2) =
    (f x_0 ^ 2 + f x_1 ^ 2) ^ 2 := by
  show (f x_0 * f x_0 + f x_1 * f x_1) ^ 2 -
       4 * ((f x_0 * f x_0) * (f x_1 * f x_1) - (f x_0 * f x_1) ^ 2) =
       (f x_0 ^ 2 + f x_1 ^ 2) ^ 2
  ring

/-- **For a rank-1 kernel, `λ_+ = f(x_0)² + f(x_1)²`**. -/
theorem lambdaPlus_rank_one (f : ℝ → ℝ) (x_0 x_1 : ℝ) :
    lambdaPlus (fun x y => f x * f y) x_0 x_1 = f x_0 ^ 2 + f x_1 ^ 2 := by
  unfold lambdaPlus
  simp only []
  rw [discriminant_rank_one_case f x_0 x_1]
  -- (f(x_0)² + f(x_1)²) is non-negative, so its square root is itself
  have h_nonneg : (0 : ℝ) ≤ f x_0 ^ 2 + f x_1 ^ 2 := by
    have h1 : 0 ≤ f x_0 ^ 2 := sq_nonneg _
    have h2 : 0 ≤ f x_1 ^ 2 := sq_nonneg _
    linarith
  have h_sqrt : Real.sqrt ((f x_0 ^ 2 + f x_1 ^ 2) ^ 2) = f x_0 ^ 2 + f x_1 ^ 2 :=
    Real.sqrt_sq h_nonneg
  rw [h_sqrt]
  show (f x_0 * f x_0 + f x_1 * f x_1 + (f x_0 ^ 2 + f x_1 ^ 2)) / 2 =
       f x_0 ^ 2 + f x_1 ^ 2
  ring

/-- **For a rank-1 kernel, `λ_- = 0`**. -/
theorem lambdaMinus_rank_one (f : ℝ → ℝ) (x_0 x_1 : ℝ) :
    lambdaMinus (fun x y => f x * f y) x_0 x_1 = 0 := by
  unfold lambdaMinus
  simp only []
  rw [discriminant_rank_one_case f x_0 x_1]
  have h_nonneg : (0 : ℝ) ≤ f x_0 ^ 2 + f x_1 ^ 2 := by
    have h1 : 0 ≤ f x_0 ^ 2 := sq_nonneg _
    have h2 : 0 ≤ f x_1 ^ 2 := sq_nonneg _
    linarith
  have h_sqrt : Real.sqrt ((f x_0 ^ 2 + f x_1 ^ 2) ^ 2) = f x_0 ^ 2 + f x_1 ^ 2 :=
    Real.sqrt_sq h_nonneg
  rw [h_sqrt]
  show (f x_0 * f x_0 + f x_1 * f x_1 - (f x_0 ^ 2 + f x_1 ^ 2)) / 2 = 0
  ring

/-- **The spectral gap for a rank-1 kernel is `f(x_0)² + f(x_1)²`**. -/
theorem spectral_gap_rank_one_eq_sum_sq (f : ℝ → ℝ) (x_0 x_1 : ℝ) :
    lambdaPlus (fun x y => f x * f y) x_0 x_1 -
    lambdaMinus (fun x y => f x * f y) x_0 x_1 = f x_0 ^ 2 + f x_1 ^ 2 := by
  rw [lambdaPlus_rank_one f x_0 x_1, lambdaMinus_rank_one f x_0 x_1]
  ring

/-! ## §2 — Honest scope marker -/

/-- **Honest scope** for this file: concrete spectral identities at
    rank-1 kernels. -/
theorem SpectralExamplesRankOne_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.determinant_rank_one_case
#print axioms PrincipiaTractalis.TuringEncoding.discriminant_rank_one_case
#print axioms PrincipiaTractalis.TuringEncoding.lambdaPlus_rank_one
#print axioms PrincipiaTractalis.TuringEncoding.lambdaMinus_rank_one
#print axioms PrincipiaTractalis.TuringEncoding.spectral_gap_rank_one_eq_sum_sq
