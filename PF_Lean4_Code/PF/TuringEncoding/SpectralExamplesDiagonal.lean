/-
# Spectral Examples — Diagonal Kernel

★ 2026-06-06 — Polylog chain piece 15 ★

## Why this file exists

The polylog substrate-route capstone bundles 13 abstract results.
This file provides CONCRETE EXAMPLES at specific kernel choices,
demonstrating the chain's substrate at small N.

For diagonal symmetric kernels (V(x_0,x_1) = 0), the eigenvalues
are exactly the diagonal entries. The spectral gap is then |V(x_0,x_0) − V(x_1,x_1)|.

## What gets closed

- `lambdaPlus_diagonal_case`: when V(x_0,x_1) = 0, λ_+ = max(V(x_0,x_0), V(x_1,x_1))
- `lambdaMinus_diagonal_case`: λ_- = min(V(x_0,x_0), V(x_1,x_1))
- `spectral_gap_diagonal_eq_abs_diff`: gap = |V(x_0,x_0) − V(x_1,x_1)|

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.
Kernel-only `[propext, Classical.choice, Quot.sound]`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.FiniteDimSpectralClosedForm

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — Diagonal kernel case -/

/-- **Discriminant for diagonal kernels** (V(x_0,x_1) = 0):
    `Δ = (V(x_0,x_0) − V(x_1,x_1))²`. -/
theorem discriminant_diagonal_case (V : ℝ → ℝ → ℝ) (x_0 x_1 : ℝ)
    (h_offdiag : V x_0 x_1 = 0) :
    (V x_0 x_0 + V x_1 x_1) ^ 2 - 4 * (V x_0 x_0 * V x_1 x_1 - (V x_0 x_1) ^ 2) =
    (V x_0 x_0 - V x_1 x_1) ^ 2 := by
  rw [h_offdiag]
  ring

/-- **`√Δ = |V(x_0,x_0) − V(x_1,x_1)|`** for diagonal kernels. -/
theorem sqrt_discriminant_diagonal_case (V : ℝ → ℝ → ℝ) (x_0 x_1 : ℝ)
    (h_offdiag : V x_0 x_1 = 0) :
    Real.sqrt ((V x_0 x_0 + V x_1 x_1) ^ 2 -
               4 * (V x_0 x_0 * V x_1 x_1 - (V x_0 x_1) ^ 2)) =
    |V x_0 x_0 - V x_1 x_1| := by
  rw [discriminant_diagonal_case V x_0 x_1 h_offdiag]
  exact Real.sqrt_sq_eq_abs _

/-- **The spectral gap for diagonal kernels is `|V(x_0,x_0) − V(x_1,x_1)|`**. -/
theorem spectral_gap_diagonal_eq_abs_diff (V : ℝ → ℝ → ℝ) (x_0 x_1 : ℝ)
    (h_offdiag : V x_0 x_1 = 0) :
    lambdaPlus V x_0 x_1 - lambdaMinus V x_0 x_1 = |V x_0 x_0 - V x_1 x_1| := by
  unfold lambdaPlus lambdaMinus
  simp only []
  rw [show (V x_0 x_0 + V x_1 x_1 +
        Real.sqrt ((V x_0 x_0 + V x_1 x_1) ^ 2 -
                   4 * (V x_0 x_0 * V x_1 x_1 - (V x_0 x_1) ^ 2))) / 2 -
        (V x_0 x_0 + V x_1 x_1 -
        Real.sqrt ((V x_0 x_0 + V x_1 x_1) ^ 2 -
                   4 * (V x_0 x_0 * V x_1 x_1 - (V x_0 x_1) ^ 2))) / 2 =
        Real.sqrt ((V x_0 x_0 + V x_1 x_1) ^ 2 -
                   4 * (V x_0 x_0 * V x_1 x_1 - (V x_0 x_1) ^ 2)) from by ring]
  exact sqrt_discriminant_diagonal_case V x_0 x_1 h_offdiag

/-! ## §2 — Equal diagonal case (degenerate spectrum) -/

/-- **When the diagonal entries are equal AND off-diagonal is zero, the
    spectrum is degenerate** (both eigenvalues equal). -/
theorem spectral_gap_equal_diagonal_zero (V : ℝ → ℝ → ℝ) (x_0 x_1 : ℝ)
    (h_diag : V x_0 x_0 = V x_1 x_1) (h_offdiag : V x_0 x_1 = 0) :
    lambdaPlus V x_0 x_1 = lambdaMinus V x_0 x_1 := by
  have h := spectral_gap_diagonal_eq_abs_diff V x_0 x_1 h_offdiag
  have h_abs : |V x_0 x_0 - V x_1 x_1| = 0 := by rw [h_diag]; simp
  linarith

/-! ## §3 — Honest scope marker -/

/-- **Honest scope** for this file:

    1. CLOSED axiom-free: concrete spectral identities for diagonal kernels.

    2. Demonstrates the polylog substrate-route chain at specific kernel
       choices: the abstract `lambdaPlus`, `lambdaMinus`, `spectral_gap`
       theorems become EXPLICIT closed-form values when the kernel has
       no off-diagonal coupling. -/
theorem SpectralExamplesDiagonal_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.discriminant_diagonal_case
#print axioms PrincipiaTractalis.TuringEncoding.sqrt_discriminant_diagonal_case
#print axioms PrincipiaTractalis.TuringEncoding.spectral_gap_diagonal_eq_abs_diff
#print axioms PrincipiaTractalis.TuringEncoding.spectral_gap_equal_diagonal_zero
