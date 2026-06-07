/-
# Hilbert-Schmidt Bound for the Framework's V_P Kernel

★ 2026-06-06 — Polylog chain piece 13 ★

## Why this file exists

For a matrix `M`, the Hilbert-Schmidt norm is `‖M‖_HS = √(Σ_ij M_ij²)`.
For the framework's V_P kernel uniformly bounded by `B = a/(a-1)`, each
entry satisfies `|M_ij| ≤ B`, so `M_ij² ≤ B²`, and the HS norm squared
is bounded by `N² · B²`.

This file proves that bound axiom-free.

## What gets closed

- `kernelMatrix_HS_norm_sq_bound`: for the framework's V_P kernel
  at sample points of `Fin N`, the Hilbert-Schmidt norm squared is
  bounded by `N² · (a/(a-1))²` when `a > 1`.

This is the load-bearing trace-class bound for the continuum limit.

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.
Kernel-only `[propext, Classical.choice, Quot.sound]`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.GeometricSeriesLimit
import PF.TuringEncoding.FiniteDimSpectralOperatorBound

namespace PrincipiaTractalis.TuringEncoding

/-! ## §1 — Entry-wise squared bound -/

/-- **For the framework's V_P kernel at `a > 1`, each entry squared is
    bounded by `(a/(a-1))²`**. -/
theorem fractalKernel_entry_sq_bound (Nlevels : ℕ) (a α : ℝ) (d : ℝ → ℝ → ℝ)
    (ha : 1 < a) (x y : ℝ) :
    (fractalKernelTruncated Nlevels a α d x y) ^ 2 ≤ (a / (a - 1)) ^ 2 := by
  have h_bound : |fractalKernelTruncated Nlevels a α d x y| ≤ a / (a - 1) :=
    fractalKernel_uniform_bound Nlevels a α d ha x y
  have h_bound_pos : 0 < a / (a - 1) := by
    have ha_pos : 0 < a := lt_trans zero_lt_one ha
    have ham1_pos : 0 < a - 1 := by linarith
    positivity
  -- |x| ≤ B and 0 ≤ B implies x² ≤ B²; sq_abs gives x² = |x|²
  have h1 : (fractalKernelTruncated Nlevels a α d x y) ^ 2 =
            |fractalKernelTruncated Nlevels a α d x y| ^ 2 := (sq_abs _).symm
  rw [h1]
  have h_nonneg : (0 : ℝ) ≤ a / (a - 1) := le_of_lt h_bound_pos
  nlinarith [abs_nonneg (fractalKernelTruncated Nlevels a α d x y), h_bound, h_nonneg]

/-! ## §2 — Sum-of-squares bound -/

/-- **The sum-of-squares bound** for the framework's V_P kernel matrix
    sampled on `Fin N`: the Hilbert-Schmidt norm squared is bounded by
    `N² · (a/(a-1))²`. -/
theorem fractalKernel_matrix_HS_sq_bound {N : ℕ} (Nlevels : ℕ)
    (a α : ℝ) (d : ℝ → ℝ → ℝ) (ha : 1 < a) (sample : Fin N → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N,
      (kernelMatrix (fractalKernelTruncated Nlevels a α d) sample i j) ^ 2 ≤
    (N : ℝ) ^ 2 * (a / (a - 1)) ^ 2 := by
  unfold kernelMatrix
  calc ∑ i : Fin N, ∑ j : Fin N,
        (fractalKernelTruncated Nlevels a α d (sample i) (sample j)) ^ 2
      ≤ ∑ i : Fin N, ∑ j : Fin N, (a / (a - 1)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact fractalKernel_entry_sq_bound Nlevels a α d ha (sample i) (sample j)
    _ = (N : ℝ) ^ 2 * (a / (a - 1)) ^ 2 := by
        rw [Finset.sum_const]
        simp [Finset.card_univ, Fintype.card_fin]
        ring

/-! ## §3 — Honest scope marker -/

/-- **Honest scope** for this file:

    1. CLOSED axiom-free:
       - `fractalKernel_entry_sq_bound`: each entry² ≤ (a/(a-1))²
       - `fractalKernel_matrix_HS_sq_bound`: HS norm² ≤ N²·(a/(a-1))²

    2. WHAT THIS UNLOCKS: the framework's V_P kernel matrix has bounded
       Hilbert-Schmidt norm at finite N, with explicit bound. This is
       the load-bearing trace-class structure needed for the continuum
       limit to L²(K_P, μ).

    3. CONTINUUM-LIMIT M3 RESIDUAL: extending the HS bound uniformly
       as N → ∞ (where N = |sample points| → ∞ for fractal K_P).
       The bound `N² · (a/(a-1))²` is not uniform — for the continuum
       limit, the kernel must be normalized by `1/N²` to give a
       Hilbert-Schmidt operator. This is the precise mathlib target. -/
theorem HilbertSchmidtBound_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.fractalKernel_entry_sq_bound
#print axioms PrincipiaTractalis.TuringEncoding.fractalKernel_matrix_HS_sq_bound
