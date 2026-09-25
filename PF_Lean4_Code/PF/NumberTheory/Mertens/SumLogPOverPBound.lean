/-
# PF.NumberTheory.Mertens.SumLogPOverPBound

**Date**: 2026-09-25
**Landing**: Mertens M3b — Chebyshev-strength bound on `∑_{p ≤ N} log p / p`.

**Status**: Combines M3a (Abel identity) + M1 (Θ upper) + mathlib's
`harmonic_le_one_add_log` to give:

    ∑_{p ≤ N, p prime} log p / p  ≤  log 4 · (2 + log N)      for N ≥ 1.

Chebyshev-strength (Mertens first theorem with a worse constant).
The sharp `∑ log p / p = log N + O(1)` requires the lower Θ bound (M4).

## Kernel status

Zero project axioms; only `propext, Classical.choice, Quot.sound`.
-/

import PF.NumberTheory.Mertens.SumLogPOverPAbel
import PF.NumberTheory.Mertens.ChebyshevUpper
import Mathlib.NumberTheory.Harmonic.Bounds

namespace PF.NumberTheory.Mertens

open Finset

/-- Abbreviation: the first Chebyshev function. `abbrev` so it unfolds
transparently for later `show`/`exact` steps. -/
noncomputable abbrev theta (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ)

lemma theta_le (N : ℕ) : theta N ≤ (N : ℝ) * Real.log 4 :=
  theta_upper N

/-- **Boundary term bound.** For `N ≥ 1`, `Θ(N) · N⁻¹ ≤ log 4`. -/
lemma boundary_bound (N : ℕ) (hN : 1 ≤ N) :
    theta N * (N : ℝ)⁻¹ ≤ Real.log 4 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  calc theta N * (N : ℝ)⁻¹
      ≤ ((N : ℝ) * Real.log 4) * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right (theta_le N) (inv_pos.mpr hN_pos).le
    _ = Real.log 4 * ((N : ℝ) * (N : ℝ)⁻¹) := by ring
    _ = Real.log 4 := by rw [mul_inv_cancel₀ (ne_of_gt hN_pos)]; ring

/-- **Pointwise bound on the Abel sum term.**
For each `k`, `Θ(k) · (k⁻¹ - (k+1)⁻¹) ≤ log 4 · (k+1)⁻¹`. -/
lemma sum_term_pointwise_bound (k : ℕ) :
    theta k * ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹)
      ≤ Real.log 4 * ((k + 1 : ℕ) : ℝ)⁻¹ := by
  have h_log4_nn : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  by_cases hk : k = 0
  · subst hk
    -- theta 0 = 0: range 1 = {0}, 0 is not prime, filter is empty.
    have h_theta_zero : theta 0 = 0 := by
      show (∑ p ∈ (Finset.range 1).filter Nat.Prime, Real.log (p : ℝ)) = 0
      rw [show (Finset.range 1) = {0} from rfl]
      rw [Finset.filter_singleton]
      simp [Nat.not_prime_zero]
    rw [h_theta_zero, zero_mul]
    -- Goal: 0 ≤ log 4 * (0+1)⁻¹
    have : ((0 + 1 : ℕ) : ℝ)⁻¹ = 1 := by push_cast; norm_num
    rw [this, mul_one]
    exact h_log4_nn
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have h_theta_nn : 0 ≤ theta k := by
      apply Finset.sum_nonneg
      intro p hp
      have hp_prime := (Finset.mem_filter.mp hp).2
      exact Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
    -- Rewrite the difference of inverses.
    have h_diff : ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹)
                = 1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp
      ring
    -- Θ(k) ≤ k · log 4.
    have h_theta_bound : theta k ≤ (k : ℝ) * Real.log 4 := theta_le k
    -- Combine.
    rw [h_diff]
    have h_denom_pos : (0 : ℝ) < (k : ℝ) * ((k + 1 : ℕ) : ℝ) := mul_pos hk_pos hk1_pos
    have h_inv_denom_nn : (0 : ℝ) ≤ 1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) := by positivity
    calc theta k * (1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)))
        ≤ ((k : ℝ) * Real.log 4) * (1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right h_theta_bound h_inv_denom_nn
      _ = Real.log 4 * ((k + 1 : ℕ) : ℝ)⁻¹ := by
          field_simp

/-- **Aggregate bound on the Abel sum term.** -/
lemma sum_term_aggregate_bound (N : ℕ) :
    ∑ k ∈ Finset.range N,
        theta k * ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹)
      ≤ Real.log 4 * (1 + Real.log N) := by
  have h_log4_nn : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- Pointwise ≤ log 4 · (k+1)⁻¹.
  have h_ptwise :
      ∑ k ∈ Finset.range N,
          theta k * ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹)
        ≤ ∑ k ∈ Finset.range N, Real.log 4 * ((k + 1 : ℕ) : ℝ)⁻¹ :=
    Finset.sum_le_sum (fun k _ => sum_term_pointwise_bound k)
  -- ∑ log 4 · (k+1)⁻¹ = log 4 · harmonic N.
  have h_harmonic_eq :
      ∑ k ∈ Finset.range N, Real.log 4 * ((k + 1 : ℕ) : ℝ)⁻¹
        = Real.log 4 * ((harmonic N : ℚ) : ℝ) := by
    rw [← Finset.mul_sum]
    congr 1
    show ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)⁻¹ = ((harmonic N : ℚ) : ℝ)
    unfold harmonic
    push_cast
    rfl
  -- harmonic_le_one_add_log gives the bound.
  have h_harmonic_bound : ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log N :=
    harmonic_le_one_add_log N
  calc ∑ k ∈ Finset.range N,
          theta k * ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹)
      ≤ ∑ k ∈ Finset.range N, Real.log 4 * ((k + 1 : ℕ) : ℝ)⁻¹ := h_ptwise
    _ = Real.log 4 * ((harmonic N : ℚ) : ℝ) := h_harmonic_eq
    _ ≤ Real.log 4 * (1 + Real.log N) :=
        mul_le_mul_of_nonneg_left h_harmonic_bound h_log4_nn

/-- **M3 — Chebyshev-strength bound on `∑_{p ≤ N} log p / p`.**
For `N ≥ 1`,

    `∑_{p ≤ N, p prime} log p / p ≤ log 4 · (2 + log N)`. -/
theorem sum_log_p_over_p_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ)
      ≤ Real.log 4 * (2 + Real.log N) := by
  rw [sum_log_p_over_p_abel_expansion]
  -- With `theta` as an `abbrev`, the goal LHS is definitionally
  -- `theta N * N⁻¹ + ∑ k, theta k * (k⁻¹ - (k+1)⁻¹)`.
  have h_boundary := boundary_bound N hN
  have h_sum := sum_term_aggregate_bound N
  calc theta N * (N : ℝ)⁻¹
        + ∑ k ∈ Finset.range N,
            theta k * ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹)
      ≤ Real.log 4 + Real.log 4 * (1 + Real.log N) :=
        add_le_add h_boundary h_sum
    _ = Real.log 4 * (2 + Real.log N) := by ring

/-! ## Axiom sanity gate -/

#print axioms sum_log_p_over_p_le

end PF.NumberTheory.Mertens
