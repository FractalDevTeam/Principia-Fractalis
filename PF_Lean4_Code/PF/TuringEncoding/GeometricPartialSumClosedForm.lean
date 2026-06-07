/-
# Geometric Partial Sum Closed Form

★ 2026-06-06 — Polylog chain piece 10 ★

## Why this file exists

Per `FiniteDimSpectralOperatorBound.lean`, the framework's V_P kernel
bound at truncation N is `Σ_{n=0}^N a^{-n}` — a geometric partial sum.
For this bound to be USEFUL (i.e., to give a finite operator-norm
estimate uniform in N), we need its closed-form value and its limit
as `N → ∞`.

This file closes that gap axiom-free.

## What gets closed

- `geometric_partial_sum_closed_form_real`: for `a > 0` with `a ≠ 1`,
  `Σ_{n=0}^N a^{-n} = (1 - a^{-(N+1)})/(1 - a^{-1})`.

- `geometric_partial_sum_bound_when_a_gt_one`: for `a > 1`,
  `Σ_{n=0}^N a^{-n} ≤ a/(a-1)` for all N.

- `fractalKernel_uniform_bound`: combining with `fractalKernel_entry_bound`,
  the V_P kernel entries are UNIFORMLY bounded by `a/(a-1)` independent
  of truncation N.

This is the load-bearing uniformity needed for the continuum-limit M3.

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.
Kernel-only `[propext, Classical.choice, Quot.sound]`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.FiniteDimSpectralOperatorBound
import Mathlib.Algebra.GeomSum

namespace PrincipiaTractalis.TuringEncoding

/-! ## §1 — Geometric partial sum closed form -/

/-- **Geometric partial sum closed form (real case)**: for `a > 0`,
    `a ≠ 1`, `Σ_{n=0}^N a^{-n} = (1 - a^{-(N+1)})/(1 - a^{-1})`.

    Equivalently, `Σ (1/a)^n = (1 - (1/a)^{N+1})/(1 - 1/a)`. -/
theorem geometric_partial_sum_closed_form_real (a : ℝ) (N : ℕ)
    (ha : a ≠ 1) (ha_pos : 0 < a) :
    ∑ n ∈ Finset.range (N + 1), (a ^ n)⁻¹ =
    (1 - (1/a) ^ (N + 1)) / (1 - 1/a) := by
  have h_inv : ∀ n : ℕ, (a ^ n)⁻¹ = (1/a) ^ n := by
    intro n
    rw [one_div, inv_pow]
  simp_rw [h_inv]
  have h_inv_ne_one : (1 / a) ≠ 1 := by
    intro h
    have : a = 1 := by
      field_simp at h
      linarith
    exact ha this
  rw [geom_sum_eq h_inv_ne_one (N + 1)]
  -- (q^(N+1) - 1)/(q - 1) where q = 1/a
  -- Rewrite to (1 - q^(N+1))/(1 - q)
  -- (q^(N+1) - 1)/(q - 1) = (1 - q^(N+1))/(1 - q) via negation
  have h_denom_ne : (1 / a - 1) ≠ 0 := by
    intro h
    have : 1 / a = 1 := by linarith
    exact h_inv_ne_one this
  have h_pos_denom_ne : (1 - 1 / a) ≠ 0 := by
    intro h; apply h_denom_ne; linarith
  rw [show ((1 / a) ^ (N + 1) - 1) = -(1 - (1 / a) ^ (N + 1)) from by ring,
      show ((1 / a) - 1) = -(1 - 1 / a) from by ring,
      neg_div_neg_eq]

/-! ## §2 — Uniform bound for `a > 1` -/

/-- **For `a > 1`, the geometric partial sum is uniformly bounded** by
    `a/(a-1)` for all N. -/
theorem geometric_partial_sum_bound_when_a_gt_one (a : ℝ) (N : ℕ) (ha : 1 < a) :
    ∑ n ∈ Finset.range (N + 1), (a ^ n)⁻¹ ≤ a / (a - 1) := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have ha_ne_one : a ≠ 1 := ne_of_gt ha
  rw [geometric_partial_sum_closed_form_real a N ha_ne_one ha_pos]
  -- (1 - (1/a)^(N+1))/(1 - 1/a) ≤ a/(a-1)
  -- Since 0 < 1/a < 1, (1/a)^(N+1) ≥ 0, so (1 - (1/a)^(N+1)) ≤ 1
  -- And (1 - 1/a) = (a - 1)/a > 0
  -- So (1 - (1/a)^(N+1))/(1 - 1/a) ≤ 1/(1 - 1/a) = a/(a - 1)
  have h_inv_a_lt_one : 1/a < 1 := by
    rw [div_lt_one ha_pos]; exact ha
  have h_inv_a_pos : 0 < 1/a := by positivity
  have h_inv_a_nonneg : 0 ≤ 1/a := le_of_lt h_inv_a_pos
  have h_inv_a_pow_nonneg : 0 ≤ (1/a) ^ (N + 1) := pow_nonneg h_inv_a_nonneg _
  have h_one_sub_pow_le : 1 - (1/a) ^ (N + 1) ≤ 1 := by linarith
  have h_one_minus_inv_pos : 0 < 1 - 1 / a := by linarith
  -- Now (1 - (1/a)^(N+1)) / (1 - 1/a) ≤ 1 / (1 - 1/a) = a/(a-1)
  have h_step1 : (1 - (1/a) ^ (N + 1)) / (1 - 1 / a) ≤ 1 / (1 - 1 / a) := by
    apply div_le_div_of_nonneg_right h_one_sub_pow_le (le_of_lt h_one_minus_inv_pos)
  -- 1/(1 - 1/a) = a/(a-1)
  have h_step2 : 1 / (1 - 1 / a) = a / (a - 1) := by
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have ham1_ne : a - 1 ≠ 0 := by linarith
    field_simp
  rw [h_step2] at h_step1
  exact h_step1

/-! ## §3 — Uniform bound for the fractal kernel -/

/-- **The framework's V_P kernel is UNIFORMLY bounded by `a/(a-1)`**
    independent of truncation level `N`. This is the key uniformity
    result for the continuum-limit M3. -/
theorem fractalKernel_uniform_bound (Nlevels : ℕ) (a α : ℝ) (d : ℝ → ℝ → ℝ)
    (ha : 1 < a) (x y : ℝ) :
    |fractalKernelTruncated Nlevels a α d x y| ≤ a / (a - 1) :=
  le_trans (fractalKernel_entry_bound Nlevels a α d ha x y)
           (geometric_partial_sum_bound_when_a_gt_one a Nlevels ha)

/-! ## §4 — Honest scope marker -/

/-- **Honest scope** for this file:

    1. CLOSED axiom-free:
       - `geometric_partial_sum_closed_form_real`: exact closed form
       - `geometric_partial_sum_bound_when_a_gt_one`: uniform bound `a/(a-1)`
       - `fractalKernel_uniform_bound`: V_P kernel uniformly bounded

    2. WHAT THIS UNLOCKS: the framework's V_P kernel is now bounded
       UNIFORMLY by `a/(a-1)` for all `x, y, N, α, d` (assuming `a > 1`).
       This uniformity is the load-bearing property for:
       - Hilbert-Schmidt extension to L²(K, μ)
       - Compact operator structure
       - Continuum-limit spectral convergence

    3. CONTINUUM-LIMIT M3 RESIDUAL: the uniform bound enables the
       finite-dim → infinite-dim spectral convergence. With the kernel
       uniformly bounded, mathlib's compact operator infrastructure
       can be applied (when M2.1-M2.3 are in place). -/
theorem GeometricPartialSumClosedForm_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.geometric_partial_sum_closed_form_real
#print axioms PrincipiaTractalis.TuringEncoding.geometric_partial_sum_bound_when_a_gt_one
#print axioms PrincipiaTractalis.TuringEncoding.fractalKernel_uniform_bound
