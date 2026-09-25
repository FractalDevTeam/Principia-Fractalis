/-
# PF.NumberTheory.Mertens.SumLogPOverPAbel

**Date**: 2026-09-25
**Landing**: Mertens M3a — Abel expansion of `∑_{p ≤ N} log p / p`.

**Status**: Kernel-clean identity, no bounds yet. Companion file
`SumLogPOverPBound.lean` (M3b) will consume this to derive the explicit
Chebyshev-strength bound.

## What this file delivers

1. `primeLog k := if k.Prime then log k else 0` — the coefficient sequence.
2. `sum_primeLog_eq_theta` — `∑_{k ≤ N} primeLog k = Θ(N)` (the first Chebyshev function).
3. `sum_primeLog_mul_inv_eq_sum_log_p_over_p` — converts the weighted form to the sum-over-primes form.
4. `sum_log_p_over_p_abel_expansion` — the Abel identity applied at (a k, f k) = (primeLog k, (k : ℝ)⁻¹):
       `∑_{p ≤ N} log p / p = Θ(N) · N⁻¹ + ∑_{k < N} Θ(k) · (k⁻¹ - (k+1)⁻¹)`.

## Kernel status

Zero project axioms; only `propext, Classical.choice, Quot.sound`.
-/

import PF.NumberTheory.Mertens.ChebyshevUpper
import PF.NumberTheory.Mertens.AbelSummation

namespace PF.NumberTheory.Mertens

open Finset

/-- The prime-indicator log sequence: `primeLog k = log k` if `k.Prime`,
`0` otherwise. Nonneg on all `k` (log is nonneg for primes ≥ 2). -/
noncomputable def primeLog : ℕ → ℝ := fun k =>
  if k.Prime then Real.log (k : ℝ) else 0

lemma primeLog_nonneg (k : ℕ) : 0 ≤ primeLog k := by
  unfold primeLog
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  · exact le_refl 0

/-- The prime-log partial sum equals the sum of `log p` over primes ≤ N. -/
lemma sum_primeLog_eq_theta (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), primeLog k
      = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) := by
  unfold primeLog
  rw [← Finset.sum_filter]

/-- The weighted prime-log sum with `(k : ℝ)⁻¹` weights equals the classical
`∑ log p / p` sum over primes. -/
lemma sum_primeLog_mul_inv_eq_sum_log_p_over_p (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), primeLog k * (k : ℝ)⁻¹
      = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
          Real.log (p : ℝ) / (p : ℝ) := by
  unfold primeLog
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  rw [div_eq_mul_inv]

/-- **M3a — Abel expansion of `∑ log p / p`.**
    `∑_{p ≤ N} log p / p = Θ(N) · N⁻¹ + ∑_{k < N} Θ(k) · (k⁻¹ - (k+1)⁻¹)`,
where `Θ(n) := ∑_{p ≤ n} log p` (the first Chebyshev function).

Proof: apply `abel_summation` at `a k = primeLog k`, `f k = (k : ℝ)⁻¹`,
then rewrite both sides via the two conversion lemmas above. -/
theorem sum_log_p_over_p_abel_expansion (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ)
      = (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ))
          * (N : ℝ)⁻¹
        + ∑ k ∈ Finset.range N,
            (∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime, Real.log (p : ℝ))
              * ((k : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ)⁻¹) := by
  rw [← sum_primeLog_mul_inv_eq_sum_log_p_over_p]
  rw [abel_summation primeLog (fun k => (k : ℝ)⁻¹) N]
  rw [sum_primeLog_eq_theta]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_primeLog_eq_theta]

/-! ## Axiom sanity gate -/

#print axioms sum_log_p_over_p_abel_expansion

end PF.NumberTheory.Mertens
