/-
# PF.NumberTheory.Mertens.SumOneOverPCrudeBound

**Date**: 2026-09-25
**Landing**: Mertens M5-crude — crude upper bound on `∑_{p ≤ N} 1/p`.

**Status**: Kernel-clean. Delivers `∑_{p ≤ N} 1/p ≤ 1 + log N` via the
trivial `∑_{p ≤ N} 1/p ≤ ∑_{k ∈ [1,N]} 1/k = harmonic N ≤ 1 + log N`.

**Weaker than Mertens second theorem** (`∑ 1/p = log log N + M + o(1)`).
The `log log N` rate requires either:
  (a) Euler's product identity `∏_{p ≤ N} 1/(1-1/p) = ∑_{n : primes(n) ⊆ [2,N]} 1/n`
      + inequality `-log(1-x) ≤ x + x²` on `[0, 1/2]`, giving `∑ 1/p ≥ log log N - C`.
  (b) Second Abel summation on M3's `∑ log p / p` bound with `f_k = 1/log k`,
      giving `∑ 1/p ≤ log log N + C` from the sharper input.

Both routes are substantial follow-up landings (M5-Euler-lower and M5-Abel-upper).
This crude bound is the fast landing that fits in one file.

## Kernel status

Zero project axioms; only `propext, Classical.choice, Quot.sound`.
-/

import PF.NumberTheory.Mertens.SumLogPOverPBound
import Mathlib.NumberTheory.Harmonic.Bounds

namespace PF.NumberTheory.Mertens

open Finset

/-- **M5-crude — crude upper bound on `∑_{p ≤ N} 1/p`.**
For every `N : ℕ`, `∑_{p ≤ N, p prime} 1/p ≤ 1 + log N`.

Proof: The prime sum is bounded by the harmonic sum, since primes are
integers ≥ 2. Then mathlib's `harmonic_le_one_add_log` finishes. -/
theorem sum_one_over_p_crude (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
      ≤ 1 + Real.log N := by
  -- Step 1: bound prime sum by full sum over 1..N via 1/p ≤ 1/p on primes only.
  -- Equivalently: sum over primes ≤ N of 1/p ≤ sum over k ∈ range N of 1/(k+1).
  have h_prime_le_harmonic :
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
        ≤ ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)⁻¹ := by
    -- Recast the RHS as ∑_{n ∈ Icc 1 N} 1/n and use subset-monotonicity.
    have h_recast :
        ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)⁻¹
          = ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := by
      rw [Finset.range_eq_Ico]
      rw [Finset.sum_Ico_add' (fun (i : ℕ) => ((i : ℕ) : ℝ)⁻¹) 0 N 1]
      simp only [Finset.Ico_add_one_right_eq_Icc]
    rw [h_recast]
    -- Now: ∑_{p prime, p ≤ N} 1/p ≤ ∑_{n ∈ Icc 1 N} 1/n.
    -- The subset relation: primes ≤ N (in range (N+1) ∩ Prime) are a subset of Icc 1 N.
    have h_subset :
        (Finset.range (N + 1)).filter Nat.Prime ⊆ Finset.Icc 1 N := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      have hp_prime := hp.2
      rw [Finset.mem_Icc]
      exact ⟨hp_prime.one_lt.le, by omega⟩
    have h_convert :
        ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
          = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, ((p : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [one_div]
    rw [h_convert]
    apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
    intro n hn _
    rw [Finset.mem_Icc] at hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    exact inv_nonneg.mpr hn_pos.le
  -- Step 2: the RHS is (harmonic N : ℝ), bounded by 1 + log N.
  have h_harmonic_eq :
      ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)⁻¹
        = ((harmonic N : ℚ) : ℝ) := by
    unfold harmonic
    push_cast
    rfl
  have h_harmonic_bound : ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log N :=
    harmonic_le_one_add_log N
  linarith

/-! ## Axiom sanity gate -/

#print axioms sum_one_over_p_crude

end PF.NumberTheory.Mertens
