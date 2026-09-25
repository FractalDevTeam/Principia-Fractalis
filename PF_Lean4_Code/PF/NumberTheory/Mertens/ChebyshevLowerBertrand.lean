/-
# PF.NumberTheory.Mertens.ChebyshevLowerBertrand

**Date**: 2026-09-25
**Landing**: Mertens M4-Bertrand — Θ lower bound iterated from Bertrand's postulate.

**Status**: Kernel-clean. Weaker than Chebyshev-strength `Θ(N) ≥ c·N`; delivers
`Θ(2^K) ≥ K · log 2` and consequently `Θ(N) ≥ log 2 · ⌊log₂ N⌋`. Not sufficient
to chain to full Brun (which needs the linear Chebyshev lower bound).

The full Erdős-Chebyshev `Θ(N) ≥ (log 2) · N + O(√N log N)` requires the
central-binomial p-adic analysis (Kummer + Legendre in `padicValNat` +
`centralBinom_le_of_no_bertrand_prime` structure). Estimated 500-1500 LOC;
deferred to a follow-up M4-full landing.

## Kernel status

Zero project axioms; only `propext, Classical.choice, Quot.sound`.
-/

import PF.NumberTheory.Mertens.SumLogPOverPBound
import Mathlib.NumberTheory.Bertrand

namespace PF.NumberTheory.Mertens

open Finset

/-- If a prime `p` sits in `(N, M]`, then adding `log p` to `Θ(N)` stays
below `Θ(M)`. -/
lemma theta_add_log_prime_le
    (N M p : ℕ) (hp : p.Prime) (hNp : N < p) (hpM : p ≤ M) :
    theta N + Real.log (p : ℝ) ≤ theta M := by
  have hNM : N ≤ M := by omega
  have hp_not_in_N : p ∉ (Finset.range (N + 1)).filter Nat.Prime := by
    intro h
    rw [Finset.mem_filter, Finset.mem_range] at h
    omega
  have hp_in_M : p ∈ (Finset.range (M + 1)).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp⟩
  have h_subset :
      insert p ((Finset.range (N + 1)).filter Nat.Prime) ⊆
      (Finset.range (M + 1)).filter Nat.Prime := by
    intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hq_mem
    · exact hp_in_M
    · rw [Finset.mem_filter, Finset.mem_range] at hq_mem ⊢
      exact ⟨by omega, hq_mem.2⟩
  unfold theta
  calc (∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (q : ℝ))
        + Real.log (p : ℝ)
      = ∑ q ∈ insert p ((Finset.range (N + 1)).filter Nat.Prime),
          Real.log (q : ℝ) := by
        rw [Finset.sum_insert hp_not_in_N]; ring
    _ ≤ ∑ q ∈ (Finset.range (M + 1)).filter Nat.Prime,
          Real.log (q : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
        intro q hq _
        have hq_prime := (Finset.mem_filter.mp hq).2
        exact Real.log_nonneg (by exact_mod_cast hq_prime.one_lt.le)

/-- **M4-Bertrand — lower bound on Θ at powers of 2.**
For every `K : ℕ`, `K · log 2 ≤ Θ(2^K)`.

Proof: induction on `K`. Base `K = 0`: `Θ(1) = 0 ≥ 0`. Step: Bertrand's
postulate gives a prime `p ∈ (2^K, 2·2^K] = (2^K, 2^(K+1)]`, which
contributes at least `log 2` (since `p ≥ 2`), and the previous
`Θ(2^K) ≥ K·log 2` is preserved by `theta_add_log_prime_le`. -/
theorem theta_pow_two_lower (K : ℕ) :
    (K : ℝ) * Real.log 2 ≤ theta (2 ^ K) := by
  induction K with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    unfold theta
    apply Finset.sum_nonneg
    intro q hq
    have hq_prime := (Finset.mem_filter.mp hq).2
    exact Real.log_nonneg (by exact_mod_cast hq_prime.one_lt.le)
  | succ K ih =>
    have h2Kne : (2 ^ K : ℕ) ≠ 0 := by positivity
    obtain ⟨p, hp_prime, hp_gt, hp_le⟩ :=
      Nat.exists_prime_lt_and_le_two_mul (2 ^ K) h2Kne
    have h_pow : 2 * 2 ^ K = 2 ^ (K + 1) := by ring
    rw [h_pow] at hp_le
    have h_log_p : Real.log 2 ≤ Real.log (p : ℝ) := by
      apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      exact_mod_cast hp_prime.two_le
    have h_step := theta_add_log_prime_le (2 ^ K) (2 ^ (K + 1)) p
                      hp_prime hp_gt hp_le
    have h_cast : ((K + 1 : ℕ) : ℝ) * Real.log 2
                = (K : ℝ) * Real.log 2 + Real.log 2 := by push_cast; ring
    rw [h_cast]
    linarith

/-! ## Axiom sanity gate -/

#print axioms theta_pow_two_lower

end PF.NumberTheory.Mertens
