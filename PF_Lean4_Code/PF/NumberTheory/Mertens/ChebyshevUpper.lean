/-
# PF.NumberTheory.Mertens.ChebyshevUpper

**Date**: 2026-09-25
**Landing**: Mertens M1 — Chebyshev-strength upper bound on
`Θ(N) = ∑_{p ≤ N} log p`.

**Status**: Kernel-clean; direct consequence of mathlib's
`Nat.primorial_le_4_pow`. This is the first landing on the six-step Mertens
chain (see `codex/MERTENS_ATTACK_PLAN_2026-09-25.md`).

## What this file delivers

1. `theta_upper : ∑_{p ≤ N, p prime} log p ≤ N · log 4`
   — the classical Chebyshev-4 upper bound on the first Chebyshev function.

Downstream: Landing M3 (`∑ log p / p ≤ log N + C`) and M5 (Mertens' second theorem)
consume this bound via Abel summation.

## Kernel status

Zero project axioms; only `propext, Classical.choice, Quot.sound`
(the mathlib base). Kernel-clean per `principia_MASTER_DIRECTIVE.md`.
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PF.NumberTheory.Mertens

open Finset Nat

/-- **Chebyshev-strength upper bound (Θ upper).** For every `N : ℕ`,
    `∑_{p ≤ N, p prime} log p ≤ N · log 4`.

    Proof: `log ∘ primorial = ∑ log` and `primorial N ≤ 4^N`. -/
theorem theta_upper (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ)
      ≤ (N : ℝ) * Real.log 4 := by
  have h_pos : (0 : ℝ) < (primorial N : ℝ) := by exact_mod_cast primorial_pos N
  have h_bound : (primorial N : ℝ) ≤ (4 : ℝ) ^ N := by
    exact_mod_cast primorial_le_4_pow N
  -- Rewrite LHS as `log (primorial N)`.
  have h_prod_cast : (primorial N : ℝ)
      = ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (p : ℝ) := by
    unfold primorial
    push_cast
    rfl
  have h_sum_eq :
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ)
        = Real.log ((primorial N : ℕ) : ℝ) := by
    rw [h_prod_cast, Real.log_prod]
    intro p hp
    have hp_prime := (Finset.mem_filter.mp hp).2
    exact_mod_cast hp_prime.ne_zero
  rw [h_sum_eq]
  calc Real.log ((primorial N : ℕ) : ℝ)
      ≤ Real.log ((4 : ℝ) ^ N) := Real.log_le_log h_pos h_bound
    _ = (N : ℝ) * Real.log 4 := Real.log_pow 4 N

/-! ## Axiom sanity gate -/

#print axioms theta_upper

end PF.NumberTheory.Mertens
