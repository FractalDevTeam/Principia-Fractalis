/-
# PF.NumberTheory.Mertens.AbelSummation

**Date**: 2026-09-25
**Landing**: Mertens M2 — Abel summation (partial summation) for finite sums.

**Status**: Kernel-clean reusable identity. Not Mertens-specific — used
throughout analytic number theory to convert `∑ a k · f k` bounds into
bounds involving partial sums `A n := ∑_{k ≤ n} a k` and differences of `f`.

## What this file delivers

1. `abel_summation` — for any `CommRing R` and `a f : ℕ → R`:

       ∑_{k ≤ N} a k · f k
         = (∑_{k ≤ N} a k) · f N  +  ∑_{k < N} (∑_{j ≤ k} a j) · (f k - f (k+1))

Downstream: M3 (`∑ log p / p ≤ log N + C`) applies this with
`a k = if k.Prime then log k else 0` and `f k = 1/k`.

## Kernel status

Zero project axioms; only `propext, Classical.choice, Quot.sound`.
Kernel-clean per `principia_MASTER_DIRECTIVE.md`.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

namespace PF.NumberTheory.Mertens

open Finset

/-- **Abel summation (partial summation), finite form.** For any commutative
ring `R` and sequences `a f : ℕ → R`,

    ∑_{k=0}^{N} a k · f k
      = (∑_{k=0}^{N} a k) · f N
        + ∑_{k=0}^{N-1} (∑_{j=0}^{k} a j) · (f k - f (k+1)).

Proof: induction on `N`; the inductive step expands both sides via
`Finset.sum_range_succ` and closes by `ring`. -/
theorem abel_summation {R : Type*} [CommRing R] (a f : ℕ → R) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), a k * f k
      = (∑ k ∈ Finset.range (N + 1), a k) * f N +
        ∑ k ∈ Finset.range N,
          (∑ j ∈ Finset.range (k + 1), a j) * (f k - f (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    -- Expand LHS: split off the k = N+1 term.
    rw [Finset.sum_range_succ (fun k => a k * f k) (N + 1)]
    -- Apply the induction hypothesis to the leading sum.
    rw [ih]
    -- Expand the accumulator on the RHS.
    have hσ : (∑ k ∈ Finset.range (N + 1 + 1), a k)
            = (∑ k ∈ Finset.range (N + 1), a k) + a (N + 1) :=
      Finset.sum_range_succ a (N + 1)
    -- Expand the RHS difference sum: split off the k = N term.
    rw [Finset.sum_range_succ
        (fun k => (∑ j ∈ Finset.range (k + 1), a j) * (f k - f (k + 1))) N]
    rw [hσ]
    ring

/-! ## Axiom sanity gate -/

#print axioms abel_summation

end PF.NumberTheory.Mertens
