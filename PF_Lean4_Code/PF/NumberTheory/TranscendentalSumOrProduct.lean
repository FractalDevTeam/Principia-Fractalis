/-
# PF.NumberTheory.TranscendentalSumOrProduct

★ 2026-08-24 — Option A of the r318 / Rank 6 dependency reduction ★

## Content

The generic field-theoretic schema:

  For a field extension `L / K` and elements `x, y ∈ L`, if `x` is
  transcendental over `K`, then at least one of `x + y` and `x * y`
  is transcendental over `K`.

Proved via the elementary quadratic-transitivity argument:
suppose both `x + y` and `x * y` are algebraic over `K`.  Both lie in
the subalgebra `K' := Subalgebra.algebraicClosure K L` (the algebraic
elements of `L` over `K`).  Then `x` is a root of the monic
polynomial

    P(T) = T² − (x + y) · T + (x · y)

with coefficients in `K'`.  Hence `IsAlgebraic K' x`.  Since `K'` is
algebraic over `K` (`Algebra.IsAlgebraic K (algebraicClosure K L)`
is a mathlib instance), transitivity via
`IsAlgebraic.restrictScalars K` yields `IsAlgebraic K x`, contradicting
transcendence of `x`.

## Semantic value

This landing REMOVES one precise uncertainty:

- BEFORE:  the "at least one of `π + e` and `π · e` is transcendental
  over `ℚ`" claim depended on an informal algebraic-transitivity
  argument PLUS a missing kernel theorem `Transcendental ℚ Real.pi`
  (or its `e` counterpart).

- AFTER:  the algebraic step is kernel-verified generically as
  `Transcendental.add_or_mul_left`.  The ONLY remaining specialisation
  dependency is a formal transcendence theorem for `π` or `e` — and
  that is a genuine mathlib gap (WIP PR #6718 on Lindemann-Weierstrass;
  Jujian Zhang's `e_transcendental.lean` lives outside mathlib).

This file makes NO claim about `π`, `e`, or any specific number.  It
is a reusable algebra theorem.

## Axiom budget

Zero project axioms, zero sorries.  All theorems depend only on
`[propext, Classical.choice, Quot.sound]`.

## Non-goal (do not add)

- Do NOT specialise this schema at `(π, e)` in this file.  Such a
  specialisation would require an unproved transcendence input, which
  is BANNED by MASTER DIRECTIVE §I.2 (no unproved classical fact
  disguised as a theorem).

- Do NOT rename this schema to imply anything about `π + e` or
  `π · e`.  Its statement is generic.

Author: Claude Opus 4.7. 2026-08-24.
-/
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral

namespace PF.NumberTheory.TranscendentalSumOrProduct

open Polynomial

/-- **Generic sum-or-product transcendence schema.**

Given a field extension `L / K` and elements `x, y ∈ L`, if `x` is
transcendental over `K` then at least one of `x + y` and `x * y` is
transcendental over `K`.

Proof sketch: suppose both `x + y` and `x * y` are algebraic over `K`.
Both lie in the subalgebra `K' := Subalgebra.algebraicClosure K L`.
Over `K'`, the element `x` is a root of the monic quadratic
`T² − (x + y) · T + (x · y)`, hence `IsAlgebraic K' x`.  Since `K'` is
algebraic over `K` (mathlib instance
`Algebra.IsAlgebraic K (Subalgebra.algebraicClosure K L)`), transitivity
via `IsAlgebraic.restrictScalars K` gives `IsAlgebraic K x`,
contradicting transcendence of `x`. -/
theorem Transcendental.add_or_mul_left
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x y : L} (hx : Transcendental K x) :
    Transcendental K (x + y) ∨ Transcendental K (x * y) := by
  -- Contrapositive: assume both `x + y` and `x * y` are algebraic over `K`;
  -- derive `IsAlgebraic K x`, contradicting `hx`.
  by_contra hne
  push_neg at hne
  obtain ⟨hsum_nt, hprod_nt⟩ := hne
  -- Unfold `Transcendental` to obtain `IsAlgebraic` hypotheses.
  rw [Transcendental, not_not] at hsum_nt hprod_nt
  have hsum : IsAlgebraic K (x + y) := hsum_nt
  have hprod : IsAlgebraic K (x * y) := hprod_nt
  -- Work in `K' := Subalgebra.algebraicClosure K L`, the K-subalgebra
  -- of `L` consisting of elements algebraic over `K`.
  set K' : Subalgebra K L := Subalgebra.algebraicClosure K L with hK'_def
  -- `s, p ∈ K'` correspond to `x + y, x * y` respectively.
  let s : K' := ⟨x + y, hsum⟩
  let p : K' := ⟨x * y, hprod⟩
  -- The monic quadratic `P := X² − C s · X + C p ∈ K'[X]`.
  let P : K'[X] := X ^ 2 - C s * X + C p
  -- `x`, viewed as an element of `L`, is a root of `P`.
  have hs_val : (algebraMap K' L) s = x + y := rfl
  have hp_val : (algebraMap K' L) p = x * y := rfl
  have hroot : aeval (x : L) P = 0 := by
    show aeval (x : L) (X ^ 2 - C s * X + C p) = 0
    rw [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, aeval_C,
        hs_val, hp_val]
    ring
  -- `P` is nonzero: coefficient at degree 2 evaluates to `1 ≠ 0` in `K'`.
  have hcoeff2 : P.coeff 2 = 1 := by
    show (X ^ 2 - C s * X + C p : K'[X]).coeff 2 = 1
    rw [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    simp
  have hP_ne : P ≠ 0 := by
    intro h
    have h0 : P.coeff 2 = 0 := by rw [h]; simp
    exact one_ne_zero (hcoeff2.symm.trans h0)
  -- Therefore `x` is algebraic over `K'`.
  have hx_alg_K' : IsAlgebraic K' (x : L) := ⟨P, hP_ne, hroot⟩
  -- Transitivity: `K'` is algebraic over `K`, so `x` is algebraic over `K`.
  have hx_alg_K : IsAlgebraic K x := hx_alg_K'.restrictScalars K
  exact hx hx_alg_K

/-- Symmetric form: swap the roles of `x` and `y`. -/
theorem Transcendental.add_or_mul_right
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x y : L} (hy : Transcendental K y) :
    Transcendental K (x + y) ∨ Transcendental K (x * y) := by
  have := Transcendental.add_or_mul_left (x := y) (y := x) hy
  simpa [add_comm, mul_comm] using this

end PF.NumberTheory.TranscendentalSumOrProduct

-- Axiom check.
#print axioms
  PF.NumberTheory.TranscendentalSumOrProduct.Transcendental.add_or_mul_left
#print axioms
  PF.NumberTheory.TranscendentalSumOrProduct.Transcendental.add_or_mul_right
