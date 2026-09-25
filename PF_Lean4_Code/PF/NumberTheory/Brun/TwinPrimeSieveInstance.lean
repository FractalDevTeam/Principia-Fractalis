/-
# PF.NumberTheory.Brun.TwinPrimeSieveInstance

**Date**: 2026-09-23
**Landing**: Brun B1 — twin-prime Selberg-sieve setup.
**Status**: A concrete `BoundingSieve` instance for the twin-prime problem,
formulated on top of the mathlib primitive `Mathlib.NumberTheory.SelbergSieve`.

The sifting problem is `{ n * (n + 2) : 3 ≤ n ≤ N }`, sifted by the primes
strictly below `z`. The local density `ν` at an odd prime `p` is `2/p`
(two forbidden residue classes: `n ≡ 0 (p)` and `n ≡ -2 (p)`); the local
density at `p = 2` is `1/2` (only odd `n` keep `n(n+2)` coprime to 2).

## What this file delivers

1. `twinNuOnPrime : ℕ → ℝ`  — the local density at primes.
2. `twinNu : ArithmeticFunction ℝ` — extended multiplicatively via
   `ArithmeticFunction.prodPrimeFactors`, with `IsMultiplicative`
   supplied by mathlib for free.
3. `twinProdPrimes z := ∏ p ∈ Nat.primesBelow z, p`, with
   `Squarefree` proved via pairwise coprimality of distinct primes.
4. `twinSupport N := (Finset.Ioc 2 N).image (fun n => n * (n + 2))`,
   `twinWeights := fun _ => (1 : ℝ)`, `twinTotalMass N := (N : ℝ)`.
5. `twinPrimeSieve N z : BoundingSieve` — packages the seven axioms
   demanded by `mathlib`'s `structure BoundingSieve`.

## What this file is NOT

- Not a discharge of Brun's theorem.
- Not a bound on the twin-prime count (Landing B2).
- Not a convergence claim on `∑ 1/p + 1/(p+2)` over twin-prime pairs
  (Landing B3).
- Not conditional on any PF-substrate machinery; stands entirely on
  the mathlib upstream.

## Kernel status

Zero project axioms.  All proofs decidable / reducing to mathlib.
Kernel-clean per `principia_MASTER_DIRECTIVE.md`.
-/

import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.PrimeFin

namespace PF.NumberTheory.Brun

open Finset

/-! ## Local density on primes -/

/-- The local density of surviving residue classes at each prime for the
twin-prime sifting problem.  `ν(2) = 1/2` because only odd `n` avoid
`2 ∣ n(n+2)` collapsing to `2 ∣ n`; `ν(p) = 2/p` for odd primes because
`p ∣ n(n+2)` iff `n ≡ 0 (p)` or `n ≡ -2 (p)`, two residue classes out of `p`. -/
noncomputable def twinNuOnPrime : ℕ → ℝ := fun p =>
  if p = 2 then (1 : ℝ) / 2 else (2 : ℝ) / (p : ℝ)

/-- `twinNu`, extended to all of `ℕ` as an `ArithmeticFunction ℝ` via
`ArithmeticFunction.prodPrimeFactors`.  On a squarefree `d`, `twinNu d`
equals the product of `twinNuOnPrime` over the prime factors of `d`.
Mathlib supplies the `IsMultiplicative` proof automatically. -/
noncomputable def twinNu : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors twinNuOnPrime

lemma twinNu_isMultiplicative : twinNu.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

/-- Explicit evaluation of `twinNu` at a prime. -/
lemma twinNu_apply_prime {p : ℕ} (hp : p.Prime) : twinNu p = twinNuOnPrime p := by
  simp only [twinNu, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero,
    hp.primeFactors, Finset.prod_singleton]

/-- `twinNu` is strictly positive on every prime. -/
lemma twinNu_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < twinNu p := by
  rw [twinNu_apply_prime hp]
  unfold twinNuOnPrime
  split_ifs with h
  · norm_num
  · have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    positivity

/-- `twinNu` is strictly below one on every prime.  At `p = 2` this is
`1/2 < 1`; at odd primes `p ≥ 3` this is `2/p ≤ 2/3 < 1`. -/
lemma twinNu_lt_one_of_prime {p : ℕ} (hp : p.Prime) : twinNu p < 1 := by
  rw [twinNu_apply_prime hp]
  unfold twinNuOnPrime
  split_ifs with h
  · norm_num
  · have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h)
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    rw [div_lt_one hp0]
    exact_mod_cast hp2

/-! ## Sifting primes -/

/-- Product of all primes strictly below `z`.  This is the mathlib primitive
`Nat.primesBelow z`, folded as an ordinary product; it plays the role of
`P(z)` in the classical presentation of the Selberg sieve. -/
noncomputable def twinProdPrimes (z : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow z, p

lemma twinProdPrimes_squarefree (z : ℕ) : Squarefree (twinProdPrimes z) := by
  unfold twinProdPrimes
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hpp : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hqp : q.Prime := Nat.prime_of_mem_primesBelow hq
    simp only [Function.onFun]
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes hpp hqp).mpr hpq
  · intro p hp
    exact (Nat.prime_of_mem_primesBelow hp).squarefree

/-! ## Sifting-set support and weights -/

/-- Sifting-set support: `{ n * (n + 2) : 3 ≤ n ≤ N }`.  The map
`n ↦ n * (n + 2)` is strictly monotone on `ℕ`, so `Finset.image`
preserves cardinality of the range. -/
noncomputable def twinSupport (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 2 N).image (fun n => n * (n + 2))

/-- Constant weight `1` on all naturals.  The sifting of the support is
carried out by the `Coprime prodPrimes _` filter in `siftedSum`; the
weights themselves are all `1`. -/
def twinWeights : ℕ → ℝ := fun _ => 1

lemma twinWeights_nonneg : ∀ n : ℕ, 0 ≤ twinWeights n := fun _ => by
  unfold twinWeights; norm_num

/-- The total-mass approximation `X ≈ N`.  A tighter approximation
(e.g. `N - 2` from `Finset.Ioc 2 N`) would change only the constant in
downstream error terms; `X = N` is the classical choice. -/
def twinTotalMass (N : ℕ) : ℝ := (N : ℝ)

/-! ## The `BoundingSieve` instance -/

/-- The `BoundingSieve` instance for the twin-prime problem, parameterised by
the sifting bound `N` and the level `z`.  Downstream files (Landing B2)
will apply `siftedSum_le_mainSum_errSum_of_upperMoebius` to a concrete
Selberg-Λ² coefficient sequence to obtain the classical bound
`π₂(N) ≤ O(N / (log N)²)`. -/
noncomputable def twinPrimeSieve (N z : ℕ) : BoundingSieve where
  support := twinSupport N
  prodPrimes := twinProdPrimes z
  prodPrimes_squarefree := twinProdPrimes_squarefree z
  weights := twinWeights
  weights_nonneg := twinWeights_nonneg
  totalMass := twinTotalMass N
  nu := twinNu
  nu_mult := twinNu_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => twinNu_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp _ => twinNu_lt_one_of_prime hp

/-- Sanity check: the instance is well-typed and inhabits `BoundingSieve`. -/
noncomputable example (N z : ℕ) : BoundingSieve := twinPrimeSieve N z

end PF.NumberTheory.Brun
