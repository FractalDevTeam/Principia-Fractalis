/-
# PF.NumberTheory.Brun.TwinPrimeCountUpperBound

**Date**: 2026-09-24
**Landing**: Brun B2-Legendre — instantiate mathlib's generic upper-bound
sieve theorem at the Legendre-Eratosthenes upper Möbius sequence, yielding
a real formal upper bound on the twin-prime sifted sum.

**Status**: Kernel-clean formal bound on `(twinPrimeSieve N z).siftedSum`
via mathlib's `siftedSum_le_mainSum_errSum_of_upperMoebius` at the classical
Legendre choice `μ⁺ = μ · 𝟙[d ∣ prodPrimes]`. Uses only mathlib primitives
that exist in this toolchain (v4.24.0-rc1).

## What this file delivers

1. `muLegendre s : ℕ → ℝ` — Möbius on divisors of `s.prodPrimes`, zero elsewhere.
2. `muLegendre_isUpperMoebius s : IsUpperMoebius (muLegendre s)` —
   the classical proof via `(μ * ζ : ArithmeticFunction ℝ) = 1`.
3. `twin_legendre_bound N z` — the direct instantiation of the sieve
   inequality at the twin-prime instance:
       `siftedSum ≤ totalMass * mainSum μ⁺ + errSum μ⁺`.

## What this file does NOT deliver (named gaps)

For Brun-strength `π₂(N) = O(N / (log N)²)` and downstream convergence
(Landing B3), two further pieces are needed and are NOT in this mathlib:

- **Mertens-type decay**: `∏_{p ≤ z} (1 - 2/p) ≤ C / (log z)²`.
  Requires either an in-repo development or a mathlib Mertens
  contribution. Checked on 2026-09-24: no `Merten*` file exists.
- **Selberg Λ² or truncated-Möbius upgrade**: the current Legendre
  bound has error `≤ 2^{π(z)}`, which is exponential in `z` and thus
  only useful at `z ≲ log N` — insufficient for Brun. A truncated
  Möbius sieve (Brun 1919) or Λ² sieve (Selberg 1947) is required.
  Mathlib's `SelbergSieve.lean` (225 LOC) supplies only the abstract
  `BoundingSieve` structure and the generic inequality; no concrete
  Λ² construction is shipped.

## Kernel status

Zero project axioms; only `propext`, `Classical.choice`, `Quot.sound`
(the mathlib base). Kernel-clean per `principia_MASTER_DIRECTIVE.md`.
-/

import PF.NumberTheory.Brun.TwinPrimeSieveInstance
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.ArithmeticFunction

namespace PF.NumberTheory.Brun

open Finset ArithmeticFunction BoundingSieve

/-! ## The Legendre upper Möbius sequence -/

/-- The Legendre-Eratosthenes upper Möbius sequence: the Möbius function
on divisors of `s.prodPrimes`, extended by zero elsewhere. -/
noncomputable def muLegendre (s : BoundingSieve) : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then ((moebius d : ℤ) : ℝ) else 0

/-! ## Möbius-divisor sum identity -/

/-- Classical Möbius identity: for any `m`, `∑_{d ∣ m} μ(d) = [m = 1]`.
Follows from `μ * ζ = 1` in `ArithmeticFunction ℝ` via `coe_mul_zeta_apply`. -/
lemma sum_moebius_divisors_real (m : ℕ) :
    ∑ d ∈ m.divisors, ((moebius d : ℤ) : ℝ)
      = if m = 1 then (1 : ℝ) else 0 := by
  -- `μ * ζ = 1` as `ArithmeticFunction ℝ`, where μ, ζ are auto-coerced.
  have hμζ : (μ * ζ : ArithmeticFunction ℝ) = 1 := coe_moebius_mul_coe_zeta
  have happ : (μ * ζ : ArithmeticFunction ℝ) m = (1 : ArithmeticFunction ℝ) m := by
    rw [hμζ]
  rw [coe_mul_zeta_apply, ArithmeticFunction.one_apply] at happ
  -- happ : ∑ d ∈ m.divisors, (↑μ : ArithmeticFunction ℝ) d = if m = 1 then 1 else 0
  exact happ

/-! ## The upper-Möbius property -/

/-- Key rewrite: over divisors of `n ≠ 0`, the Legendre sequence sums
to the Möbius sum on divisors of `Nat.gcd n s.prodPrimes`. -/
lemma sum_muLegendre_eq_gcd_moebiusSum
    (s : BoundingSieve) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, muLegendre s d
      = ∑ d ∈ (Nat.gcd n s.prodPrimes).divisors, ((moebius d : ℤ) : ℝ) := by
  have hprod : s.prodPrimes ≠ 0 := s.prodPrimes_ne_zero
  have hgcd_ne : Nat.gcd n s.prodPrimes ≠ 0 := by
    intro h
    exact hn ((Nat.gcd_eq_zero_iff.mp h).1)
  -- Step 1: unfold muLegendre as filter
  have h1 : ∑ d ∈ n.divisors, muLegendre s d
      = ∑ d ∈ n.divisors.filter (fun d => d ∣ s.prodPrimes),
          ((moebius d : ℤ) : ℝ) := by
    rw [sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    unfold muLegendre
    split_ifs <;> rfl
  -- Step 2: filter set = divisors of gcd
  have h2 : n.divisors.filter (fun d => d ∣ s.prodPrimes)
      = (Nat.gcd n s.prodPrimes).divisors := by
    ext d
    simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hd_n, _⟩, hd_p⟩
      exact ⟨⟨hd_n, hd_p⟩, hgcd_ne⟩
    · rintro ⟨⟨hd_n, hd_p⟩, _⟩
      exact ⟨⟨hd_n, hn⟩, hd_p⟩
  rw [h1, h2]

/-- `muLegendre s` satisfies `IsUpperMoebius`. -/
lemma muLegendre_isUpperMoebius (s : BoundingSieve) :
    IsUpperMoebius (muLegendre s) := by
  intro n
  by_cases hn : n = 0
  · subst hn
    simp [muLegendre, Nat.divisors_zero]
  · -- n ≠ 0
    rw [sum_muLegendre_eq_gcd_moebiusSum s hn]
    rw [sum_moebius_divisors_real]
    -- Goal: (if n = 1 then 1 else 0) ≤ if Nat.gcd n s.prodPrimes = 1 then 1 else 0
    by_cases h1 : n = 1
    · subst h1
      simp
    · simp only [if_neg h1]
      split_ifs <;> norm_num

/-! ## The Legendre upper bound on siftedSum -/

/-- The classical Legendre upper bound applied to a `BoundingSieve`:
    `siftedSum ≤ totalMass · mainSum μ⁺ + errSum μ⁺`
where `μ⁺` is the Möbius function restricted to divisors of `prodPrimes`. -/
theorem legendre_upper_bound (s : BoundingSieve) :
    s.siftedSum ≤ s.totalMass * s.mainSum (muLegendre s) + s.errSum (muLegendre s) :=
  siftedSum_le_mainSum_errSum_of_upperMoebius (muLegendre s) (muLegendre_isUpperMoebius s)

/-- Instantiated at the twin-prime sieve of B1: for every `N, z : ℕ`,
the Legendre inclusion-exclusion bound on the twin-prime sifted sum. -/
theorem twin_legendre_bound (N z : ℕ) :
    (twinPrimeSieve N z).siftedSum ≤
      (twinPrimeSieve N z).totalMass *
        (twinPrimeSieve N z).mainSum (muLegendre (twinPrimeSieve N z)) +
      (twinPrimeSieve N z).errSum (muLegendre (twinPrimeSieve N z)) :=
  legendre_upper_bound (twinPrimeSieve N z)

/-! ## Axiom sanity gate -/

#print axioms muLegendre_isUpperMoebius
#print axioms legendre_upper_bound
#print axioms twin_legendre_bound

end PF.NumberTheory.Brun
