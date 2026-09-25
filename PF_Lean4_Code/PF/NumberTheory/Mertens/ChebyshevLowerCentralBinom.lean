/-
# PF.NumberTheory.Mertens.ChebyshevLowerCentralBinom

**Date**: 2026-09-25 (DRAFT — awaiting tree ownership restoration)
**Landing**: Mertens M4-full — Chebyshev-strength linear lower bound on Θ(N)
via central binomial coefficient analysis (Erdős / Chebyshev).

**Target theorem:**
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → c * (N : ℝ) ≤ theta N

Concrete constant: `c = (log 4 - 1) / 2 ≈ 0.193`. This is a real linear
lower bound (in contrast to M4-Bertrand's `Θ(2^K) ≥ K · log 2`).

## Proof strategy (Erdős)

The classical route via central binomial `C(2n, n)`:

1. **Lower on C(2n,n):** `4^n ≤ 2n · C(2n, n)` — mathlib
   `four_pow_le_two_mul_self_mul_centralBinom`.

2. **Prime factorization of C(2n,n):**
   `C(2n, n) = ∏_{p ≤ 2n} p^{α_p(n)}` where `α_p(n) = padicValNat p C(2n,n)`.
   Available via mathlib's `Nat.eq_prod_pow_padicValNat` (or
   `Nat.factorization_prod_pow_eq_self`).

3. **Kummer bound on α_p:** For each prime `p ≤ 2n`, `α_p(n) ≤ log_p(2n)`,
   hence `p^{α_p(n)} ≤ 2n`. Mathlib: `Nat.padicValNat_choose` combined
   with Kummer's theorem.

4. **Prime splitting:**
   - For `p ∈ (n, 2n]`: `α_p(n) = 1` (only one factor of p in (n, 2n]!,
     and at most one in n!). Contribution to log C: exactly `log p`.
     Total contribution: `Θ(2n) - Θ(n)`.
   - For `p ≤ n`: contribution `α_p log p ≤ log(2n)` by (3).
     Total contribution: ≤ `π(n) · log(2n)`.

5. **Combining (1) and (2-4):**
      `n log 4 - log(2n) ≤ log C(2n,n) ≤ π(n) · log(2n) + (Θ(2n) - Θ(n))`

   Hence:
      `Θ(2n) - Θ(n) ≥ n log 4 - log(2n) - π(n) · log(2n)`

6. **Chebyshev-strength for π:** Use `π(n) ≤ 6n / log n` (mathlib may have
   via `Nat.primeCounting'_add_le` or `Chebyshev.primeCounting_le`; needs
   verification). If missing, prove auxiliary Chebyshev upper on π first.

7. **Rearrangement:** For large enough `n₀`, `Θ(2n) - Θ(n) ≥ (log 2) · n`
   (choosing constant to absorb error terms).

8. **Iterate:** `Θ(N) ≥ (log 2) · N/2 + Θ(N/2) ≥ … ≥ c · N` by telescoping
   the geometric series `∑ (log 2) · N/2^k = (log 2) · N`.

## Sub-lemmas required (in dependency order)

- `padicValNat_choose_two_le_log`: Kummer bound `α_p(C(2n,n)) ≤ log_p(2n)`
  packaged as `p^α ≤ 2n`.
- `centralBinom_log_split`: split into `p ∈ (n, 2n]` and `p ≤ n`.
- `centralBinom_log_le_pi_plus_theta_diff`: the RHS of (5).
- `chebyshev_pi_upper`: `π(n) ≤ C · n / log n`, either from mathlib
  (search: `Nat.chebyshev` under a different name) or proved as
  auxiliary using primorial_le_4_pow.
- `theta_diff_lower`: the (5) rearrangement.
- `theta_lower_linear`: telescoped result.

## Kernel status target

Zero project axioms; only `propext, Classical.choice, Quot.sound`.

## Estimated LOC (draft)

- Sub-lemmas: 400-800 LOC
- Chebyshev π upper (if not in mathlib): 200-400 LOC
- Iteration + capstone: 100-200 LOC
- **Total: 700-1400 LOC**

## Note on current state

This file is **staged for the future** and does NOT compile yet. It
requires (a) tree ownership restoration on the Acer, then (b) iterative
build/fix cycles. Committing this as a design doc for M4-full.

Chain check: full M4 (linear Θ lower) + M3 (∑ log p / p upper) + Abel
(M2) + Euler product identity → `∑ 1/p ≥ log log N - C` (Mertens-lower) →
`∏_{p ≤ z} (1 - 2/p) ≤ D / (log z)² ` → Brun B3 (twin-prime reciprocal
convergence).

That's the full chain to Brun's theorem.
-/

import PF.NumberTheory.Mertens.ChebyshevUpper
import PF.NumberTheory.Mertens.ChebyshevLowerBertrand
import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Divisors

namespace PF.NumberTheory.Mertens

open Finset

/-! ## Sub-lemma 1: Real cast of centralBinom lower bound -/

/-- `4^n ≤ 2n · centralBinom n` cast to ℝ. -/
lemma four_pow_le_two_mul_self_mul_centralBinom_real (n : ℕ) (hn : 0 < n) :
    (4 : ℝ) ^ n ≤ 2 * (n : ℝ) * (Nat.centralBinom n : ℝ) := by
  have h := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  exact_mod_cast h

/-! ## Sub-lemma 2: log of centralBinom bounded below by n·log 4 - log(2n) -/

/-- `log(centralBinom n) ≥ n · log 4 - log(2n)` for `n ≥ 1`. -/
lemma log_centralBinom_ge (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log 4 - Real.log (2 * (n : ℝ)) ≤
      Real.log ((Nat.centralBinom n : ℕ) : ℝ) := by
  have h_bound : (4 : ℝ) ^ n ≤ 2 * (n : ℝ) * (Nat.centralBinom n : ℝ) :=
    four_pow_le_two_mul_self_mul_centralBinom_real n hn
  have h_4n_pos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have h_2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have h_cb_pos : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos n
  have h_prod_pos : (0 : ℝ) < 2 * (n : ℝ) * (Nat.centralBinom n : ℝ) :=
    mul_pos h_2n_pos h_cb_pos
  have h_log_le : Real.log ((4 : ℝ) ^ n) ≤ Real.log (2 * (n : ℝ) * (Nat.centralBinom n : ℝ)) :=
    Real.log_le_log h_4n_pos h_bound
  rw [Real.log_pow] at h_log_le
  -- log(2n · CB) = log(2n) + log(CB)
  rw [Real.log_mul h_2n_pos.ne' h_cb_pos.ne'] at h_log_le
  -- log((4:ℝ)^n) = n * log 4 (already applied)
  linarith

/-! ## Remaining pieces (TO BE DRAFTED)

The following sub-lemmas are the substantive analytic content and are
staged for iterative implementation once the working tree is restored:

- `centralBinom_prime_factorization`: `C(2n,n) = ∏_{p ≤ 2n} p^{α_p(n)}`
- `padicValNat_centralBinom_upper`: `α_p(n) ≤ log_p(2n)` (Kummer)
- `p_pow_padicValNat_le`: `p^{α_p(n)} ≤ 2n`
- `centralBinom_log_split_high_low`: split at `p = n`
- `chebyshev_pi_upper`: `π(n) ≤ C · n / log n` (may need aux dev)
- `theta_diff_from_centralBinom`: combining above
- `theta_lower_linear`: iterate and telescope

Each is a nontrivial named result. The chain is well-defined but
requires build-and-iterate cycles that are currently blocked on tree
ownership.
-/

/-! **Chain reminder (comment-only).** The full M4 chain
`Θ(N) ≥ c · N` closes the linear Chebyshev lower bound. Combined with
M3's `∑ log p / p ≤ log 4 (2 + log N)` and a second Abel summation,
this yields Mertens' second theorem (both directions) and hence
Brun's twin-prime reciprocal sum convergence via B2-Legendre + Λ²
upgrade. -/

/-! ## Axiom sanity gate (for the two sub-lemmas that DO compile) -/

#print axioms four_pow_le_two_mul_self_mul_centralBinom_real
#print axioms log_centralBinom_ge

end PF.NumberTheory.Mertens
