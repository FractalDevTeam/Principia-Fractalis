# MERTENS' THEOREMS — LEAN ATTACK PLAN

**Date:** 2026-09-25
**Author of plan:** Claude, at Pabs's direction (session 2026-09-24/25)
**Chain:** Downstream dependency of Brun B3. B2-Legendre landed
(`PF/NumberTheory/Brun/TwinPrimeCountUpperBound.lean`, commit `5227adad`) but
gives no asymptotic decay without Mertens-type product estimates.
**Predecessor plan:** `codex/BRUN_ATTACK_PLAN_2026-09-18.md`

---

## 0. LITERAL EXTERNAL STATEMENT

Three classical theorems (Mertens 1874):

**M-I (First Theorem, Chebyshev-strength):**
```
∑_{p ≤ x} (log p) / p  =  log x + O(1)
```

**M-II (Second Theorem):**
```
∑_{p ≤ x} 1/p  =  log log x + M + o(1)      (M = Meissel–Mertens constant)
```

**M-III (Third Theorem, product form):**
```
∏_{p ≤ x} (1 - 1/p)  =  e^{-γ} / log x · (1 + o(1))
```

Also required for Brun (derivable from M-III by a `1 - 2/p = (1-1/p)² · (1 + O(1/p²))` identity):
```
∏_{p ≤ x, p odd} (1 - 2/p)  =  O(1 / (log x)²)
```

**External status.** PROVED (Mertens 1874). Standard modern proof uses Chebyshev
bounds on `Θ(x) = ∑_{p ≤ x} log p` plus Abel/partial summation.

**Note on scope.** For downstream Brun-strength `π₂(N) = O(N/(log N)²)` we do NOT
need explicit constants. We need **existence** of `C > 0` such that
`∏_{p ≤ x, odd} (1 - 2/p) ≤ C / (log x)²` for `x ≥ x₀`. The Meissel–Mertens
constant `M` and Euler-Mascheroni `γ` are dispensable.

---

## 1. MATHLIB RUNWAY AUDIT (accurate as of 2026-09-25, v4.24.0-rc1)

| Primitive | Status | Path |
|---|---|---|
| `Nat.primeCounting`, `π'`, monotone | ✅ | `Mathlib/NumberTheory/PrimeCounting.lean` |
| `Nat.ArithmeticFunction.vonMangoldt` (Λ) | ✅ | `Mathlib/NumberTheory/VonMangoldt.lean` |
| `vonMangoldt_sum : ∑_{d ∣ n} Λ d = log n` | ✅ | ibid. |
| `Λ * ζ = log`, `log * μ = Λ`, `μ * log = Λ` | ✅ | ibid. |
| `sum_moebius_mul_log_eq : ∑ μ(d)·log d = -Λ(n)` | ✅ | ibid. |
| `vonMangoldt_le_log : Λ n ≤ log n` | ✅ | ibid. |
| `Nat.primorial n = ∏_{p ≤ n} p` | ✅ | `Mathlib/NumberTheory/Primorial.lean` |
| **`primorial_le_4_pow : n# ≤ 4^n`** | ✅ | ibid. — **KEY: gives upper Chebyshev Θ(n) ≤ n·log 4** |
| `Bertrand.exists_prime_lt_and_le_two_mul` | ✅ | `Mathlib/NumberTheory/Bertrand.lean` |
| Real Abel summation / partial summation | ⚠️ NOT AS `Abel_summation` — need to hand-roll from `Finset.sum_range_succ` |
| `∑_{p ≤ x} log p ≤ C · x` (Θ upper) | ⚠️ derivable in 20 LOC from `primorial_le_4_pow` |
| `∑_{p ≤ x} log p ≥ C · x` (Θ lower) | ❌ classical Erdős proof; likely 200-400 LOC. Bertrand.lean's central-binomial machinery is close but not packaged for direct use. |
| `∑_{p ≤ x} 1/p` bounds | ❌ needs Θ bounds + partial summation |
| `∏_{p ≤ x} (1 - 1/p)` bounds | ❌ needs ∑ 1/p bounds + log-of-product identity |
| Meissel–Mertens constant, Euler-Mascheroni | ❌ not in mathlib; NOT NEEDED for Brun-strength |

**Verdict:** Mathlib has strong scaffolding for the **upper Mertens direction**
(Θ upper is nearly free from `primorial_le_4_pow`). The **lower direction** is a
real project. For Brun we need BOTH directions.

---

## 2. LANDING DECOMPOSITION

**Landing M1 — `PF/NumberTheory/Mertens/ChebyshevUpper.lean`.**
Turn `primorial_le_4_pow` into an explicit Θ-upper bound.
```lean
theorem theta_upper : ∀ N : ℕ, ∑ p ∈ N.primesBelow, Real.log p ≤ N * Real.log 4
```
Bulk: rewrite `log(primorial N) = ∑_{p ≤ N} log p` and apply
`Real.log_le_log`. **Estimated ~80 LOC.** Trivial.

**Landing M2 — `PF/NumberTheory/Mertens/AbelSummation.lean`.**
General Abel summation for finite sums (partial summation):
```lean
theorem abel_summation (a : ℕ → ℝ) (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N+1), a n * f n =
      A N * f N - ∑ n ∈ Finset.range N, A n * (f (n+1) - f n)
  where A n := ∑ k ∈ Finset.range (n+1), a k
```
Reusable across the Mertens chain. **Estimated ~150 LOC** (careful with edge cases).

**Landing M3 — `PF/NumberTheory/Mertens/SumLogPOverP.lean`.**
From M1 + M2:
```lean
theorem sum_log_p_over_p_le : ∀ N : ℕ, 2 ≤ N →
    ∑ p ∈ N.primesBelow, Real.log p / p ≤ Real.log N + C
```
for an explicit `C`. **Estimated ~300 LOC.** Real number theory.

**Landing M4 — `PF/NumberTheory/Mertens/ChebyshevLower.lean`.**
The hard direction: `Θ(N) ≥ c·N` for some `c > 0`, from central binomial
coefficient analysis. Uses `Nat.centralBinom` and the exponent decomposition
that Bertrand.lean already contains internally. May be extractable from
Bertrand.lean's helpers with modest work. **Estimated ~400-600 LOC.**

**Landing M5 — `PF/NumberTheory/Mertens/MertensSecondUpper.lean`.**
From M2 + M3 + M4:
```lean
theorem sum_one_over_p_bounds :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧
      ∀ N : ℕ, 2 ≤ N →
        Real.log (Real.log N) - C₁ ≤
          ∑ p ∈ N.primesBelow, (1 : ℝ) / p ∧
        ∑ p ∈ N.primesBelow, (1 : ℝ) / p ≤
          Real.log (Real.log N) + C₂
```
**Estimated ~400 LOC.** The main Mertens payload.

**Landing M6 — `PF/NumberTheory/Mertens/ProductBound.lean`.**
The Brun-shaped bound:
```lean
theorem twin_prime_product_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 3 ≤ N →
        ∏ p ∈ N.primesBelow with p.Prime ∧ Odd p, (1 - (2 : ℝ)/p)
          ≤ C / (Real.log N)^2
```
From M5 via `1 - 2/p ≤ exp(-2/p)` and `log ∘ prod = sum ∘ log`. **Estimated ~250 LOC.**

**Total estimate:** ~1600-1800 LOC across six files. **Weeks of work.**
Each landing is real, reusable, and mathlib-contribution-quality.

---

## 3. RISK / GOTCHAS

- **Abel summation edge cases.** The classical formula assumes N ≥ 1; the empty-sum edge case needs care.
- **`Nat.primesBelow` vs `Finset.filter`.** Mathlib uses `Nat.primesBelow` (returns Finset). Sums over it need conversion when switching to product-over-filter formulations.
- **`log 0 = 0` convention.** Real.log 0 = 0 in Lean/mathlib; watch for degenerate N ≤ 1 cases in all landings.
- **`exp` vs `1 - x` inequality.** `1 - x ≤ exp(-x)` for x ≥ 0 is trivial; the reverse `exp(-x) ≤ 1 - x + x²/2` gives us the log-product estimate. Both are in mathlib.
- **Central binomial exponent decomposition.** In Bertrand.lean this is `centralBinom_factorization_small`. Extracting for M4 may require refactoring or copying the internal lemma.

---

## 4. WHY THIS LANDING MATTERS FOR PF

1. **Unblocks Brun B3.** Once M6 lands, B2-Legendre + M6 + error-term analysis give the classical `π₂(N) = O(N/(log N)²)`, and B3 (convergence) follows by comparison with `Summable (fun n => 1/(n·(log n)²))`.
2. **First real Mertens formalization in Lean 4 mathlib-adjacent code.** Isabelle has Mertens; Lean 4 does not (checked 2026-09-25). All six landings would be direct mathlib-PR candidates.
3. **Enables further sieve landings.** Sathe-Selberg-Delange, Rankin trick — all consume Mertens-shaped inputs. Getting M1–M6 down opens the whole analytic-NT bench.
4. **Chebyshev-strength `π(N)` bounds** fall out as corollaries. Removes another mathlib gap that `TwinPrimeConjectureFrameworkAttack.lean` currently uses `native_decide` to avoid.

---

## 5. ORDER OF OPERATIONS

1. **M1 first** (today, ~80 LOC): trivial from `primorial_le_4_pow`. Momentum landing.
2. M2 (Abel summation) — reusable infrastructure. Land second.
3. M3, M5, M6 (upper direction) — chain from M1 + M2. All achievable without lower Θ.
4. **Pause point after M6-upper-only.** Even without M4, an upper bound `∑ 1/p ≤ log log N + C` gives us `∏(1 - 2/p) ≥ C'/log² N` (lower on product = upper on log-product). We need the OPPOSITE inequality for Brun (upper on product), which requires M4/M5-lower. So the upper chain alone is nice but insufficient for Brun.
5. M4 (lower Θ) is the real research investment. Consider whether extracting from Bertrand.lean helpers is faster than writing fresh.
6. M5-lower + M6 finish.
7. `#print axioms` gate on every landing.

---

## 6. WHAT THIS PLAN IS NOT

- Not the exact Meissel–Mertens constant (M) or Euler-Mascheroni (γ) values. Existence of constants suffices.
- Not the tightest bounds. Chebyshev-strength (`4^n` upper) is enough; we don't need PNT.
- Not conditional on any PF substrate machinery. Stands entirely on mathlib.

---

## 7. STATUS

- **B2-Legendre landed** `PF/NumberTheory/Brun/TwinPrimeCountUpperBound.lean`, commit `5227adad` on `brun-b1`, kernel-clean.
- **Mertens M1:** ready to start.
- **This plan doc:** to be committed to `codex/MERTENS_ATTACK_PLAN_2026-09-25.md` (pending review).
