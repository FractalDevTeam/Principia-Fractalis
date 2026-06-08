# R_f at integer α — closed forms (PROVED)

**Date**: 2026-05-23 evening generative session.
**Status**: PROVED. Will become Lean theorems.

## Statement

The manuscript's fractal-resonance function
$$R_f(\alpha, s) := \sum_{n=1}^{\infty} \frac{e^{i\pi\alpha\, D_3(n)}}{n^s}$$
(where $D_3(n)$ is the base-3 digital sum) admits explicit closed forms at every INTEGER value of $\alpha$:

| $\alpha$ | $R_f(\alpha, s)$ | Status at $s=1$ |
|---|---|---|
| $0$ | $\zeta(s)$ | pole |
| $1$ | $-\eta(s)$ | $R_f(1,1) = -\log 2$ |
| $2$ | $\zeta(s)$ | pole |
| $3$ | $-\eta(s)$ | $R_f(3,1) = -\log 2$ |
| $k$ even | $\zeta(s)$ | pole |
| $k$ odd | $-\eta(s)$ | $-\log 2$ |

In particular **R_f(α, 1) is finite and equals −log 2 at every odd integer α**, and singular at every even integer α.

## Proof

**Key Lemma.** Since $3 \equiv 1 \pmod 2$, we have $3^i \equiv 1 \pmod 2$ for all $i \geq 0$. Therefore for any non-negative integer $n = \sum_i a_i 3^i$ (base-3 expansion, $a_i \in \{0,1,2\}$):
$$n \equiv \sum_i a_i \pmod 2 = D_3(n) \pmod 2.$$

**Corollary.** $(-1)^{D_3(n)} = (-1)^n$ for all $n \geq 0$.

**Theorem (α = 1).** $R_f(1, s) = \sum_n (-1)^{D_3(n)}/n^s = \sum_n (-1)^n / n^s = -\eta(s)$ for $\Re(s) > 0$, where $\eta$ is the Dirichlet eta function. At $s = 1$, $R_f(1, 1) = -\eta(1) = -\log 2$. ∎

**Theorem (α = 2).** $e^{i\pi \cdot 2 \cdot D_3(n)} = 1$ for all $n$, so $R_f(2, s) = \sum 1/n^s = \zeta(s)$, with a pole at $s = 1$. ∎

**Theorem (α = k integer).** $e^{i\pi k D_3(n)} = ((-1)^k)^{D_3(n)} = ((-1)^k)^n$ (by the Corollary). So:
- $k$ even: $R_f(k, s) = \zeta(s)$
- $k$ odd: $R_f(k, s) = -\eta(s)$

## Why this matters

1. **Confirms R_f(1, 1) = −log 2 exactly** — earlier reported as a numerical observation, now PROVED.
2. **Explains the α=2 recursion pole** found earlier: $R_f(2, s) = \zeta(s)$ inherits the $\zeta$ pole.
3. **Makes R_f trivial at integer α** — all the framework's interesting content lives at NON-INTEGER α.
4. **Refutes any "universal closed form at s = 1"**: at integer α the value is $-\log 2$ (odd) or singular (even), neither equal to $\pi/(10\alpha)$ for any α. Confirms the prior agent's 100-digit refutation of $\pi\alpha/10$ and $\pi/(10\alpha)$ at integer α.
5. **Suggests R_f is a multiplicative twist of $\zeta$ by the base-3 digital character** — this is a Dirichlet series with a non-Dirichlet character (since $D_3$ mod 2 isn't a character mod any fixed modulus). Genuinely new object whose closed form at non-integer α requires Lerch-type expansions.

## Lean theorem (to be written)

```lean
namespace PrincipiaTractalis.Analytic

/-- Base-3 digital sum has the same parity as n, since 3 ≡ 1 (mod 2). -/
theorem d3_parity (n : ℕ) : d3 n % 2 = n % 2 := by
  -- induction on the base-3 expansion of n
  sorry

/-- (-1)^{D_3(n)} = (-1)^n for all n. -/
theorem neg_one_pow_d3 (n : ℕ) : (-1 : ℝ)^(d3 n) = (-1 : ℝ)^n := by
  rw [show (-1 : ℝ)^(d3 n) = (-1 : ℝ)^(d3 n % 2) from ...,
      show (-1 : ℝ)^n = (-1 : ℝ)^(n % 2) from ...,
      d3_parity]

/-- R_f(1, s) = -η(s) for Re(s) > 0. -/
theorem Rf_alpha_one (s : ℂ) (hs : 0 < s.re) :
    Rf 1 s = -etaFunction s := by
  unfold Rf
  congr 1
  ext n
  rw [show Complex.exp (Complex.I * π * 1 * (d3 n : ℂ)) = (-1)^(d3 n) from ...,
      neg_one_pow_d3]
  -- = (-1)^n / n^s, sum is -η(s)
  sorry

/-- R_f(1, 1) = -log 2 EXACTLY. -/
theorem Rf_one_one : Rf 1 1 = -Real.log 2 := by
  rw [Rf_alpha_one]
  -- -η(1) = -log 2
  sorry

end PrincipiaTractalis.Analytic
```
