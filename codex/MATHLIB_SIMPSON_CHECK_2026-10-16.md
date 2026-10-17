# mathlib Simpson check — 2026-10-16

**Rio's question:** Does mathlib have a certified Simpson's rule with
explicit remainder bound?

**Verdict:** **No.** Not Simpson, not trapezoid, not any composite
Newton–Cotes rule. The closest existing result is Taylor's theorem with
the Lagrange remainder (pointwise, not a quadrature rule).

## Evidence (exhaustive search of `.lake/packages/mathlib/`)

* `grep -ri "simpson\|Simpson" .lake/packages/mathlib/` — **zero hits**
  (file name, theorem name, or comment).
* `grep -ri "cotes" .lake/packages/mathlib/` — **zero** (`quadrat` hits
  are all about quadratic *forms*, unrelated).
* `grep -ri "quadrature" .lake/packages/mathlib/` — **zero**.
* `grep -ri "trapezoid" .lake/packages/mathlib/` — **zero**.
* `grep -ri "newton[-_]?cotes\|midpoint_rule\|composite_rule"
  .lake/packages/mathlib/` — **zero**.

The `midpoint` hits in mathlib (`Mathlib/Analysis/Normed/Affine/AddTorsor.lean`,
`Mathlib/Analysis/Convex/Between.lean`) are all about the geometric midpoint
of two points, not a quadrature rule.

The `Mathlib/MeasureTheory/Integral/` folder has 50+ files; none implement
a composite quadrature-with-remainder theorem.

## Closest existing result

**`taylor_mean_remainder_lagrange`** in
`.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean:321`:

```lean
/-- **Taylor's theorem** with the Lagrange form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable in the closed
set `Icc x₀ x` and `n+1`-times differentiable on the open set `Ioo x₀ x`.
Then there exists an `x' ∈ Ioo x₀ x` such that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x₀)^{n+1}}{(n+1)!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$
is the $n+1$-th iterated derivative. -/
theorem taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
    (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ x' ∈ Ioo x₀ x, f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)!
```

Also present: `taylor_mean_remainder` (Cauchy form) at line 289.

This is **pointwise**: `|f(x) − P_n(x)| ≤ M·(x−x₀)^(n+1) / (n+1)!` for `M`
an upper bound on `|f⁽ⁿ⁺¹⁾|` on the interval. It is a *foundation* for
Simpson, not Simpson itself. Simpson requires:
  1. Taylor at `n = 3` on each panel (via `taylor_mean_remainder_lagrange`),
  2. The exactness of Simpson for cubics (standard cancellation argument),
  3. Composition over `k` panels via mathlib's
     `intervalIntegral.sum_integral_adjacent_intervals`.

## In-house precedent

PF has already built the analogous machinery at **second order** in
`PF/Analytic/XiQuadrature.lean`:

* `midpoint_rule_error` (line 335):
  ```
  |(∫ x in a..b, f x) - (b − a) · f((a+b)/2)| ≤ M · (b − a)^3 / 24
  ```
  under hypotheses on `f'`, `f''`, and `|f''| ≤ M`.

* `composite_midpoint_error` (line 399): the composite version over `n`
  equal panels, same proof pattern.

The Simpson lemma is a direct generalisation: fourth-order error bound
`M · (b − a)^5 / 2880` per panel under `|f⁽⁴⁾| ≤ M`, composed to
`M · (b − a) · h^4 / 180` for `n` panels of width `h = (b − a)/n`.

## Recommendation

**Build.** The in-house `midpoint_rule_error` + `composite_midpoint_error`
pattern is the exact template; Simpson is one more Taylor-degree step
(n=3 instead of n=1) and the per-panel-exactness-for-cubics observation.
No new mathlib dependencies — `taylor_mean_remainder_lagrange` +
`sum_integral_adjacent_intervals` + `intervalIntegral.integral_const`
suffice.

Estimate: `simpson_rule_error` + `composite_simpson_error` ≈ 300–500 L
of Lean, matching the existing `midpoint_rule_error` structure. One
reusable lemma, kernel-clean under the standard three-axiom bar.

Potential mathlib contribution: yes, straightforward. Taylor+Simpson is
textbook; it would land in `Mathlib/Analysis/Calculus/` and the
upstreaming conversation starts the moment the local lemma is green and
has no PF-specific dependencies.

## Downstream unblocked

Per Rio's note, the Simpson lemma unblocks: 493×–2055× panel reduction,
add-on tightening, Tier-3, the 390-box program.
