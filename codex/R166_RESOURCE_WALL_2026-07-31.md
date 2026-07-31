# r166 (5077a1 torsion-free): the mathematics is fine, the resources are not

**Status: NOT PROVED.** `PF/TorsionTrivial5077a1_r166.lean` exists as a worked
draft, is marked NOT VERIFIED in its header, and is deliberately **not** imported
by `PF.lean`.

## Why it matters

r164 gives the parallelogram law for `ĥ` on 5077a1 but *conditionally* — it needs
`P, Q, P ± Q` non-torsion. By Jordan–von Neumann a function satisfying the
parallelogram identity on an abelian group **is** a quadratic form, so
bi-additivity of the pairing is a *consequence* of an **unconditional** law, not
an extra input. Torsion-freeness is exactly what makes the law unconditional.
So r166 is the gate to `rank ≥ 3`:

  r166 torsion-free → unconditional law → bi-additivity free → 3×3 → rank ≥ 3.

## The mathematics is verified numerically

Bound `κ^(1/3) = 47` since `47³ = 103823 ≤ 105754 < 110592 = 48³`. Of the **2783**
rationals of naïve height ≤ 47:
- exactly **two** survive one application of `x ↦ f x / g x`: `1 ↦ 14`, `2 ↦ 21`;
- **neither** survives the second;
- no `g(x) = 0` among them.

Same structure as r155 for 389a1 (183 candidates, bound 12). Nothing subtle is
missing; this is a finite check that is known to come out the right way.

## The measured wall

`decide +kernel` does not scale from 183 to 2783 on this hardware.

- A single block of 2783: stack overflow; then, with `ulimit -s 262144` and
  `maxRecDepth 1000000`, reduction gets **stuck** at `List.decidableBAll`.
- Measured working ceiling for one block: 95 ✓, 285 ✓, 570 ✓, **1140 ✓**, 2783 ✗.
- Split into four blocks of ≤1140 — and the *first* block reached **12.9 GB RSS**
  in ~60 s on a 15 GB machine with swap already exhausted. Killed deliberately
  (`LEAN_EXIT=137`) to protect the box; memory recovered to 2 GB used.

That is ~11 MB of kernel term per candidate, so the cost is dominated by `Rat`
arithmetic: normalization gcds on numerators up to **22 digits**, with the whole
`Finset ℚ` and every intermediate materialized without sharing.

## Two fixes, in order of preference

**(1) Restrict to perfect-square denominators — a 7.7× cut, measured.**
For an integral Weierstrass model a rational point has `x = a/e²`, so the
denominator of `x` is a perfect square. Squares ≤ 47 are `1, 4, 9, 16, 25, 36`,
giving **363** candidates instead of 2783 (13.0%). The two real survivors `1`
and `2` have denominator 1, so **the reduction loses nothing** — verified.
At the observed scaling, six blocks of 95 come to ~1.1 GB each: comfortable.
Cost: the `x = a/e²` lemma needs a p-adic valuation argument (if `p | den(x)`
then `v_p(x) = −m` forces `v_p(y) = −3m/2`, so `m` is even). That is real Lean
work but standard, and it is reusable for every curve in the cohort.

**(2) Reformulate the decidable check over `ℤ × ℕ` pairs.** Avoid `ℚ` entirely
in the predicate: carry `(a, b)` with explicit integer polynomials for the
numerator and denominator of `f(a/b)/g(a/b)`, and compare heights via integer
`gcd`. Keeps everything where the kernel has GMP acceleration and drops `Rat`'s
structure and invariant overhead. Larger rewrite, but it also lifts the ceiling
for every future curve.

## What is unaffected

r156–r165 are all verified and pushed; `lake build PF` = 4669 jobs, zero
`sorryAx`. 5077a1 has the canonical height, the two-sided quasi-parallelogram
bounds, the exact parallelogram law and the multiple law. Only the removal of the
side conditions is outstanding.
