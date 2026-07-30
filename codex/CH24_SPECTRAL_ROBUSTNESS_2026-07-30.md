# ch24 spectral operator: robustness sweep and the conductor confound (2026-07-30)

Follow-up to `codex/CH24_SPECTRAL_TEST_2026-07-28.md`, which found that the
phi/e **multiplicity** formula (Conjecture rank-equality-fractal) showed no rank
signal, but that the **dominant |eigenvalue|** of the discretized operator was
monotone in rank at about +2 per rank. This document tests that surviving claim.

Script: `codex/ch24_spectral_robustness.py` (rerunnable, ~3 min).
Curve coefficients are taken verbatim from the Lean definitions in
`PF/E*RankOne_r1*.lean`, not from memory. Bad primes are detected from the
discriminant, so no conductor value is trusted as input.

## The flaw in the original test

It used 11a1 (r=0), 37a1 (r=1), 389a1 (r=2), 5077a1 (r=3) — conductors
11, 37, 389, 5077. **Rank and conductor increase together**, so a rank signal
and a conductor signal are indistinguishable in that sample. I should have
caught this when I recorded the finding.

## Finding 1 — grid-convergent, NOT cutoff-convergent

`lambda_max` converges in the grid to 4 significant figures (120 -> 240 -> 480
changes the 4th digit only). It does **not** converge in the prime cutoff:

| PMAX | 11a1 | 37a1 | 389a1 | 5077a1 | naive slope |
|---|---|---|---|---|---|
| 500   | 0.0037 | 1.3833 | 2.3269 | 3.4659 | 1.133 |
| 1500  | 0.0680 | 1.5184 | 2.4895 | 3.5815 | 1.151 |
| 5000  | 0.0900 | 1.5482 | 2.6382 | 3.7437 | 1.205 |
| 15000 | 0.0858 | 1.5883 | 2.6760 | 4.0099 | 1.286 |

The values and the slope drift monotonically upward with PMAX. So `lambda_max`
is **not a convergent functional of E** as PMAX -> infinity; it appears to grow
slowly without bound. Any theorem about it needs a normalization first.

This is consistent with the Mestre–Nagao heuristic, where
`sum_{p<X} a_p/p ~ -rank * log log X`: rank enters with a coefficient AND the
sum diverges in the cutoff. That would explain the rank signal and the drift
simultaneously, and it tells you what the normalization should look like.

## Finding 2 — the magnitudes do NOT reproduce the 2026-07-28 numbers

That doc recorded `0.3188, 2.5747, 4.4835, 6.4893`. Under the discretization
documented in the script here (collocation at x_j=(j+0.5)/grid, linear
interpolation, a_p by quadratic-residue lookup) the same four curves give
`0.0680, 1.5184, 2.4895, 3.5815` at the same nominal settings (grid 240,
PMAX 1500). Monotonicity persists; the scale does not. **The specific numeric
values in the earlier doc should not be cited.**

## Finding 3 — THE CONFOUND TEST, and it does not go the way I expected

Nine curves of classical rank 1 whose `rank >= 1` is kernel-verified in this
corpus (r131–r142), conductors 37..106 — a ~3x spread at FIXED rank
(grid 480, PMAX 5000):

```
 37a1 1.5482   43a1 1.4219   53a1 1.4825   61a1 1.3049   79a1 1.1188
 83a1 1.1170   89a1 1.0585  101a1 1.1548  106a1 1.2588
mean 1.274, sd 0.177, spread/mean 0.38
corr(lambda_max, conductor) at fixed rank = -0.81
```

So at fixed rank, `lambda_max` **decreases** with conductor. The conductor
effect is real (|corr| ~ 0.8) but it runs **opposite** to the apparent rank
effect. It therefore cannot manufacture the Sweep-A trend — it partially
cancels it.

## Finding 4 — controlling for conductor RECOVERS the factor of 2

All twelve curves, `lambda_max ~ a*rank + b*log N + c` (grid 480, PMAX 5000):

| model | rank coeff | log N coeff | R^2 |
|---|---|---|---|
| rank only        | +1.243 | —      | 0.970 |
| log N only       | —      | +0.561 | 0.857 |
| **rank + log N** | **+1.985** | **-0.366** | **0.990** |

Independent check on the log-N coefficient, using only the nine rank-1 curves
(rank held fixed): **-0.400**, R^2 = 0.73 — agreeing with the -0.366 from the
joint fit. Two independent estimates of the conductor term coincide.

Residual sd of the two-variable fit: 0.0998, against a per-rank step of 1.985.

**Interpretation.** The original "+2 per rank" was right after all, but for a
reason the original test could not see: the naive slope is 1.24 because the
negative conductor term partially cancels a rank term of ~2. Controlling for
conductor recovers +1.985 ~ 2.

## What this does and does not establish

Established (numerically, not proved):
- `lambda_max` carries a rank signal of ~2 per rank once conductor is
  controlled, grid-stable, with residual scatter ~0.1.
- The phi/e multiplicity formulation still shows nothing (2026-07-28, Finding 1).

NOT established, and these are load-bearing limitations:
1. **n = 1 at ranks 0, 2 and 3.** Nine curves at rank 1, one each at 0, 2, 3.
   The rank coefficient is driven by three single points. This is the dominant
   weakness and the first thing to fix.
2. **No cutoff limit.** Finding 1: the statistic diverges slowly in PMAX. There
   is no limit object yet, so there is nothing to state a theorem about.
3. It is a numerical observation about a *discretized* operator, and says
   nothing about BSD.

## How to proceed

1. Break the n=1 problem: more curves at ranks 0, 2, 3. Rank 0 is easy and
   rigorous — 37 is the minimal conductor for rank 1 (Cremona), so every curve
   of conductor < 37 has rank 0. Ranks 2 and 3 need LMFDB values, which should
   be labelled classical rather than kernel-verified.
2. Find the normalization that makes the statistic cutoff-stable, guided by
   Mestre–Nagao (`sum a_p/p ~ -rank log log X`). Candidates: divide by
   `log log PMAX`, or use a smoothed/weighted cutoff.
3. Only then is there a candidate bridge to Research Problem 2 of ch24 — and it
   should be sought against this statistic, NOT the phi/e multiplicity.
