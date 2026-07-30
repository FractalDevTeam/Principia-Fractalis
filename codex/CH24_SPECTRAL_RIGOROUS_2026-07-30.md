# ch24 spectral operator: the rigorous statement (2026-07-30)

Supersedes the numeric claims of `CH24_SPECTRAL_TEST_2026-07-28.md` and
sharpens `CH24_SPECTRAL_ROBUSTNESS_2026-07-30.md`.
Script: `codex/ch24_spectral_robustness.py`.

## Provenance of the inputs (stated first, because the conclusion depends on it)

- `rank >= 1` is **kernel-verified** in this corpus for nine curves
  (37a1, 43a1, 53a1, 61a1, 79a1, 83a1, 89a1, 101a1, 106a1) and `rank >= 2`
  for 389a1.
- That the ranks are **exactly** 1, 2, 3 is **classical (Cremona), NOT
  kernel-verified**. The regressions below use cited rank values as the
  independent variable. This is the single largest external dependency.
- Curve coefficients are read from the Lean definitions; bad primes are
  detected from the discriminant. Those two inputs are not trusted to memory.
- n = 9 at rank 1, but **n = 1 at ranks 0, 2 and 3**.

## What is solid

**S1. The conductor coefficient is real and cutoff-stable.**
Regressing `lambda_max` on `log N` within the nine rank-1 curves (rank held
fixed) gives `b = -0.3996`, `se = 0.093`, `b/se = -4.3`. Across cutoffs
PMAX = 1500 / 5000 / 15000 it reads `-0.3956 / -0.3996 / -0.3968` — converged
to three figures. At fixed rank, `lambda_max` decreases with conductor.

**S2. There is a genuine rank dependence, and it survives a demanding
consistency check.** Using the rank-1 curves to define the baseline
`f(N) = 2.961 - 0.400 log N`, the three single-curve ranks each give an
independent estimate of the per-rank step:

| curve | rank | log N | extrapolation | estimate of a |
|---|---|---|---|---|
| 11a1   | 0 | 2.40 | 1.21 **below** the fitted range | 1.913 +/- 0.172 |
| 389a1  | 2 | 5.96 | 1.30 **above** | 2.060 +/- 0.165 |
| 5077a1 | 3 | 8.53 | 3.87 **above** | 2.096 +/- 0.200 |

These extrapolate the conductor law **in opposite directions and by very
different distances**, and agree to within 0.1 (sd of the three = 0.097). A
misspecified conductor law would break the 3.87-unit extrapolation far worse
than the 1.21-unit one. It does not. That is non-trivial evidence that
`lambda_max` responds to rank and not merely to conductor.

## What is NOT established, and this is the headline

**F1. The number "2 per rank" is NOT a well-defined constant.** It is the
value at PMAX = 5000. The conductor-controlled step drifts monotonically with
the prime cutoff:

| PMAX | 500 | 1500 | 5000 | 15000 |
|---|---|---|---|---|
| a | 1.786 | 1.950 | 2.023 | 2.071 |

and successive steps exceed the quoted standard errors, so those errors
(extrapolation only) understate the true uncertainty. My hypothesis that
controlling for conductor would remove the drift was **wrong**: the naive slope
drifted by 0.153 over this range, `a` drifts by 0.285 — the drift got larger,
not smaller.

**F2. Model-free evidence that `a` grows without bound.** The *growth of*
`lambda_max` in the cutoff is itself proportional to rank:

```
growth(500 -> 15000):  11a1 0.082   37a1 0.205   389a1 0.349   5077a1 0.544
fit: growth = 0.153*rank + 0.066,   R^2 = 0.989
```

If the per-rank gap widens as the cutoff grows, the per-rank step cannot have a
finite limit under this normalization. This is exactly the Mestre-Nagao
signature: `sum_{p<X} a_p/p ~ -rank * loglog X`, where rank enters with a
coefficient that itself grows in X.

**F3. Four cutoffs cannot decide convergence.** Divergent fit
`a = 0.643 loglog(PMAX) + 0.635` gives R^2 = 0.950; convergent fit
`a = 2.604 - 4.979/log(PMAX)` gives R^2 = 0.973. Both fit. The data does not
separate them. F2 is the reason to favour divergence, and F2 is model-free.

## The rigorous statement of what survives

> For this discretization, `lambda_max` is a rank-sensitive statistic with a
> cutoff-stable conductor correction of `-0.40 log N`, and its rank sensitivity
> **grows with the prime cutoff at a rate proportional to rank**. No
> cutoff-independent per-rank coefficient exists under this normalization.

The phi/e **multiplicity** formulation — which is what ch24 actually states as
Conjecture (rank-equality-fractal) — still shows no signal at all.

## Consequence for the book

The figure "approximately 2 per rank" must not be cited as a constant, and I
put exactly that figure into ch24 earlier today. It has been corrected in the
same commit as this document. The defensible claim is rank *sensitivity* plus
the conductor law, with the normalization left open.

## How to proceed, in order

1. **Fix the normalization first.** There is no object to state a theorem about
   until `lambda_max` is divided by something that makes it cutoff-stable. The
   Mestre-Nagao form suggests `loglog PMAX`, but `a/loglog PMAX` is *not* flat
   either (0.978, 0.980, 0.944, 0.915), so the right normalization is an open
   question, not a guess to be plugged in.
2. **Then break n = 1.** Rank 0 is rigorous: 37 is the minimal conductor for
   rank 1 (Cremona), so every curve of conductor < 37 has rank 0. Ranks 2 and 3
   need LMFDB values, to be labelled classical.
3. **Widen the conductor range at fixed rank using our own machinery.** The
   conductor law is currently fit over N = 37..106 and extrapolated to 5077.
   The r131-template proves `rank >= 1` for any curve with a non-torsion point
   via a dyadic chain; adding kernel-verified `rank >= 1` curves at N in the
   hundreds-to-thousands would turn that extrapolation into interpolation.
4. Only after 1-3 is there a candidate bridge to ch24's Research Problem 2.
