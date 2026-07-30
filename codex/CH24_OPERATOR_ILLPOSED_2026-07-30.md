# ch24's spectral operator is ill-posed as written, and the repair costs the signal

Resolves step 1 ("fix the normalization") of `CH24_SPECTRAL_RIGOROUS_2026-07-30.md`.
Script: `codex/ch24_spectral_robustness.py` plus the two analyses recorded here.

## 1. The operator as written has no PMAX limit -- shown directly

ch24's operator (Definition, spectral-operator-bsd) is

    (T_E f)(x) = sum_{p} (a_p / p) * exp(i*pi*alpha*D(p)*x) * f(x/p).

Its matrix entries are dominated by `S_s(x) = sum_{p<X} (a_p/p^s) exp(i pi alpha D(p) x)`
at **s = 1**. Direct partial sums for 5077a1 out to X = 200000:

| tail window | s = 1 | s = 1.5 |
|---|---|---|
| [5000, 15000)    | 0.3167 | 0.0041 |
| [15000, 50000)   | 0.0789 | 0.0008 |
| [50000, 200000)  | **0.1556** | 0.0006 |

At s = 1 the tails do not shrink -- the third is larger than the second -- and
the absolute mass per window grows (9.60, 16.74, 32.84). The partial sums
wander (|S| = 0.958, 0.850, 0.822, 1.117, 1.067, 1.185 at x = 0.25). At s = 1.5
they converge to four figures.

This is forced by the Hasse bound: `|a_p| <= 2 sqrt(p)`, so `|a_p/p^s| <= 2 p^{1/2-s}`
and absolute convergence needs **s > 3/2**.

**ch24 is internally inconsistent.** Its analytic scaffold rests on the named
hypothesis `LSeriesAbsConvergenceForReSGreaterThanThreeHalves` -- i.e. it
*already* identifies Re(s) > 3/2 as the convergent range -- while its spectral
operator is defined at s = 1, outside that range. The operator is not a
well-defined bounded object in the limit, so no eigenvalue of it is either.
That, not sampling, is why every per-rank coefficient drifted with the cutoff.

## 2. The principled repair works: at s > 3/2 the operator IS well posed

Taking s = 1.75 (inside the chapter's own convergent range), grid 480:

| PMAX | 11a1 (r0) | 37a1 (r1) | 389a1 (r2) | 5077a1 (r3) | slope | R^2 |
|---|---|---|---|---|---|---|
| 1500  | 0.0764 | 0.4390 | 0.4916 | 0.6769 | 0.1854 | 0.907 |
| 5000  | 0.0764 | 0.4391 | 0.4920 | 0.6774 | 0.1856 | 0.907 |
| 15000 | 0.0764 | 0.4392 | 0.4921 | 0.6777 | 0.1857 | 0.907 |
| 50000 | 0.0764 | 0.4392 | 0.4921 | 0.6778 | 0.1857 | 0.907 |

`lambda_max` is stable to four significant figures across a 33x range of cutoff,
and the per-rank slope is flat to three figures. **This is the first
cutoff-independent version of the statistic.** The conductor law survives too
and is equally stable: `b = -0.1731`, se 0.0392, `b/se = -4.42`, corr `-0.858`,
identical at PMAX 5000 and 50000.

## 3. But the repair costs almost all of the discriminating power

| | s = 1 (ill-posed) | s = 1.75 (well posed) |
|---|---|---|
| per-rank slope | 1.98 | **0.186** |
| within-rank-1 sd | 0.099 | 0.076 |
| slope / sd | ~20 | **~2.4** |
| gap rank1 -> rank2 | ~1.1 | **0.053** |
| R^2 (rank only) | 0.997 | 0.907 |

The rank ordering persists (0.076 < 0.439 < 0.492 < 0.678) and rank 0 and rank 3
remain clearly separated. **But the rank1 -> rank2 gap, 0.053, is smaller than
the within-rank-1 scatter, 0.076.** On this evidence the well-posed operator
does not resolve rank 1 from rank 2.

So the strong signal at s = 1 was substantially an artifact of the divergence:
the divergent part amplified the between-rank spread. Removing it leaves a real
but weak effect.

Caveat that cuts both ways: n = 1 at ranks 0, 2, 3, so "does not resolve rank 2"
compares a single curve against a nine-curve cluster. That is the right
comparison to make, and it is also the reason the conclusion is provisional.

## 4. What this means for ch24

- Conjecture (rank-equality-fractal), the phi/e **multiplicity** formula: still
  no signal, at either s (2026-07-28, Finding 1).
- The **dominant-eigenvalue** mechanism: becomes mathematically well posed only
  at s > 3/2, and there it does not separate adjacent ranks on present evidence.
- The operator's definition should be changed to s > 3/2 regardless of the rank
  question, because at s = 1 it does not define an operator in the limit. That
  is a correctness fix, independent of whether the rank mechanism survives.

## 5. How to proceed

1. **Change the operator definition** in ch24 to `a_p/p^s`, `s > 3/2`,
   consistent with the chapter's own convergence hypothesis. This is not
   optional -- it is what makes the object exist.
2. Then ask whether ANY functional of the well-posed operator separates ranks:
   the dominant eigenvalue does so only weakly. Candidates worth testing are the
   full spectral distribution, or the trace powers `tr(T^n)` which the chapter's
   Research Problem 1 already connects to `log L_f`.
3. Break n = 1 at ranks 0, 2, 3 before treating item 2's answer as settled.
4. Widening the conductor range at fixed rank with our own r131-template remains
   worthwhile: at s = 1.75 the conductor law is fit over N = 37..106 and still
   extrapolated to 5077.
