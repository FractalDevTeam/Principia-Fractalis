# Midpoint wiring — progress snapshot 2026-10-17

**Scope:** Rio's directive to wire `composite_midpoint_error` into the
Fourier panel generator (74×–179× panel reduction, free). c=27/4 failed
honestly first (gate-1 margin −0.011 at zero residue — not a residue
problem; `c²·R_ub + c·I_ub` on raw aggregates already exceeds 3/4). Box
march stopped as planned.

## Done (kernel-clean)

File: `PF/Analytic/FourierPanels/FourierTermC2_2026_10_16.lean` (~290 L).

**Three-axiom bar verified** `[propext, Classical.choice, Quot.sound]` on:

* `hasDerivAt_fourier_plus_term`: `fourier_plus_term c n` has derivative
  `fourier_plus_termD1 c n u` at every `u`, where
  `fourier_plus_term c n u = (exp(u/2) + 1) · (2 · exp(-π(n+1)² · exp u))
                             · cos((c/2) · u)`.
* `hasDerivAt_fourier_plus_termD1`: the first-derivative function has
  derivative `fourier_plus_termD2 c n u` at every `u`. Second derivative
  given by the six-term Leibniz expansion.

**Key new lemma** (vs the `thetaTerm` template): `hasDerivAt_Q'` — the
exp-factor's first derivative `Q'(u) = -2A·exp u · exp(-A·exp u)`, with
derivative `Q''(u) = 2·exp(-A·exp u)·exp u·(A²·exp u − A)` obtained by the
product rule of the two chain-ruled factors. This is where "`exp u` inside
the exponent" shows up — Rio flagged it as "the sole difference". Proven
kernel-clean via `h_neg_A_exp.mul h_outer_exp` on the `hasDerivAt_mul3`
scaffold, exactly matching the `thetaTerm`-template factor organization.

## Not done (next in this file)

* `abs_fourier_plus_termD2_le` — the pointwise `C²` bound. Six-term
  triangle inequality using `abs_triple_le` (same lemma as `thetaTerm`),
  with factor bounds (12 of them):
    `|P| ≤ E+1`, `|P'| ≤ E/2`, `|P''| ≤ E/4` where `E = exp(T/2)`;
    `|Q| ≤ 2B`, `|Q'| ≤ 2A·B`, `|Q''| ≤ 2A·(A·exp T − 1)·B`
      (using `exp u · exp(-A·exp u) ≤ B` on `[0, T]` — monotone-decreasing
       for `A ≥ 1`, max at `u = 0`), where `B = exp(-A)`;
    `|R| ≤ 1`, `|R'| ≤ |c|/2`, `|R''| ≤ (c/2)²`.
  Target: `|fourier_plus_termD2 c n u| ≤ fourier_plus_termM c n T` for
  `u ∈ [0, T]`. Estimated ~80 L; same shape as `abs_thetaTermD2_le`
  (XiQuadrature.lean:650–718).

* `abs_fourier_plus_termD2_sum_le` — sum over `n ∈ Finset.range 3`
  (the `N3` cutoff). Trivial once the single-term bound is done.
  ~5 L (`Finset.abs_sum_le_sum_abs` + `Finset.sum_le_sum`).

* Analogous `_minus_` variants (sin in place of cos, `exp(u/2) − 1`
  growth factor). The minus-side proof differs in one factor bound
  (`|exp(u/2) − 1| ≤ E − 1` on `u ≥ 0`); rest identical. ~150 L copy.

## Not done (separate file — generator wiring)

* `scripts/gen_fourier_panels_c*.py` modification: emit midpoint-rule
  panels with the `composite_midpoint_error` instantiation per Seg
  rather than the current `decide +kernel` range bricks. Each panel
  becomes a one-line `midpoint_rule_error` application; width `h` tied
  to the target per-panel error `≤ M·h³/24`.

* Measurement step: lines-per-panel on Seg01 of some c-value with the
  new generator, vs the current ~1000-L range-brick emission. Rio's
  claim: 74×–179× fewer panels needed.

## Resources used

* Started 20:04 (after c=27/4 Seg02 build was interrupted); completed
  derivative chain by ~21:50. ~1h45m elapsed.
* Build cost: `lake build FourierTermC2_2026_10_16` ≈ 1.4 s (cold replay).
* No c=27/4 pilot built (gate failed on raw aggregates; no residue
  tightening available).

## Honest-failure confirmation at c=27/4

Grand totals extracted from in-tree `Seg0*_c27_4_2026_10_16.lean`
(Seg01 completed kernel-clean, Seg02 interrupted by `pkill`; the Seg
files are text and their panel theorem signatures were extracted via
Python before the loop was terminated):

```
R_lb = 411750991/32000000000 ≈ 0.012867
R_ub = 5217012603/320000000000 ≈ 0.016303
I_lb = 709097/64000000000 ≈ 0.0000111
I_ub = 607043541/320000000000 ≈ 0.001897

c² · R_ub + c · I_ub = (729/16)·0.016303 + (27/4)·0.001897
                     ≈ 0.7428 + 0.01280 ≈ 0.7556 > 3/4 = 0.75  (fail by 0.0056)
```

Margin at residue = 0 (impossible): −0.01090.  No residue lever closes
this; needed Gate-2 strategy call per Rio's directive. Box march stopped
at c=53/8 as the last landed pilot.
