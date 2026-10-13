# RH right-edge sign facts R1/R2/R3 — independent numerical verification (Colab + local)

Date: 2026-10-09. Author: Pablo Cohen + Claude Opus 4.8.

## What was verified

The finite-region Riemann-Hypothesis formalization (`riemannHypothesis_below_15`)
reduces to three sign facts on the right edge `sigma = Re s = 1`, for the EXACT
Lean object

    riemannXiEntire(s) = (s*(s-1)*completedRiemannZeta0(s) + 1) / 2        (RiemannXiEntire_r325.lean:81)
    completedRiemannZeta0(s) = pi^(-s/2) Gamma(s/2) zeta(s) + 1/s + 1/(1-s)  (mathlib convention)

- **R1**: `Re xi(1+it) > 0` on `t in [0, 13]`
- **R2**: `Im xi(1+it) > 0` on `t in [13, 29/2]`
- **R3**: `Re xi(1+it) < 0` on `t in [29/2, 15]`

These match `re_xi_edge` / `im_xi_edge` in `RightEdgeSignsProof_2026_10_09.lean`:
`Re xi(1+it) = (1 - t^2*Re L0 - t*Im L0)/2`, `Im xi(1+it) = (-t^2*Im L0 + t*Re L0)/2`.

## Method

High-precision mpmath (`mp.dps = 30`), dense uniform grid, computing the genuine
Lean object. The point `t=0` (`s=1`) is the removable point where `s(s-1)=0`
annihilates zeta's pole, giving `xi(1)=1/2` exactly (= Lean `R1_at_zero`).

**Convention witness** (independent): the functional equation `xi(s)=xi(1-s)` holds
numerically to machine precision on `sigma=1` — `|xi(1+it)-xi(-it)|` = 5.08e-32
(t=3.7), 0 (t=13), 0 (t=14.5). This proves we are computing the genuine entire
completed xi, not a lookalike.

## Result (both environments, identical to all printed digits)

| fact | extremum | at t | violations | samples |
|---|---|---|---|---|
| R1  Re>0 on [0,13]    | min Re = **+2.509405e-03** | 13.0000 | 0 | 6501 |
| R2  Im>0 on [13,14.5] | min Im = **+4.141834e-04** | 14.5000 | 0 | 3001 |
| R3  Re<0 on [14.5,15] | max Re = **-5.591037e-04** | 14.5000 | 0 | 1001 |

Zero sign violations across 10,503 samples. The minimum margins all occur at the
segment boundaries (t=13 for R1, t=14.5 for R2 and R3) — i.e. exactly where the
sign transitions are; this tells the certified proof where it will be delicate.

Cross-check:
- Local: Windows, mpmath 1.4.1 — ran in 4.0 s.
- Colab Pro, Python 3 hosted runtime — ran in 17.97 s.
- Outputs byte-for-byte identical on every printed digit.

Colab notebook (Pablo's Drive, psolorzano@gmail.com):
`PF_RH_rightedge_signfacts_R1R2R3_verify.ipynb`
https://colab.research.google.com/drive/1hW0_m6FQBbHJ4jhMAlgF3z_IiQuGHu9l

## Honest scope — what this is and is NOT

- This is **numerical triage**: it confirms the facts the Lean proof ASSUMES are
  true everywhere sampled, and would have caught a sign violation if one existed.
- It is **NOT a proof** of R1/R2/R3, and **NOT** a proof of the Riemann Hypothesis,
  and **NOT** a Clay solution. A dense grid is not an interval cover.
- The real gate is unchanged: a **certified t-boxed interval-quadrature producer**
  for `L0` (~180-230 boxes, a months-scale compute campaign) that bounds the sign
  over whole intervals, not sample points. The tiny boundary margins above
  (2.5e-3, 4.1e-4, 5.6e-4) say that producer must be tight near t=13 and t=14.5.
- Unconditional progress already landed in Lean: `R1_on_neighborhood`
  (`R1Neighborhood_2026_10_09.lean`) proves `Re xi(1+it) > 0` on `[0, delta]` for
  some `delta>0`, kernel-clean `[propext, Classical.choice, Quot.sound]`, non-vacuous.
  R1 remains open on `[delta, 13]`.

Script of record: `rh_edge_verify.py` (this directory), validated locally before the
Colab run.
