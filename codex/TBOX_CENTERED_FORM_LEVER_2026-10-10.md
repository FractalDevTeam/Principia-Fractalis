# The centered-form lever kills the interval-dependency loss — 2026-10-10

Author: Pablo Cohen. Feasibility measurement (mpmath dps=40, not a certificate).

## Claim tested

`TBOX_CAMPAIGN_COST_2026-10-01.md` found the 232-box / 75.9-day certified
RH-below-15 campaign is set by a **402x interval-dependency loss**, not by the
mathematics, and named the lever: evaluate the `t`-dependence with a centered /
mean-value form instead of naive interval arithmetic. This tests that lever.

## Method

`Re xi(1+it) = (1 - t^2 A(t) - t B(t))/2`, `A=Re Lambda0(1+it)`, `B=Im Lambda0`.
For a tight `t`-box `[c-r, c+r]` (r=0.005) at each segment's margin-limited point,
compare three widths of `Re xi` (and `Im xi` for R2):
- TRUE: max-min over a dense sample (the real variation).
- NAIVE: interval-evaluate the formula with each t-subterm (T, T^2, A, B) as an
  independent interval — the dependency problem the current Lean generator incurs.
- CENTERED: `f(c) + f'([box])*[-r,r]`, the first-order mean-value form.

## Result

| segment (margin point) | TRUE | NAIVE | CENTERED | naive/true | centered/true |
|---|---|---|---|---|---|
| R1 (t=13)   | 3.84e-5 | 1.49e-3 | 3.86e-5 | **38.7x** | 1.00x |
| R2 (t=14.5) | 6.07e-6 | 1.81e-4 | 6.09e-6 | **29.8x** | 1.00x |
| R3 (t=14.5) | 7.44e-6 | 1.37e-3 | 7.50e-6 | **184x**  | 1.01x |

**The centered form recovers the true sensitivity to within 1%.** The naive loss
is 30-184x on these boxes (same order as TBOX_COST's independent 402x at a nearby
point). R3 — which drives 136 of the 232 boxes — sees the largest loss, so it
benefits most.

## Consequence (estimate, not a re-cost)

Box count at a margin-limited point scales as sensitivity, so centered-form boxes
are 30-184x wider there => 30-184x fewer boxes at the points that SET the count.
A conservative whole-campaign estimate: 232 boxes -> order-10 boxes, 76 serial
days -> day-scale. This is the feasibility flip that makes certified R1/R2/R3
(hence the fully-wired finite-rectangle RH, `rh_below_15_conditional`) achievable
without a months-long campaign.

## What this is / is NOT

- NOT a certificate: uses mpmath sampled min/max, not outward-rounded intervals.
  The real certified campaign needs (a) a centered-form generator emitting
  `f(c) + f'(box)*[-r,r]` per box, and (b) a rigorous interval bound on the
  derivative `f'` over each box — the genuinely new ingredient (f' is smoother and
  bounded, so a coarse interval bound suffices; it can itself use a centered form).
- NOT progress on the open Riemann Hypothesis. `riemannHypothesis_below_15` is RH
  on one finite rectangle, classically known since Riemann/Gram. This lever makes
  FORMALIZING that known instance feasible; it does not touch the open problem.

## Next concrete step

Prototype the rigorous derivative bound `|d/dt Re xi(1+it)|` over a t-box (interval
or Arb/python-flint ball arithmetic), then re-cost the campaign with the centered
generator. If the order-10-box estimate holds, implement the generator transpose
(scripts/emit_box_segment.py already does the box geometry; the change is the
per-box integrand evaluation) and run R1 as the pilot (loosest margin).

Script: scratchpad/tbox_centered_form_lever.py (feasibility model, not certs).
