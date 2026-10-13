# RETRACTED: the uniform-modulus Lipschitz route for RH right-edge boxes — 2026-10-10

Pablo's correction (he retracted his own earlier advice). DO NOT build the
segment-wide Lipschitz constant via the uniform-modulus theta bound.

## Why the Lipschitz/uniform-modulus route is WRONG on sigma = 1

`|x^{s/2}| = x^{1/2}` is uniform in t — true but useless, because taking the
modulus DISCARDS the phase of `x^{it/2}`, and on the right edge the phase IS the
whole story:
- The theta integral gives `I(1+it) ≈ 1/s + 1/(1-s) ≈ 0.005` at t ≈ 14.
- True `Λ(1+it)` = that integral minus the pole terms ≈ 1e-5 (Λ decays like
  e^{-πt/4}).
- So `ξ(1+it) = s(s-1)Λ(s)/2` is ~500x smaller than the pieces it is built from,
  and the SAME cancellation sits inside `f' = (g'I + gI')/2`.
- A uniform-modulus bound keeps the pieces, loses the cancellation. At t=14.5 it
  gives L ≈ 0.5 against a true |f'| ≈ 0.03 — a factor 15-20 off. That is ~260
  boxes on R3 (worse than naive 136) and ~100-150 on R1 (worse than theta's 53).

My earlier "derivative bound is close to free" plan was wrong by 15-20x. The Arb
centered-form result (R3 = 13 boxes) already proved the phase-keeping composite is
what works; the modulus shortcut does not.

## What DOES work (the Lean route), and its cost

Mirror Arb's centered form in Lean, keeping the phase:
1. Enclose `I(s)` and `I'(s)` over the t-box as NARROW intervals that keep the
   phase, through the existing theta-quadrature panels. `I'` is the SAME integral
   with the weight `(i log x)/2` — the same machinery with one extra factor per node.
2. Form `f'(box) = (g'·I + g·I')/2` as interval arithmetic ON THE SUM — never as
   `|g'||I| + |g||I'|`. Exact rationals make the cancellation harmless; only the
   interval widths matter.
3. Then `f(box) ⊆ f(c) + f'(box)·[-r, r]` (mean-value form).

Back-of-envelope with widths ~ 2r·|I'|: R3 ≈ 15-20 boxes in Lean (vs Arb's 13).
Day-scale survives; the shortcut does not.

## Consequence for the generator transpose

`scripts/emit_box_segment.py` must emit, per box: the existing `I` panels AND a
parallel set of `I'` panels (integrand × `(i log u)/2`), then assemble
`f'(box) = (g'I + gI')/2` and the centered enclosure `f(c) + f'(box)[-r,r]`, all in
the vendored interval arithmetic with exact rational nodes. Not a modulus bound.

## VERIFIED under my own hand (mpmath dps=40), with one refinement

- **Cancellation confirmed, larger than stated:** at t=14.5 the two ~1 pieces of
  `Re ξ = (1 - t²·ReΛ₀ - t·ImΛ₀)/2` are `1` and `t²·ReΛ₀ = 0.99644`; they cancel to
  ~3.6e-3, and `Re ξ = -5.591e-4` is **~1789× smaller** than `1`. The phase is the
  whole story — a modulus bound loses it. GPT's conclusion stands.
  (Naming note: GPT's "true Λ ≈ 1e-5" is the theta part `π^{-s/2}Γ(s/2)ζ(s)` =
  5.6e-6 − 3.6e-6i; the full `Λ₀` ≈ 4.7e-3, pole-dominated. The cancellation that
  matters is the `1` vs `t²·ReΛ₀` cancellation in `Re ξ`, not inside `Λ₀`.)

- **Refinement — the box count is enclosure-width-limited, not derivative-limited.**
  The TRUE pointwise `|d/dt Re ξ|` on [14.5,15] is **~7e-4** (profile: 7.0e-4 at
  t=14.5 down to 3.0e-4 at t=15), not 0.03. With R3 margin ~5.6e-4 the true
  derivative alone would allow a box radius ~0.75 → ~1 box. The 0.03 effective bound
  (hence Arb's 13 / GPT's 15-20 boxes) is the INTERVAL WIDTH of `f'(box)`, ~40×
  looser than the true derivative. Three levels, measured:
    1. true derivative ~7e-4  -> ~1 box (ideal, needs exact f')
    2. phase-keeping interval ~0.03 -> 13 (Arb) / 15-20 (Lean est.) boxes
    3. uniform-modulus ~0.5 -> ~260 boxes (RETRACTED route)
  Consequence: the Lean route's box count falls as the `I`/`I'` panel enclosures
  tighten. There is headroom below 13-20 if the theta-panel widths are narrowed;
  "day-scale" is the conservative figure, not the floor.
