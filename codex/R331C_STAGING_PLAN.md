# r331c staging plan — right edge sectors

Written 2026-09-06 during the C1 rebuild. **Scaffolding only: nothing here has been
elaborated.** No build slot was taken; both machines are on C1.

## Where r331c sits

From `codex/R331B_PROGRESS_2026-08-26.md:1265-1275`, the roadmap is:

    T15 boundary zero-free            (r331b + r329b + r328)   <- LANDED
      -> unconditional argument principle (r327)                <- LANDED
      -> r331c: right sectors -> principal-log contour = 1
      -> r331d: multiplicity Nat = 1
      -> literal riemannHypothesis_below_15

r331b evaluated the *right-hand side* of the count identity's premises. r331c starts
on the *left-hand side*: pinning the contour integral itself to the value 1, by
controlling the argument of xi along the boundary so the principal branch of the
logarithm does not wrap.

## What r331c must prove

`RiemannXiThetaBoxEnclosure_r331a.lean:32-34` names the two targets literally:

    r331c (RIGHT LOW:  closes  Re xi(1+it) > 1/1000)
          (RIGHT HIGH: closes  Im xi(1+it) > 1/20000)

on the right vertical `sigma = 1`, `t` ranging over `[0, 15]`.

The consumers already exist, unused, in r331a section 5:

- `re_xi_lower_bound_from_enclosures`  -> RIGHT LOW
- `im_xi_lower_bound_from_enclosures`  -> RIGHT HIGH

r331b used only the third (`re_xi_upper_bound_from_enclosures`). The other two were
built for r331c and have never been instantiated.

## The blocking architectural mismatch — read this first

**Every r331a structure and consumer ranges over sigma at a FIXED t.**

    structure BoxReEnclosure (sigma_lo sigma_hi t A B : Prop)
      bounds : forall sigma, sigma_lo <= sigma -> sigma <= sigma_hi -> A <= (Lambda0 (sigma+ti)).re <= B

    re_xi_lower_bound_from_enclosures ... : forall sigma, sigma_lo <= sigma -> sigma <= sigma_hi -> m <= (xi (sigma+ti)).re

r331c needs the transpose: **t ranging over a box at FIXED sigma = 1**. The existing
structures cannot express that. Instantiating `sigma_lo = sigma_hi = 1` fixes t per
instance, which would require one instance per point of `[0,15]`.

So r331c cannot reuse r331a's structures directly. It needs a t-ranged analogue.
This is the single most important thing to know before starting, and it is not
written down anywhere else in the corpus.

**What IS reusable, unchanged:**

- `re_xi_at_s (sigma t)` and `im_xi_at_s (sigma t)` (r331a section 2) — both already
  general in both arguments. These are the closed forms r331c needs.
- The whole quadrature/envelope machinery, if it can be re-parameterised in t.

At `sigma = 1` the polynomial factors collapse usefully:

    p1 = sigma(sigma-1) - t^2  ->  -t^2
    q1 = t(2 sigma - 1)        ->   t

so, directly from `re_xi_at_s` / `im_xi_at_s`:

    Re xi(1+it) = (1 - t^2 * Lambda0.re - t * Lambda0.im) / 2
    Im xi(1+it) = (-t^2 * Lambda0.im + t * Lambda0.re) / 2

Both targets therefore reduce to enclosures of `Lambda0(1+it).re` and
`Lambda0(1+it).im` over t-boxes — exactly the r331b pattern with sigma and t swapped.

## Staging

**Stage C0 — transpose the r331a interface (light, no numerics).**
New module `RiemannXiEdgeEnclosure_r331c.lean`:
- `structure EdgeReEnclosure (t_lo t_hi sigma A B)` and `EdgeImEnclosure`
- `re_xi_lower_bound_from_edge` / `im_xi_lower_bound_from_edge`, proved from
  `re_xi_at_s` / `im_xi_at_s` by the same monotone-step pattern the box bridges use
- the `sigma = 1` specialisations of the polynomial factors above

Cost: comparable to r331a (282 lines, elaborates in seconds). No interval arithmetic.
A skeleton is staged alongside this plan.

**Stage C1 — Lambda0 enclosures in t.** The r331b producers bound
`Lambda0(sigma+15i)` by quadrature in `u` at fixed t. For r331c the integrand's t
enters through `cos((t/2) log u)` and `sin((t/2) log u)`, so the t-dependence is
oscillatory where the sigma-dependence was monotone. **The amplitude-monotonicity
arguments r331b relies on (`box_pow_sum_lb/ub`) do not transfer.** Expect this to be
the real work, not stage C0.

**Stage C2 — partition `[0,15]` in t.** The r331b analogue of the Gate-B manifest:
a t-partition with a per-box margin, adaptive width, emitter-driven, gated for
contiguity and measure. `emit_box_bridge.py` and `emit_top_union.py` are structurally
reusable if stage C1 produces segment certificates of the same shape.

**Stage C3 — assemble** the two edge theorems and hand them to whatever r331d needs
for the winding-number argument.

## Warnings carried forward from r331b

1. **Do not re-render a parsed rational.** Three separate defects came from two code
   paths formatting the same number differently. Emit the source's own literal, or
   discharge the bound with `linarith` at the call site.
2. **`approx` has no lemma for a bare integer literal.** Integer-valued coefficients
   must be emitted as `2n/2`. At `sigma = 1` the factor `q1 = t` is far more likely to
   land on integers than anything in r331b, so this will bite early and often.
3. **One `lake build` per module.** Never one invocation per box.
4. **Audits come from `#print axioms`, never from RC** (gate item B0).
5. Every long-running unit gets a supervisor.

## Explicitly NOT started

No numerics, no generator, no partition, no elaboration. Stage C0's skeleton is
written but unbuilt. Starting C1 needs a free machine, which C1-the-gate-item
currently owns.
