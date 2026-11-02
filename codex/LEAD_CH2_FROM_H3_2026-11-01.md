# A non-circular candidate route to deriving ch₂ = 0.95 from H₃

Written 2026-11-01. This is a **research lead with a named obstruction**, not a
result. It is recorded because it is the first candidate source for the `20` in
`ch₂ = 19/20` that is not back-solved from `0.95` itself.

## What the corpus already proves

`PF/FrameworkCrossDomainAnchors.lean`

```
:155  noncomputable def Phi_threshold : ℝ := 2 * Real.log 20
:167  theorem Phi_threshold_eq_log_400 : Phi_threshold = Real.log 400
:223  theorem iit_saturation_at_threshold :
        (1 - Real.exp (-Phi_threshold / 2)) = 19 / 20
```

The saturation identity is exact, and the mechanism is elementary:
`exp(-log(400)/2) = 400^(-1/2) = 1/20`, so `1 - 1/20 = 19/20` with no
approximation anywhere. Verified independently at 30 dps.

## Why it is NOT currently a derivation of 0.95

The same file's docstring, `:222`, states the direction of reasoning:

> "Phi = 2·log 20: **solving 0.95 = 1 − e^{−Φ/2} gives Φ = 2·log 20**"

So `Phi_threshold` was obtained by inverting the very equation the theorem
proves. The identity is a faithful reparametrisation of `0.95`, not an
independent route to it. **Any claim that the IIT saturation identity derives
ch₂ = 0.95 is circular**, and the corpus is honest about this in its own
docstring. It must not be cited as a derivation.

## The lead: the 20 is an icosahedral invariant

`20` is a genuine invariant of the same group that already supplies `π/10`:

| quantity | value |
|---|---|
| icosahedron faces | **20** |
| dodecahedron vertices (dual) | **20** |
| `2·h(H₃)` | **20** |
| `\|W(H₃)\|/d₂ = 120/6` | **20** |

and it is **not** equal to the other H₃ counts — roots 30, reflections 15,
`\|W\|` 120, `rank·h` 30 — so the identification is specific rather than a
free choice among invariants.

The corpus already proves, kernel-only and axiom-free, in
`PF/H3CoxeterOrigin.lean`:

```
:87   H3_Coxeter_number : ℕ := 10
:111  H3_Coxeter_half_arg : (2π / h(H₃)) / 2 = π/10
:211  sin_pi_div_ten_eq_inv_two_phi : sin(π/10) = 1/(2·goldenRatio)
```

So `h(H₃) = 10` already carries the universal coupling `π/10 = π/h(H₃)`.

**If the `20` can be obtained from H₃ independently of `0.95`, then
`ch₂ = 1 - 1/(2h(H₃))` and `π/10 = π/h(H₃)` collapse into ONE group-theoretic
fact, and two of the framework's asserted constants become structural at once.**

Measured: nothing in the Lean corpus connects `20`, `400`, or `Phi_threshold`
to H₃ or to the icosahedron. The grep for `2 * H3_Coxeter_number` and for
`400` near `Coxeter|H3|icosa` returns nothing. This connection is absent.

## The obstruction, stated precisely

What is missing is a reason the integrated-information saturation value should be
the icosahedral face count. Specifically, to close this one needs:

> **Target.** An argument, independent of `ch₂ = 0.95`, that the saturation
> value of the integrated-information measure on the substrate equals `20`
> (equivalently: that `Φ_threshold = 2 log(2h(H₃))`), derived from the
> icosahedral structure rather than fitted to the threshold.

Until that exists this is a numerical identification, and the framework already
carries too many of those. It is logged as a lead, not as support.

## Why it is still worth having

The book's current justification of `0.95` is weaker than this lead.
`ch26:580` reads:

> **ASSERTED (numerology)** --- ch₂ = 0.95 = 6/π² + ε_quantum

`6/π² = 0.60793`, so that account needs `ε_quantum = 0.34207` — a correction
amounting to **36% of the value being explained**, with no source. The H₃ route
needs no fudge term at all; it needs one theorem. A target that is one statement
away is a better position than a fitted remainder, and it is falsifiable: if the
saturation value provably is not `20`, the route closes and that is also
progress.

## Do not overclaim this

Three things that are NOT established and must not be written into the book:

1. that `ch₂ = 0.95` is derived — it is not;
2. that the IIT saturation identity supports `0.95` — it is circular by its own
   docstring;
3. that `20 = 2h(H₃)` is a mechanism — it is an identification awaiting one.
