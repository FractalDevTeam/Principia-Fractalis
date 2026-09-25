# r331b release note — DRAFT for Pablo's review

Status: draft. Nothing here is published. Public HEAD remains 96c71da7.

---

## What this release contains

A machine-checked proof, in Lean 4 against mathlib `v4.24.0-rc1`, of an **exact
zero-counting identity for the classical entire Riemann xi function on one rectangle**:

    PrincipiaTractalis.RiemannXiT15Endgame.xi_T15_zero_count_identity_unconditional

    RectangleIntegral' (fun s => logDeriv riemannXiEntire s) z15 w15
      = sum over rho in Z, (analyticOrderNatAt riemannXiEntire rho : C)

where the rectangle is `z15 = 0` to `w15 = 1 + 15i` — that is, `[0,1] x [0,15]` — and
`Z` is the finite set of zeros of `riemannXiEntire` in its interior, produced from
`finite_zeros_rectangle`.

The theorem has **no hypotheses**. Verified by `#check @`, which displays every binder
including implicit ones and returns a type with none. Its axiom dependencies are
exactly `[propext, Classical.choice, Quot.sound]` — the three mathlib relies on
everywhere. No project axioms, no `sorry`, no `native_decide`.

## What it does NOT contain

**This is not a proof of the Riemann Hypothesis, and it is not evidence for one.**

It is a contour-integral identity on a single bounded rectangle. It says the winding
of `logDeriv xi` around that rectangle equals the multiplicity-weighted count of zeros
inside it. It says nothing about where those zeros lie, nothing about any other
rectangle, and nothing about the critical line.

Specifically, the release does **not** establish:

- that any zero of xi lies on the critical line;
- that the zeros in this rectangle are simple;
- any statement about height beyond t = 15;
- any Millennium Prize problem, in whole or in part.

Repository material on P vs NP, Navier-Stokes, Hodge, BSD and Yang-Mills is unaffected
by this release and remains as previously characterised: conditional scaffolding
resting on undischarged named hypotheses. In particular the P vs NP axis remains
conditional on `PolylogEigenvalueConjecture`, which the repository's own
`AlphaRealizationNoGo.lean` proves is *equivalent* to the separation it is used to
derive.

## How it is proved

The T=15 rectangle boundary has four edges. Three were already discharged in earlier
work in this repository:

| edge | source | status before r331b |
|---|---|---|
| left vertical, `Re s = 0` | r328 `riemannXiEntire_ne_zero_on_re_zero` | proved |
| right vertical, `Re s = 1` | r328 `riemannXiEntire_ne_zero_on_re_one` | proved |
| bottom, `Im s = 0`, `sigma in [0,1]` | r329b `bottomEdgeZeroFree_proved` | proved |
| top, `Im s = 15` | — | **the sole residual** |

r328 reduces the top edge to its right half `sigma in [1/2, 1]` by the r326 reflection
identity. r331b discharges that half.

The method is a certified numerical enclosure. `Re xi(sigma + 15i)` is expressed
through `completedRiemannZeta0`, whose real and imaginary parts are bounded by
interval-arithmetic quadrature over a 40-segment partition of `u in [1,5]`, plus one
analytic tail envelope. `[1/2, 1]` is partitioned into 18 boxes of width 1/16, 1/32 or
1/64, chosen adaptively so that every box closes. Each box yields

    Re xi(sigma + 15i) < -1/10000    on that box,

and a case split over the partition assembles them into the same statement on all of
`[1/2, 1]`. Since `Re z < 0` forces `z != 0`, that is exactly the residual r328/r329b
required.

All interval computation is kernel-checked via the vendored `girving/interval` library
using `approx` and `decide +kernel`. The `interval` tactic, which uses
`native_decide`, is banned in this repository and is not used.

## Scale and reproducibility

- 18 boxes, 40 segments each, 4835 generated Lean files (4115 panels + 720 M
  certificates)
- ~191 machine-hours of kernel checking, run across two machines
- every certificate is machine-generated; all generators, configuration and the
  partition manifest are committed alongside the output
- headline margins are xi-space: weakest box +2.211191e-05, strongest +2.004865e-04

## Honest caveats

1. **One rectangle, and the shape has a hard ceiling at T = 15.54.** The result is
   `T = 15`. It does not scale: the r331c read-back of 2026-09-08 measured the
   right-edge argument budget and found `arg xi(1+it)` first reaches pi at
   **t = 15.54**, with max arg on [0,15] of 2.9383 (margin 0.2033 rad). The budget
   is about pi per zero, so **this proof shape works at T = 15 and fails by T = 16.**
   Any sequel at greater height needs a different device, not more compute.
2. **Numerical certificates, not closed forms.** The proof is a very large finite
   computation checked by the Lean kernel. It is sound if the kernel and mathlib are
   sound; it offers no new analytic insight into xi.
3. **The margins are thin by design.** The weakest box closes with xi-space margin
   2.2e-05 against a target of 1e-04. The partition was chosen adaptively to make
   every box close, not to leave comfortable headroom.
4. **`RiemannXiTopEdgeScaffolding_r330` is not part of this chain.** It reaches the
   same residual by a Taylor-remainder route but still requires an unproven uniform
   second-derivative bound. It is superseded scaffolding and must not be cited as
   support.
5. **MHI majorants are outward-rounded in box 0.** 680 of the 720 M certificates
   use `MHI = 2*sum(B_n)` exactly. The 40 in box 0 (produced by the older
   generator) are rounded outward, i.e. LOOSER; none is tighter. A looser
   majorant enlarges the quadrature error term and therefore widens the
   certified interval, so the direction is the sound one and the achieved
   margin is smaller than the theoretical best. See `MHI_OVERRIDE_TABLE.md`.
6. **Not independently reviewed.** No external referee has checked this.
