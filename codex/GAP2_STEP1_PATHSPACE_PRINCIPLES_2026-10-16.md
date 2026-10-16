# Gap 2, step 1 — survey of path-space variational principles

**Date:** 2026-10-16 (Legion). Literature survey + structural analysis.
Nothing proved here. No Lean (none of this is in mathlib — see the gap-2
scope note).

**Target** (gap-2 (i)-(iii), `D` free): a covariant variational principle on
path-space measures over `(M,g)` whose stationary points necessarily
**(a)** are diffusions (continuous, finite nonzero quadratic variation, no
jump part), **(b)** have diffusion tensor `a^{mu nu} = 2D g^{mu nu}`, and
**(c)** with `D` constant.

**Headline: the closest existing principle is NOT Yasue / Guerra-Morato /
Zambrini.** All three fix the diffusion coefficient in the admissible class
and vary only the drift, so (a),(b),(c) are properties of their function
space, not conclusions. The closest is the **JKO / Otto / Lott-Sturm-Villani
entropy-gradient-flow framework**, which genuinely *derives* (b) — but is
one-sided (dissipative) where the target needs Nelson's two-sided structure.

---

## The three principles Rio named

### Yasue (1981), stochastic calculus of variations

* **Assumes:** the admissible class is already the Nelson diffusions
  `dX = b\,dt + \sqrt{2D}\,dW` with `D` **fixed**. Variation is over the
  drift `b` only. Action
  `J = E\int_0^T [\tfrac{m}{2}\cdot\tfrac12(|b|^2 + |b_*|^2) - V]\,dt`,
  equivalently `\tfrac m2(|v|^2 - |u|^2) - V` in mean/osmotic variables.
* **Stationary points:** satisfy Nelson's stochastic Newton law
  `m\,a = -\nabla V` with `a = \tfrac12(D_+D_- + D_-D_+)`, hence the Madelung
  equations, hence Schrödinger.
* **Falls short of:** (a), (b), (c) — all three. "Is a diffusion" is
  admissibility; "tensor conformal to `g`" is built into `\sqrt{2D}\,dW`; `D`
  constant is a choice. Yasue is the **law -> dynamics** direction done
  properly; it is not a derivation of the law.

### Guerra-Morato (1983), stochastic control formulation

* **Assumes:** a stochastic optimal-control problem — minimise
  `E\int[\tfrac m2|b|^2 - V]` subject to the *state equation* being an SDE
  whose diffusion coefficient is fixed at `hbar/2m`. Control = drift.
* **Stationary points:** the optimal control reproduces Schrödinger via HJB /
  the Hamilton-Jacobi-Madelung system.
* **Falls short of:** identically to Yasue, and more explicitly: the
  coefficient `hbar/2m` sits in the *constraint*, i.e. it is data of the
  problem. Also imports `hbar` by name.

### Zambrini (1986 onward), Euclidean quantum mechanics / Bernstein processes

* **Assumes:** Bernstein (reciprocal) processes — genuinely **two-sided**,
  built from a pair of positive solutions of forward/backward heat equations.
  This is the rigorous home of Nelson's `+-` structure and of Schrödinger's
  own 1931-32 problem. The heat equation's parameter **is** the diffusion
  coefficient, fixed in advance.
* **Stationary points:** a time-symmetric class of diffusions in bijection
  with solution pairs; the Euclidean analogue of quantum dynamics.
* **Falls short of:** (b),(c) for the same reason. **But it is the best
  structural match to the target's `+-`**, and should be the time-symmetry
  template for anything built.

**Common defect, stated once:** all three are variational principles *over
drifts within a fixed diffusion class*. The object gap 2 needs to be
*derived* is exactly the object all three *fix before varying*.

---

## The closest existing principle: entropy gradient flow in Wasserstein geometry

### JKO (Jordan-Kinderlehrer-Otto, 1998) + Otto calculus

The heat equation / Fokker-Planck equation **is** the gradient flow of the
Boltzmann entropy with respect to the Wasserstein-2 metric on probability
measures over `(M,g)`. The `W_2` metric is built from `g` (Benamou-Brenier:
`W_2^2(\mu_0,\mu_1) = \inf \int\!\!\int |v|^2_g \,d\mu\,dt`).

**Why this matters for gap 2:** here the diffusion is **not assumed** — it is
the *solution* of a variational problem (steepest descent of entropy in a
geometry built from `g`). The resulting generator's principal part is
`\Delta_g`. So **(b) comes out rather than going in.** This is the one place
in the literature where "diffusion tensor conformal to the metric" is a
conclusion of a variational principle.

### Lott-Sturm-Villani, von Renesse-Sturm

Strengthens the link in the geometry -> diffusion direction: Ricci curvature
bounds are **equivalent** to convexity of entropy along `W_2` geodesics
(`CD(K,N)`), and equivalently to gradient/contraction estimates for the heat
semigroup. So the geometry genuinely controls the second-order behaviour of
the metric-canonical diffusion, as an equivalence, not a one-way bound.

Supporting: **Bakry-Emery `Gamma`-calculus** states (b) intrinsically as
`\Gamma(f,f) = |\nabla f|^2_g`; **Eells-Elworthy-Malliavin** constructs the
process realising it on the frame bundle.

### Exactly where it falls short of the target

1. **One-sided.** Gradient flow is dissipative and time-directed. The target
   needs Nelson's time-symmetric `+-` structure, which is *not* a gradient
   flow. Fix direction: the **entropic interpolation / Schrödinger bridge**
   (Léonard's survey; Zambrini's Bernstein processes) is the time-symmetric
   version of the same variational idea — minimise relative entropy w.r.t. a
   reference Brownian motion.
2. **The conformal factor is still an input.** In JKO it is the mobility /
   entropy normalisation; in the Schrödinger-bridge formulation it is the
   reference measure's noise level `\epsilon = 2D`. **(c) is untouched:**
   nothing forces `D` constant rather than a scalar field, and nothing fixes
   its value.
3. **It yields Fokker-Planck, not Nelson.** The output is the evolution of
   `\rho`, not the two-sided diffusion whose Nelson acceleration gives
   Schrödinger. Bridging that is exactly Zambrini's territory.
4. **(a) is partly answered, interestingly.** Jump processes are *not*
   excluded by fiat but by the choice of metric/functional: `W_2` + Boltzmann
   entropy gives local (diffusive) flow, while non-local functionals or
   `W_1`-type metrics give jump/fractional dynamics. So in this framework
   "why a diffusion and not a jump process" becomes "why `W_2` and Boltzmann
   entropy" — a sharper and more tractable question than before.

---

## The construction I would actually try

**Entropic interpolation (Schrödinger bridge) over the Wasserstein geometry of
`(M,g)`, with the reference measure the metric-canonical Brownian motion.**

* time-symmetric by construction (so the `+-` structure is native, per
  Zambrini);
* the geometry enters only through `g` (so (b) is inherited from JKO/Otto
  rather than assumed);
* the unknown is a measure on **path space**, which is the shape the gap-2
  scope note argued is forced — an equation in `T_{mu nu}` provably cannot
  fix path-level data;
* the single remaining free parameter is the reference noise `\epsilon = 2D`.

**Then the precise remaining problems are:**
* **(c)** a rigidity statement: show no stationary point has `D` as a
  non-constant scalar field — presumably from covariance plus a homogeneity
  argument on the reference measure;
* **(iv)** fixing `\epsilon`. Already settled negatively for `G,c,m`
  (mass-scaling) and for the substrate (`hbar` is imported — see the
  substrate-`hbar` report). So `\epsilon` stays a parameter, and the write-up
  must say so.

**Expected honest outcome:** a derivation of (a),(b) and plausibly (c), with
`D` free. That is real: it would convert three postulates into one parameter.
It would **not** be a derivation of quantum mechanics, because `hbar` remains
an input and because Wallstrom's objection (see the gap-3 note) still stands
between Madelung/Nelson and Schrödinger.

---

## Confidence

What each principle **assumes and concludes** I am confident of at the level
stated. I have **not** re-derived the theorems, and no specific theorem
numbers, constants, or precise hypotheses are asserted here — anything used
downstream should be checked against the primary sources (Yasue 1981;
Guerra-Morato 1983; Zambrini 1986; JKO 1998; Otto 2001; Lott-Villani 2009;
Sturm 2006; von Renesse-Sturm 2005; Léonard's entropic-interpolation survey;
Bakry-Emery; Eells-Elworthy-Malliavin). The claim that JKO/Otto is the
*closest* candidate is my structural judgement, not a cited result.
