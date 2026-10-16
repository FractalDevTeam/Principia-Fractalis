# Gap 2 built: the Schrödinger bridge derives the fluctuation law and produces the WRONG SIGN of the quantum potential

**Date:** 2026-10-16 (Legion, compute on Acer). Construction, not scoping. No
Lean — none of this mathematics exists in mathlib. Labels FACT / ARITHMETIC /
JUDGEMENT / OPEN throughout.

**Headline, two parts, both verified symbolically in 1-D and 3-D:**

1. **The target of gap 2 comes out.** `⟨dξ^μ dξ^ν⟩ = ε g^{μν}|dt| = 2D g^{μν}|dt|`
   is forced, not postulated, for *every* finite-entropy law on path space over
   metric Brownian motion. The osmotic relation and the continuity equation come
   out exactly. Nelson's `±` is resolved: it is the sign of `dt`, and the law is
   `|dt|`.
2. **The dynamics it produces is not quantum mechanics.** The bridge's
   `(ρ, v)` satisfies
   `∂_t S + |∇S|²/2m − Q = 0`, i.e. **Madelung with the quantum potential's
   sign reversed** — Zambrini's Euclidean quantum mechanics. Verified exactly:
   `HJ − Q = 0`, `HJ + Q ≠ 0`.

**And a third result, which kills the two-lane closure Rio asked me to watch
for:** the bridge's densities are **strictly positive on the open time
interval**, for *any* endpoint data including nodal data. So the construction
produces no nodes, the nodal-sector quantization result (`NODAL.md` §3c) applies
**vacuously**, and the hoped-for closure "the bridge yields smooth densities, so
the nodal sector closes from the other side" **does not occur**. It is not that
the densities are smooth at the nodes; it is that there are no nodes.

---

## 1. The construction

**Data:** a Riemannian manifold `(M,g)` — the geometry side — and two endpoint
densities `ρ_0, ρ_T` — the matter side. One free parameter `ε > 0`.

**Reference measure:** `R` = Brownian motion on `(M,g)` with generator
`(ε/2)Δ_g`, `Δ_g` the unweighted Laplace–Beltrami operator.

**The law:** `P` = the minimiser of the relative entropy `H(P|R)` over path
measures with the prescribed marginals (Schrödinger's 1931/32 problem;
entropic interpolation).

**Solution form — FACT (classical; Schrödinger, Jamison, Zambrini, Léonard).**
`dP/dR = f_0(X_0)·g_T(X_T)` with `f, g ≥ 0`, and the time-marginal factorises
as `ρ_t = f_t·g_t` where

* `g` solves the **forward** heat equation `∂_t g = +(ε/2)Δ_g g`;
* `f` solves the **backward** heat equation `∂_t f = −(ε/2)Δ_g f`.

**Doob h-transform — FACT, and the place I got it wrong first (see §6).** The
forward drift is `ε∇log h` for the factor `h` that is *space-time harmonic*,
`(∂_t + (ε/2)Δ)h = 0` — that is `f`, not `g`. So

  `b = ε∇log f`,  `b* = −ε∇log g`,  `u = (b−b*)/2`,  `v = (b+b*)/2`.

## 2. What is derived — the gap-2 target itself

### 2a. Continuous paths, no jump part — DERIVED. FACT (standard)

`H(P|R) < ∞` entails `P ≪ R` (relative entropy is `+∞` off absolute
continuity, by definition). `R` is supported on continuous paths, so `P` is
too. **A jump process is not excluded by fiat; it has infinite entropy relative
to Brownian motion.** This answers conclusion (a) of the scope note, and it
sharpens the step-1 survey's own observation (`GAP2_STEP1:118`) that "why a
diffusion and not a jump process" becomes a question about the functional: here
the functional is relative entropy and the answer is forced.

### 2b. The fluctuation law — DERIVED, as rigidity. FACT (Girsanov) + JUDGEMENT on what that buys

Girsanov: an equivalent change of measure on path space alters the **drift**
only. Quadratic variation is a pathwise, measure-class invariant. Hence for
every `P` with `H(P|R) < ∞`,

  **`[X^μ, X^ν]_t = ε g^{μν} t`,  i.e.  `⟨dξ^μ dξ^ν⟩ = ε g^{μν}|dt| = 2D g^{μν}|dt|`, `D = ε/2`.**

**Nelson's `±` is resolved.** Nelson writes `E[Δξ_i Δξ_j] = 2Dδ_{ij}Δt` forward
and the same backward; the `±` in `⟨dξ²⟩ = ±2Ddt` is the **sign of the time
increment**, not a sign ambiguity in the law. Quadratic variation along the
reversed filtration is the same process (FACT, standard for Bernstein
processes), so the two-sided law is `|dt|` with a single `D`. This was listed as
an open item in the scope note; it is now closed.

**What this buys, stated honestly.** The law is *not* derived from nothing — it
is inherited from `R`. What is derived is **rigidity**: the fluctuation law
cannot be perturbed at all, only the drift can. So the postulate
"`⟨dξ²⟩ = 2Ddt`" is traded for the postulate "the dynamics is a finite-entropy
perturbation of metric Brownian motion." That is one input for one input — but
the second is structural and single, and it carries (a), (b), the osmotic
relation and time symmetry with it. **JUDGEMENT:** this is a real reduction, and
it is the honest ceiling of the construction. It is not a derivation of the
fluctuation law *ex nihilo*, and must never be written up as one.

### 2c. Osmotic relation and continuity — EXACT. ARITHMETIC (verified, 1-D and 3-D)

With the drifts of §1:

| check | residual |
|---|---|
| `u − (ε/2)∇log ρ` | **0** |
| `∂_t ρ + ∇·(ρv)` | **0** |

So Nelson's osmotic equation `u = D∇log ρ` comes out with `D = ε/2` — the same
`D` as the fluctuation law, not an independent constant. That coincidence is a
genuine structural output.

### 2d. Time symmetry — NATIVE. FACT

The construction is built from a *pair* of forward/backward heat solutions and
is invariant under `t ↦ T−t` with `f ↔ g`. Nelson's `±` structure is not
imposed; it is the solution's shape. This is Zambrini's Bernstein/reciprocal
class, flagged in the step-1 survey (`GAP2_STEP1:50-58`) as "the best structural
match to the target's `±`". Confirmed: it is.

### 2e. Conclusion (c) — the conformal factor — REDUCED, not closed

`D` is constant and the Laplacian unweighted because `R` is *metric* Brownian
motion and `g` is the only datum. A position-dependent `D(x)` would require a
weighted generator, i.e. a reference measure carrying data beyond `g`. So (c)
reduces to **canonicity of the reference**: `D` constant iff `R` is built from
`g` alone. **The value of `D` is untouched.** `D = ħ/2m` is the value that makes
`v` Nelson's current velocity, and `ħ` enters here exactly as it enters
everywhere else in this corpus — as an input (`SUBSTRATE_HBAR_IS_INPUT`).

## 3. The decisive negative: the sign of the quantum potential

Set `ρ = fg`, `S = (mε/2)log(f/g)` (so `v = ∇S/m`), `ħ := mε`, `V = 0`. Then,
**verified exactly by symbolic computation in 1-D and again in 3-D:**

```
HJ  :=  ∂_t S + |∇S|²/(2m)
Q   :=  −(ħ²/2m) · Δ√ρ / √ρ

HJ + Q  ≠  0        <-- true Madelung (quantum)        FAILS
HJ − Q  =  0        <-- sign-reversed (Euclidean)      HOLDS IDENTICALLY
```

The two expressions `HJ` and `Q` come out **term-by-term identical**, so the
cancellation is exact and structural, not a near-miss.

**Consequence.** The entropy-minimising bridge satisfies the Madelung system
with `Q → −Q`: the quantum potential is repulsive where quantum mechanics needs
it attractive. The construction produces Zambrini's **Euclidean** quantum
mechanics — the imaginary-time theory — and **not** quantum mechanics. The
step-1 survey flagged this as the gap ("It yields Fokker–Planck, not Nelson…
Bridging that is exactly Zambrini's territory", `GAP2_STEP1:109-112`). It is now
not a flag but a computed identity, with the sign made explicit.

**Can the sign be absorbed? — JUDGEMENT: no, not cheaply.** The formal
substitution `ε → iε` maps Euclidean to quantum. But `iε` is not a diffusion
coefficient: a complex diffusivity has no path measure, and the entire
construction of §1–2 — absolute continuity, Girsanov, quadratic variation,
positivity — is a statement about a real measure on path space. The sign
reversal is therefore a wall, not bookkeeping. **This is the known reason Nelson
used the Yasue / Guerra–Morato action rather than relative entropy**: the Yasue
functional `E∫[(m/4)(|b|²+|b*|²) − V]dt` is not an entropy, is not convex, and
is precisely what flips the sign. Convexity is what makes the bridge
well-posed and what makes it Euclidean. **You cannot have both.**

**So: gap 2's kinematics is derivable by this route; gap 2's dynamics is not.**

## 4. Nodes: the two-lane closure is vacuous — ARITHMETIC (verified) + FACT

Rio's instruction was to watch the regularity of the produced density at nodes,
on the reading that `NODAL.md` §3c reduced Wallstrom to "`ρ` smooth at the
nodes" and this construction produces `ρ`.

**Result: `ρ_t > 0` strictly, for `0 < t < T`, for every endpoint pair.**

* `f, g ≥ 0` by construction, and each solves a heat equation. The strong
  maximum principle gives `f_t > 0` for `t < T` and `g_t > 0` for `t > 0`
  (unless identically zero). Hence `ρ_t = f_t g_t > 0` on the open interval.
  **FACT (parabolic strong maximum principle).**
* Verified numerically against genuinely nodal endpoint data
  `ρ_0(x) = x²e^{−x²}` (exact node at `x = 0`): heat-smoothing fills the node
  immediately — `g(0, τ) = 2.6e−12` at `τ = 1e−6`, `1.0e−4` at `τ = 1e−4`,
  `9.7e−3` at `τ = 1e−2`, and `min_x g > 0` at every `τ > 0`. **ARITHMETIC.**
* Also `ρ ∈ C^∞` (indeed real-analytic in `x`) on the open interval, by
  parabolic regularity. **FACT.**

**Therefore:** `{ρ_t = 0} = ∅`, so `H¹(supp ρ_t \ nodes; ℤ) = 0`, circulation is
forced to `0`, and `NODAL.md` §3c is satisfied **with an empty hypothesis set**.

**The closure Rio hoped for does not happen.** The statement "the bridge yields
smooth densities, so the nodal sector closes from the other side" is true only
in the degenerate sense that there is nothing to close. The construction
produces **only the zero-circulation sector** — no vortex states, no nonzero
angular momentum. This is the classical **nodal problem of stochastic
mechanics** resurfacing at exactly the point where the two lanes were supposed
to meet. It is a real obstruction to the bridge route, independent of §3, and it
would remain even if the sign problem were solved.

**JUDGEMENT on where that leaves the nodal result.** `NODAL.md` §3c is
unaffected as mathematics — it is a statement about Madelung data with nodes.
What is now known is that *this* construction cannot supply such data. The two
results do not compose.

## 5. Net ledger for gap 2

| conclusion | status after the build |
|---|---|
| (a) diffusion, not jump process | **DERIVED** (finite entropy ⟹ `P ≪ R`) |
| (b) `⟨dξ^μdξ^ν⟩ = 2Dg^{μν}|dt|`, `±` resolved | **DERIVED as rigidity** (Girsanov); inherited from `R`, not from nothing |
| osmotic `u = D∇log ρ`, same `D` | **EXACT** (verified) |
| continuity `∂_tρ + ∇·(ρv) = 0` | **EXACT** (verified) |
| time-symmetric `±` structure | **NATIVE** (Bernstein pair) |
| (c) `D` constant, unweighted `Δ_g` | **REDUCED** to canonicity of `R` |
| (d) value `D = ħ/2m` | **INPUT** (unchanged) |
| **the dynamical law** | **WRONG SIGN — Euclidean, not quantum** (computed) |
| **nodal / vortex sector** | **NOT PRODUCED** — `ρ > 0` strictly (computed) |

**Three postulates → one postulate plus one parameter, for the kinematics only.**
The dynamics is not obtained. Both failures are now sharp, computed, and
attributable: the sign to the convexity of relative entropy, the nodes to the
strong maximum principle.

## 6. Method note — worth keeping

My first run assigned the forward drift to `g` (the forward-heat factor). The
**osmotic check still passed**, because `u` is symmetric in `f ↔ g`. The
**continuity check failed**, with residual `ε(f·Δg − g·Δf)` — and I had printed
"continuity holds identically" above it in the same script without reading the
number. Only the residual being nonzero caught it. Had I trusted the osmotic
check alone I would have carried the swapped drifts into §3, where they would
have produced a different and wrong sign verdict.

**Two lessons.** A symmetric check cannot detect an antisymmetric error — the
osmotic relation was structurally incapable of catching this. And a script that
prints its conclusion as a literal string next to its own residual will lie to
you. This is the second time in two days that a verification harness reported
the opposite of the truth (`NODAL.md`: the one-sided probe of a radial
singularity). Both were caught; neither should have been written that way.

## 7. What would have to change — OPEN

1. **Replace the variational principle.** Relative entropy is convex and gives
   Euclidean dynamics. Yasue / Guerra–Morato gives quantum dynamics and is not
   convex, hence has no bridge-style existence theory on general `(M,g)`. A
   principle that is both would be the actual result. **No lead.**
2. **Reach the nodal sector.** Any route must admit path measures whose
   densities vanish on a codimension-2 set. The strong maximum principle says a
   finite-entropy perturbation of Brownian motion cannot. So this needs either
   a degenerate reference measure or a non-diffusive admissible class — and the
   first thing to check is whether either survives (a). **No lead.**
3. **Literature check, mandatory before any of this is built on.** §2 is
   Léonard's survey and Zambrini's programme and I claim no novelty for it; §3's
   sign reversal is, to my recollection, standard in that literature and I have
   **not** verified attribution. §4's positivity obstruction is the classical
   nodal problem of stochastic mechanics (Carlen; Wallstrom) and likewise
   standard. Primary sources: Schrödinger 1931/32; Jamison 1974/75; Zambrini
   1986; Carlen 1984; Wallstrom 1994; Léonard 2014 survey; Chen–Georgiou–Pavon.
   **Treat all of §2–§4 as rediscovered, not new, until someone checks.**

---

## Label summary

* **FACT (standard):** bridge solution form `dP/dR = f_0 g_T` and the
  forward/backward heat pair; Doob h-transform drift `ε∇log h` from the
  space-time harmonic factor; `H(P|R) < ∞ ⟹ P ≪ R`; Girsanov changes drift
  only, quadratic variation invariant; parabolic strong maximum principle and
  parabolic regularity; quadratic variation unchanged along the reversed
  filtration.
* **ARITHMETIC (computed here, 1-D and 3-D):** osmotic residual `0`; continuity
  residual `0`; `HJ − Q = 0` and `HJ + Q ≠ 0`; the nodal heat-smoothing figures.
* **JUDGEMENT (mine):** that rigidity-under-finite-entropy is a real but bounded
  reduction and must not be written as a derivation of the fluctuation law; that
  `ε → iε` is a wall rather than bookkeeping, and that convexity is the
  mechanism; that §3's and §4's obstructions are independent; that `NODAL.md`
  §3c and this construction do not compose.
* **NOT established:** that no path-measure construction can produce quantum
  dynamics or nodal densities. What is established is that **this** one — the
  entropy-minimising bridge over metric Brownian motion — does neither, and
  why.
