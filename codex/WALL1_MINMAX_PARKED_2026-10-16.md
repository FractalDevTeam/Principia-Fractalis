# Wall 1, min-max attempt: nothing live hosts Pavon's functional. Gap 2 parks.

**Date:** 2026-10-16 (Legion, compute on Acer). Bounded search, executed and
closed. No Lean. Labels FACT / ARITHMETIC / JUDGEMENT / OPEN throughout.
Verification: `codex/wall1_minmax_verify.py`, all checks PASS.

**Order:** narrow to min-max existence theory for Pavon's saddle-point
stochastic action (Pavon, *Hamilton's principle in stochastic mechanics*,
J. Math. Phys. **36**, 6774–6800 (1995), DOI 10.1063/1.531187 — reference
confirmed), convex in `v`, concave in `u`, `min_v max_u`. Is there **any**
min-max existence result on path space that could host it? Closest theorem,
and what exactly fails on carry-over? Stop condition: if nothing live, park.

**Verdict: nothing live. Gap 2 parks.** Three independent obstructions, all
computed here, not inferred:

1. **The wall is an identity, not an observation.** The quantum potential *is*
   the osmotic kinetic energy. So the quantum sign is **equivalent** to an
   indefinite action — non-convexity is not a defect of Pavon's particular
   choice, it is forced.
2. **The indefinite action has no coercivity in either direction**, and its
   min/max variables are not independent. This kills both standard routes
   (Sion-type minimax, mountain-pass) at the hypothesis, not in the details.
3. **The one existence framework that does allow law-dependent coupling —
   mean-field games — carries the Euclidean sign anyway.** Checked directly,
   because this was the live risk; see §4.

---

## 1. The wall restated as an identity — ARITHMETIC (verified symbolically and numerically)

With `u = D∇log ρ`, `D = ħ/2m`, and `Q = −(ħ²/2m)Δ√ρ/√ρ`:

> **`∫ρ·(m/2)|u|² = ∫ρ·Q = (ħ²/8m)·I(ρ)`**,  `I` = Fisher information.

Symbolic difference exactly `0`; numerically equal to 9 digits for Gaussian,
bimodal and skewed densities (the integration by parts carries no boundary
term for decaying `ρ`).

**Consequence — the load-bearing point of this note.** The sign of `Q` in the
dynamics **is** the sign of the osmotic term in the action:

| action | osmotic term | dynamics |
|---|---|---|
| relative entropy `H(P|R)` (bridge) | `+(m/2)|u|²` → convex | **Euclidean** (`HJ − Q = 0`) |
| Yasue / Guerra–Morato / Pavon | `−(m/2)|u|²` → indefinite | **quantum** (`HJ + Q = 0`) |

By Girsanov, `H(P|R) = E∫|b|²/(2ε)dt` with `b = v + u`, so entropy necessarily
delivers `|v|² + |u|²`. The quantum action necessarily needs `|v|² − |u|²` — a
**difference of squares**, hence an indefinite quadratic form.

So **convexity ⟺ Euclidean sign** is a theorem, not a coincidence of the
constructions tried. Rio's framing was right and this is its proof. The
corollary matters for how the search was scoped: you cannot look for a
"well-posed non-convex principle" that happens to give the quantum sign — the
quantum sign *is* the non-convexity. Any hosting theorem must handle an
indefinite functional head-on.

## 2. The closest existing theorem — FACT

**Fleming–Souganidis (1989), Indiana Univ. Math. J.: existence of the value for
two-player zero-sum stochastic differential games.** The lower and upper value
functions satisfy the dynamic programming principle and are the unique
viscosity solutions of the Bellman–Isaacs equations, given the **Isaacs
condition** `inf_v sup_u H = sup_u inf_v H`. Extended to the case **without**
the Isaacs condition via mixed strategies (Buckdahn–Li–Quincampoix,
arXiv:1407.7326; also arXiv:1307.4686).

This is a genuine `min–max` existence theory on path space — the right species
of theorem. It does not host Pavon's functional, for one structural reason and
one quantitative one.

### 2a. The domain is not a product set — the structural failure. JUDGEMENT (diagnosis), FACT (the hypothesis)

Fleming–Souganidis, and every descendant including the mixed-strategy
extension, assumes **two players drawing from their own fixed control sets**.
Mixed strategies relax *Isaacs*, not the product structure — a mixed strategy
is a randomisation over one player's own set.

In Pavon's functional, `u` is **not a control**. It is
`u = D∇log ρ`, and `ρ` is the law of the very process whose drift is
`b = v + u`. The maximiser's admissible set is a *function of the minimiser's
choice*. There is no product domain, so there is no game, so there is nothing
for the Isaacs machinery to act on. **This is not a gap to be filled by a
sharper theorem of the same kind; it is a category mismatch.** What the
`min_v max_u` notation denotes is a critical point of a difference-of-convex
functional of a single variable — the pair `(ρ, ρv)` — not a saddle over a
product.

### 2b. No coercivity in either direction — the quantitative failure. ARITHMETIC (verified)

With `m = ħ = 1`, `J[ρ,v] = ∫ρ(1/2)|v|² − I(ρ)/8`:

* **Unbounded below.** Hold `v ≡ 0` and oscillate: `ρ_k = e^{−x²}(1+0.9\sin kx)²`,
  smooth, positive and normalised at every `k`. Then `J = −I(ρ_k)/8` and
  `I(ρ_k) = 3.29, 6.64, 20.45, 75.79, 297.17, 1182.70, 4724.79` for
  `k = 1,2,4,8,16,32,64` — ratio converging to **×4.00 per doubling**, i.e.
  `I ∼ k²`. So `J → −∞`.
* **Unbounded above.** Hold `ρ` Gaussian and scale `v = c·x`: `J = 0.75, 3.75,
  15.75, 63.75` for `c = 2,4,8,16`. So `J → +∞`.

**What this kills.** Sion/von Neumann minimax needs convex–concave **on a
product** plus compactness on one side — fails on both counts (§2a and here).
Mountain-pass (Ambrosetti–Rabinowitz) needs a Palais–Smale condition and a
geometry with a bounded-below local structure — the `−I(ρ)` direction is
unbounded below along smooth normalised densities, so the required geometry is
absent. Note the mechanism is the Fisher information of §1: the *same* term
that supplies the quantum sign is the one that destroys coercivity. **They
cannot be separated.**

## 3. Where a hosting theorem would have to live — OPEN, stated as a spec

Not "no such theorem can exist" — that would need its own proof and I have not
got one (cf. the standing impossibility-vs-absence rule). What is established
is the **specification** any hosting theorem must meet, which is now sharp:

1. handle an **indefinite** functional (forced, by §1);
2. on a domain that is **not a product** — the maximising variable determined
   by the law of the minimiser's own process (forced, by §2a);
3. with **no coercivity in either direction** on any space containing smooth
   oscillatory densities (forced, by §2b).

**JUDGEMENT:** I know of no theorem in stochastic control, differential games,
mean-field games, or infinite-dimensional critical-point theory meeting all
three, and (1)+(3) together are the combination that standard critical-point
theory is built to avoid. If such a result exists it is not in the places this
search looked.

## 4. The mean-field-game route — checked, because it was the real risk. ARITHMETIC (verified)

MFG is the one framework that **does** allow the coupling to depend on the law,
so requirement (2) above is native there, and MFG existence theory is
substantial (Lasry–Lions, Cardaliaguet, Carmona–Delarue). That literature also
advertises a correspondence with the nonlinear Schrödinger equation under
`μσ² → ħ` (e.g. arXiv:2006.01221 and the Schrödinger-approach-to-MFG line).
**If that correspondence were a real-time identification, MFG existence theory
would host the quantum sign and this note's verdict would be wrong.** So I
tested it rather than taking it on trust.

Take the standard MFG forward–backward system,

* HJB (backward): `−∂_tφ − (ε/2)Δφ + |∇φ|²/2 = V`,
* FP (forward): `∂_tρ + ∇·(ρ v_mfg) = (ε/2)Δρ`, `v_mfg = −∇φ`,

absorb the FP diffusion into the velocity — `v_c := v_mfg − (ε/2)∇log ρ`, which
makes continuity exact (**verified: residual 0**) and is precisely the osmotic
decomposition — and set `S := −(φ + (ε/2)log ρ)` so `v_c = ∇S`. Then with
`ħ := ε`:

```
S_t + |grad S|^2/2 - Q - V  =  0        <-- HOLDS IDENTICALLY
S_t + |grad S|^2/2 + Q + V  =/= 0
```

**The MFG system carries the Euclidean sign.** `V_cost` versus `V_mech` is a
genuine convention — a cost is minimised, a mechanical potential is not — but
the sign of `Q` is **not** a convention: it is fixed by the diffusion term, and
it comes out Euclidean.

**Two consequences.**

* The MFG↔NLS correspondence in that literature **cannot be a real-time
  identification**; it must route through an analytic continuation. That is
  consistent with Rio's already-dead lead (Wick rotation at path-measure
  level, no theorem) and does not revive it.
* Independently, arXiv:2302.05938 (*Mean Field Optimization Problem Regularized
  by Fisher Information*) adds Fisher as a **convex regulariser** and obtains a
  **unique minimiser** with exponential convergence, as a gradient flow in
  relative entropy. That is the exact mirror image of our problem: `+I(ρ)` is
  well-posed and Euclidean; `−I(ρ)` is what we need and is unbounded below.
  **The MFG literature's well-posedness lives entirely on the sign we cannot
  use.** Third independent confirmation of §1.

## 5. Verdict and ledger

**Stop condition met: nothing live. Gap 2 parks.**

| question | answer |
|---|---|
| Is there min-max existence theory on path space? | **Yes** — Fleming–Souganidis 1989 and descendants |
| Can it host Pavon's functional? | **No** — domain is not a product set (§2a) |
| Could a coercivity-based route work instead? | **No** — unbounded both directions (§2b) |
| Does MFG, which allows law-dependence, host it? | **No** — carries the Euclidean sign (§4) |
| Is the non-convexity removable? | **No** — it is equivalent to the quantum sign (§1) |

**What is banked and keeps its value regardless:** the kinematic half of gap 2
stands as built (`GAP2_BRIDGE_CONSTRUCTED_2026-10-16.md`, commit `97cae4ca`) —
no-jump, the fluctuation law as Girsanov rigidity with Nelson's `±` resolved,
osmotic relation and continuity exact, native time symmetry, `(c)` reduced to
canonicity of the reference. That does not depend on wall 1 and is not
withdrawn by this note. What is parked is the attempt to obtain the **dynamics**
by a path-space variational principle.

**JUDGEMENT on the lane.** Wall 1 and the nodal obstruction
(`ρ > 0` strictly, so no vortex sector) are independent, and both would have to
fall. With wall 1 now an identity rather than an obstacle, the honest reading is
that the Nelson route's dynamics does not come from a path measure at all — and
the one rigorous Euclidean→quantum bridge that does exist in mathematical
physics (Osterwalder–Schrader reconstruction) buys the Hamiltonian at the cost
of the trajectories, which were the point of the route. **Flagged as an
observation, not a lead, and not pursued** — it is outside this order's scope
and would be a different programme.

---

## Label summary

* **FACT (standard, verified by reference):** Pavon 1995 J. Math. Phys. 36,
  6774–6800, DOI 10.1063/1.531187; Fleming–Souganidis 1989 existence of value
  under Isaacs, value = unique viscosity solution of Bellman–Isaacs;
  mixed-strategy extension without Isaacs (arXiv:1407.7326, arXiv:1307.4686);
  Girsanov giving `H(P|R) = E∫|b|²/2ε dt`; arXiv:2302.05938 obtaining a unique
  minimiser from `+`Fisher as an entropy gradient flow.
* **ARITHMETIC (computed here):** the identity
  `∫ρ(m/2)|u|² = ∫ρQ = (ħ²/8m)I(ρ)` (symbolic difference 0; numeric to 9
  digits, three density shapes); `I(ρ_k) ∼ k²` with the tabulated values and
  the ×4.00 ratio; unboundedness above; the MFG continuity residual 0 and
  `S_t + |∇S|²/2 − Q − V = 0` identically.
* **JUDGEMENT (mine):** that the product-domain failure is a category mismatch
  rather than a gap to be filled; that (1)+(3) of the §3 spec is the
  combination critical-point theory is built to avoid; the reading in §5 that
  the dynamics does not come from a path measure; the OS-reconstruction
  observation.
* **NOT established:** that no min-max existence theorem could ever host an
  indefinite, non-product, non-coercive functional of this shape. §3 states the
  spec such a theorem would have to meet; it is an absence, not an
  impossibility.
* **Attribution caution:** §1's identity (osmotic energy = quantum potential =
  Fisher information) is, to my recollection, standard in the
  Madelung/Fisher-information literature and I claim no novelty for it — only
  that it was verified here and that its *use* as the equivalence
  "convexity ⟺ Euclidean sign" is the framing this note rests on. Check against
  the primary sources before anything is written up.
