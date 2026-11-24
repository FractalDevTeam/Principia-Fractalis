# Track B1 — Representation-safety test

**Question Rio named as the pivot**: Is Eq. (28), the reconnection criterion, a property of the spacetime or a property of the (tetrad, transport congruence) representation?

**Status**: prose argument + algebraic-rank sketch. SymPy worked example pending.

---

## The two transformation groups

Eq. (28) is stated for a fixed tetrad label $\hat\alpha$ and a fixed transport $u^\mu$. Physical reality of reconnection requires invariance under:

- **Local Lorentz** $\Lambda^{\hat\alpha}{}_{\hat\beta}(x)$ on the tetrad frame (rotates the $\hat\alpha$ index).
- **Transport-congruence** changes $u^\mu \to u'^\mu$.

### (i) Local Lorentz covariance

Under $e'^{\hat\alpha} = \Lambda^{\hat\alpha}{}_{\hat\beta}(x)\, e^{\hat\beta}$:
- $\mathcal{F}'^{\hat\alpha}{}_{\mu\nu} = \Lambda^{\hat\alpha}{}_{\hat\beta}(x)\, \mathcal{F}^{\hat\beta}{}_{\mu\nu}$
- From Eq. (22), $\mathcal{R}'^{\hat\alpha}{}_\nu = \Lambda^{\hat\alpha}{}_{\hat\beta}(x)\, \mathcal{R}^{\hat\beta}{}_\nu$

Both sides of Eq. (28) transform in the same tetrad representation. If $\mathcal{R}^{\hat\alpha}{}_\nu = \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\zeta^\lambda$ in one tetrad, the same $\zeta$ works in a rotated tetrad. **Reconnection as a "there exists no $\zeta$" statement is local-Lorentz invariant.** `[deriv]`

Caveat: the statement **"reconnection occurs for the $\hat 0$ component"** is NOT Lorentz-invariant — a rotation mixes $\hat\alpha$ labels. The invariant content is: "no $\zeta$ absorbs the non-ideal term for the full collection $\{\mathcal{R}^{\hat\alpha}\}_{\hat\alpha=0..3}$."

### (ii) Transport-congruence covariance

Under $u \to u'$, equation (22) gives a **different** $\mathcal{R}$ because $\mathcal{R}$ is defined by $u$. The reconnection criterion then asks: does there exist $\zeta$ with $u' - \zeta$ smooth and nonvanishing such that $\mathcal{R}'^{\hat\alpha}{}_\nu = \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\zeta^\lambda$?

Writing $u' = u + \delta u$, $\mathcal{R}' = (u + \delta u)^\lambda \mathcal{F}^{\hat\alpha}{}_{\lambda\nu} = \mathcal{R}^{\hat\alpha}{}_\nu + \delta u^\lambda \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}$.

So choosing $\zeta = \delta u$ **always** gives $\mathcal{R}'^{\hat\alpha}{}_\nu = \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\zeta^\lambda + \mathcal{R}^{\hat\alpha}{}_\nu$, which equals $\mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\zeta^\lambda$ iff $\mathcal{R} = 0$ (the original was ideal). For non-ideal original $\mathcal{R}$, no choice of $\delta u$ trivially absorbs the new non-ideal term.

More carefully: the question is whether the NEW criterion for $u'$ is equivalent to the OLD criterion for $u$. They are related by the transformation of $\mathcal{R}$ under $u \to u'$. The absorption condition is:

$$(\mathcal{R}^{\hat\alpha}_\nu + \delta u^\lambda \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}) = \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\, \zeta'^\lambda$$

for some $\zeta'$ with $w' = u' - \zeta'$ smooth. Equivalently:

$$\mathcal{R}^{\hat\alpha}_\nu = \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\, (\zeta' - \delta u)^\lambda$$

which is the ORIGINAL absorption condition with $\zeta = \zeta' - \delta u$. And $w' = u' - \zeta' = u - (\zeta' - \delta u) = u - \zeta = w$. **The absorbing flow $w$ is congruence-independent.** `[deriv]`

**Therefore**: reconnection, defined by the impossibility of a smooth nonvanishing $w$ with $w^\lambda \mathcal{F}^{\hat\alpha}{}_{\lambda\nu} = 0$, is a statement about $\mathcal{F}^{\hat\alpha}$ and the spacetime admitting a smooth kernel vector field — not about the arbitrary initial choice of $u$.

---

## Algebraic rank reformulation

The reconnection criterion is equivalent to: **$\mathcal{F}^{\hat\alpha}{}_{\lambda\nu}$ (viewed at each point as a linear map $\zeta^\lambda \mapsto \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\zeta^\lambda$) does not admit a smooth global nonvanishing section of its kernel subbundle intersecting a neighborhood of $u$**.

At each spacetime point, $\mathcal{F}^{\hat\alpha}{}_{\mu\nu}$ for fixed $\hat\alpha$ is an antisymmetric 4×4 real matrix. Rank is 0, 2, or 4.

- **Rank 0**: $\mathcal{F}^{\hat\alpha} = 0$ pointwise; Eq. (22) gives $\mathcal{R} = 0$; everything trivial.
- **Rank 4** (non-degenerate): kernel is {0}; no nonzero $\zeta$ satisfies $\mathcal{F}^{\hat\alpha}\zeta = 0$. The linear map $\zeta \mapsto \mathcal{F}\zeta$ is bijective on $\mathbb{R}^4$. For any $\mathcal{R}^{\hat\alpha}{}_\nu$ satisfying the constraint $u^\nu \mathcal{R}_\nu = 0$, a unique $\zeta$ solves $\mathcal{R} = \mathcal{F}\zeta$. **The question collapses to: does the resulting $w = u - \zeta$ have a global smooth non-vanishing extension?** If yes, no reconnection; if no, reconnection. This is a **topological / global** question about the vector-bundle structure, not a local one.
- **Rank 2** (generic for radiative fields / Petrov Type II/III): kernel is 2-dimensional. Image of $\mathcal{F}\cdot$ is 2-dimensional. The constraint $u^\nu \mathcal{R}_\nu = 0$ cuts $\mathcal{R}$ to a 3-dim subspace. The image is 2-dim, so generic $\mathcal{R}$ is NOT in the image. **For rank-2 $\mathcal{F}^{\hat\alpha}$, reconnection is generic.** `[deriv]`

### Verdict

The reconnection criterion is **NOT a pure representation artifact**. It reduces to:

1. A **local algebraic condition**: rank of $\mathcal{F}^{\hat\alpha}$ and whether $\mathcal{R}$ lies in its image.
2. A **global topological condition**: whether $w = u - \zeta$ admits a smooth nonvanishing global extension.

Both are tetrad-covariant and congruence-independent (up to the trivial relabeling shown above). **The paper's framework is representation-safe.** `[deriv]`

---

## Caveats

- The rank-2 generic argument is at a **single point**. The full criterion requires absence of $w$ as a smooth field over a region. This is strictly weaker than I argued (a point-wise obstruction is sufficient but not necessary for global obstruction). For rank-4 $\mathcal{F}^{\hat\alpha}$ everywhere, obstruction is purely topological.
- I did not construct the explicit SymPy flat-space example Rio asked for. The question "can tetrad choice alone create artificial reconnection on Minkowski?" is answered **no** by the local-Lorentz covariance argument above — but a worked example would make it concrete and discoverable.
- B2 (Schwarzschild ideal-congruence check) and B3 (literature sweep) remain not-done.

---

## Status

Track B1 **conditionally cleared** (prose + algebraic sketch). Not formally falsifying; paper framework survives this probe. Worked SymPy example and B2/B3 would strengthen the verdict but do not change the conclusion. `[open]`: full falsification of representation-dependence awaits worked example.
