# Track A — Verified reading & claim inventory

**Source**: Comisso & Asenjo, "Reconnection of Gravitational Fields," arXiv:2609.25241 (PRD 114, 084095, 2026). PDF text extracted locally on 2026-11-10 from the arXiv PDF (962 lines, pdftotext). All equations below are quoted from that extraction.

**Grading convention** (Rio's rule): `[paper]` = in the paper; `[quote]` = author quote not in paper; `[deriv]` = our derivation; `[open]` = open.

---

## Dependency chain, verbatim

**(12) Ideal Ohm-type condition** `[paper]`
$$u^\lambda \mathcal{F}^{\hat\alpha}{}_{\lambda\nu} = 0$$
Assumption on transport $u^\mu$ (timelike four-velocity). Implies / combined with identity $\nabla_{[\lambda}\mathcal{F}^{\hat\alpha}{}_{\mu\nu]} = 0$ to give (14).

**(14) Lie-transport statement** `[paper]`
$$(\mathcal{L}_u \mathcal{F}^{\hat\alpha})_{\mu\nu} = 0$$
Depends on (12) + algebraic identity.

**(18) Flux conservation** `[paper]`
$$\frac{d\Phi^{\hat\alpha}}{d\tau} = 0$$
Follows from (14) by the transport theorem for differential forms (quoted inline, not re-derived).

**(22) Non-ideal generalization** `[paper]`
$$u^\lambda \mathcal{F}^{\hat\alpha}{}_{\lambda\nu} = \mathcal{R}^{\hat\alpha}{}_\nu$$
Forces $u^\nu \mathcal{R}^{\hat\alpha}{}_\nu = 0$ by antisymmetry.

**(23) Non-ideal Lie transport** `[paper]`
$$(\mathcal{L}_u \mathcal{F}^{\hat\alpha})_{\mu\nu} = \nabla_\mu \mathcal{R}^{\hat\alpha}{}_\nu - \nabla_\nu \mathcal{R}^{\hat\alpha}{}_\mu$$

**(24) Flux change** `[paper]`
$$\frac{d\Phi^{\hat\alpha}}{d\tau} = \int_{S(\tau)} \nabla_{[\mu}\mathcal{R}^{\hat\alpha}{}_{\nu]} \, d\Sigma^{\mu\nu}$$

**(25) Local breakdown** `[paper]`: $\nabla_{[\mu}\mathcal{R}^{\hat\alpha}{}_{\nu]} \neq 0$.

**(28) Reconnection criterion (the pivot)** `[paper]`
Necessary condition for gravitational reconnection:
$$\mathcal{R}^{\hat\alpha}{}_\nu \neq \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\, \zeta^\lambda \quad \text{for every } \zeta^\mu \text{ with } w^\mu \equiv u^\mu - \zeta^\mu \text{ smooth and nonvanishing.}$$
Reason: if such $\zeta$ existed, (22) becomes $w^\lambda \mathcal{F}^{\hat\alpha}{}_{\lambda\nu} = 0$ (eq. 27), ideal transport applies with $w$ replacing $u$ — slip, not reconnection.

**(30) Reconnection rate under translational symmetry** `[paper]`
$$\frac{d\Phi^{\hat\alpha}_{\rm rec}}{d\tau} = \int_{C_{\rm sep}} u^\lambda \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\, dl^\nu$$

**(31) General reconnection rate** `[paper]`
$$\frac{d\Phi^{\hat\alpha}_{\rm rec}}{d\tau} = \max_\Upsilon \int_\Upsilon u^\lambda \mathcal{F}^{\hat\alpha}{}_{\lambda\nu}\, dl^\nu$$
over integral curves $\Upsilon$ of $u^\lambda \,{}^*\mathcal{F}^{\hat\alpha\mu}{}_\lambda$.

**(36) Energy-momentum exchange density** `[paper]`
$$X_{\hat\alpha} = 4\pi\sqrt{-g}\,\big(\mathcal{F}_{\hat\alpha\hat\beta\hat\gamma} + \mathcal{F}_{\hat\gamma\hat\beta\hat\alpha} - \mathcal{F}^{\hat\beta}{}_{\hat\alpha\hat\gamma}\big)\, A^{\hat\gamma}{}_\nu T^\nu{}_{\hat\beta}$$

**(40) Helicity divergence** `[paper]`
$$\nabla_\mu K^\mu = 2 \mathcal{R}^{\hat\alpha}{}_\mu \, {}^*\mathcal{F}^{\hat\alpha\mu\nu}\, u_\nu$$

**(42) Helicity change** `[paper]`
$$\frac{dH}{d\tau} = 2\int_{\Sigma(\tau)} \mathcal{R}^{\hat\alpha}{}_\mu \, {}^*\mathcal{F}^{\hat\alpha\mu\nu}\, u_\nu\, dV$$
(up to boundary flux; gauge invariance of $H$ requires closed $\Sigma$ or vanishing boundary term).

**(58) 3+1 induction** `[paper]`
$$\alpha\,\frac{\partial}{\partial t}\big(\sqrt{\gamma}\,\boldsymbol{\mathcal{B}}^{\hat\alpha}\big) - \nabla\times\big(\boldsymbol{v}\times\boldsymbol{\mathcal{B}}^{\hat\alpha}\big) = \nabla\times\!\left(\frac{\alpha}{\Gamma}\boldsymbol{\mathcal{R}}^{\hat\alpha}\right)$$

**(59) Local gravitational Reynolds-like number** `[paper]`
$$\Xi^{\hat\alpha}_\mathcal{R} \equiv \frac{\lVert \nabla\times(\boldsymbol{v}\times\boldsymbol{\mathcal{B}}^{\hat\alpha}) \rVert}{\lVert \nabla\times(\tfrac{\alpha}{\Gamma}\boldsymbol{\mathcal{R}}^{\hat\alpha}) \rVert}$$
$\Xi \sim \mathcal{O}(1)$ is **necessary context, not sufficient**. The paper's own caveat: "The presence of a significant non-ideal contribution alone is not sufficient for gravitational reconnection, which additionally requires that the non-ideal term cannot be eliminated by a redefinition of the spatial transport field, i.e. $\mathcal{R}^{\hat\alpha} \neq \zeta\times\boldsymbol{\mathcal{B}}^{\hat\alpha}$ (see condition (28))."

**(62) Vector reconnection rate (translational symmetry)** `[paper]`
$$\frac{d\Phi^{\hat\alpha}_{\rm rec}}{dt} = \int_{C_{\rm sep}} dl\,\hat\zeta \cdot \big(\alpha\boldsymbol{\mathcal{E}}^{\hat\alpha} + \boldsymbol{\beta}\times\boldsymbol{\mathcal{B}}^{\hat\alpha}\big) \cdot \hat\zeta$$

**(63) Vector general reconnection rate** `[paper]`
$$\frac{d\Phi^{\hat\alpha}_{\rm rec}}{dt} = \max_\Upsilon \int_\Upsilon dl\,\alpha\, \frac{\boldsymbol{\mathcal{E}}^{\hat\alpha}\cdot \boldsymbol{\mathcal{B}}^{\hat\alpha}}{|\boldsymbol{\mathcal{B}}^{\hat\alpha}|}$$
Driven by $\boldsymbol{\mathcal{E}}^{\hat\alpha}\cdot \boldsymbol{\mathcal{B}}^{\hat\alpha}$ — the gravitational analogue of plasma reconnection's $\boldsymbol{E}\cdot\boldsymbol{B}$.

**(66) Helicity evolution in 3+1 form** `[paper]`
$$\frac{dH}{dt} = 2\int_{\Sigma_t} d^3x\, \alpha\sqrt{\gamma}\,\frac{\boldsymbol{\mathcal{R}}^{\hat\alpha}\cdot\boldsymbol{\mathcal{B}}^{\hat\alpha}}{\Gamma}$$
up to boundary flux.

---

## Section IV enumeration of origins of $\mathcal{R}^{\hat\alpha}{}_\nu$ (VERBATIM paper text)

> "A nonvanishing $\mathcal{R}^{\hat\alpha}{}_\nu$ may have different origins."

1. "when **no transport congruence exists** for which Eq. (12) is satisfied." `[paper]`
2. "**Singularities, including those associated with black-hole spacetimes**, may constitute one possible source of non-ideal behavior." `[paper]`
3. "Other structures, such as **topological defects**, may also be relevant if they induce a departure from the ideal gravitational Ohm-type condition." `[paper]`
4. "Another possibility is that $\mathcal{R}^{\hat\alpha}{}_\nu$ represents an **effective coarse-grained description in which unresolved degrees of freedom are encoded in a non-ideal constitutive relation**. These unresolved degrees of freedom may belong to either the matter or gravitational sector. In the gravitational sector, they may include gravitational-wave modes on scales not resolved by the effective description." `[paper]`
5. "**Quantum effects** may also enter such an effective description. For example, quantum-field effects associated with **Hawking radiation** can influence the spacetime geometry through their backreaction." `[paper]`
6. "**Modifications of general relativity**, such as $f(R)$ gravity or theories involving **Lorentz violation in the gravitational sector**, alter the gravitational dynamics relative to general relativity. If such modifications produce a departure from the ideal gravitational Ohm-type condition, their effect could in principle be represented phenomenologically by $\mathcal{R}^{\hat\alpha}{}_\nu$." `[paper]`

**Important paper framing** (quoted): "Here, rather than specifying a particular form of $\mathcal{R}^{\hat\alpha}{}_\nu$, we examine the general conditions for gravitational reconnection."

---

## What the paper does NOT contain (negative inventory)

| Claim from Yahoo/ScienceAlert | In paper? | Source |
|---|---|---|
| Rotating black hole energy extraction via reconnection | **No** | Author quote only, not derived or stated in PRD |
| Jets from gravitational reconnection | **No** | Author quote only |
| Specific LIGO signature | **No** | Author quote only |
| Numerical simulation result | **No** | Paper is a framework; no simulation presented |
| Worked example / closed-form calculation | **No** | Paper is all general machinery |
| Specific functional form for $\mathcal{R}^{\hat\alpha}{}_\nu$ | **No** | Explicitly declined: "rather than specifying a particular form..." |
| Any α-value or numerical prediction | **No** | Paper silent on numerics |

The Yahoo/ScienceAlert claims are author-quote context, not PRD results. Do not propagate.

---

## Status

Track A **complete**. Dependency chain reconstructed, Section IV enumeration verbatim, negative inventory recorded. Nothing in the paper has been upgraded above its paper-level status.

Next: Track B1 (representation-safety test).
