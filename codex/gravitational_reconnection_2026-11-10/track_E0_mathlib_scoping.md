# Track E0 — Mathlib differential-forms scoping

**Question**: Does the pinned mathlib have the API needed to state eq. (12)-(66) of the paper at the three-axiom bar, or does formalization require a private differential-forms library?

**Method**: grep `.lake/packages/mathlib/Mathlib/` for the ingredient APIs the paper uses.

---

## Findings (2026-11-10, local mathlib pin)

| Ingredient | Mathlib status | Exact location |
|---|---|---|
| `AlternatingMap` (pointwise alternating multilinear) | **Present** | `Mathlib/LinearAlgebra/AlternatingMap/*` |
| `ExteriorAlgebra` | **Present** | `Mathlib/LinearAlgebra/ExteriorAlgebra/*` |
| Smooth manifolds + tangent bundle | **Present** | `Mathlib/Geometry/Manifold/*` |
| `mlieBracket` (Lie bracket of vector fields on a manifold) | **Present** | `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean` (`def mlieBracket`, line 72) |
| `DifferentialForm` as a named type on a manifold | **Absent** | No match for `DifferentialForm`, `exteriorDerivative`, `extDeriv`, or `wedge` under `Geometry/` |
| **Lie derivative of a differential form** | **Absent** | No match for `lieDeriv`, `LieDerivative`, `LieDeriv ` in `Geometry/` (only Lie bracket of vector fields) |
| Stokes' theorem on manifolds | **Absent** | No match for `Stokes` under `Geometry/` |
| Flow of a vector field (integral curves) | **Partial** | `Mathlib/Geometry/Manifold/IntegralCurve/*` present; needed but not sufficient |

**Pinned toolchain**: Lean v4.24.0-rc1 (verified from earlier session builds).

## Verdict

**The paper's core machinery is NOT formalizable at the 3-axiom bar in current mathlib without building a private differential-forms library on manifolds.** `[deriv]`

Gap list, concretely:
1. Differential forms as sections of $\Lambda^k T^*M$ on a manifold, not just pointwise `AlternatingMap`. (Alternating maps exist in linear algebra but not as a bundle-valued type on `Manifold`.)
2. Exterior derivative $d$ as an operator on that type.
3. Lie derivative $\mathcal{L}_X$ of a $k$-form (currently only Lie bracket of vector fields exists).
4. Stokes' theorem $\int_{\partial M} \omega = \int_M d\omega$.

Each of these is a nontrivial mathlib contribution. Items 1–3 are in-flight across several mathlib efforts (the author has seen activity on `Mathlib/Geometry/Manifold/VectorField/` which includes `LieBracket.lean`) but have not landed. Stokes on manifolds is a known mathlib gap.

## Rio's stop rule triggers

Rio: *"if the API gap requires building a private differential-forms library, stop at the scoping report and say so. Do not silently build one."*

**Stopped.** Track E closes at scoping. The report above is the deliverable.

**Not feasible yet. Missing**: `DifferentialForm` type on manifolds, exterior derivative, Lie derivative of forms, Stokes' theorem on manifolds.

## What IS feasible in Lean now (narrow lane, not recommended)

A pure-$\mathbb{R}^n$ Stage-1 formalization using `AlternatingMap` and Fréchet derivatives could state **eq. (12) on $\mathbb{R}^4$** — but this is not the paper's content, which lives on a general manifold with tetrad structure. Stage 1 would formalize the EM analogue, not gravitational reconnection. Rio's Stage-1 note says "Stage 2 (manifolds) only if E0 shows the API is really there." It does not.

Formal Lean work on this paper **is not recommended** until mathlib's manifold-forms infrastructure matures. Revisit in 6-12 months.
