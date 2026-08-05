# The fractal-dimension direction: what the numerics say, and what is provable

**Date:** 2026-08-05. Opened after the r183–r204 transfer-operator arc.
**Motivation (Pablo's standing principle):** the framework's engine is
scaling / self-similarity. This record establishes where that is *already*
load-bearing in the corpus, and picks the next target accordingly.

## Where the scaling principle is load-bearing (not metaphor)

Two independent instances, both already kernel-checked:

1. **The canonical height is a renormalization limit.**
   `ĥ(R) = lim_n log H(2ⁿR)/4ⁿ` — double the point, divide by 4, iterate.
   The exponent `4 = 2²` IS the scaling dimension; the payoff law
   `ĥ(kR) = k²ĥ(R)` is the scaling law. r173 sharpened this: the *group is
   never needed* — it is Tate telescoping, pure scaling (r171/r173).
2. **The transfer operator is an IFS object.** The Gauss inverse branches are
   the archetypal self-similar system; `Tr(Lⁿ)` is a sum over `Kⁿ` words —
   the orbit tree at depth n — and r204's determinant assembles all depths.

Same engine both sides: a quantity defined as a limit over exponentially many
rescaled copies. Where the principle STOPS being a theorem: "everything
scales" proves nothing until one names *which* self-map and *which* exponent.
Every landed stone is an instance of naming those two precisely.

## Numerical findings (this session)

**(a) Our Lefschetz traces do NOT give clean dimension approximants.**
Solving `Tr(L_s^n) = 1` for the Gauss K=3 system:

| n | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| s_n | 0.5475 | 0.7288 | 0.6970 | 0.7037 | 0.7031 |

Oscillating about the true value, not monotone. Cause: our trace carries the
Lefschetz denominator `1/(1−Φ′_α)`, which shares the exponential growth rate
(hence the same pressure in the limit) but distorts finite levels. Recorded so
nobody builds a dimension claim on the raw trace equation.

**(b) The elementary cylinder bracket IS rigorous and does work.**
On the invariant interval `J = [1/(K+1), 1]`, bracketing by sup/inf of
`|Φ′_α|` over level-n cylinders (Falconer):

| n | bracket for dim_H(E₃) | width |
|---|---|---|
| 4 | [0.665868, 0.734942] | 0.069 |
| 6 | [0.678456, 0.724965] | 0.047 |
| 8 | [0.685046, 0.720014] | 0.035 |

**Every level contains Jenkinson–Pollicott's 0.705660908029.** Convergence is
slow — classical bounded-distortion loss, not an implementation defect.
Each bracket is a finite sum of explicit algebraic numbers: formalizable.

Caveat found the hard way: the bracket must be taken on the INVARIANT
interval. On `[0,1]` the level-1 sup is `|φ₁′(0)| = 1` exactly, the branch is
not a contraction there, and the upper equation has no root.

## mathlib feasibility scan

- `dimH` exists; `dimH_le_of_hausdorffMeasure_ne_top`,
  `le_dimH_of_hausdorffMeasure_ne_zero`, `dimH_iUnion`, `dimH_union`.
- `MeasureTheory.hausdorffMeasure_le_liminf_sum` — the covering bound.
  **The upper half is directly reachable.**
- `le_hausdorffMeasure` — the mass distribution principle. The lower half is
  reachable but needs a Gibbs/Bernoulli measure built on the Cantor set.
- **No IFS, self-similar, Moran, or thermodynamic-formalism theory anywhere.**
  That layer is ours to build.

## The plan

- **r205 (in progress).** (i) A general covering engine
  `dimH_le_of_bounded_covers` — no dynamics, mathlib-candidate shaped.
  (ii) The classical Moran/Falconer IFS upper bound: for a bounded
  self-covering set with contracting Lipschitz branches,
  `Σ_j Lip(φ_j)^d ≤ 1 ⟹ dimH ≤ d`. (iii) The Gauss instantiation, with the
  attractor taken as a hypothesis (self-covering), NOT constructed.
  The level-n refinement is free: apply the level-1 theorem to the word
  system — the same device as r191/r192.
- **r206.** The lower bound: mass distribution principle + a Gibbs measure.
  The harder half.

## Scope discipline for this direction

This is not a Millennium result and must never be presented as one. It is:
the first nontrivial fractal dimension in a proof assistant (to our
knowledge); it reuses the operator machinery of r183–r204; and the
pressure/Bowen apparatus it forces us to build is the same apparatus Mayer's
route to Selberg runs on. That last point is the honest connection to the RH
front — a shared tool, not a shortcut.
