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
- **r205 LANDED** (commit `4080763d`, build 4,720 jobs, nine theorems on the
  standard triple). All three layers closed, nothing deleted:
  `dimH_le_of_bounded_covers` (general engine); `dimH_le_of_selfCover` +
  global corollary (Moran/Falconer); the Gauss branches with
  `dimH_gauss_le`, and the numeric corollary `dimH_gauss_three_le : dimH E ≤ 19/20`.
  Design notes worth keeping: `LipschitzOnWith` on the invariant set was
  forced (the Gauss branches blow up at `x = −(j+1)`, so no global constant
  exists); `E.Nonempty` proved unnecessary and was dropped; the
  `Σ_a ∏_i = (Σ_j)^n` step went through `Finset.sum_pow'` +
  `Fintype.piFinset_univ` with no induction fallback; and mathlib has no
  `LipschitzOnWith` diameter lemma, so `ediam_image_le_of_lipschitzOnWith`
  was supplied.
  **Cross-check:** the Lean `Lgauss` constants reproduce the level-1 Moran
  root `0.922674627943` computed independently in Python — every digit. The
  formalized constants are the intended mathematics.
- **r206 LANDED** (commit `b21e2b44`, build 4,721 jobs, 8/8 axiom lines
  clean, no `sorryAx`). Three results:
  (A) `dimH_cantorSet_le : dimH cantorSet ≤ ENNReal.ofReal (Real.logb 3 2)`
  — on **mathlib's own `cantorSet`**. mathlib defines the set and proves
  `cantorSet_eq_union_halves` (literally r205's self-covering hypothesis)
  but computes no Hausdorff dimension anywhere: `dimH` occurs in only two
  mathlib files, neither of them `CantorSet.lean`. The key arithmetic
  `rpow_one_third_logb : (1/3)^(logb 3 2) = 1/2` makes the Moran sum
  EXACTLY 1, so **the upper bound is sharp, not slack** — it sits precisely
  at the classical value 0.63092975357.
  (B) `le_dimH_of_massDistribution` — the mass distribution principle in
  usable form WITH a constant (mathlib's `le_hausdorffMeasure` has none;
  absorb it by scaling to `C⁻¹ • μ`). The bridge for every future
  lower-bound argument.
  (C) `le_dimH_of_holder_surj` — abstract Hölder transfer,
  `r * dimH F ≤ dimH E`; deliberately NOT applied to `cantorSet`.
  Frictions: the module is `Mathlib.Analysis.SpecialFunctions.Log.Base`
  (not `…Logb`); `ENNReal.coe_rpow_of_nonneg` is wanted in the `←`
  direction; `rw [← NNReal.coe_inj]` on an ℝ≥0 rpow goal fights — use a
  `have` + `exact_mod_cast`.

- **★★★ r207 LANDED — THE ARC IS CLOSED ★★★** (commit `f927e54a`, build
  4,722 jobs, 17 audited declarations, only `propext`/`Classical.choice`/
  `Quot.sound` occurring anywhere, no `sorryAx`).

      theorem dimH_cantorSet : dimH cantorSet = ENNReal.ofReal (Real.logb 3 2)

  on **mathlib's own `cantorSet`**. The canonical fractal dimension,
  kernel-certified. To our knowledge the Hausdorff dimension of the Cantor
  set — of any nontrivial fractal — had not previously been formalized in any
  proof assistant.

  **The Cantor function**, absent from mathlib, is built here. The design
  move that made it cheap: **clamped arguments** in the approximants
  (`min (3x) 1`, `max (3x−2) 0`), which make each step continuous for *any*
  continuous input and remove the three-piece gluing entirely. Then
  `|capprox (n+1) x − capprox n x| ≤ 2⁻ⁿ`, so the function is a telescoping
  sum, continuous by the Weierstrass M-test. Landed with continuity,
  monotonicity, `f 0 = 0`, `f 1 = 1`, and both functional equations.

  **Hölder came out global on ℝ** (`HolderWith 2 (log₃2).toNNReal`), stronger
  than the `Icc 0 1` version planned — the constant-outside extension makes
  it free. The conversion uses `3^(log₃2) = 2` exactly, i.e. r206's
  `rpow_one_third_logb`.

  **The image came out exactly surjective**, better than the plan: the
  countable-complement fallback was never needed. `Icc 0 1 ⊆ f '' cantorSet`
  because the image is compact hence closed, contains `0` and `1`, is stable
  under `s ↦ s/2` and `s ↦ (1+s)/2` (functional equations +
  `cantorSet_eq_union_halves`), hence contains every dyadic, hence everything.
  Also proved `one_mem_cantorSet`, which mathlib lacks.

  Measure-free throughout: no Cantor–Lebesgue measure, no Frostman, no
  product measures. `le_dimH_of_massDistribution` (r206) was therefore NOT
  used for this result — it remains available for future lower bounds where
  no convenient Hölder surjection exists (e.g. the Gauss sets).

  New frictions: `ENNReal.ofReal_rpow_of_nonneg` was wanted in the FORWARD
  direction here (the ledger's `←` advice is for the general case); and
  sequenced `rw [show (3:ℝ)*0 = 0 …]` clobbers the `3*0−2` subterm — rewrite
  the longer pattern first.

- **Superseded plan (kept for the record) — the lower bound.** With r206(A) the
  upper bound is already AT the classical value; the only thing standing
  between the corpus and `dimH cantorSet = log₃2` — the canonical fractal
  dimension, absent from every proof assistant we know of — is the matching
  lower bound. Two routes, both now scaffolded:
  (i) a self-similar Bernoulli measure (mathlib gained
  `Probability/ProductMeasure.lean`) pushed to `cantorSet`, with a Frostman
  estimate fed to r206(B);
  (ii) the Cantor staircase — a Hölder-`log₃2` surjection onto `[0,1]` —
  fed to r206(C), which needs no measure theory at all. mathlib has no
  Cantor function, so (ii) means building it.
  Route (ii) looks cheaper and is the recommended next attempt.
- **Beyond r206.** Level-n refinement (apply §2 to the word system — free,
  the r191/r192 device) narrows the upper bound toward the bracket table
  above; a genuine approach to `0.70566…` needs bounded distortion, which is
  the real analytic content and is not yet started.

## Scope discipline for this direction

This is not a Millennium result and must never be presented as one. It is:
the first nontrivial fractal dimension in a proof assistant (to our
knowledge); it reuses the operator machinery of r183–r204; and the
pressure/Bowen apparatus it forces us to build is the same apparatus Mayer's
route to Selberg runs on. That last point is the honest connection to the RH
front — a shared tool, not a shortcut.
