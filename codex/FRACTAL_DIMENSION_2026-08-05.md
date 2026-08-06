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

---

## r208 — the Gauss sets, level-2 refinement (commit `60f38712`)

**File:** `PF/GaussDimension_r208.lean`, build 4,723 jobs, ten theorems on the
standard triple.

**Why the Gauss sets are harder than the Cantor set.** The branches are Möbius,
not similarities, so `|Φ′|` varies across each cylinder (distortion) and the
dimension is the root of **no finite Moran equation**. There is no closed form
to aim at — only enclosures.

**What is still explicit at level 2.** The composites remain Möbius:

    gauss2 K i j x = (x + (j+1)) / ((i+1)·x + 1 + (i+1)(j+1))
    cgauss2 K i j  = ((K+1) / ((i+1) + (K+1)(1 + (i+1)(j+1))))²   -- exact rational

so no continuant machinery is needed at this level. The constants were
cross-checked against an independent continuant-matrix computation and agree
term for term.

**Landed:** `gauss2_mapsTo`, `gauss2_lipschitzOnWith`, `cgauss2_lt_one`,
`gauss2_selfCover` (level-1 hypothesis applied twice), the general
`dimH_gauss_le_two`, and two numeric corollaries at the planned `d` values:

| K | level-1 (r205) | **level-2 (r208)** | Moran root | true value |
|---|---|---|---|---|
| 3 | ≤ 0.9227 | **≤ 77/100** | 0.76189 | 0.7056609 |
| 2 | ≤ 0.6715 | **≤ 29/50** | 0.56995 | 0.5312805 |

The gain comes purely from the true composite derivative rather than the
product of level-1 constants. Each per-term rational split was independently
re-verified outside Lean.

**Engineering note.** The Lipschitz proof had to be factored into two pure-real
lemmas (`mobius_abs_diff`, `mobius_lip`); an inline version hit a `whnf`
heartbeat timeout because `field_simp`/`nlinarith` choke on `set`-bound lets
wrapping `Nat.cast (Fin.val i)`. Worth remembering for any future Fin-indexed
real algebra.

**Scope, unchanged and load-bearing.** Upper bounds only. No lower bound for
`E_K` exists anywhere in the corpus. `29/50` and `77/100` do NOT approach
`0.5312805` and `0.7056609` and must never be quoted as approximations to them.

## Where the fractal front stands

- **Cantor set: SOLVED.** `dimH cantorSet = log₃2` exactly (r207).
- **Gauss sets: bracketed from above only.** Certified `≤ 77/100` (K=3),
  `≤ 29/50` (K=2). Numerically the truth is inside `[0.685, 0.720]` for K=3,
  but nothing below the upper bound is proved.
- **The open half.** A lower bound for `E_K` needs a Gibbs measure fed to
  r206's `le_dimH_of_massDistribution` — the bridge exists, the measure does
  not. Sharpening the upper bound past level 2 needs bounded distortion (the
  level-n constants stop being individually explicit). Both are real analytic
  work, neither is started, and neither is shortened by anything in this arc.

---

## Level-n brackets: the gap closes without RPF

Computed from the same machinery already built (exact rational constants;
`inf|Φ'_α| = 1/(C+D)²` and `sup|Φ'_α| = 1/(C/(K+1)+D)²` from the continuant
matrix `[[A,B],[C,D]]` of the word).

| K | n | words | bracket | width |
|---|---|---|---|---|
| 2 | 1 | 2 | [0.39394246, 0.67151337] | 0.278 |
| 2 | 2 | 4 | [0.47299477, 0.56995239] | 0.097 |
| 2 | 3 | 8 | [0.48607850, 0.56034345] | 0.074 |
| 3 | 1 | 3 | [0.54106575, 0.92267463] | 0.382 |
| 3 | 2 | 9 | [0.63539350, 0.76189330] | 0.126 |
| 3 | 3 | 27 | [0.65214701, 0.74701409] | 0.095 |

True values: `dim_H(E_2) = 0.5312805`, `dim_H(E_3) = 0.7056609`.

Consequence for the plan: the enclosure narrows by **level refinement alone**,
using r208's upper machinery and r209's lower machinery unchanged — only the
constants change, and they stay exact rationals. The equilibrium state (RPF)
would instead give the sharp value in one shot. Two independent directions:

- **r210 (cheap, incremental):** rerun r209's weighted-address argument on the
  level-2 word system. Expected `dim_H(E_3) ≥ 0.635`, `dim_H(E_2) ≥ 0.472`,
  giving `[0.635, 0.762]` and `[0.473, 0.570]`. Cost: the same file with
  9 (resp. 4) words instead of 3 (resp. 2). Level 3 costs 27 words — likely
  the practical ceiling for `norm_num` on rational powers.
- **RPF / equilibrium state:** the sharp value, but requires
  Ruelle–Perron–Frobenius theory that exists in no proof assistant. Not started.

Neither r208 nor r209 shortens the RPF route.

---

## r209 — the Gauss lower bounds, and the first two-sided enclosures (`188b548b`)

**File:** `PF/GaussLowerBound_r209.lean`, 1421 lines, 25 theorems on the standard
triple, build 4,724 jobs.

    dimH_gauss_three_enclosure : 54/100 ≤ dimH E ∧ dimH E ≤ 77/100
    dimH_gauss_two_enclosure   : 39/100 ≤ dimH E ∧ dimH E ≤ 29/50

No measure is constructed. The route is strong separation plus a weighted
address map:

- `gaussGap K = 1/(K(1 + K(K+1)))`, the gap between level-1 cylinders;
  `gaussGap 2 = 1/14`, `gaussGap 3 = 1/39`, both kernel-checked.
- `gauss_antilipschitz : agauss j * |x−y| ≤ |φ_j x − φ_j y|`, `agauss j = 1/(j+2)²`,
  proved algebraically through a pure-real lemma (no MVT).
- `gaddr`, the Bernoulli address map, built by r207's clamped telescoping
  technique with weights satisfying `p_j ≤ agauss_j^s` termwise.
- Hölder **without cylinder words**: an induction on a counter, peeling one
  branch at a time. Same branch spends budget and `p_i ≤ a_i^s` absorbs the
  rescaling exactly; a different branch is finished by the explicit gap. This
  avoided the `Fin n → Fin K` word machinery entirely.
- Surjectivity by `weight_cover` (the weight blocks tile `[0,1]`) + density and
  compactness, then r206's `le_dimH_of_holder_surj`.

### Three corrections to the design that was handed to the build

Recorded because they are the substance, not bookkeeping:

1. **The gap formula.** It is `1/(K(K²+K+1))`. The guess `(K+1)(K+2)` in the
   brief gives `1/12` and `1/20`, against measured `1/14` and `1/39`. Wrong.
2. **Orientation.** The Gauss branches `φ_j(x) = 1/(x+j)` are *decreasing*, so
   the functional equation must flip: `A(φ_i u) = Q_i + p_i(1 − A u)` with
   `Q_i = Σ_{j>i} p_j`. The unflipped form specified in the brief is
   geometrically impossible and breaks the clamped extension at both endpoints.
3. **Backward covering is not enough.** `E ⊆ ⋃_j φ_j '' E` is satisfied by
   `E = ∅`, so it cannot support a lower bound. `E` nonempty, closed, and
   forward-invariant (`MapsTo (φ_j) E E`) are now hypotheses — a real gap in
   the design, not a technicality.

### What these bounds are

A Bernoulli weighting, not the Gibbs state. A Bernoulli measure cannot attain
the dimension of a nonlinear conformal attractor, so the enclosures do not
close. True values `0.7056609` (K=3) and `0.5312805` (K=2) lie strictly inside
`[0.54, 0.77]` and `[0.39, 0.58]`.

### Two ways forward, unchanged

- **Refinement (machinery exists).** Rerun r208 and r209 on the level-2 word
  system: expected `[0.635, 0.762]` for K=3, `[0.473, 0.570]` for K=2. Level 3
  costs 27 words and is likely the `norm_num` ceiling.
- **Equilibrium state / RPF (sharp, not started).** Nothing in r205–r209
  shortens it. What r209 contributes onward is `gaussGap` and the two-sided
  branch estimates, both of which any RPF construction will need.
