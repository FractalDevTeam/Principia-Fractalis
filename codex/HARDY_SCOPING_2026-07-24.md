# Hardy Scoping — Closing `PositiveOnLineZetaZeroOrdinatesNonempty`

**Date:** 2026-07-24
**Author:** read-only scoping audit (no Lean edited, no claims changed)
**Purpose:** compare the two candidate routes for discharging the single bucket-1 atom
on the RH reduction (RESIDUAL_TRIAGE_2026-07-23 §1.1, shortlist item 4), with an honest
inventory of what the pinned mathlib does and does not provide.

**Toolchain:** Lean `4.24.0-rc1`; mathlib pinned to `v4.24.0-rc1`
(rev `eed770a434957369c6262aa3fb1d6426419016d4`), checkout at
`PF_Lean4_Code/.lake/packages/mathlib/`.

---

## 0. The exact Lean target

From `PF/Analytic/HilbertPolyaPositiveImageRigidity.lean` (line 49):

```lean
def PositiveOnLineZetaZeroOrdinates : Set ℝ :=
  {t : ℝ | 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0}
```

From `PF/Analytic/HilbertPolyaPositiveReductionToCountability.lean` (line 57):

```lean
def PositiveOnLineZetaZeroOrdinatesNonempty : Prop :=
  PositiveOnLineZetaZeroOrdinates.Nonempty
```

Unfolded, the target is:

> `∃ t : ℝ, 0 < t ∧ riemannZeta (Complex.mk (1/2) t) = 0`

Notes that pin down the obligation:

- **Which zeta:** mathlib's `riemannZeta` (`Mathlib.NumberTheory.LSeries.RiemannZeta`,
  defined as `hurwitzZetaEven 0`, i.e. via the completed/Mellin route, analytically
  continued, with the convention `riemannZeta 0 = -1/2`). No project-local zeta is
  involved; the atom is stated against mathlib's function directly. Good.
- **Coercion detail:** the point is written with the anonymous constructor
  `⟨1/2, t⟩ : ℂ` (`Complex.mk`), not `1/2 + t * I`. Any proof built with the usual
  `1/2 + t * I` form needs a one-line `Complex.ext` bridge (`re = 1/2`, `im = t`).
  Trivial but must not be forgotten.
- **Strict positivity:** `0 < t` strict. Any witness `t ≈ 14.13` clears this by miles;
  nothing subtle here.
- **Sibling atom (already closed):** `PositiveOnLineZetaZeroOrdinatesCountable` was
  discharged unconditionally in Wave 59
  (`PF/Analytic/PositiveOnLineZetaOrdinatesCountableDischarge.lean`) from
  `differentiableAt_riemannZeta` + the analytic identity theorem + Lindelöf countability.
  Axiom budget of that chain: `[propext, Classical.choice, Quot.sound]`. The Nonempty
  atom is the **only** remaining bucket-1 item on the RH reduction; discharging it
  feeds `rh_wave58_countability_reduction_capstone` and collapses the honest RH
  residual to HP-program (bucket 3) + empirical-α (bucket 2).
- **Axiom-budget context:** the whole RH chain advertises
  `[propext, Classical.choice, Quot.sound]` and `#print axioms` checks are committed in
  the files. `native_decide` appears in 3 unrelated PF files but **not** on the RH chain.
  Any discharge that leans on `native_decide` (adds `Lean.ofReduceBool`) would break the
  advertised budget of the capstone. This is a real decision point for Route B (see §3).

---

## 1. Pinned-mathlib inventory (honest: present / partial / absent)

| Area | Status | Module(s) / declarations | Notes |
|---|---|---|---|
| `riemannZeta` definition + analyticity | **Present** | `Mathlib.NumberTheory.LSeries.RiemannZeta`: `riemannZeta`, `differentiableAt_riemannZeta`, `riemannZeta_zero`, `riemannZeta_one` (via `Harmonic/ZetaAsymp`) | Already exercised by Wave 59. |
| Completed zeta / functional equation | **Present** | same file: `completedRiemannZeta`, `completedRiemannZeta₀`, `differentiable_completedZeta₀`, `differentiableAt_completedZeta`, `completedRiemannZeta_one_sub`, `riemannZeta_one_sub`, `completedRiemannZeta_eq` (`Λ = Λ₀ − 1/s − 1/(1−s)`), `completedRiemannZeta_residue_one` | The FE is fully in tree. `Λ₀` is entire. |
| ζ ↔ Λ bridge (Gamma factor) | **Present** | `riemannZeta_def_of_ne_zero` (`ζ s = Λ s / Gammaℝ s`), `Complex.Gamma_ne_zero`, `Complex.Gammaℝ` API (`Mathlib.Analysis.SpecialFunctions.Gamma.*`) | On the line `s = 1/2 + it`, `t ≠ 0`, `Gammaℝ s ≠ 0`, so `Λ(s) = 0 ↔ ζ(s) = 0`. Cheap. |
| Dirichlet series representation | **Partial** | `zeta_eq_tsum_one_div_nat_cpow` — **only for `1 < re s`** | **No** representation of ζ on the critical line (no Dirichlet-eta, no truncated-sum-with-error). |
| Nonvanishing results | **Present (wrong line)** | `riemannZeta_ne_zero_of_one_le_re` (`Mathlib.NumberTheory.LSeries.Nonvanishing`) | Covers `Re ≥ 1` only. Irrelevant to on-line zeros except as sanity anchor. |
| Conjugation symmetry of ζ / Λ | **Absent** | — (`Complex.Gamma_conj` **is** present, `Gamma/Basic.lean:354`) | `riemannZeta (conj s) = conj (riemannZeta s)` is **not in tree**. This is the key missing lemma for a real-valued witness function; provable by the identity theorem (agree on `(1,∞)`) — same machinery Wave 59 already used. |
| Jacobi theta | **Present, real depth** | `Mathlib.NumberTheory.ModularForms.JacobiTheta.{OneVariable,TwoVariable,Bounds}`: `jacobiTheta_eq_tsum_nat`, `jacobiTheta_S_smul` (modular transform), `norm_jacobiTheta_sub_one_le` (**explicit** tail bound `≤ 2 e^{−π Im τ}/(1 − e^{−π Im τ})`), `isBigO_at_im_infty_jacobiTheta_sub_one` | The explicit tail bound is exactly what Route B's truncation needs. |
| Mellin transforms / abstract FE | **Present** | `Mathlib.Analysis.MellinTransform`, `Mathlib.Analysis.MellinInversion`, `Mathlib.NumberTheory.LSeries.AbstractFuncEq` (`WeakFEPair`, `StrongFEPair`, `Λ`, `Λ₀`, `functional_equation`), `HurwitzZetaEven` (`evenKernel`, `hurwitzEvenFEPair`) | `completedRiemannZeta` **is by definition** a Mellin integral of an explicit theta kernel. Extracting a concrete `∫_1^T` + tail formula is real work but all ingredients are in tree. |
| Cauchy integral formula | **Present** | `Mathlib.Analysis.Complex.CauchyIntegral`, `TaylorSeries`, `RemovableSingularity`, `AbsMax`, `PhragmenLindelof`, `Hadamard` (three-lines) | Solid. |
| Residue theorem / argument principle | **Absent** | — (grep for residue/argument-principle in `Analysis/Complex`: nothing; `ValueDistribution/` has Nevanlinna counting functions + First Main Theorem but no argument-principle zero counting usable here) | Rules out Turing/Backlund-style zero-counting routes. Do not plan through them. |
| Jensen's formula | **Absent** | (only `PosLogEqCircleAverage` fragments) | Same conclusion. |
| Certified numerics: constants | **Present (constants only)** | `Real.exp_one_gt_d9/lt_d9`, `exp_one_near_20`, `log_two_near_10` (`Analysis/Complex/ExponentialBounds`), `pi_gt_d20/pi_lt_d20` (`Analysis/Real/Pi/Bounds`) | Digit bounds for `e`, `log 2`, `π` only. |
| Certified numerics: function evaluation | **Absent** | `Real.exp_bound` / `Complex.exp_bound` (Taylor remainder, `Analysis/Complex/Exponential.lean:367,515`) exist as raw ingredients; `Tactic/NormNum/*` has **no** extension for `exp`/`log`/`cos`/`Gamma`/`zeta`; no `Interval` type, no Taylor-model tactic, no Arb-style ball arithmetic anywhere in mathlib | **This is the wall for Route B.** Every certified function value must be hand-assembled from Taylor bounds + `norm_num`, or imported from outside mathlib. |
| Euler–Maclaurin | **Absent (as such)** | `Mathlib.NumberTheory.AbelSummation` (Abel summation, order-0/1 analogue); `Harmonic/ZetaAsymp` does a bespoke order-1 EM for **real** `s` near 1 | No general EM with remainder; no complex-`s` truncated zeta with error term. |
| IVT / continuity glue | **Present (trivially)** | `intermediate_value_Icc`, `intermediate_value_Icc'`; continuity of `Λ` on the line from `differentiableAt_completedZeta` | No risk here. |
| Project-local numerics (PF side) | **Present but far below need** | `PF_Lean4_Code/IntervalArithmetic.lean` (587 lines: `Interval` struct, d8 bounds for `√2`, `φ`, `π/10`), `PF/Analytic/GammaIntervalBounds.lean`, `BookEval*` | Precedent for interval-style certification in-project, but only for algebraic constants via `norm_num`; nothing evaluates a transcendental function at a point. |

**One-line summary of the inventory:** everything *structural* (FE, theta, Mellin,
analyticity, IVT) is present; everything *quantitative* (evaluation of ζ/Λ/Γ at a point
with certified error) is absent, both from mathlib and from the project.

---

## 2. Route A — a minimal slice of Hardy's theorem

### 2.0 Shape of the minimal argument

We need ONE zero, not infinitely many. The cheapest classical skeleton, run on the
**Riemann Ξ-function** `Ξ(t) := completedRiemannZeta (1/2 + t*I)` (real-valued for real
`t`, once conjugation symmetry is proved):

1. If `Ξ(t) ≠ 0` for all `t > 0`, then (IVT + `Ξ` continuous + `Ξ(0) = Λ(1/2) ≠ 0`)
   `Ξ` has constant sign on `[0, ∞)`.
2. Hardy's integral identity: a weighted transform of `Ξ` along the line equals an
   explicit theta-type expression, e.g. the classical
   `∫₀^∞ Ξ(t)/(t²+¼) · cosh/cos kernel dt = explicit function of θ`, obtained by Mellin
   inversion of the theta representation (mathlib: `MellinInversion` + `hurwitzEvenFEPair`).
3. Asymptotics of the right-hand side as the parameter approaches the boundary
   (theta near the rotated point; uses `jacobiTheta_S_smul` + tail bounds): the RHS
   oscillates/changes sign or violates the growth that a constant-sign integrand forces.
4. Contradiction with constant sign ⇒ some `t₀ > 0` with `Ξ(t₀) = 0` ⇒ (Gamma-factor
   nonvanishing) `ζ(1/2 + i t₀) = 0`. No numerics anywhere.

### 2.1 Milestones

| # | Milestone | Content | Mathlib gaps hit | Effort class |
|---|---|---|---|---|
| A1 | **Ξ is real-valued** | Prove `completedRiemannZeta (conj s) = conj (completedRiemannZeta s)` (identity theorem: both sides analytic on ℂ∖{0,1}, agree on `(1,∞)` where the tsum is real-term); define `Xi : ℝ → ℝ`, prove continuity on `(0,∞)` | none (Wave 59-style machinery) | **days–1 week** |
| A2 | **Bridge lemma** | `(∃ a b, 0 < a ∧ a < b ∧ Xi a * Xi b < 0) → PositiveOnLineZetaZeroOrdinatesNonempty`; also the weaker `(∃ t > 0, Xi t = 0) → target`. Includes the `⟨1/2,t⟩` vs `1/2 + t*I` `Complex.ext` bridge and `Gammaℝ ≠ 0` on the line | none | **days** |
| A3 | **Concrete integral rep of Λ** | Extract from `hurwitzEvenFEPair 0` the explicit formula `Λ(s) = ∫₁^∞ (θ(iu)−1)/2 · (u^{s/2−1} + u^{(1−s)/2−1}) du − 1/s − 1/(1−s)` as a usable lemma | none in principle; unfolding `WeakFEPair`/`evenKernel` plumbing is fiddly | **1–3 weeks** |
| A4 | **Hardy transform identity** | Mellin/Fourier inversion to get the weighted-Ξ integral identity; justify all interchanges (Fubini + dominated convergence with the theta tail bound) | `MellinInversion` present but never exercised at this level; interchange lemmas are bespoke | **1–3 months** |
| A5 | **Boundary asymptotics + contradiction** | Behavior of the theta side at the boundary (modular transform at the rotated point, uniform error control); derive the sign contradiction against a constant-sign Ξ | the analysis is standard-on-paper but every estimate is bespoke in Lean; nothing reusable in tree | **2–4 months** |

### 2.2 Hardest step and honest total

**A5** (with A4 close behind). These are exactly the "substantial formalization" the
triage flagged. Total: **4–9 months** of focused expert effort. Zero numerics, zero
new axioms; end product (Hardy-slice) would be a genuinely publishable mathlib
contribution (ITP-paper grade — nobody has this in any prover, see §4).

### 2.3 Risk

The estimate chain in A4/A5 is research-grade formal analysis. Paper proofs compress
"by dominated convergence" and "for T large enough" into lines that each cost weeks.
Realistic failure mode: 6 months in, A4 done, A5 half-done, no discharged atom. Note
partial mitigation: even a stalled Route A leaves A1–A3 as standalone value (A1/A2 are
also Route B's first two milestones, A3 is Route B's third).

---

## 3. Route B — certified numerical zero at t ≈ 14.1347

### 3.0 Shape of the argument (numerics-minimal form)

Do **not** define the Riemann–Siegel Z or θ functions (arg Γ is avoidable). Use the same
real witness `Ξ(t) = Λ(1/2+it)` as Route A:

- `Ξ(14) < 0 < Ξ(15)` (true values: `Ξ(14) ≈ −2.05e−6`, `Ξ(14.2) ≈ +8.6e−7`,
  `Ξ(15) ≈ +6.27e−6`; sign change brackets the first zero `t₁ ≈ 14.134725`).
- IVT ⇒ `∃ t ∈ (14, 15), Ξ(t) = 0` ⇒ bridge lemma ⇒ target. `0 < t` is free.

Verified this session with an order-6 Euler–Maclaurin evaluation (pure Python, 60
terms): `Z(14) ≈ −0.1056`, `Z(14.2) ≈ +0.0520`, and `Λ(1/2+it)` real to 20 digits —
the sign gap is comfortable, not marginal.

### 3.1 What the certified evaluation actually requires

Evaluate `Λ(s) = Λ₀(s) − 1/s − 1/(1−s)` at `s = 1/2 + 14i` and `1/2 + 15i` via the A3
integral representation:

- **Tail:** integrand ≤ `2e^{−πu}·u^{−3/4}·(1+ε)` (from `norm_jacobiTheta_sub_one_le`,
  in tree); truncating at `u = 8` leaves tail `< 10^{−10}`. Cheap and fully in-tree.
- **Cancellation:** at `s = 1/2+14i`, the pole part `1/s + 1/(1−s) ≈ 5.0955e−3` and
  `Λ₀(s)` agree to ~3 digits; `Λ ≈ −2e−6`. So the integral over `[1,8]` must be
  certified to absolute error `≲ 5·10^{−7}`, i.e. ~13–14 correct bits **after** a
  3-digit cancellation → need ~24 bits of working precision. Modest for interval
  arithmetic; brutal by hand.
- **Integrand evaluations:** each point needs certified `exp(−πn²u)` (n = 1..3),
  `u^{−3/4}`, and `cos/sin((t/2)·log u)` (the oscillation `u^{it/2}`; phase sweeps ~15
  rad over `[1,8]`, a few oscillations). With a rigorous 2nd-derivative bound and
  composite Simpson, order 10³–10⁴ certified interval evaluations. **This cannot be
  hand-written as `norm_num` chains**; it needs a computable (kernel-reducible)
  rational/dyadic interval-arithmetic layer with proven `exp`/`log`/`cos` enclosures
  (mathlib has the raw Taylor-remainder lemmas `Real.exp_bound` etc., and `π` to d20 —
  the ingredients exist, the framework does not).

### 3.2 Milestones

| # | Milestone | Content | Effort class |
|---|---|---|---|
| B1 | = A1 (Ξ real + continuous) | shared | **days–1 week** |
| B2 | = A2 (bridge lemma) | shared | **days** |
| B3 | = A3 (concrete integral rep + tail bound ≤ 10⁻¹⁰ at cutoff 8) | shared | **1–3 weeks** |
| B4 | **Certified quadrature engine** | dyadic-rational interval type with proven arithmetic; certified enclosures for `exp`, `log`, `cos`, `rpow` on the needed ranges; verified composite-Simpson (or midpoint + derivative bound) with an error theorem; must run inside the kernel (`decide`-free `norm_num`-style reflection or well-founded computation) if the axiom budget is to be preserved | **2–4 months from scratch**; **2–6 weeks** if adopting an existing Lean interval library (see risk) |
| B5 | **Two evaluations + glue** | certify `Ξ(14) < 0`, `Ξ(15) > 0`; IVT; discharge the atom; `#print axioms` check | **days–1 week** once B4 exists |

Total: **~3–5 months from scratch**, potentially **~1–2 months** with an imported
interval library.

### 3.3 Hardest step and risks

**B4**, unambiguously. Three specific risks, in order of severity:

1. **Axiom budget vs. compute budget.** The honest fast path for bulk interval
   computation in Lean is `native_decide` — which adds `Lean.ofReduceBool` and would
   **break the advertised `[propext, Classical.choice, Quot.sound]` budget** of the RH
   capstone chain (the corpus's committed `#print axioms` lines would change).
   Kernel-only evaluation of ~10⁴ dyadic interval ops is feasible (this is
   Flyspeck-scale-minus-several-orders) but needs careful engineering to keep
   elaboration/kernel time sane.
2. **External dependency.** Geoffrey Irving's `interval` library (github.com/girving/interval)
   is real prior art for exactly this style of certified computation in Lean 4
   [uncertainty flag: my knowledge of its axiom profile and current toolchain support is
   from before 2026; it must be checked against `v4.24.0-rc1`, and parts of it have used
   `native_decide`-adjacent tricks]. Adopting it trades months of work for a dependency
   + axiom question; vendoring a minimal slice is a middle path.
3. **Precision bookkeeping.** The 3-digit cancellation at `t = 14` is fixed and known;
   if a chosen quadrature scheme's constants are sloppy by 10², the point count grows
   10×, hitting kernel-time limits. Mitigation: the sign margin at `t = 15`
   (`+6.3e−6`) and `t = 14` (`−2.1e−6`) is known in advance, so the precision target is
   not a moving goalpost.

---

## 4. Shared infrastructure (both routes) and prior art

**Shared (build first regardless of route choice):**

1. `completedRiemannZeta_conj` / `riemannZeta_conj` (conjugation symmetry) — absent
   from mathlib, needed by both, and a clean upstream PR on its own.
2. `Xi : ℝ → ℝ` real-valued witness + continuity on `(0,∞)`.
3. Bridge lemma: sign change (or zero) of `Xi` on `(0,∞)` ⇒
   `PositiveOnLineZetaZeroOrdinatesNonempty`, including the `Complex.mk` vs `+ t*I`
   bridge and `Gammaℝ`-nonvanishing on the line.
4. (A3/B3) concrete truncated theta-integral representation of `Λ` with explicit tail
   bound — Route B needs it for evaluation; Route A needs it as the launchpad for the
   Hardy transform.

**Prior art (from training knowledge, no web access — flag: verify before citing):**

- **Isabelle/HOL (Eberl et al.):** AFP `Zeta_Function` (analytic continuation +
  functional equation), AFP `Euler_MacLaurin`, AFP `Prime_Number_Theorem`
  (Eberl–Paulson). None of these contains an on-line zero or Hardy's theorem.
- **HOL Light (Harrison):** analytic PNT via Newman; nonvanishing on `Re = 1` only.
- **To my knowledge, no proof assistant has ever certified a single on-critical-line
  zeta zero, nor formalized Hardy 1914.** Either route, completed, is a first.
  [Moderate confidence; a check of AFP/mathlib activity after early 2026 is advised.]
- **Unformalized rigorous numerics:** Arb (Johansson) computes ζ zeros with certified
  ball arithmetic and is the reference for what B4's error analysis should look like;
  Coq's CoqInterval shows the whole pipeline is feasible in a kernel-checked setting.
- **Lean 4 interval arithmetic:** girving/interval (see §3.3 risk 2).

---

## 5. Recommendation

**Recommend Route B, entered through the shared milestones, with a hard go/no-go gate
before B4.**

Reasons, soberly:

- Route B's endpoint is **bounded**: the target values and margins are known constants
  (`−2.1e−6` / `+6.3e−6`); the only open-ended cost is engineering (B4). Route A's
  endpoint is **unbounded**: A4–A5 are research-grade formal analysis where paper-to-Lean
  expansion factors of 3–10× are normal.
- The first three milestones are **identical** for both routes, so no work is wasted
  before the fork. Decide A vs B only after B3, when the integral representation is in
  hand and a realistic kernel-time experiment for interval arithmetic can be run in a
  day.
- **Single biggest risk, Route B:** no kernel-acceptable numerics path — i.e. B4 is
  only practical via `native_decide`, which breaks the RH chain's advertised axiom
  budget. If the owner is willing to accept `Lean.ofReduceBool` **on this one atom**
  (documented loudly), Route B's risk collapses and the total drops toward 1–2 months.
  If the budget is non-negotiable, Route B is 3–5 months with real engineering risk.
- **Single biggest risk, Route A:** A5 stalls after months with nothing discharged;
  effort class is honestly 4–9 months and the variance is high.
- Honest framing for the corpus: closing this atom changes the RH reduction's status
  line from "two open atoms + one blocked" to "the only remaining RH inputs are the
  HP-program conjecture (bucket 3) and empirical-α (bucket 2)." It does **not** move
  the Clay bar, and should not be sold as doing so — same register as the triage.

---

## 6. Proposed first milestone (self-contained, PR-able even if the route stalls)

**M1: "The Riemann Ξ-function is real-valued, and a sign change implies the atom."**
One new file, e.g. `PF/Analytic/XiRealWitness.lean`, containing:

1. `completedRiemannZeta_conj : completedRiemannZeta (conj s) = conj (completedRiemannZeta s)`
   (and the `riemannZeta_conj` corollary) — proved by the identity theorem on ℂ∖{0,1}
   against the real-term tsum on `(1,∞)`; exactly the Wave 59 machinery
   (`AnalyticOnNhd`, preconnectedness of a punctured plane, `eqOn` propagation).
2. `def Xi (t : ℝ) : ℝ := (completedRiemannZeta (1/2 + t*I)).re` with
   `Xi_im_eq_zero : (completedRiemannZeta (1/2 + t*I)).im = 0` and
   `continuous_Xi_on_pos`.
3. `theorem xi_sign_change_implies_nonempty :
   (∃ a b : ℝ, 0 < a ∧ a < b ∧ Xi a * Xi b < 0) →
   PositiveOnLineZetaZeroOrdinatesNonempty` — IVT + `Gammaℝ`-nonvanishing +
   `Complex.ext` bridge to the `⟨1/2, t⟩` form.
4. Committed `#print axioms` lines; expected budget `[propext, Classical.choice, Quot.sound]`.

Why this is the right first brick:

- **Required by both routes** (it is A1+A2 = B1+B2); zero throwaway work.
- **Effort class: ~1–2 weeks** — same machinery as the already-succeeded Wave 59
  discharge, so it matches the corpus's demonstrated capability profile.
- **Independently valuable:** `riemannZeta_conj`/`completedRiemannZeta_conj` is a
  genuine mathlib gap and a clean upstream PR; the reality of Ξ is a citable standalone
  fact.
- **Honest even in failure:** if everything downstream stalls, the corpus still gains
  "the RH Nonempty atom is equivalent to a sign change of an explicit real-valued
  function" — a strictly sharper reduction than today's, in the same reduction-brick
  style as Waves 57–59.

---

*Scoping only. Nothing committed, nothing pushed, no Lean modified.*
