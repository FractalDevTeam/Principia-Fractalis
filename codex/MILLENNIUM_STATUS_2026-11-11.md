# Millennium lane cross-axis status — 2026-11-11

**Author:** Pablo Cohen. **Head at write time:** `f2393f64` on `origin/master`.
**Motivation:** After a BSD-heavy session (11 commits, 5 rank≥1 capstones, Rio
audit closed), the natural next question is where other axes stand. This memo
is the honest answer. It corrects two prior scoping docs that are stale, and
names one concrete next-step target that is bounded.

Each axis section follows the same structure: **DEPLOYED** (what's in the tree
on three-axiom bar), **FRONTIER** (what's one step away), **BLOCKER** (what's
blocking the next layer), **NEXT** (a specific, bounded target).

---

## 1. Riemann Hypothesis (RH) — partial, march in progress

### DEPLOYED (three-axiom bar, no sorry)

* `rh_below_15_conditional` (2026-10-10, `PF/Analytic/RHBelow15Conditional_2026_10_10.lean`):

      `∀ hR1 hR2 hR3, ∀ σ t, 0 ≤ σ → σ ≤ 1 → -15 ≤ t ≤ 15 →
       riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1 / 2`

  **Conditional on R1 ∧ R2 ∧ R3 — the three right-edge sign facts for the
  Riemann ξ at σ = 1 across `t ∈ [0, 15]`** (split into subranges by sign).
* Box-local Fourier march: frontier currently at `t = 12.9375`
  (commit `2b1d07d2`), marching toward `t = 13` (then 13 → 15 in three blocks).

### FRONTIER

* The box-local march at c = 829/64 = 12.953125 hit a mathematical wall
  earlier this month: gate `lhs = 1.108 > 1` at `D = 1`, and the obstruction
  is NOT `r`-tunable (verified at `r = 1/64` and `r = 1/128`). Memo
  `principia_most_efficient_path_2026-11-09.md`.
* So the box-march needs a different ingredient to cross this specific
  interval. The rest of the interval (c = 827/64 → 12.9375) landed cleanly.

### BLOCKER

* The wall at c = 829/64. Needs either a sharper box-local analytic bound,
  or a different interval decomposition, or an alternative gate inequality.

### NEXT

**Not a continuation of the existing box march.** The specific bound wall is
not a one-session fix. The right next target depends on what Pablo wants:
* **Analytic/numerical re-examination** of the box-local gate at c = 829/64 —
  is there slack in a different parameter?
* **Different route to R1/R2/R3** — a non-box analytic argument for the
  interval `[12.9375, 15]` that doesn't go through the pointwise Fourier
  gate.

Both are open-ended. **No bounded target at this time on RH.**

---

## 2. Navier–Stokes (NS) — carrier-blocked, three-item gap ORDERED

### DEPLOYED

* Vortex-stretching bound discharged `909d944f` (new file
  `NS3DVortexStretchingBoundedDischarge.lean`, 2026-11-10) — the real-gap
  close, not a marker rewire. Discharges `VortexStretchingBoundedHypothesis`
  at every Galerkin `n`.
* FujitaKato scaffold repaired `0d132cb4` — Banach bilinear operator for
  mild solutions.
* Book framing updated (`a3d4d0cf`) — the "settled anchor" language was
  retired; ch22's conditional no-blow-up thesis is explicitly the lane's
  content, NS Clay statement is open.

### FRONTIER

* Route A assembly (per `codex/ROUTEA_SPEC_UPDATE_2026-10-19.md`) names
  three mathlib-absent items:
  1. Schwartz dense in `L²` (needs mollification).
  2. Convergence of Galerkin to the weak formulation (depends on item 1).
  3. Convolution `L¹ ⋆ L² → L²` (Young's inequality for this specific
     exponent triple).

* **Three items are an ORDERED chain** (per
  `codex/NS_ROUTEA_GAP_IS_ORDERED_2026-10-29.md`): item 1 reduces to item 3
  via mollification, and item 3 is the real root. Build order: **3, then 1,
  then 2b.**

### BLOCKER

Mathlib gap. Specifically:
* Mathlib has `convolution` definition.
* Mathlib has `Integrable.integrable_convolution` for the `L¹ → L¹` case.
* Mathlib does **NOT** have `convolution` paired with `MemLp` / `eLpNorm`.
* Mathlib does **NOT** have Minkowski's **integral** inequality (the
  `Minkowski` hits in `lpSpace.lean` and `MeanInequalities.lean` are the
  finite / discrete triangle inequalities).

### NEXT

**Item 3: `‖f ⋆ g‖_{L²} ≤ ‖f‖_{L¹} ‖g‖_{L²}` (Young's inequality for p=1, q=2, r=2).**

A direct proof bypasses Minkowski's integral inequality:

      |f ⋆ g(x)|² ≤ ‖f‖_1 · (|f| ⋆ |g|²)(x)        [Cauchy-Schwarz with weight |f|]
      ∫ |f ⋆ g(x)|² dx ≤ ‖f‖_1 · ∫ (|f| ⋆ |g|²)(x) dx
                       = ‖f‖_1 · ‖f‖_1 · ‖g‖_2²  [Fubini]
      ‖f ⋆ g‖_2 ≤ ‖f‖_1 · ‖g‖_2 ✓

Estimated ~150-250 Lean lines. Day-long dedicated session. **Potentially
upstream-able to mathlib** (would close a mathlib gap the scoping doc flagged).

---

## 3. Yang–Mills (YM) — **UNCONDITIONAL reflection positivity now in tree**

### DEPLOYED

★ `wilson_reflection_positivity_of_continuous` (2026-10-29/31,
`PF/YangMills/WilsonFubiniClosed_r385.lean:415`) ★

      `theorem wilson_reflection_positivity_of_continuous
         (hL : Even L) {K : ℕ} (β : ℝ)
         (F : Fin K → GaugeField L → ℂ)
         (hF_support : ∀ i, supportedOnPlusZero (F i))
         (hF_cont : ∀ i, Continuous (F i)) :
         (Matrix.of (fun i j =>
           ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
             ∂(wilsonGibbsMeasure L β))).PosSemidef`

On three-axiom bar, no sorry. **Reflection positivity for the Wilson action
on finite even periodic lattices, for continuous test functions supported on
`Λ_+ ∪ Λ_0`.** The `hFubini` hypothesis that stood as the blocker in r362
is now discharged by `wilsonFubini_corrected`.

### FRONTIER

Five directions, each a well-defined extension:
1. **Remove `Even L`** — may not be possible; the scoping note flagged it
   as a genuine lattice hypothesis, not a formality.
2. **Remove `Continuous`** (extend to `L² / L∞` test functions) — standard
   density argument IF mathlib has the required Gram-matrix continuity.
3. **Osterwalder-Schrader reconstruction** — from lattice RP to continuum
   relativistic QFT. Multi-month project; needs the thermodynamic limit.
4. **Mass gap** — explicit lower bound on the smallest non-vacuum
   eigenvalue. Multi-year to Clay-accept.
5. **Extend to non-abelian SU(N) beyond SU(2)** — current deployed
   machinery is specific to SU(2) via `SU2HaarUnimodular_2026_10_21.lean`.

### BLOCKER

None currently. The Oct 29 scoping doc `YM_BUILD_PLAN_STALE_2026-10-29.md`
originally named `hFubini` as the single remaining blocker; its "Second
addendum" (written same day after r385 landed) already acknowledges all
seven plan tasks done. Unlike the BSD scoping doc, no correction is needed.

### NEXT

**Update `YM_BUILD_PLAN_STALE_2026-10-29.md` to acknowledge r385
completion** (bookkeeping).

For a mathematical deliverable, the most bounded direction is **(2): extend
reflection positivity from continuous to `L²` test functions** via a density
argument. Standard but requires the Gram-matrix entries to vary continuously
with the test functions in `L²`. Bounded project, days not weeks.

---

## 4. Birch–Swinnerton-Dyer (BSD) — **SESSION'S HEAVY FOCUS, mostly done**

### DEPLOYED

* **Rank ≥ 1 on five curves:** E_91a1, E_102a1, E_131a1, E_141a1, E_80b
  (see `principia_bsd_session_2026-11-11_full.md`).
* **First exact rank in the repo:** Ch24's `Ecurve_rank_eq_zero` for
  y² = x³ + x (2026-10-17). First rank UPPER bound via descent. Combined
  with `Ecurve_card = 2` (today's `186f0008`), the full group structure.
* **8 redundant Heegner mirrors** retired via leaf bridge (`f0052c1a`).
* Rio audit 4/4 complete.

### FRONTIER

Per `codex/BSD_NEXT_STEPS_2026-11-11.md`:
* **(A)** Second rank-0 curve via `a⁴ − b⁴ ≠ c²`. Day-long. Pending.
* **(B.rank≤1)** Full Selmer machinery for exact rank 1. Multi-week.
  Pending.

### BLOCKER

(A) blocks on mathlib having only `a⁴ + b⁴ ≠ c²`, not the difference form.
(B.rank≤1) blocks on mathlib having no Selmer/descent-via-isogeny machinery.

### NEXT

(A) is the bounded one. Scope in the BSD_NEXT_STEPS doc.

---

## 5. Hodge Conjecture — **BLOCKED, archive files inconsistent**

### DEPLOYED

* **Nothing proven about Hodge.** The one Hodge-adjacent asset is
  `Ch20Ch25NumericObstructions.lean` which **refutes** book worked
  examples by comparing with genuine Hodge numbers from LMFDB. That's
  negative content — correctly identifying inconsistency.

### BLOCKER (worse than YM's was)

Per `codex/HODGE_SCOPING_BLOCKED_2026-10-17.md`:
* Mathlib has **no** Kähler manifolds, Hodge decomposition, harmonic forms,
  complex manifolds, algebraic cycles, Chow groups, or cycle class map.
* Archive `ARCHIVE/*/Hodge_Conjecture_COMPLETE.lean` files are not vacuous
  — they are **INCONSISTENT** (a single axiom entails `False`).
  Machine-demonstrated at the same time.
* **No lattice surrogate** — unlike YM, Hodge is intrinsically about
  smooth projective varieties over ℂ. There is no finite regularization
  whose solution would imply anything.

### NEXT

**No tractable target in-session.** The audit layer is the right level of
engagement on this axis. Honest scope: Hodge is PARKED until mathlib
acquires Kähler/complex-manifold machinery.

---

## 6. P vs NP — **PARKED, route cannot close**

### DEPLOYED

* `P_neq_NP : spectral_gap ≠ 0` in `PF/SpectralGap.lean`. Type-checks,
  three-axiom bar — but the theorem proves a real number is nonzero, not
  a statement about complexity classes.
* `P_neq_NP_under_empirical_postulate` and friends — conditional on an
  empirical postulate not formalizable as a Clay statement.

### BLOCKER

Per `codex/PNP_SPECTRAL_GAP_PARKED_2026-10-16.md`:
* The spectral-gap route **assumes its conclusion**. Producing the
  α-assignment that the route needs is logically equivalent to proving
  `ClassP ≠ ClassNP`. Proof in the repo.

### NEXT

**No tractable target.** PARKED.

---

## Cross-axis priority ranking for next sessions

In order of tractability × impact:

| rank | axis | target | estimate |
|---|---|---|---|
| 1 | **YM** | Update stale scoping doc + extend RP to L² test functions | Days (post-scoping-fix) |
| 2 | **BSD** | (A) Second rank-0 curve via `a⁴ − b⁴ ≠ c²` | Day |
| 3 | **NS** | Young's inequality `L¹⋆L² → L²` | Day-plus |
| 4 | **RH** | Re-examine box-local gate at c = 829/64 wall | Open-ended |
| 5 | **BSD** | (B.rank≤1) Full Selmer for exact rank 1 | Weeks |
| — | Hodge | Blocked | n/a |
| — | PNP | Parked | n/a |

## Note on scoping-doc hygiene

* `BSD_SCOPING_UPPER_BOUND_IS_THE_GAP_2026-10-17.md` — was stale, corrected
  in commit `8c39e54f` today. Original was dated the same day Ch24 landed.
* `YM_BUILD_PLAN_STALE_2026-10-29.md` — was proactively updated the same
  day (second addendum) acknowledging r385. No action needed.

The general lesson: when the scoping and the breakthrough are on the same day,
only one side of the pair gets updated. Reading scoping docs alone misses the
state of the tree. This memo reads the tree.

## What this memo is NOT

* Not a Clay-prize claim on any axis.
* Not a request for Pablo to approve anything specific.
* Not a replacement for the individual scoping docs — pointers, not content.
