# Navier-Stokes scoping: the lane is genuinely the furthest along — and ONE carrier change unblocks three separate dead ends at once.

**Date:** 2026-10-17 (Legion, audit on Acer). Inventory + scoping. No Lean.
Labels FACT / MEASURED / JUDGEMENT / OPEN.

**FIRST, A PRESERVATION ACTION TAKEN.** The faithful-statement migration is on
an **unpushed** branch — `ns-faithful-migration` @ `3441342b`, worktree
`/Storage 2TB/home/xluxx/ns-faithful-wt`, 4 commits, **no remote ref**. Four
commits of EXIT-0-verified work on one disk. I bundled it before touching
anything else:

* `~/backups/ns-faithful-migration_2026-10-17.bundle` (full history, 275 MB,
  md5 `d06c6588a6225bb6f4ebe6bd3031974c`, `git bundle verify` clean)
* `~/backups/ns-faithful-THIN_2026-10-17.bundle` (the 4 commits, 15.5 KB,
  md5 `e5adf9cbb3705ff5745d7eb61a27f597`) — **copied to Legion**
  `D:\CLAUDE-i9\_backups\ns-faithful-2026-10-17\`, md5 verified identical.

**Pushing the branch to origin is the real fix and is Pablo's call** (it changes
the project's public surface). The bundles remove the single-disk risk in the
meantime.

**VERDICT: NEXT BUILD IDENTIFIED, with one structural precondition.** The
inventory is much healthier than YM or Hodge — ~7,700 lines of genuine harmonic
analysis with zero `sorry` — but three separate capstones are blocked by the
*same* cause, and it is not a missing mathlib lemma. It is the **carrier**.

> **`SchwartzMap` is a Fréchet space with no `NormedAddCommGroup` instance;
> `intervalIntegral` requires one. So Bochner integration into Schwartz space is
> structurally unavailable — permanently, not pending.** Switching the
> time-dependent field's codomain from Schwartz to a Banach space (`L²` /
> `Ḣ^{1/2}`) unblocks the bilinear operator, makes blow-up *expressible*, and
> matches the actual Fujita–Kato setting. One change, three dead ends.

---

## 1. The "literal Clay statement" file — VACUOUS. MEASURED

`PF/NavierStokes/Fefferman2000_LiteralClayNS3D_Statement_2026_06_19.lean`,
284 lines. Line 137, verbatim:

```lean
def SatisfiesLiteralNSE … := ∀ t : ℝ, 0 ≤ t → u t = u t
```

**The Navier–Stokes equation is replaced by a tautology.** The file has the
right *shape* — `IsLiteralDivergenceFree` (109), `HasBoundedEnergy` (122),
`MatchesInitialDatum` (140), assembled into
`Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000` (172) — with the actual
PDE removed. Also `literal_clay_NS_substrate_bridge_substrate_position : True
:= trivial` (278).

**So: it is not the Fefferman formulation.** It is the Fefferman *skeleton* with
the equation deleted. Confirms the prior ledger finding exactly.

**The repair already exists**, on the unpushed branch:
`Fefferman2000_Faithful_Statement_2026_10_12.lean`, elaborating EXIT 0, no
sorries, with a build-backed non-vacuity check (derivatives bound to `U`/`P`,
`ContDiffOn ⊤` both, `u₀ = 0` trivial while nonzero `u₀` forbids `U = 0`).
**That is the single most valuable artefact on this axis and it is the one that
is unpushed.**

## 2. FujitaKato1964/ — the linear theory is REAL; the bilinear step is a shell. MEASURED

**31 files, ~7,700 lines, ~212 theorems, zero `:= True`, zero `sorry`.** This is
not scaffolding-shaped; it is a genuine build. Spot-checking the load-bearing
estimate (`HeatContractsSobolev.lean:187`):

```lean
theorem homogeneousH12SeminormSqOfHeatEvolved_le_under_integrability
    (t : ℝ) (ht : 0 ≤ t) (f : ScalarSchwartz3C)
    (hIntegrable : MeasureTheory.Integrable (h12IntegrandSq f)) :
    homogeneousH12SeminormSqOfHeatEvolved t f ≤ homogeneousH12SeminormSq f
```

proved by `MeasureTheory.integral_mono_of_nonneg` — **real harmonic analysis on
real Schwartz functions, with an honest integrability side-condition.** The heat
semigroup contracting `Ḣ^{1/2}` is a true, non-trivial, correctly-proved fact.

**What is discharged (the linear theory):** heat semigroup on Fourier and
physical side (6 files), Leray projector + its linearity, div-free image, and
Sobolev contraction (6 files), Sobolev seminorms via Fourier incl. scaling and
finiteness (6 files), Gaussian derivative bounds (2), convective derivative,
vector partial derivatives, Schwartz multiplication, small data in `H^{1/2}`.

**What is NOT discharged — and the file says so itself.** `BilinearScaffold.lean`
is explicit:

> "The actual operator `B : TimeFieldR3C → TimeFieldR3C → TimeFieldR3C` requires
> Bochner integration of a time-dependent vector Schwartz field over `[0,t]`, the
> convective derivative `(u·∇)v`, and the Leray projection `P` — **substantial
> mathlib infrastructure that is not present at HEAD**. This file lays the
> structural shell…"

So §3 supplies `trivialBilinear` (**B ≡ 0**) as the inhabiting witness, and §5
`trivialBilinear_satisfies_bound` satisfies the contraction estimate with
**C = 0**. `PicardFixedPointProp B` is a typed Prop, not a theorem.

> **Fujita–Kato existence is not proved. The mild formulation's nonlinear term
> does not exist as an operator.** The honest summary: **the linear half of
> Fujita–Kato is done and real; the nonlinear half is an empty shell, correctly
> labelled.**

## 3. Beale–Kato–Majda — vacuous, and self-diagnosed correctly. MEASURED

`BealeKatoMajda1984Formalization.lean`, 623 lines. The core definition:

```lean
def SolutionBlowsUpAt (_T : ℝ) (_u : SchwartzMap (Fin 4 → ℝ) (Fin 3 → ℝ)) : Prop :=
  False
```

and the file's own comment (lines 214-226) is the best diagnosis in the lane:

> "Since smoothness for Schwartz `u` is built in (`smoothness _u := True`), the
> blowup predicate here is the constant `False` — the symbolic encoding makes
> BKM's iff trivial (False ↔ False) at the typed scope… **The literal blow-up
> content is precisely what mathlib lacks.**"

**JUDGEMENT: this is the most important sentence in the inventory, and it is
half right.** The conclusion is correct — BKM is vacuous here — but the cause is
misattributed. It is *not* that mathlib lacks the blow-up content. It is that
**a globally-Schwartz carrier assumes the conclusion**: Schwartz functions are
smooth and rapidly decaying by construction, so "fails to stay smooth" is
unstatable about them. The defect is in the choice of carrier, and it is
**fixable by us** (§6), not something to wait on mathlib for.

Genuine content does survive: `vorticityLInfinityNormAt_nonneg` (143),
`vorticity_pointwise_le_LInfinityNormAt` (159), `FiniteVorticityIntegral` (192)
— real vorticity bookkeeping. The *criterion* is what collapses.

## 4. The Stokes trio — genuine, but torus + finite truncation. MEASURED

`NS3D_StokesOperator` (242 lines, 12 thms), `NS3D_StokesPositivity` (165, 7),
`NS3D_StokesSymmetric` (140, 4). Zero `True`. Checking the content:

```lean
theorem hsInnerVecOn_stokes_symm
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ) (S : Finset (Fin 3 → ℤ)) :
    hsInnerVecOn (stokesOp u) v s S = hsInnerVecOn u (stokesOp v) s S
```

So the Stokes operator is **multiplication by `|k|²` on Fourier modes indexed by
`k ∈ ℤ³`** — the *torus* setting — and symmetry/positivity are proved against an
inner product summed over a **`Finset`** of modes, i.e. finite partial sums.

**Verdict: correct and real, with two scope limits to state plainly** — it is
`ℝ³/ℤ³` (periodic, Fefferman's (B)) rather than `ℝ³` (his (A)), and the inner
products are finite truncations rather than the full `ℓ²` sum. Both are
reasonable intermediate choices; neither should be described as the Stokes
operator on `ℝ³`.

## 5. The "OpenAI 2026" anchor — pinned. FACT

It is the **Córdoba–Martínez-Zoroa / Buckmaster–Alpöge / OpenAI-formalized 2026
NS/Euler blow-up chain**, cited at
`ConvectiveDerivativeConnection_2026_10_08.lean:72` and used across the α-web to
anchor `α_NS = 3π/2` as a "second settled anchor" alongside Perelman.

**What it gives:** a Lean-verified blow-up result for **forced** Navier–Stokes
and/or **unforced Euler**.

**What it does not give:** Fefferman's (A) and (B) — global existence and
smoothness for **unforced** NS on `ℝ³` and on the torus. Those are the
statements the Clay problem asks for, and they are untouched.

**The sharp point, and it needs a primary-source check before anyone leans on
it.** Fefferman's (C)/(D) (breakdown *with* force) require the forcing to satisfy
`|∂ᵅ_x ∂ᵐ_t f| ≤ C_{αmK}(1+|x|+t)^{-K}` for all `α, m, K`. Whether the 2026
chain's forcing meets that admissibility condition is exactly what decides
whether it settles a Clay statement or sits beside one. The prior ledger
adjudication says it does **not** settle the Clay problem ("forced-NS blowup is
not Fefferman's unforced case"), and I am reporting that verdict rather than
re-deriving it. **OPEN: verify the forcing bounds against the papers.** Until
then "externally settled" should not be used without the qualifier.

Also live on this axis: `GRAND_PROBLEM_DEPENDENCY_GRAPH:101` records NS as
"Partial (smoothness `Prop := True`)" with "`Prop := True` still present" — the
`NS_Solution` encoding's smoothness clause. That is the defect the faithful
statement on the unpushed branch exists to repair.

## 6. The gap, and the one change that closes most of it

**The Clay statement (A).** Given `u₀ : ℝ³ → ℝ³` smooth, divergence-free, with
`|∂ᵅ u₀(x)| ≤ C_{αK}(1+|x|)^{-K}` for all `α,K`, there exist
`u : ℝ³×[0,∞) → ℝ³`, `p : ℝ³×[0,∞) → ℝ` with `u, p ∈ C^∞(ℝ³×[0,∞))`,
`∂_t u + (u·∇)u = −∇p + νΔu`, `∇·u = 0`, `u(·,0) = u₀`, and bounded energy
`∫|u(x,t)|²dx < C` for all `t`.

**Gap map:**

| piece | status |
|---|---|
| the faithful *statement* | **WRITTEN**, elaborates EXIT 0 — on the **unpushed** branch |
| heat semigroup, Leray projector, Sobolev seminorms (linear theory) | **PROVED**, real, ~7,700 lines |
| the bilinear `B(u,v)` and its `Ḣ^{1/2}` estimate | **SHELL** — `B ≡ 0`, `C = 0` |
| Picard contraction ⇒ local existence (Fujita–Kato) | **typed Prop**, not proved |
| blow-up expressible at all | **NO** — carrier makes it `False` |
| global existence (the Clay content) | **OPEN** (the actual problem) |

### The precondition: change the carrier. MEASURED, and this is the finding

`BilinearScaffold` blames mathlib ("not present at HEAD", June 2026). **The real
obstruction is permanent and is ours, not mathlib's:**

* `𝓢(E,F)`'s instances stop at `AddCommGroup`, `Module`, `TopologicalSpace`,
  `UniformSpace`, `ContinuousSMul`, `IsTopologicalAddGroup`
  (`Analysis/Distribution/SchwartzSpace.lean`). There is **no
  `NormedAddCommGroup`** — Schwartz space is Fréchet, its topology given by a
  family of seminorms.
* `intervalIntegral` requires `[NormedAddCommGroup E]`
  (`MeasureTheory/Integral/IntervalIntegral/Basic.lean:55`).

**So `∫₀ᵗ (Schwartz-valued) ds` will never typecheck, at any mathlib version.**
Waiting is not a strategy.

**The fix, and what it buys — JUDGEMENT, but the three payoffs are each FACTs
about the current blockers:**

> Change `TimeFieldR3C := ℝ → VectorSchwartz3C` to a **Banach-valued** curve —
> `ℝ → (Ḣ^{1/2})³` or `ℝ → (L²)³`, realised as weighted `L²` on the Fourier
> side, which the existing seminorm files already compute with.

1. **Unblocks the bilinear operator.** `intervalIntegral` applies to
   Banach-valued integrands, so `B(u,v)(t) = ∫₀ᵗ e^{(t−s)Δ}ℙ[(u·∇)v(s)]ds`
   becomes definable — the exact thing `BilinearScaffold` could not build.
2. **Makes blow-up expressible.** An `L²`-valued curve can leave `H^s`; a
   Schwartz-valued one cannot. `SolutionBlowsUpAt` stops being `False` and
   becomes a real Prop — fixing BKM at its root rather than conceding it.
3. **Matches Fujita–Kato as actually proved.** The 1964 theorem is about mild
   solutions in `Ḣ^{1/2}`/`L³`, not Schwartz data. The current carrier is
   fighting the proof it is trying to formalise.

### Nearest concrete theorem

**Construct `B(u,v)` on the Banach carrier and prove the `Ḣ^{1/2}` bilinear
estimate** `‖B(u,v)(t)‖_{Ḣ^{1/2}} ≤ C‖u‖‖v‖`, replacing `trivialBilinear`.

Dependencies, all present: `intervalIntegral` over `[0,t]` (Banach-valued) ✅;
the heat semigroup and its `Ḣ^{1/2}` contraction ✅ (proved, §2); the Leray
projector and its contraction ✅ (proved); the convective derivative ✅
(`ConvectiveDerivative.lean`, 11 thms). **The only new ingredient is the carrier
change plus the product estimate for `(u·∇)v` in `Ḣ^{1/2}` — one genuine
analytic lemma, not a programme.**

Then `PicardFixedPointProp` becomes reachable by the standard contraction
argument, giving **local existence for small data — the first real NS theorem in
the repo.**

## 7. Where the Riemann machinery genuinely transfers

**It transfers, but narrowly, and not to the a priori estimates.**

**The genuine transfer — certified evaluation of concrete norms.**
`composite_midpoint_error` is **function-generic** (verified in the Riemann lane:
arbitrary `f, f', f'', a, b, M, n`, kernel-clean), so it applies to any 1-D
integral with a `C²` bound. And NS Sobolev seminorms in this repo *are* integrals
— `homogeneousH12SeminormSq f = ∫ h12IntegrandSq f`. So the machinery can
certify **`‖u₀‖_{Ḣ^{1/2}} ≤ c` for explicit initial data**, with the same
residue/tail/ω-gap decomposition used for the Fourier panels.

**Why that is worth having.** Fujita–Kato's global existence is conditional on
small data. Today "small data" is a hypothesis; with this transfer it becomes a
**checkable, certified property of a concrete `u₀`**. That turns
`SmallDataInH12.lean` from a typed Prop into a verifiable predicate on explicit
fields. **That is a real, if narrow, deliverable, and it is the only place the
two lanes genuinely meet.**

**Two honest limits:**

* **Dimension.** The Riemann panels are 1-D; `Ḣ^{1/2}` on `ℝ³` is a 3-D Fourier
  integral. Direct transfer needs an iterated/product rule. For **radial** data
  it reduces to a 1-D radial integral and the existing machinery applies
  verbatim — so radial initial data is where to start.
* **What does NOT transfer — and this is the important half.** The a priori
  estimates are *universal inequalities* (`∀ f`), proved by Plancherel, Hölder
  and Sobolev embedding. **Quadrature certifies a number, never a universal
  inequality.** No amount of panel machinery produces the heat-contraction or
  bilinear estimate. Anyone hoping the Riemann investment shortens the NS proof
  should read this paragraph first: it shortens the *verification of instances*,
  not the *theory*.

**One more transfer, and it is a method rather than a lemma:** the tail-bound
discipline. The existing `SobolevIntegrandIntegrable` / `SobolevSeminormFiniteness`
files carry integrability as a hypothesis; the Riemann lane's residue + analytic
tail + ω-gap decomposition is exactly the pattern for discharging such a
hypothesis with an explicit remainder. Same shape, different integrand.

## 8. Verdict

**NEXT BUILD, in order, with dependencies:**

| # | step | depends on | status |
|---|---|---|---|
| 0 | **Push `ns-faithful-migration`** (or accept the bundles as the backup) | — | **Pablo-gated**; bundles taken |
| 1 | **Switch the time-field carrier to Banach** (`Ḣ^{1/2}`/`L²`-valued) | nothing new | the precondition for 2–4 |
| 2 | **Construct `B(u,v)`** via `intervalIntegral` | 1; heat ✅; Leray ✅; convective ✅ | the next real brick |
| 3 | **The `Ḣ^{1/2}` product estimate for `(u·∇)v`** | 2 | **one genuine analytic lemma** |
| 4 | **Picard contraction ⇒ local existence, small data** | 2, 3 | first real NS theorem |
| 5 | *(parallel)* certified `‖u₀‖_{Ḣ^{1/2}}` for radial explicit data | Riemann midpoint rule ✅ | makes "small data" checkable |
| 6 | Restate BKM on the Banach carrier so blow-up is a real Prop | 1 | retires the `False` encoding |

**No blocker.** Unlike Hodge (subject absent) and unlike YM's continuum form
(four mathlib barriers), every dependency for steps 1–4 exists today. The lane's
problem was never capability — it was that three capstones were built on a
carrier that cannot support them, and the June-2026 diagnosis blamed mathlib for
what is actually a design choice.

**JUDGEMENT on the queue.** Reachability order across the four axes scoped:
**NS first** (next theorem is one carrier change plus one lemma), **YM second**
(one mathlib instance, then a real first theorem), **P/NP parked** (circular by
the repo's own iff), **Hodge last** (subject absent).

**OPEN / not done here:** the forcing-admissibility check on the 2026 anchor
(§5) — the one thing on this axis I am reporting on someone else's authority;
whether `Ḣ^{1/2}` is best realised as a bespoke weighted `L²` or via mathlib's
`Lp` (affects step 1's shape, not its feasibility); whether the existing 31
files' seminorm definitions port to the Banach carrier unchanged (they are
Fourier-side integrals, so they should, but I have not elaborated it); and I
read the FujitaKato directory by header + one spot-checked proof, not all 212
theorems.

---

## Label summary

* **FACT (read from source):** `SatisfiesLiteralNSE := ∀ t, 0 ≤ t → u t = u t`;
  `SolutionBlowsUpAt := False` and the BKM self-diagnosis comment verbatim;
  `BilinearScaffold`'s "not present at HEAD" passage, `trivialBilinear`, and the
  `C = 0` bound; the Stokes operator's `ℤ³` index and `Finset` inner products;
  the 2026 anchor's citation and its use for `α_NS = 3π/2`; the
  `GRAND_PROBLEM_DEPENDENCY_GRAPH` "`Prop := True` still present" entry.
* **MEASURED (this session):** the branch at `3441342b` with no remote ref and
  both bundle md5s verified on two machines; the 31-file / ~7,700-line /
  ~212-theorem / zero-`sorry` / zero-`True` inventory; `SchwartzMap`'s instance
  list stopping short of `NormedAddCommGroup`; `intervalIntegral`'s
  `[NormedAddCommGroup E]` requirement at line 55.
* **JUDGEMENT (mine):** that the carrier, not mathlib, is the obstruction, and
  that one change unblocks three capstones; that BKM's self-diagnosis is correct
  in conclusion and wrong in cause; that the Riemann transfer reaches instance
  verification but never universal inequalities; the reachability ordering.
* **NOT established:** the forcing admissibility of the 2026 anchor; the best
  realisation of `Ḣ^{1/2}`; that all 31 files port cleanly; full line-by-line
  reading of the FujitaKato theorems.
