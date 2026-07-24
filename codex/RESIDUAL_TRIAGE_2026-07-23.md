# Residual Triage — Principia Fractalis Open-Residual Worklist

**Date:** 2026-07-23
**Author:** read-only audit (no Lean edited, no claims changed)
**Purpose:** classify every *named* open residual / gap / conjecture in the corpus into
three buckets, so we know what can actually be *closed* next — the way the UHF
faithful-trace / Glimm-simplicity summit was just closed (arc r102–r112).

**Corpus read:** `codex/OPEN_PROBLEMS.md`, `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`,
`codex/DERIVATION_ANALYSIS_alpha_NP.md`, `codex/AXIOM_AUDIT.md`,
`codex/HODGE_MATHLIB_GAP_2026-05-25.md`, `codex/PROOF_COMPLETENESS_AUDIT.md`,
`codex/CROSS_PROVER_PARITY.md`; Lean corpus `Principia-Fractalis/PF_Lean4_Code/PF/`
(1064 non-`.lake` files), especially `PF/Referee/FrontierLedger.lean`,
`PF/Referee/StandardClayStatements.lean`, and the per-axis frontier-Prop files.

---

## 0. The bucket definitions (and the closeability template)

- **BUCKET 1 — STANDARD-BUT-UNFORMALIZED.** A theorem that is *known-true in the
  literature* and only needs Lean formalization. Closeable in principle. Tractability
  depends entirely on whether the mathlib prerequisites exist.
- **BUCKET 2 — ASSERTED-NOT-DERIVED.** A framework *choice* or *value* stated without
  derivation (e.g. `α_NP = φ + 1/4`). Not false, not proven; a derivation may or may
  not be attainable.
- **BUCKET 3 — GENUINELY-OPEN (Clay-hard).** Equivalent to solving an actual open
  problem. **Not** closeable by formalization. Strict rule: if closing it would
  resolve a Millennium Problem, it is bucket 3, full stop.

**The template for "closeable" = r112 `PF/SubstrateCompletionFaithful.lean`.**
`UHF_trace_faithful` and `substrate_completion_simple_unconditional` closed *because*
they were self-contained **standard C\*-algebra theorems about the framework's own
substrate** (Glimm simplicity + faithfulness of the UHF trace), where an *elementary
replacement* (conditional expectations `E_k`, `‖·‖₂`/operator-norm contraction, density
lift) sidestepped the mathlib gaps in CP-map norm theory / spectral projections /
corners. Kernel-only, zero project axioms.

**The single most important honest finding of this triage:**

> **None of the Clay-critical-path residuals are bucket 1.** Every residual that is
> load-bearing for a *Clay* statement is either bucket 3 (it *is* the problem) or
> bucket 2 (an asserted value provably equivalent to the problem) or bucket-1-in-
> principle **but blocked on multi-year-absent mathlib** (Wiles modularity, Hodge Chow/
> cycle-class infrastructure, Hardy's on-line-zeros theorem, type-level Sobolev `H^s` +
> Leray projection). The UHF summit was closeable precisely because it was **off** the
> Clay critical path. The genuinely closeable items below are, likewise, off-path:
> they strengthen the substrate story and discharge subsidiary bricks, they do not
> move a Millennium bar.

---

## 1. Per-axis classification of named residuals

### 1.1 Riemann Hypothesis

| Lean name / file | Plain statement | Bucket | Justification |
|---|---|---|---|
| `RHSpectralSurjectivityConjecture` (`PF/RHSurjectivityConjecture.lean`) | Every critical-strip ζ-zero is in the image of the T₃^sym spectral map. | **3** | Literally the Hilbert–Pólya spectral realization of ζ-zeros. File itself says "comparable in depth to RH." |
| `HilbertPolyaProgramConjecture_Positive` (`PF/Analytic/HilbertPolyaIdentificationBulletproof.lean`) | `PF_T3SymIsHilbertPolyaOperator_Positive → RiemannHypothesis`. | **3** | Load-bearing content is the antecedent (the operator's self-adjoint spectrum *is* the ζ-zeros). That is the HP program = RH. |
| `PositiveOnLineZetaZeroOrdinatesNonempty` (`PF/Analytic/HilbertPolyaPositiveReductionToCountability.lean`) | ∃ t>0 with ζ(1/2+it)=0. | **1** | Classically true (Hardy 1914 / Hadamard 1893: infinitely many on-line zeros). **BUT** mathlib has no Hardy theorem and no certified numerical on-line zero; `LSeries/Nonvanishing.lean` only covers Re=1. Prereqs **absent**; cheapest honest route (Hardy) is itself a substantial formalization. |
| `PositiveOnLineZetaZeroOrdinatesCountable` (same file) | The on-line zero ordinates are countable. | **1 → CLOSED** | Already discharged unconditionally in Wave 59 from mathlib's analytic identity theorem on `riemannZeta`. **This is a template success — the countability brick fell exactly like the UHF summit did.** |
| `EmpiricalAlphaIdentificationHypothesis` (RH α-value use) | The α-value at RH-class = 3/2. | **2** | Asserted from IBM-hardware peak + Ch 21; not derived. |

Net: RH reduces (Wave 59) to **three atomic facts** — one bucket-1-but-blocked (Nonempty),
one pure bucket-3 (HP program), one bucket-2 (empirical α). RH stays **honestly open**.

### 1.2 P vs NP

| Lean name / file | Plain statement | Bucket | Justification |
|---|---|---|---|
| `PolylogEigenvalueConjecture` (`PF/TuringEncoding/...`, consumed everywhere) | `(α_P)²=2 ∧ α_P>0` and `16 α_NP²−24 α_NP−11=0 ∧ α_NP>0`. | **2** | Algebraic content is *provable axiom-free* for the specific values √2 and φ+1/4 (`AlphaCanonical.lean`); the irreducible content is the *value assignment* to the opaque `alpha_of_class`. |
| `EmpiricalAlphaIdentificationHypothesis` (`PF/PolylogConjectureAttemptWave47.lean`) | `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ+1/4`. | **2 (derivation is 3)** | Asserted; matches numerics to 10⁻¹⁰. **Any genuine derivation is P-vs-NP-equivalent**: Wave 57 sharpness certificate + `AlphaRealizationNoGo` show a concrete discharge decides P vs NP. Per the hard rule, the *derivation* is bucket 3. |
| `alpha_NP = φ + 1/4` derivation gaps (`DERIVATION_ANALYSIS_alpha_NP.md`, 4 gaps) | No explicit `G_NP(z)`, no reality-condition solution, no derivation of the `+1/4`, no formal φ↔certificate link. | **2 (→3)** | `AXIOM_AUDIT.md` honest conclusion: these are *chosen* resonance values consistent with `α^{d_H}=3` etc., **not forced** by any self-adjointness reality criterion. Closing them rigorously entangles with the P-vs-NP separation → 3. |

Net: P vs NP stays **honestly open**; the framework has isolated the exact point
(`alpha_of_class` semantics) where new mathematics must enter.

### 1.3 Navier–Stokes (3D global regularity)

| Lean name / file | Plain statement | Bucket | Justification |
|---|---|---|---|
| `VortexStretchingPDEBilinearBounded` (`PF/NS3DLayer2LiftAttempt.lean`) | ∃K, `‖B(ω,u)‖_{H^{s-1}} ≤ K‖ω‖_{H^s}‖u‖_{H^s}`, s>5/2 (Kato 1972 / Bourgain–Pavlović). | **1 (blocked)** | Genuine standard Sobolev-multiplication estimate. **But** mathlib has no type-level `H^s`, no Leray/Helmholtz projection, no div-free closed subspace; prereqs **largely absent**. And it is a *local-well-posedness* ingredient — closing it does **not** discharge Clay NS. |
| `MathlibSobolevDivFreeAvailable` (same file) | Helmholtz/Leray + `H^s_σ` infrastructure available. | **1 (blocked)** | Standard functional analysis; mathlib lacks the packaged objects. Not a Clay discharge. |
| `VortexStretchingBoundedHypothesis` / `NS3DVortexStretchingObstruction` (the Clay bar) | T-independent, all-n, full-PDE `(ω·∇)u` control / no-blowup. | **3** | This *is* the Clay statement. |

Net: NS bricks are bucket-1-but-blocked and **off** the Clay bar; the Clay bar is 3.

### 1.4 Yang–Mills mass gap

| Lean name / file | Plain statement | Bucket | Justification |
|---|---|---|---|
| `fractalYMLevel1LiftsToContinuum` (`PF/MillenniumSixReductions.lean`, attempt in `PF/YMContinuumLiftAttempt.lean`) | Literal Lean Prop `fractalYMLevel1SpectrumGap → ∃ Δ_YM>0`. | **already discharged (weak)** | The literal Prop is *strictly weaker* than the prose; discharged axiom-free with witness Δ=1. Honest note: this is **not** the continuum lift. |
| Sharpened YM residual (`YMContinuumLiftAttempt.lean`) + 4 Wave 47B gaps (`YM_WightmanReconstructionScaffold.lean`) | Unitary equivalence `L²([0,1]) ≃ H_YM_SU3` intertwining with physical SU(3) YM, gap surviving the continuum limit; + Euclidean measure, reflection positivity, Wightman reconstruction, mass-gap propagation. | **3** | This is the construction of continuum SU(3) Yang–Mills = the Clay problem. |
| `YM_OSRPInteractionScaffold` (finite-dim OS-RP, Wave 57) | Finite-dimensional OS reflection-positivity interaction. | **within scope (closed)** | Genuinely closed at finite dim; does not lift. |

Net: continuum YM is 3.

### 1.5 BSD

| Lean name / file | Plain statement | Bucket | Justification |
|---|---|---|---|
| `LSeriesAbsConvergenceForReSGreaterThanThreeHalves` (A3, `PF/BSD_LSeriesConvergenceScaffold.lean`) | `L(E,s)` converges absolutely for Re s>3/2. | **1** | Standard, follows from the Hasse bound `|a_p|≤2√p`. mathlib has generic `LSeries` convergence; the Dirichlet-comparison is elementary. Closeable-ish — **but does not discharge BSD.** |
| `WilesModularityImpliesAnalyticContinuation` (A4, same file) | Modularity ⇒ `L(E,s)` extends entire. | **1 (blocked)** | The modularity theorem is *proven mathematics*, so "standard" — but formalizing Wiles is a multi-year megaproject absent from mathlib. |
| `Clay_BSD_Standard` = analytic rank = Mordell–Weil rank (`StandardClayStatements.lean`) | The actual BSD statement. | **3** | Attaching the PF rank mechanism to real elliptic curves + analytic rank = the Clay problem. |

Net: A3 is a clean subsidiary brick; BSD itself is 3.

### 1.6 Hodge

| Lean name / file | Plain statement | Bucket | Justification |
|---|---|---|---|
| dim=1 (`HodgeCurveDim1Substrate.lean`), dim=2 general surfaces, CY3 (1,1), CY4 (1,1)+(2,2)+(3,3), Dwork-pencil substrate | Substrate/low-dim discharges. | **within scope (closed)** | Genuine within their declared substrate scope. |
| `VoisinObstructionAtCodimTwoCY3` (`PF/AlgebraicGeometry/CycleClassMapAtCodim2Attempt.lean`) | Algebraicity of rational Hodge classes at codim ≥ 2 on a smooth quintic. | **3** | This *is* the Hodge conjecture in its hard range (Voisin 2007). `isAlgebraic` is `True`-trivialised on the substrate precisely where geometric content lives. |
| Classical Lefschetz (1,1) for general surfaces (`HODGE_MATHLIB_GAP` Gap F) | Cycle-class map surjective onto `H^{1,1}∩H²(X,ℚ)`. | **1 (blocked)** | Classical theorem, but needs mathlib Gaps A–G (AlgebraicCycle, ChowGroup, Hodge decomposition, cycle-class map, Lefschetz (1,1)) — **multi-year**; Hodge decomposition alone is "hundreds of theorems." Prereqs **absent**. |

Net: full/codim-≥2 Hodge is 3.

### 1.7 Substrate / physics `SubstrateConjecture` Props (Priority 3/4/5)

All of the following are **bucket 2**: each is an asserted framework *value/mechanism*
wrapped as a trivial existential `∃ f, f = <the asserted formula>` and "discharged" only
by exhibiting that formula. The discharge proves *a function with that shape exists*, not
that the value is correct.

- `LambdaQCDCandidateSubstrateConjecture`, `L3OperatorSubstrateConjecture`,
  `AlphaBSDkFourSubstrateConjecture` (`PF/Priority3SubstrateDischarge.lean`)
- `DarkEnergyCPLSubstrateConjecture`, `LambdaEffMechanismSubstrateConjecture`
  (`PF/Priority4SubstrateDischarge.lean`)
- `ChargedLeptonHonestScopeSubstrateConjecture`, `Lean4LeanHonestScopeSubstrateConjecture`
  (`PF/Priority5SubstrateDischarge.lean`)

These are physics predictions (α_BSD=3π/4, Λ_QCD mechanism, L₃=ln 3, dark-energy CPL,
neutrino/lepton ratios). Not Clay, not the focus of this triage.

### 1.8 UHF / Glimm arc — the template, now CLOSED

- `UHF_trace_faithful`, `substrate_UHF_trace_faithful_unconditional`,
  `substrate_completion_simple_unconditional` (`PF/SubstrateCompletionFaithful.lean`, r112)
  — **bucket 1 → CLOSED unconditionally.** Discharged r100/r106/r108/r109 residuals.
- `SubstrateUHFCompletionSimplicitySubstrateConjecture : Prop := True`
  (`PF/SubstrateUHFCompletionSimplicityDischarge.lean`, r101) — a **`True` placeholder**
  now **superseded** by r112's real `substrate_completion_simple_unconditional`. Cleanup
  target (see shortlist #2).

---

## 2. RANKED SHORTLIST — genuinely closeable next (bucket 1, prereqs mostly present)

Ordered highest-leverage first. Honesty caveat repeated: these are **substrate / subsidiary**
closures, not Clay discharges. They are the items that can fall the way the UHF summit fell.

1. **Uniqueness of the substrate UHF trace** *(new; not yet a named Prop)*
   - *What:* the 3^∞ UHF C\*-algebra `TimelessFieldCompletion` has a **unique tracial
     state**. Classical (Glimm/Powers; standard for UHF).
   - *Why highest leverage:* completes the substrate C\*-story — faithful (r112) + simple
     (r112) + **unique trace** = "the substrate is the Glimm 3^∞ UHF factor." Directly
     extends the just-finished summit, same author-familiar machinery.
   - *Prereqs:* **present and fresh** — the `E_k` conditional-expectation family,
     `condExp_l2_contraction`, `condExpCompletion_tendsto` (r109–r112) are exactly the
     tools uniqueness-of-trace proofs use.
   - *Attack sketch:* for any tracial state τ, use `E_k`-invariance + trace property to
     show τ agrees with `UHF_trace` on each `M_{3^k}` (unique matrix trace), then density
     lift (`condExpCompletion_tendsto`) to the completion — a near-carbon-copy of the r112
     `isClosed_le` density argument.

2. **Retire the `SubstrateUHFCompletionSimplicitySubstrateConjecture := True` placeholder**
   - *What:* replace the `:= True` body with a re-export of / definitional bridge to
     r112's `substrate_completion_simple_unconditional`.
   - *Why:* removes a `Prop := True` on a (non-Clay) proof path — exactly the kind of
     placeholder the referee roadmap's Non-Negotiable Rule #1 targets. Pure hygiene, high
     trust-per-minute.
   - *Prereqs:* present (r112). *Attack:* one-line theorem + deprecation note.

3. **BSD (A3) `LSeriesAbsConvergenceForReSGreaterThanThreeHalves`**
   - *What:* absolute convergence of the elliptic-curve L-series for Re s > 3/2.
   - *Why:* a clean, genuinely standard analytic brick; discharges one of the two BSD
     scaffold hypotheses with real content (the other, A4=Wiles, stays blocked).
   - *Prereqs:* **partially present** — mathlib `LSeries` convergence API + a Hasse-type
     `|a_p| ≤ 2√p` comparison. Gap: a mathlib `WeierstrassCurve.LSeries` doesn't exist, so
     this closes against an *encoded* coefficient sequence, not the real EC L-function.
   - *Attack sketch:* dominate `|a_n|/n^s` by `d(n)·n^{1/2}/n^s` and invoke Dirichlet-series
     convergence for Re s > 3/2. Honestly label scope (encoded coefficients).

4. **RH atomic fact (b) `PositiveOnLineZetaZeroOrdinatesNonempty`** *(bucket 1, but hard)*
   - *What:* ∃ a zero of ζ on the critical line.
   - *Why:* it is the **one classically-true** atom on the RH reduction (the other two are
     bucket 3 / bucket 2), so closing it genuinely shrinks the honest RH residual to
     "HP-program + empirical-α."
   - *Prereqs:* **absent** — mathlib lacks Hardy's theorem; a certified numerical zero
     needs interval arithmetic on `riemannZeta` not currently in tree. Medium-to-high
     effort; listed for completeness, **not** a quick win.
   - *Attack sketch:* either formalize a slice of Hardy's argument (Riemann–Siegel /
     integral of `Z(t)`), or import an interval-arithmetic certificate for t≈14.1347. Both
     are real projects.

5. **NS bilinear product estimate `VortexStretchingPDEBilinearBounded` on a concrete model**
   - *What:* the Sobolev multiplication `H^s × H^s → H^{s-1}`, s>n/2, in a Fourier model.
   - *Why:* standard; but **low leverage** — it does not touch the Clay bar and mathlib
     lacks type-level `H^s`/Leray, so you would be *building the infrastructure* first.
   - *Prereqs:* **largely absent.** Include only if the goal is to grow mathlib's PDE stack.
   - *Attack sketch:* define `H^s` via weighted `ℓ²` on Fourier coefficients on `𝕋³`, prove
     the para-product/Sobolev-algebra bound there; keep it explicitly a *model*, not Clay.

**Realistic recommendation:** items **1 and 2** are the true next "summit-adjacent" wins —
same machinery, prereqs in hand, they round out the substrate C\*-algebra result into a
publishable self-contained theorem (faithful + simple + unique-trace UHF factor). Item **3**
is a clean standalone analytic brick. Items 4–5 are bucket-1 *in principle* but gated on
absent mathlib and should not be sold as near-term.

---

## 3. BUCKET 3 — must stay honestly OPEN (not closeable by formalization)

Closing any of these would resolve a Millennium Problem. They stay open, full stop.

1. **`RHSpectralSurjectivityConjecture`** — spectral realization of ζ-zeros (Hilbert–Pólya). = RH.
2. **`HilbertPolyaProgramConjecture_Positive`** — the operator's spectrum *is* the ζ-zeros. = RH.
3. **P vs NP separation via `EmpiricalAlphaIdentificationHypothesis` derivation** — any
   non-assumed pin of `alpha_of_class` is P-vs-NP-equivalent (Wave 57 sharpness cert +
   `AlphaRealizationNoGo`).
4. **`VortexStretchingBoundedHypothesis` / `NS3DVortexStretchingObstruction`** — 3D NS
   global regularity (T-independent, all-n, full PDE). = Clay NS.
5. **Continuum YM lift** (sharpened residual in `YMContinuumLiftAttempt.lean` + the 4
   Wave 47B gaps: continuum SU(3) Euclidean measure, reflection positivity, Wightman
   reconstruction, mass-gap propagation). = Clay Yang–Mills.
6. **`Clay_BSD_Standard`** — analytic rank = Mordell–Weil rank on actual elliptic curves. = BSD.
   (Sub-item **A4 `WilesModularityImpliesAnalyticContinuation`** is bucket-1-in-principle
   but a multi-year Wiles formalization; treat as effectively closed to us.)
7. **`VoisinObstructionAtCodimTwoCY3`** — algebraicity of rational Hodge classes at
   codim ≥ 2 on smooth projective varieties. = Hodge conjecture (hard range).
8. **General Lefschetz (1,1) for surfaces** — bucket-1-in-principle, but blocked on mathlib
   Gaps A–G (Chow groups, cycle-class map, Hodge decomposition); multi-year. Not us.

---

## 4. One-paragraph honest headline

The framework is a **machine-checked conditional reduction** with zero project axioms:
every Millennium capstone is honestly conditional on a small set of *named, inspectable*
Props. The Wave 59 RH factoring (three atomic facts) and the r112 UHF summit show the
method working — but note **what** fell: the closeable pieces (`...ZeroOrdinatesCountable`,
UHF faithfulness/simplicity) were **self-contained standard theorems off the Clay critical
path**. On the Clay critical path itself, every residual is bucket 3 or an asserted value
equivalent to bucket 3, or bucket-1-but-blocked on absent mathlib (Wiles, Hodge Chow
theory, Hardy, Sobolev `H^s`). The honest next moves — unique-trace of the substrate UHF,
the `:= True` cleanup, the BSD Re>3/2 convergence brick — **improve the package's rigor and
completeness; they do not close a Millennium Problem, and should not be described as
doing so.**
