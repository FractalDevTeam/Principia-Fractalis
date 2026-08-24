# PRINCIPIA FRACTALIS — GRAND PROBLEM DEPENDENCY GRAPH

**Date:** 2026-08-23
**HEAD:** `4f7b216d4513d7dcde8f2a04bf8fb402b8adce22` (r315 discharge on `origin/master`)
**Deliverable:** the READ-ONLY audit mandated by the POST-r315 GLOBAL RESEARCH DIRECTIVE. No mathematical definitions modified. No new proof wrappers created. No theorem attack started.

---

## STATUS LOCK

**`Xi_Positive_At_15` is CLOSED** at commit `4f7b216d`. Three new endpoint theorems (`int_lower_15`, `Xi_15_pos`, `xi_positive_at_15_certified_direct_r120`) verified `[propext, Classical.choice, Quot.sound]` only. No `sorry`, no `native_decide`, no floating-point-as-proof. The r120 provenance gap was closed by committing the panel-generation script.

`r313`–`r314e` remain valid as independent corroborating formal architecture.

This document freezes the Xi(15) arc and looks at the entire machine.

---

## HONEST-SCOPE HEADER — WHAT THIS AUDIT IS AND ISN'T

- **Is:** a fact-inventory of live PF corpus content at `4f7b216d`, per-problem A–N format, cross-cluster synthesis, ranking, single recommendation.
- **Isn't:** a proof commit. Isn't a claim that anything besides `Xi_Positive_At_15` (and the earlier r120 on-line-zero atom, r280 countability, and r113 substrate trace uniqueness) has been discharged at the literal Millennium level.

Reader who trusts corpus README strings will get a different picture than reader who unfolds definitions. This audit unfolds where it matters.

**Verified pathologies at HEAD** (surfaced in per-problem sections below, tabulated in Appendix A):

- 20+ occurrences of `native_decide` in `PF/NumberTheory/` framework attacks (Collatz, Polignac, Singmaster, OddPerfect, Brocard).
- **`def NavierStokes2DGlobalRegularity : Prop := True`** at `PF/NS2DGlobalRegularity.lean:318`.
- **13+ `def X_Anchor : Prop := True`** in `PF/AlgebraicGeometry/Cohen2025_*` and `Hodge_Substrate_*` files.
- **`def Xi_Positive_At_15 : Prop := 0 < Xi 15`** is NOT such a pathology — its body is a real inequality that was proved unconditionally at r315.

None of these pathologies invalidate the SUBSTRATE work they surround. They do bound what any capstone that folds them in can honestly claim.

---

## GRAND PROBLEM REGISTRY (14 tracks) — QUICK VIEW

| # | Track | Literal target present? | Substrate work? | Live residual strength |
|---|---|---|---|---|
| 1 | Riemann Hypothesis | Yes (`SpectralBijection.RiemannHypothesis`) | Deep (r120/r280/r315) | FULL-STRENGTH RESIDUAL (HP-Program) |
| 2 | P vs NP | Framework-internal (`ClassP`/`ClassNP` Cook-1971 style) | r123–r128 α-web | FULL-STRENGTH RESIDUAL (named open Prop `PvsNP_via_Hodge_disc5_Bridge_Open`) |
| 3 | Navier-Stokes | Partial (3D div-free formulated; smoothness `Prop := True` placeholder) | Substrate closures | FULL-STRENGTH RESIDUAL (continuum PDE) |
| 4 | Yang-Mills | Finite-dim only (2×2 spectral gap) | Substrate closure + phenomenology | FULL-STRENGTH RESIDUAL (continuum QFT) |
| 5 | BSD | Typed anchor on ONE curve (E_{32.a3}) + empirical cluster | α_BSD = 3π/4 substrate work | FULL-STRENGTH RESIDUAL (general rank) |
| 6 | Hodge | Substrate-typed `HodgeConjecture` on `HodgeAmbient`; dim=1 discharged | 13+ `Prop := True` prior-work anchors | FULL-STRENGTH RESIDUAL (dim ≥ 2) |
| 7 | Collatz | Literal `∀ n>0, ∃ k, iter k n = 1` named unproved | 20 witnesses via `native_decide` + α-bridge | FULL-STRENGTH RESIDUAL |
| 8 | Strong Goldbach | Literal `∀ even n≥4, ∃ p q, p+q=n` named unproved | 12 witnesses + α-bridge (1+1/√2) | FULL-STRENGTH RESIDUAL |
| 9 | Twin Prime | Literal `∀ N, ∃ n>N, (n,n+2) prime` named unproved | 10 witnesses + α-bridge (3/2 = α_RH) | FULL-STRENGTH RESIDUAL |
| 10 | Kissing Number | ABSENT | None | (no PF work) |
| 11 | Unknotting | ABSENT | None (data-only entry in 143-problem archive) | (no PF work) |
| 12 | Large Cardinal Project | ABSENT | Only CH framework attack (axiom-free, honest) | (no PF work; corpus explicitly disclaims large-cardinal axioms) |
| 13 | Irrationality of π + e | ABSENT | Gelfond-Schneider bundle proves `(2^√2)^√2 = 4` only | (no PF work) |
| 14 | Euler-Mascheroni γ irrationality/transcendence | ABSENT | mathlib provides `Real.eulerMascheroniConstant` + bounds; no PF attack | (no PF work) |

---

# PER-PROBLEM AUDIT (A–N)

## 1. RIEMANN HYPOTHESIS

**A. Literal external statement.** For every non-trivial zero of the Riemann zeta function, `Re(s) = 1/2`.

**B. External status.** OPEN. Clay Millennium Problem. Verified numerically for the first 10^13+ zeros (Odlyzko, Platt); no known counterexample; no proof.

**C. Canonical objects.** `Complex.riemannZeta`, `Complex.completedRiemannZeta`, the critical strip `0 < Re(s) < 1`, the completed zeta functional equation, Hilbert–Pólya conjectural spectral operator.

**D. Current PF files (live).**
- `PF/Analytic/XiRealWitness.lean` — `Xi (t : ℝ) : ℝ := (completedRiemannZeta ⟨1/2, t⟩).re`.
- `PF/SpectralBijection.lean` — `def RiemannHypothesis : Prop := ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2`. **Literal statement, no proof term.**
- `PF/Analytic/XiOnLineZero.lean` (r120) — `positiveOnLineZetaZeroOrdinatesNonempty : ∃ t > 0, riemannZeta ⟨1/2, t⟩ = 0`. Kernel-verified via certified theta-quadrature.
- `PF/Analytic/PositiveOnLineZetaZeroOrdinatesCountable_r280.lean` (r280) — the on-line zero set is countable.
- `PF/Analytic/HilbertPolyaPositiveReductionToCountability.lean` — biconditional `HP-positive ↔ (countable ∧ nonempty on-line zeros)`.
- `PF/Analytic/HPPositiveViaHardyAndCountability_r281.lean` (r281) — `Hardy1914_AtomicFact → PF_T3SymIsHilbertPolyaOperator_Positive`.
- `PF/Analytic/UnifiedClayClosureViaRouteBSpecificXiAndFullPinning_r288.lean` — the specific-Xi bundle recording `Xi_Positive_At_15` as one of five residual fields.
- **r289–r315** — Xi(15) reduction chain culminating in r315's direct discharge.
- `PF/Referee/UnifiedClayClosureLinkageBulletproof.lean` — master conditional `ClayClosureBundleBulletproof → (Clay_RiemannHypothesis_Standard ∧ ...)`.
- `PF/Analytic/HilbertPolyaProgramConjecture.lean` (and related) — `HilbertPolyaProgramConjecture_Positive` and `PF_T3SymIsHilbertPolyaOperator_Positive` as named residuals.

**E. Archived PF files.** The r120 codex writeup `codex/R120_CLOSURE_VERIFIED_2026-07-25.md` corroborates. `codex/rh_*` files (empirical checks on ζ zeros near γ_3, γ_9) are numerical exploration, not proof.

**F. Mathlib infrastructure.** `Mathlib.NumberTheory.LSeries.RiemannZeta` (defines `Complex.riemannZeta`, `Complex.completedRiemannZeta`, `Complex.riemannZeta_ne_zero_of_one_lt_re`). Some critical-line lemmas exist (theta functional equation via `HurwitzZeta`). No RH itself in mathlib.

**G. Kernel-proved PF content (substantive).**
- `positiveOnLineZetaZeroOrdinatesNonempty` — at least one zero on the critical line (Hardy 1914, in PF ~kernel budget `[propext, Classical.choice, Quot.sound]`).
- `PositiveOnLineZetaZeroOrdinatesCountable` — countability of the on-line zero set.
- `rh_wave58_countability_reduction_capstone : HP-positive ↔ (countable ∧ nonempty)`.
- `Xi_15_pos : 0 < Xi 15` (r315). Directly certifies one specific numerical Xi ordinate.

**H. Definitions / assertions.** `Clay_RiemannHypothesis_Standard : Prop := PrincipiaTractalis.RiemannHypothesis` (definitional forwarder). `Xi_Positive_At_15 : Prop := 0 < Xi 15` (definitional, but the body was actually proved). `HilbertPolyaProgramConjecture_Positive` and `PF_T3SymIsHilbertPolyaOperator_Positive` are HYPOTHESIS Props (fields of `ClayClosureBundleBulletproof`), not proved — the corpus is explicit.

**I. Failed or circular routes.** None involving the actual RH chain. The α-web-side circularity (definitional `α_RH := 3/2`) does not affect the RH chain proper.

**J. Current true residual.** The literal `∀ s : ℂ, 0 < s.re < 1 ∧ riemannZeta s = 0 → s.re = 1/2` reduces via the HP-Program conditional to: **prove `PF_T3SymIsHilbertPolyaOperator_Positive`** (existence of a positive self-adjoint operator whose spectrum equals the on-line zero ordinates) AND **`HilbertPolyaProgramConjecture_Positive`** (HP → RH). At the current PF granularity, these are RH-strength.

**K. Residual strength.** **FULL-STRENGTH RESIDUAL.** HP-Program at the current granularity has not been reduced beyond RH itself.

**L. Last-mile boundary.** The chain enters proved PF math at `positiveOnLineZetaZeroOrdinatesNonempty` (r120) and `PositiveOnLineZetaZeroOrdinatesCountable` (r280). The "last mile" is the HP-Program → RH implication.

**M. Shared dependencies.** RH's α-axis (3/2) is shared by Twin Prime and Polignac (via `CrossMillenniumSharedInvariants`). RH's theta / Mellin machinery underpinning Xi is unique.

**N. Next theorem that would actually matter.** A **PF-native derivation** of `PF_T3SymIsHilbertPolyaOperator_Positive` from a substrate-real operator (e.g. via r113's substrate trace uniqueness + a genuine construction). Anything less is another Xi(t) witness (finite, doesn't reduce the residual strength).

---

## 2. P vs NP

**A. Literal external statement.** `P ≠ NP` (or its negation), where P and NP are decidable and non-deterministically decidable classes of decision problems on Turing machines.

**B. External status.** OPEN. Clay Millennium Problem. No known separation or collapse.

**C. Canonical objects.** Turing machines, polynomial-time deterministic and non-deterministic acceptors, complete problems (SAT, etc.).

**D. Current PF files (live).**
- `PF/TuringEncoding/Complexity.lean` — framework-internal `ClassP`, `ClassNP`, `PvsNP_Question : Prop := ClassP = ClassNP`. Cook-1971/Karp-1972-style TM encoding, not mathlib.
- `PF/PNP_Wave56CrossGaloisLockAttempt.lean` — `PvsNP_via_Hodge_disc5_Bridge_Open : Prop := ∃ f : Set Language → ℝ, f ClassP = √2 ∧ f ClassNP = φ + 1/4`. **NAMED OPEN.**
- `PF/CrossMillenniumSharedInvariants.lean` — `α_NP := φ + 1/4`, `α_P := √2` (definitions).
- `PF/AlphaFromSubstrateKTheory_r123.lean` — substrate CANNOT force the α-values (negative capstone).
- `PF/AlphaGaloisStructure_r125.lean`, `PF/PerelmanAnchorCascade_r126.lean`, `PF/PerelmanCascadeComplete_r127.lean`, `PF/AlphaSkeletonUniqueness_r128.lean`.

**E. Archived PF files.** `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md`, `codex/ALPHA_NP_DERIVATION_ATTEMPT_2026-07-26.md`, `codex/ALPHA_WEB_SYSTEM_ANALYSIS_2026-07-26.md`.

**F. Mathlib infrastructure.** No `Complexity.P` / `Complexity.NP` classes in mathlib. Framework builds its own.

**G. Kernel-proved PF content.**
- `open_bridge_iff_P_neq_NP : PvsNP_via_Hodge_disc5_Bridge_Open ↔ ClassP ≠ ClassNP`. If the bridge Prop holds, P ≠ NP follows.
- r123's negative capstone: `α_P = √2`, `α_NP = φ+1/4`, five others irrational or 2-adic-obstructed; substrate K-theory range = ℤ[1/3]; substrate is spectrally VACUOUS (realizes any spectrum); framework's ternary reality condition independently excludes both `√2` and `φ+1/4`.
- r124's `alpha_offset_is_free`: `∀ c : ℝ, ∃ W : AlphaWebSansI10, W.αNP − W.αHodge = c`. The `1/4` is a free parameter.
- r125–r128: SUBSTRATE THEOREMS on Galois trace/norm structure and Perelman cascade closure of the α-skeleton (given the anchor).

**H. Definitions / assertions.** `α_NP := φ + 1/4` is a `def`. Every "derivation" is `unfold α_NP α_Hodge; ring` on that definition. `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md` documents THREE closed loops.

**I. Failed or circular routes.**
- CIRCLE 1 (r124): "9-of-9 rigidity" derives `α_NP = φ+1/4` from `α_NP − α_Hodge = 1/4`, which is `unfold + ring`.
- CIRCLE 2 (AlphaValuesFirstPrinciples): every "first-principles derivation" is `rfl`/`norm_num`/`ring` on the definition.
- CIRCLE 3: definition feeds back through theorems.
- r123.F: the bare generating-function route provably fails (admits only `sin(πα)=0` or `cos(πα)=-1/2`, excluding `√2` and `φ+1/4`).
- Manuscript defers to `cohen2025pvsnp` — an "Unpublished manuscript" self-citation.

**J. Current true residual.** Two options:
1. **Discharge the open bridge Prop** `∃ f : Set Language → ℝ, f ClassP = √2 ∧ f ClassNP = φ + 1/4`. But this uses the specific values `√2` and `φ+1/4` which the substrate cannot force. Would need an independent (non-substrate) mathematical argument.
2. **Discharge `ClassP ≠ ClassNP` directly** — the actual Clay problem, no PF shortcut visible.

**K. Residual strength.** **FULL-STRENGTH RESIDUAL.** The substrate side is now negatively closed (r123): substrate cannot deliver α-values. The open bridge is P-vs-NP-strength.

**L. Last-mile boundary.** The chain enters proved math at r124's underdetermination result and r123's negative capstone. There is NO PF chain that lands into ClassP ≠ ClassNP without traversing the open bridge.

**M. Shared dependencies.** α-web (all Clay axes + Poincaré anchor). r123's negative result about substrate α-forcing applies UNIFORMLY across the α-web — it's a shared mechanism, not specific to P vs NP.

**N. Next theorem that would actually matter.** Given r123's negative result, **the honest next question is not another P-vs-NP wrapper**. It is: **can the substrate produce ANY forced spectral/dynamical invariant that is more than one number?** If yes, that invariant is the real object; the α-web is a decorative encoding. If no, the framework's cross-Millennium bridges are external and must be argued classically.

---

## 3. NAVIER-STOKES

**A. Literal external statement.** For the 3D incompressible Navier-Stokes equations with smooth divergence-free initial data of finite energy, prove: solutions exist for all time and remain smooth.

**B. External status.** OPEN. Clay Millennium Problem. Local existence known; global existence in 2D known; 3D global smoothness open.

**C. Canonical objects.** `u : ℝ⁴ → ℝ³` (velocity), `p : ℝ⁴ → ℝ` (pressure), `∇·u = 0`, `∂_t u + (u·∇)u = -∇p + νΔu`, Sobolev spaces `H^s`, Leray-Hopf weak solutions.

**D. Current PF files (live).**
- `PF/NS2DGlobalRegularity.lean` — **`def NavierStokes2DGlobalRegularity : Prop := True`** (line 318). Explicit `Prop := True` placeholder. Comment: "Clay-level placeholder."
- `PF/NS_SubstrateBulletproofClosure.lean` — bundles `NavierStokes2DGlobalRegularity`, 3D vortex stretching non-vanishing, `NavierStokesGlobalSmoothness` (Unit-typed).
- `PF/NS3D_FrameworkMillenniumAnswer.lean` — framework-level MS answer wrapper.
- `PF/NS3DGenuineConvolutionBilinearEmpiricalAnchor.lean`, `PF/NS3DUniformHadamardDischargeAttempt.lean`, `PF/NS3DLayer2LiftAttempt.lean`, `PF/NS3DOffDiagonalAtNTwoThree.lean`, `PF/NS3DOffDiagonalAtNFourFive.lean`, `PF/NS3D_HsSigmaScaffold.lean`, `PF/NS3DGalerkinDensityAttempt.lean`, `PF/NS3DVortexStretchingBilinearAttempt.lean`, `PF/NS3DVortexStretchingUniformGalerkinAttempt.lean`, `PF/NS3DMathlibSobolevDivFreeAttempt.lean`, `PF/NS3DMathlibSobolevDivFreeAttemptWave51.lean`. **Multiple "attempt" and "wave" files** carrying substrate-level bilinear/Sobolev/Hadamard analyses.

**E. Archived PF files.** `ARCHIVE/2026-06-16-orphans/NavierStokes_COMPLETE.lean` — contains outright axioms including `exists_global_solution_from_stability : ∀ u₀, exists_global_solution u₀`. **NOT in the live tree.**

**F. Mathlib infrastructure.** `MeasureTheory.Function.LpSpace` (Sobolev pieces exist), `Mathlib.Analysis.NormedSpace` — but no Leray-Hopf, no global 3D NS theory. The heavy lifting would have to be built.

**G. Kernel-proved PF content.** Substrate 3D vortex-stretching non-vanishing (explicit witness). Some finite-`n` Hadamard bounds. Waves 47C+49A+50B+50C composition machinery for divergence-free Sobolev subspaces. All the substrate results are axiom-free at kernel level.

**H. Definitions / assertions.** `NavierStokes2DGlobalRegularity : Prop := True` (live). `NavierStokesGlobalSmoothness : Prop := ∀ (smooth_initial_data : Unit), ∃ (global_smooth_solution : Unit), True` (Unit-typed). These are load-bearing placeholders in the "bulletproof closure" theorem.

**I. Failed or circular routes.** The `NavierStokes_COMPLETE.lean` archive attempted an axiom-based closure and was moved to `orphans/`. That path was correctly abandoned.

**J. Current true residual.** The literal Clay statement requires a smooth `u : ℝ⁴ → ℝ³` solution for all time and all smooth initial data. The corpus delivers substrate-level bilinear/Sobolev pieces; the leap to global smoothness is the Unit-typed placeholder. **No smooth solution construction exists.**

**K. Residual strength.** **FULL-STRENGTH RESIDUAL.** The substrate-level pieces (bilinear estimates, orthogonal projection to div-free, some Hadamard bounds) are legitimate PDE prerequisites. They do not amount to a solution.

**L. Last-mile boundary.** Chain enters proved math at Wave 47C+49A+50B+50C composition (div-free Sobolev projection). Everything past that is `Prop := True`.

**M. Shared dependencies.** α_NS = 3π/2 in the α-web. The Sobolev/orthogonal-projection machinery is generic; not shared with other tracks.

**N. Next theorem that would actually matter.** A **rigorous a priori estimate** ruling out finite-time blowup in a nontrivial class of 3D smooth initial data — e.g. the Ladyzhenskaya-Prodi-Serrin criteria in a formalized shape. Anything less than a genuine PDE-level inequality on `‖∇u(t)‖_{L^∞}` won't move the residual.

---

## 4. YANG-MILLS

**A. Literal external statement.** For a compact simple non-abelian gauge group (e.g. SU(2), SU(3)) on `ℝ⁴`, construct a Wightman-axiomatic quantum field theory of the corresponding Yang-Mills action with a positive mass gap (`inf spec(H) − 0 > 0` where H is the Hamiltonian).

**B. External status.** OPEN. Clay Millennium Problem. Lattice Monte Carlo evidence for a gap; no continuum construction on ℝ⁴.

**C. Canonical objects.** Gauge field `A_μ : ℝ⁴ → 𝔤`, curvature `F_{μν} = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]`, YM action `-¼ tr F² d⁴x`, path integral measure, Osterwalder-Schrader / Wightman reconstruction, Hamiltonian in the physical Hilbert space, mass gap.

**D. Current PF files (live).**
- `PF/YM_SubstrateBulletproofClosure.lean` — `YM_bulletproof_substrate_closure` bundles: `α_YM = 2`, 2×2 interacting Hamiltonian gap `0 < 1/2`, trace = 2, Bochner–Minlos R⁴ typed statement, `MeasureTheory.IsProbabilityMeasure standardGaussianR4`, `0 < YangMills.Lambda_QCD`, glueball mass in (1770, 1780) MeV, gap in (419, 421) MeV.
- `PF/YM_FrameworkMillenniumAnswer.lean` — framework-level wrapper.
- `PF/YM_ContinuumWightmanV3.lean`, `PF/YM_ContinuumWightmanV4.lean` — Wightman-scoped attempts (labeled "axiom-free framework theorem").
- `PF/YM_SchwartzReflectionConcreteWitness.lean` — reflection-positivity witness attempt (line 50 mentions an axiom for time-reflection positivity; needs unfold to confirm).
- `PF/YMReflectionPositivityToyAttempt.lean` — toy model.

**E. Archived PF files.** `ARCHIVE/2026-06-16-orphans/YM_Equivalence.lean` — axioms: `fractal_resonance_sum_converges`, `R_f_meromorphic_at_2`, `yang_mills_measure_exists`, `minlos_theorem`, `confinement_via_measurement`. **NOT in the live tree** but referenced conceptually. `AxiomAudit.lean` at HEAD lists `YM_pillar_axioms` including `R_f_meromorphic_at_2`, `yang_mills_measure_exists`, `minlos_theorem` — need to check whether these are declared as `axiom` in the LIVE tree or merely REFERENCED.

**F. Mathlib infrastructure.** Basic measure theory + Gaussians. No Wightman axioms, no nuclear spaces of test functions, no reflection positivity, no OS reconstruction.

**G. Kernel-proved PF content.** 2×2 finite-dimensional Hamiltonian with gap `1/2 > 0` and trace = 2. Bochner–Minlos R⁴ typed statement (needs unfolding — likely a schematic Prop). Standard Gaussian on R⁴ is a probability measure (mathlib). `YangMills.Lambda_QCD > 0` — needs unfold; likely a definition-level positivity.

**H. Definitions / assertions.** `α_YM := 2`. `Lambda_QCD`, glueball mass, gap MeV bounds — likely `def`-based constants set to specific decimals matching lattice-QCD phenomenology. If so, the "in (419, 421)" is a `norm_num` check on the constant, not a physical prediction.

**I. Failed or circular routes.** Archive's outright axiom-based closure. If `R_f_meromorphic_at_2` or `yang_mills_measure_exists` remain as declared `axiom`s in the live tree (needs immediate verification per Appendix A), that's a §I.2 violation.

**J. Current true residual.** Literal Clay YM needs a rigorous continuum QFT on ℝ⁴ with positive spectrum gap in the physical Hilbert space. Corpus delivers a finite-dim toy + phenomenology. Wightman reconstruction, nuclearity, reflection positivity are all open.

**K. Residual strength.** **FULL-STRENGTH RESIDUAL.**

**L. Last-mile boundary.** Chain enters proved math at the 2×2 Hamiltonian spectral gap (linear algebra). Everything above is placeholder / axiom-tagged.

**M. Shared dependencies.** α_YM = 2 in α-web. `standardGaussianR4` shared with any continuum-QFT track. Would-be shared with NS if a rigorous PDE-continuum bridge existed.

**N. Next theorem that would actually matter.** A **rigorous lattice YM construction of the physical Hilbert space** with a proven positive spectral gap in the continuum limit — even for SU(2) on `ℤ⁴` at finite lattice spacing. Anything less is finite-dim decoration.

---

## 5. BSD

**A. Literal external statement.** For an elliptic curve `E/ℚ`, the algebraic rank equals the order of vanishing of the Hasse-Weil L-function `L(E, s)` at `s = 1`.

**B. External status.** OPEN. Clay Millennium Problem. Rank ≤ 1 cases with additional hypotheses proven (Coates-Wiles, Gross-Zagier, Kolyvagin).

**C. Canonical objects.** `EllipticCurve ℚ`, `MordellWeil E ℚ`, `E.rank`, Hasse-Weil `L(E, s)`, Selmer groups, Shafarevich-Tate group.

**D. Current PF files (live).**
- `PF/BSDMordellWeilRankZeroTypedEmpiricalAnchor.lean` — `IBMHardwareAlphaBSDEmpiricalAnchor` + `MordellWeilRankZeroTyped` on the single curve E_{32.a3} (LMFDB, rank 0, CM by ℤ[i], torsion ℤ/2×ℤ/2).
- `PF/BSDCoatesWilesRankZeroAttempt.lean` — references Coates-Wiles for rank-zero via CM.
- `PF/BSDLFunctionBridgeRank0.lean` — uses α_BSD = 3π/4 as a substrate phase, not a classical L-function.
- `PF/AlphaBSDIntegralBundle.lean`, `PF/AlphaBSDSigmaPositive_r228.lean`, `PF/AlphaBSDUpperBracketCantor_r245.lean` — substrate σ-sign, Cantor-bracket results.
- `PF/EllipticTrace_r194.lean` (referenced in `codex/BSD_TRACE_RANK_2026-08-03.md`).
- `codex/BSD_TRACE_RANK_2026-08-03.md`, `codex/BSD_NONTORSION_ARC_PLAN_2026-07-27.md`, `codex/BSD_UNIVERSAL_SECANT_2026-08-05.md`.

**E. Archived PF files.** Various early BSD attempts in `ARCHIVE/`.

**F. Mathlib infrastructure.** `Mathlib.NumberTheory.EllipticCurve` — group law, coordinates. No `EllipticCurve.rank` in a general sense. No `LSeries` for elliptic curves. No BSD infrastructure.

**G. Kernel-proved PF content.** `σ(α_BSD) > 0`, `σ(α_BSD) < log_3 2`, `α_BSD = 3π/4` substrate oscillator identities. `MordellWeilRankZeroTyped` typed Prop on E_{32.a3} + LMFDB data anchor. All axiom-free at kernel level.

**H. Definitions / assertions.** `α_BSD := 3π/4`. `IBMHardwareAlphaBSDEmpiricalAnchor` bundles an IBM-CSV 11-problem clustering observation. The typed anchor `MordellWeilRankZeroTyped` on E_{32.a3} is a `def` bundling four clauses (curve identity, CM certificate, torsion, LMFDB rank 0). The "rank 0" is a NAMED external fact, not derived.

**I. Failed or circular routes.** The "empirical anchor" chain is a definitional bundle, not a derivation of why the IBM-CSV cluster sits at 3π/4.

**J. Current true residual.** The literal Clay BSD requires the rank-L-vanishing equality for ALL elliptic curves over ℚ. The corpus provides: substrate α-work + typed Prop on ONE curve + IBM-CSV empirical cluster. **The general rank mechanism is entirely open.**

**K. Residual strength.** **FULL-STRENGTH RESIDUAL.**

**L. Last-mile boundary.** Chain enters proved math at the α_BSD substrate identities and at the LMFDB-verified single-curve rank-zero data. Everything past that is empirical or typed-only.

**M. Shared dependencies.** α_BSD = 3π/4 in the α-web. `EllipticCurve` machinery in mathlib is minimal; would be shared with any arithmetic-geometry track that materializes.

**N. Next theorem that would actually matter.** A **general rank-0 discharge** for a family of CM elliptic curves via a formalized Coates-Wiles chain (not just a typed anchor on one curve). This would move BSD from "one-anchor-plus-heuristic" to "family theorem, rank-0 case" and match published (1977) mathematics.

---

## 6. HODGE

**A. Literal external statement.** For a smooth projective complex algebraic variety `X`, every rational Hodge class (an element of `H^{2p}(X, ℚ) ∩ H^{p,p}(X)`) is a rational linear combination of classes of algebraic subvarieties.

**B. External status.** OPEN. Clay Millennium Problem. Lefschetz (1,1)-theorem gives the codimension-1 case for all X. Full conjecture open in codim ≥ 2.

**C. Canonical objects.** Smooth projective complex variety, Hodge decomposition, `H^{p,p}(X)`, algebraic cycles, cycle-class map `cl : CH^p(X)_ℚ → H^{2p}(X, ℚ)`.

**D. Current PF files (live).**
- `PF/MillenniumSixReductions.lean` — `def HodgeConjecture : Prop := ∀ (H : HodgeAmbient), ∀ (class_idx : ℕ), HodgeAlgebraicRepresentation H class_idx`. `HodgeAmbient` is a typed record (dim, p, betti), NOT a smooth projective variety.
- `PF/AlgebraicGeometry/HodgeCurveDim1Substrate.lean` — dim=1 discharge via divisor machinery (Lefschetz (1,1) at codim 1 on curves).
- `PF/AlgebraicGeometry/HodgeK3Dim2Substrate.lean` — K3 surface substrate (Lefschetz (1,1) at codim 1 on K3 surfaces).
- `PF/AlgebraicGeometry/Cohen2025_HodgeConjecture_NamedAnchors_2026_06_19.lean` — **6× `Prop := True`** anchors citing the prior 2025 Cohen manuscript.
- `PF/AlgebraicGeometry/Hodge_Substrate_NamedAnchors_2026_06_19.lean` — **7× `Prop := True`** anchors citing Hodge 1941, Deligne 1971/1968, Griffiths 1969, Cattani-Deligne-Kaplan 1995, Voisin 2002/2007.
- `PF/AlgebraicGeometry/CycleClassMapAtCodim2Attempt.lean` — `VoisinObstructionAtCodimTwoCY3 : Prop := True` (line 502).
- `PF/AlgebraicGeometry/VoisinObstructionTypedUpgrade.lean` — attempts to type-upgrade two `Prop := True` placeholders.
- `PF/AlphaHodgeSigmaPositive_r226.lean`, `PF/AlphaHodgeUpperBracketCantor_r243.lean`, `PF/AlphaHodgeTighterHalfBracket_r248.lean`.
- `PF/Hodge_SixSubstrateClassesBundle.lean` — named bundle for curve, K3, abelian surface, CY3, CY4, generic surface (substrate proxies, not varieties).

**E. Archived PF files.** `HODGE_MATHLIB_GAP_2026-05-25.md` in codex — audits mathlib gaps: smooth projective ℂ-variety, Hodge decomposition, Hodge class, cycle-class map, Lefschetz (1,1) all MISSING in mathlib.

**F. Mathlib infrastructure.** Nearly nothing at the Hodge level. Some `AlgebraicGeometry` scheme framework, but no complex analytic Hodge theory. Multi-year project.

**G. Kernel-proved PF content.** `σ(α_Hodge) > 0`, `σ(α_Hodge) < log_3 2`, tighter half-bracket refinement. Dim=1 divisor case for the HodgeAmbient-typed statement. All axiom-free at kernel level.

**H. Definitions / assertions.** **`Prop := True` × 13+** anchors citing prior work. `α_Hodge := φ`. `HodgeConjecture` on `HodgeAmbient` (substrate record), not on `SmoothProjectiveVariety ℂ`.

**I. Failed or circular routes.** The `Prop := True` anchor pattern is honest about scope (it names prior work), but it does not provide any mathematical content. `VoisinObstructionTypedUpgrade` (2026-06-02) is an in-progress cleanup.

**J. Current true residual.** The literal Clay Hodge requires the cycle-class-map surjectivity on `H^{2p}(X, ℚ) ∩ H^{p,p}(X)` for all smooth projective ℂ-varieties in all codimensions p. The corpus has dim=1 discharge only. **7+ mathlib foundational structures are missing.**

**K. Residual strength.** **FULL-STRENGTH RESIDUAL** at the classical level. The substrate-level statement `HodgeConjecture` on `HodgeAmbient` is discharged for dim=1 only, and its bridge to actual varieties is not made.

**L. Last-mile boundary.** Chain enters proved math at the dim=1 divisor discharge and the substrate α-work. Everything past that is `Prop := True` or missing mathlib.

**M. Shared dependencies.** α_Hodge = φ shared with `α_NP = φ + 1/4` (the P-vs-NP bridge uses this connection). Cohen2025 anchors shared with the P-vs-NP "Hodge disc5 bridge."

**N. Next theorem that would actually matter.** **Formalize the cycle-class map** `cl : CH^1(X)_ℚ → H²(X, ℚ)` for smooth projective ℂ-surfaces in mathlib-native shape and prove Lefschetz (1,1) at codim 1. This unlocks the K3 substrate to be a real theorem instead of a substrate proxy. From there, codim-2 is the actual Clay residual.

---

## 7. COLLATZ

**A. Literal external statement.** `∀ n : ℕ, n > 0 → ∃ k, collatzIter k n = 1`.

**B. External status.** OPEN. Verified computationally to n ≈ 2^68. Tao 2019: "almost all orbits attain almost bounded values."

**C. Canonical objects.** `collatzStep : ℕ → ℕ`, iterated map, stopping time.

**D. Current PF files (live).**
- `PF/NumberTheory/CollatzConjectureFrameworkAttack.lean` — `CollatzConjecture : Prop` (named unproved), 20 concrete witnesses (each via `native_decide`), α_Collatz = log₂ 3 bracket, `CollatzMatches3kSubstrate` (base-3 substrate witness), typed Props for Tao 2019 / Krasikov-Lagarias 2003 / Terras 1976. Capstone `CollatzFrameworkAttack`.

**E. Archived PF files.** `ARCHIVE/.../CollatzFractal.lean` (φ-based approach, abandoned), `codex/COLLATZ_FRACTAL_RESONANCE_APPROACH.md`, `collatz_via_substrate_v1.tex`.

**F. Mathlib infrastructure.** `Mathlib.NumberTheory.Collatz` — basic `Collatz.next`, iteration lemmas. No conjecture proof.

**G. Kernel-proved PF content.** 20 concrete trajectories reach 1 (finitary). α_Collatz = log₂ 3 ≈ 1.585 with interval bracket. `CollatzMatches3kSubstrate` witnessed by the trivial (0, 1) pair.

**H. Definitions / assertions.** `CollatzConjecture` literal. Tao / KL / Terras are typed unproved Props.

**I. Failed or circular routes.** None besides the abandoned φ approach.

**J. Current true residual.** The literal conjecture. Framework provides finite verification + α-axis identification (base-3 substrate is genuinely 3, so log₂ 3 is not numerology — it's the ternary log). No infinite-orbit result.

**K. Residual strength.** **FULL-STRENGTH RESIDUAL.**

**L. Last-mile boundary.** Chain enters proved math at the 20 concrete witnesses and the log₂ 3 bracket. Everything past that is typed-only or the literal conjecture.

**M. Shared dependencies.** Base-3 substrate shared with the entire PF framework (ternary is the substrate's base). Not shared with other number-theory tracks specifically.

**N. Next theorem that would actually matter.** A **proven Lyapunov / potential decrease** — even for a restricted class of initial conditions — that goes beyond finite verification. The abandoned φ-approach was chasing this; the framework backed off. The current corpus does not have a live Lyapunov proof attempt.

**⚠ HEAD verification:** the 20 witnesses use `native_decide`, which adds `Lean.ofReduceBool` to the axiom budget. Any capstone bundling those witnesses INHERITS `Lean.ofReduceBool`. Per MASTER DIRECTIVE §I.2 this violates "no `native_decide` on load-bearing paths." The corpus discloses this openly ("kernel reduction for `native_decide`"), but the disclosure does not remove the axiom. Fix would be `decide` (kernel-native) instead — feasible for small n but slower; or precomputed rewriting proofs.

---

## 8. STRONG GOLDBACH

**A. Literal external statement.** `∀ n : ℕ, n ≥ 4 → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n`.

**B. External status.** OPEN. Verified to `4 · 10^18` (Oliveira, Silva, Herzog, Pardi 2014). Weak Goldbach proved (Helfgott 2013).

**C. Canonical objects.** `Nat.Prime`, sum decomposition, Hardy-Littlewood circle method singular series.

**D. Current PF files (live).**
- `PF/NumberTheory/GoldbachConjectureFrameworkAttack.lean` — `GoldbachConjecture` literal, 12 witnesses (`by decide`), α_Goldbach = 1 + 1/√2, Hardy-Littlewood coeff, typed Chen 1973 / Vinogradov 1937 / Helfgott 2013 / HL asymptotic / Oliveira 2014. `GoldbachViaFrameworkSpectralCascade` oracle-parametric Prop. Verified-up-to-20 axiom-free (`GoldbachVerifiedUpToBound 20`).

**E. Archived PF files.** `goldbach_via_substrate_v1.tex`.

**F. Mathlib infrastructure.** `Nat.Prime`, `Nat.instDecidablePrime`. Circle method not in mathlib.

**G. Kernel-proved PF content.** 12 concrete decompositions (axiom-free via `decide`; NOT `native_decide` here). α_Goldbach = 1 + 1/√2 positivity. HL coeff bracket. `helfgott_implies_vinogradov` implication (typed).

**H. Definitions / assertions.** `GoldbachConjecture` literal. Chen/Vinogradov/Helfgott/Oliveira typed Props (published, unformalized).

**I. Failed or circular routes.** None.

**J. Current true residual.** The literal conjecture. Framework provides α-axis identification `α_Goldbach = 1 + 1/√2` linking Poincaré unit + Vinogradov minor-arc exponent. Interesting substrate identity: `α_Goldbach · α_P = α_P + 1` where `α_P = √2`. No infinite result.

**K. Residual strength.** **FULL-STRENGTH RESIDUAL.**

**L. Last-mile boundary.** Chain enters proved math at the 12 witnesses (kernel `decide`), α bracket, HL coeff bracket.

**M. Shared dependencies.** α_P = √2 shared with the α-web; α_Goldbach = 1 + 1/√2 is derived from √2 substrate. Cross-references to `CrossMillenniumSharedInvariants`.

**N. Next theorem that would actually matter.** A **major arc estimate in Lean** for the singular series — formalize the Hardy-Littlewood constant `2C₂ ≈ 1.32` with an explicit error bound. That's a substantial-but-tractable mathlib-adjacent goal that would connect PF's α-work to real analytic number theory.

---

## 9. TWIN PRIME

**A. Literal external statement.** `∀ N : ℕ, ∃ n > N, Nat.Prime n ∧ Nat.Prime (n + 2)`.

**B. External status.** OPEN. Zhang 2013 + Polymath 8b 2014: `∃ k ≤ 246 (even), infinitely many prime pairs at gap k`. Twin primes = k=2 case.

**C. Canonical objects.** `Nat.Prime`, twin-prime pair, admissible tuples (Maynard-Tao sieve), Hardy-Littlewood constant `C_2 ≈ 0.6601618`.

**D. Current PF files (live).**
- `PF/NumberTheory/TwinPrimeConjectureFrameworkAttack.lean` — `TwinPrimeConjecture` literal, 10 witnesses (`decide`), α_TwinPrime = 3/2 = α_RH (**shared axis!**), typed Polymath ≤ 246 / Brun 1919 / HL asymptotic. `TwinPrimeViaSpectralCascade` oracle-parametric Prop. `twinPrimeConstant := 0.6601618158`, `brunConstant := 1.902160583104`.

**E. Archived PF files.** `twin_prime_via_substrate_v1.tex`.

**F. Mathlib infrastructure.** `Nat.Prime` + decidability. No twin-prime density theory.

**G. Kernel-proved PF content.** 10 concrete pairs (axiom-free `decide`). α_TwinPrime = α_RH = 3/2 (`rfl` from definitions). C_2 and Brun constant positivity brackets.

**H. Definitions / assertions.** `TwinPrimeConjecture` literal. Polymath / Brun / HL typed Props.

**I. Failed or circular routes.** None. Note the α equality `α_TwinPrime = α_RH` is definitional (both are set to `3/2`) — this is honest naming, not derivation. The claim "twin primes sit on the RH axis" is a substrate architectural assertion, not a theorem.

**J. Current true residual.** The literal conjecture. Framework provides identification with RH critical-line α (definitional) + finite witnesses + constants.

**K. Residual strength.** **FULL-STRENGTH RESIDUAL.**

**L. Last-mile boundary.** Chain enters proved math at witnesses and constant brackets.

**M. Shared dependencies.** **α_RH = α_TwinPrime = α_Polignac = 3/2** — this is the α-axis identification pattern. Common object: `CrossMillenniumSharedInvariants`. If a substrate spectral-cascade oracle is ever built that legitimately produces prime detection at scale, all three collapse.

**N. Next theorem that would actually matter.** **Formalize Brun's theorem** (`∑ 1/p over twin primes converges`) in Lean/mathlib. This is a real, published, tractable result. It's the smallest classical twin-prime theorem missing from formal mathematics. Would tie PF's `brunConstant` bracket to the actual convergent sum.

---

## 10. KISSING NUMBER PROGRAM

**A. Literal external statement.** For each dimension `n`, compute or bound `τ_n = max number of unit n-spheres tangent to a central unit n-sphere without overlap`.

**B. External status.** τ₁=2, τ₂=6, τ₃=12 (all classical), τ₄=24 (Musin 2003), τ₈=240 (Odlyzko-Sloane / Levenshtein 1979), τ₂₄=196560 (same). Dimensions 5–7, 9–23 (except 8), 25+ OPEN.

**C. Canonical objects.** Sphere packings, root lattices (E₈, Leech), spherical codes, LP bounds.

**D. Current PF files (live).** **NONE.**
- Grep for `kissing|Kissing|τ_n|tau_n|sphere_packing|Packing|contact_number` in `PF_Lean4_Code/` and `codex/`: **ZERO substantive hits.**
- E₈ appears only as a background fact in `HodgeK3Dim2Substrate.lean` (K3 cohomology lattice `H²(K3, ℤ) ≃ 2·E₈(-1) ⊕ 3·U`), not as a sphere-packing object.

**E. Archived PF files.** None.

**F. Mathlib infrastructure.** No kissing-number formalization in mathlib. Some root-system machinery.

**G. Kernel-proved PF content.** None on kissing. Substantial content on H₃ Coxeter (h=10, exponents {1,5,9}, `sin(π/10) = 1/(2φ)`) — real, axiom-free, but unrelated to kissing.

**H. Definitions / assertions.** None.

**I. Failed or circular routes.** None (nothing attempted).

**J. Current true residual.** Everything. No PF work on kissing exists.

**K. Residual strength.** **NO PF WORK** (not a FULL-STRENGTH residual on PF's plate; it's simply not on the plate).

**L. Last-mile boundary.** N/A.

**M. Shared dependencies.** E₈ appears in Hodge K3 substrate. H₃ Coxeter machinery is real PF work but is used for α-substrate architecture, not sphere packing.

**N. Next theorem that would actually matter.** If Pabs's directive to include kissing is more than curatorial, the entry point would be: **formalize `τ₈ = 240` via the E₈ lattice minimum-norm-vector count** (Levenshtein / Odlyzko-Sloane 1979). This is a proved external result but not in mathlib. Would be a fresh multi-month formalization project; not adjacent to any existing PF work.

---

## 11. UNKNOTTING PROGRAM

**A. Literal external statement.** Ambiguous — the corpus's 143-problem archive phrases the target as **"Prove the Unknotting Problem is in NP"** (complexity classification). External math has multiple related targets: (A) decidability of unknot recognition (KNOWN — Haken 1961, Kuperberg 2014 also shows knottedness is in coNP), (B) NP membership of unknot recognition (KNOWN — Hass-Lagarias-Pippenger 1999), (C) unknotting number computation (hard for specific knots), (D) knot genus problem.

**B. External status.** Depends on the target. Decidability KNOWN. NP membership of unknottedness KNOWN. Various other knot-invariant complexity questions OPEN.

**C. Canonical objects.** Knot diagrams, Reidemeister moves, knot group, Alexander polynomial, Jones polynomial, normal surfaces (Haken).

**D. Current PF files (live).** **NONE.** Only appears as archived data entry #83 in the 143-problem IBM dataset (`ARCHIVE/.../143 Problems Solved On IBM.py`).

**E. Archived PF files.** IBM 143-problem CSV entry only.

**F. Mathlib infrastructure.** Minimal knot-theory content in mathlib.

**G. Kernel-proved PF content.** None.

**H. Definitions / assertions.** None.

**I. Failed or circular routes.** None (nothing attempted).

**J. Current true residual.** Everything. Also: pick a target. The 143-problem framing "in NP" was already externally proved by Hass-Lagarias-Pippenger (1999); formalizing that would be a legitimate but existing-mathematics project.

**K. Residual strength.** **NO PF WORK.**

**L. Last-mile boundary.** N/A.

**M. Shared dependencies.** None with the current corpus.

**N. Next theorem that would actually matter.** If unknotting were prioritized: **formalize a piece of the HLP-1999 NP-membership proof** in mathlib. This is a real result but unformalized. Fresh project.

---

## 12. LARGE CARDINAL PROJECT

**A. Literal external statement.** Not a single problem; a program. Sample targets: prove the existence of an inaccessible cardinal (RELATIVE-CONSISTENCY, not provable in ZFC), formalize the consistency-strength hierarchy, prove relative equiconsistencies, construct inner models.

**B. External status.** Inaccessibles / measurables / Woodins / supercompacts have well-understood consistency-strength relations (external mathematics). Existence provably not proved in ZFC.

**C. Canonical objects.** Cardinal, elementary embedding, inner model, `L`, `V=L`, `V=HOD`.

**D. Current PF files (live).**
- `PF/SetTheory/ContinuumHypothesisFrameworkAttack.lean` — the ONLY set-theory file. `ContinuumHypothesis : Prop := continuum = aleph_1` (typed, not proved). Proves the substrate cardinality dichotomy (finite ℵ₀ levels + macroscopic 𝔠).
- NO large-cardinal files anywhere.

**E. Archived PF files.** `ARCHIVE/2026-06-16-orphans/AXIOM_ELIMINATION_REPORT.md` **explicitly disclaims** large-cardinal axioms as "example of what is NOT present." Zero smuggling risk detected.

**F. Mathlib infrastructure.** `Cardinal.aleph`, `Cardinal.continuum`, `Cardinal.aleph0_lt_continuum`, `Cardinal.aleph_one_le_continuum`. Reasonable set-theory but no large cardinals.

**G. Kernel-proved PF content.** CH file substrate dichotomy `ℵ₀ < 𝔠` and `ℵ₁ ≤ 𝔠` (from mathlib), axiom-free capstone `continuum_hypothesis_framework_attack_capstone`.

**H. Definitions / assertions.** `ProvableFromZFC (P : Prop) := P` — an opaque identity stub (external citation, honest).

**I. Failed or circular routes.** None.

**J. Current true residual.** Everything on the large-cardinal side. Pick a target first — currently there is no PF Large Cardinal Project.

**K. Residual strength.** **NO PF WORK.**

**L. Last-mile boundary.** N/A.

**M. Shared dependencies.** None.

**N. Next theorem that would actually matter.** If pursued: **formalize the relative-consistency of an inaccessible with ZFC** (i.e. build `L_κ` or similar), NOT existence. Any existence claim would be an axiom (§I.2 violation).

---

## 13. IRRATIONALITY OF π + e

**A. Literal external statement.** `Real.pi + Real.exp 1 ∉ ℚ` (equivalently `Irrational (Real.pi + Real.exp 1)`).

**B. External status.** OPEN. `π` and `e` are separately transcendental (Lindemann 1882, Hermite 1873). Neither `π + e` nor `π · e` is known to be irrational; but AT LEAST ONE of them is transcendental (elementary: their sum and product cannot both be algebraic).

**C. Canonical objects.** `Real.pi`, `Real.exp 1`, `Irrational`, Lindemann-Weierstrass theorem.

**D. Current PF files (live).**
- `PF/AlphaGelfondSchneiderBundle.lean` — proves `(2^√2)^√2 = 4` (Gelfond-Schneider illustration), NOT π+e.
- No file addresses `Real.pi + Real.exp 1`.

**E. Archived PF files.** None.

**F. Mathlib infrastructure.** `Real.pi`, `Real.exp 1`, `Irrational`, `Real.irrational_pi`. Partial Lindemann-Weierstrass in `Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart` (analytical framework only, no LW statement). `e` transcendence NOT in mathlib. π + e status NOT in mathlib.

**G. Kernel-proved PF content.** None on π+e. Some irrationality results for α-values (`irrational_alpha_P = √2`, `irrational_alpha_NS = 3π/2`, `irrational_alpha_BSD = 3π/4`, `irrational_alpha_QG = √(2π)`) all axiom-free via `Real.irrational_pi`.

**H. Definitions / assertions.** None.

**I. Failed or circular routes.** None.

**J. Current true residual.** Everything. Genuine research residual: π+e irrationality is not known to any known technique.

**K. Residual strength.** **NO PF WORK. FULL-STRENGTH OPEN PROBLEM externally.**

**L. Last-mile boundary.** N/A.

**M. Shared dependencies.** Real π / e machinery in mathlib shared with any transcendence track.

**N. Next theorem that would actually matter.** If pursued: **formalize the elementary fact "at least one of π+e, πe is transcendental"** in mathlib. This uses Lindemann-Weierstrass on the polynomial with roots π and e; requires the LW theorem statement (currently only analytical infrastructure in mathlib). Real target for π+e irrationality itself requires new mathematics — not attempted anywhere externally either.

---

## 14. EULER-MASCHERONI γ

**A. Literal external statement.** `Real.eulerMascheroniConstant ∉ ℚ` (irrationality) or stronger, `¬ IsAlgebraic ℚ Real.eulerMascheroniConstant` (transcendence).

**B. External status.** OPEN. Both irrationality and transcendence unresolved.

**C. Canonical objects.** `γ = lim (H_n − log n)`, `H_n = ∑_{k=1}^n 1/k`.

**D. Current PF files (live).** **NONE.** Files with "Gamma" in name pertain to the Gamma function `Real.Gamma`, not γ:
- `AlphaGammaAtAlphaBundle.lean`, `AlphaGammaFunctionAxisAnchorBundle.lean`, `AlphaQGGammaHalfIntegerLadder.lean` — all Γ values at α-axes, not γ irrationality.

**E. Archived PF files.** None.

**F. Mathlib infrastructure.** `Real.eulerMascheroniConstant : ℝ` (Mathlib.NumberTheory.Harmonic.EulerMascheroni). Proves `1/2 < γ < 2/3` and `γ = lim (H_n - log n)`. No irrationality claim.

**G. Kernel-proved PF content.** None on γ.

**H. Definitions / assertions.** None in PF.

**I. Failed or circular routes.** None.

**J. Current true residual.** Everything. FULL-STRENGTH OPEN.

**K. Residual strength.** **NO PF WORK. FULL-STRENGTH OPEN PROBLEM externally.**

**L. Last-mile boundary.** N/A.

**M. Shared dependencies.** Harmonic-sum machinery in mathlib.

**N. Next theorem that would actually matter.** If pursued: no known route to γ irrationality/transcendence exists in mathematics. Formalizing existing partial results (e.g. relations between γ and integrals) would be curatorial. Not adjacent to any PF work.

---

# XIV. CROSS-PROBLEM DEPENDENCY GRAPH

## Shared mechanisms (TESTED, not assumed)

### 1. α-web (`CrossMillenniumSharedInvariants`)

**Members:** α_Poincaré = 1, α_P = √2, α_YM = 2, α_RH = 3/2, α_Hodge = φ, α_NP = φ + 1/4, α_BSD = 3π/4, α_NS = 3π/2, α_QG = √(2π).

**Substrate status (per r123):** SUBSTRATE CANNOT FORCE THESE VALUES. K-theory range = ℤ[1/3]; only α_Poincaré = 1 and α_YM = 2 fit. Others irrational or 2-adic-obstructed. Substrate is spectrally VACUOUS (realizes any spectrum). Ternary reality condition independently excludes √2 and φ+1/4.

**α-axis identifications:**
- α_RH = α_TwinPrime = α_Polignac = **3/2** (definitional; TwinPrime / Polignac ride on RH's axis by naming).
- α_NP = α_Hodge + 1/4 = **φ + 1/4** (definitional; underpins the P-vs-NP-via-Hodge open bridge Prop).
- α_YM = α_P² = **2** (proven algebraic tower structure with α_Poincaré).

**Cluster:** RH ∪ TwinPrime ∪ Polignac ∪ (via α_Goldbach = 1 + 1/√2 also touches α_P) Goldbach → **ANALYTIC / ADDITIVE PRIME** cluster. Real shared PF object: `CrossMillenniumSharedInvariants` + the r120–r315 Xi/theta machinery for RH. Twin/Polignac/Goldbach do NOT depend on Xi machinery; only on the α-axis identifications (which per r123 are external constraints, not substrate-forced).

### 2. Substrate T_∞ (r113 + r123)

**Kernel-proved (r113 substrate_UHF_trace_unique):** the projective-limit von Neumann algebra `π(T_∞)″` is the Glimm 3^∞ UHF factor, uniquely traced.

**Kernel-proved (r123):** substrate is (i) K-theoretically ℤ[1/3]-bounded, (ii) spectrally vacuous, (iii) tracially unique (ONE state, not nine).

**Conjecture 8.X.2 (nine extremal traces ↔ nine α-values):** **FALSIFIED.** One tracial state ≠ nine.

**Implication for the α-web:** The α-values are EXTERNAL inputs to the framework, not substrate-derived. Every "derivation" theorem (`α_X = Y` for specific Y) uses `unfold + ring` or `rfl` on the definition.

**Cluster:** T_∞ substrate underpins BSD/Hodge/YM/NS/RH/P-vs-NP substrate-level results indirectly (via α-web), but does not FORCE any of the specific α-values. Substrate + r123 negative capstone are shared ACROSS ALL 6 CLAY AXES.

### 3. Xi / theta / Mellin / interval-engine (RH-exclusive)

**Members:** `Xi_split_intervalIntegral`, `Xi_tail_bound`, `omega_partial_error`, `abs_thetaTermD2_sum_le_at`, `composite_midpoint_error`, `XiOnLineZeroConstants`, `XiPanels/*`, `XiPanelsT15/*`. All r120 / r315 machinery.

**Cluster:** RH (r120 on-line-zero atom, r280 countability, r315 Xi(15) positivity). Not shared with other tracks. Very deep and reusable for future Xi(t) work — but per DIRECTIVE §XI FREEZE, no more Xi(t) chasing.

### 4. `native_decide` / `Prop := True` load-bearing artifacts (POLICY GAPS)

**Members:**
- Collatz witnesses: `native_decide` (20 uses) → `Lean.ofReduceBool` in capstone axiom budget.
- Polignac: `native_decide` (k=246 witness).
- Singmaster, OddPerfect, Brocard: also `native_decide`.
- NS2DGlobalRegularity: `Prop := True` (line 318). NavierStokesGlobalSmoothness: Unit-typed.
- Hodge Cohen2025 anchors: 6× `Prop := True`.
- Hodge substrate anchors: 7× `Prop := True`.
- Hodge CycleClassMapAtCodim2Attempt / VoisinObstructionAtCodimTwoCY3: `Prop := True`.

**Cluster:** These are honest-scope disclosures (comments say so) but they are POLICY VIOLATIONS on load-bearing paths per MASTER DIRECTIVE §I.2 and §I.5. Repairing these is a **shared refactor** across the α-web/NumberTheory attacks and the Hodge/NS substrate. VoisinObstructionTypedUpgrade shows a partial repair template already in the tree.

### 5. Perelman anchor cascade

**Members:** r126–r128 (Perelman anchor forces 6 of 9 α-values via cascade). The Perelman anchor `α_Poincaré = 1` is a substrate constant (mathlib primitive).

**Cluster:** Applies to the α-web derivation side (r125's Galois structure combined). But per r123, even this cascade is a SUBSTRATE derivation showing the α-values satisfy Galois-relation constraints — it does NOT force them from first principles. The cascade is a CONDITIONAL closure (given anchor α_Poincaré = 1 as substrate primitive).

## Rejected clusters (tested, no shared mechanism found)

- **Kissing + Coxeter/H3/E8:** H₃ is real PF work; kissing is empty. E₈ appears only as background in Hodge K3 lattice, not as a packing object. **No shared PF mechanism.**
- **Continuum (NS + YM):** both need Wightman/PDE continuum machinery that PF does not build. Both have substrate closures at the finite-dim / Sobolev-Galerkin level. **Adjacent but not shared** — no theorem is used by both.
- **Foundational (Large Cardinal + CH + Turing complexity):** CH file is isolated. TuringEncoding/Complexity is isolated (framework-internal). No Large Cardinal file exists. **No cluster.**
- **π+e + γ (transcendence cluster):** both empty in PF; mathlib LW infrastructure incomplete. **No cluster.**

---

# XVII. RANKING — CANDIDATE NEXT ATTACKS

Ranked per DIRECTIVE §XVII (10 factors: axes affected, PF centrality, residual < famous problem, existing kernel infra, literal-theorem yield, falsifiability, circularity risk, cost, novelty, reusability).

| Rank | Candidate | Axes affected | PF centrality | Residual < famous? | Infra | Cost | Circularity risk |
|---|---|---|---|---|---|---|---|
| 1 | **Substrate reality-check: does r113 + r123 close Conjecture 8.X.2 in the negative?** | ALL 6 Clay + all α-web | HIGHEST | YES (settles Priority 1a) | r113 + r123 fully proved | LOW | LOW |
| 2 | **Remove `native_decide` from Collatz + Polignac + Singmaster capstones** | Number theory (Collatz, Polignac, Twin-Prime-adjacent) | HIGH | YES (cleanup, not new math) | full existing structure | LOW-MED | ZERO |
| 3 | **Type-upgrade the 13+ `Prop := True` Hodge anchors** (following VoisinObstructionTypedUpgrade pattern) | Hodge, P-vs-NP-bridge, cross-Millennium capstones | HIGH | Depends — some can genuinely upgrade | mathlib Hodge gap is huge | HIGH | LOW (honest scope preserved) |
| 4 | **Formalize Brun's theorem** (`∑ 1/p over twin primes converges`) | Twin Prime, Polignac | MED | YES (Brun 1919 is < Twin Prime) | mathlib prime infrastructure | MED | ZERO |
| 5 | **Formalize Lefschetz (1,1) at codim 1 for K3 surfaces via mathlib cycle-class map** | Hodge, indirectly BSD | HIGH | YES (Lefschetz 1924, a real theorem) | Needs mathlib extensions | HIGH | LOW |
| 6 | **Formalize the elementary fact "at least one of π+e, πe is transcendental"** | π+e track | LOW | YES (uses only Lindemann-Weierstrass on `x² − (π+e)x + πe`) | Requires LW statement in mathlib | MED-HIGH | ZERO |
| 7 | **Formalize `τ_8 = 240` via E₈ lattice minimum-vector count** | Kissing (fresh) | LOW | YES (Odlyzko-Sloane 1979) | E₈ lattice already in mathlib | HIGH | ZERO |
| 8 | **Genuine PDE a priori estimate** (Ladyzhenskaya-Prodi-Serrin) formalized | NS | HIGH | YES (individual criteria are theorems) | mathlib gap enormous | VERY HIGH | LOW |
| 9 | **Formalize lattice YM SU(2) mass gap at finite spacing** | YM | HIGH | YES (finite spacing is easier than continuum) | mathlib gap enormous | VERY HIGH | LOW |
| 10 | **Formalize Coates-Wiles rank-0 discharge for a family of CM elliptic curves** | BSD | MED | YES (published 1977) | Some mathlib elliptic-curve infra | HIGH | LOW |
| 11 | **Prove `PF_T3SymIsHilbertPolyaOperator_Positive` from a substrate-constructed self-adjoint operator** | RH | HIGHEST | RH-STRENGTH | full Xi/theta machinery + r113 substrate | VERY HIGH | HIGH (definitional recovery risk) |
| — | Kissing / Unknotting / Large Cardinal (new dedicated attacks) | isolated | LOW | Depends on target | Nothing | HIGH | Depends |

## Notes on the ranking

- **Rank 1** is unusual because it isn't a NEW theorem — it's a **documentation / declaration** step: recognize that r113 + r123 have already settled the extremal-trace-uniqueness question negatively, promote that finding from "audit result" to "corpus-visible statement," and update OPEN_PROBLEMS.md Problem 1a to reflect that Conjecture 8.X.2 is FALSIFIED. This affects EVERY track that hangs on α-substrate derivation claims.
- **Rank 2** is a POLICY-COMPLIANCE cleanup, not new math. But leaving `native_decide` in load-bearing capstones is a live §I.2 violation that undermines every claim of "kernel-clean."
- **Ranks 3–10** are honest-mathematics targets adjacent to existing PF infrastructure, each with a real literal-theorem endpoint.
- **Rank 11** (RH via HP-operator from substrate) is the most PF-central and most externally significant if it lands — but it is RH-strength and carries HIGH circularity risk (the substrate is now negatively closed for α-forcing; producing a specific operator whose spectrum matches ζ zeros without smuggling assumptions is exactly the RH problem).

---

# XVIII. RECOMMENDED NEXT LANDING

## The graph chooses: **Rank 1 — substrate reality-check and Priority 1a resolution.**

### Statement of the recommended landing

Author a new documentation/formalization landing that does two things:

1. **Formal-corpus update.** Add a Lean file `PF/Analytic/ConjectureEightXTwoFalsified.lean` (or edit the existing `AlphaFromSubstrateKTheory_r123.lean` + `OPEN_PROBLEMS.md`) that STATES, in Lean:
   - `theorem conjecture_8X2_nine_extremal_traces_falsified : ¬ (∃ (T : Fin 9 → TracialState T_∞), Function.Injective T)` — proved by `substrate_UHF_trace_unique` + injectivity contradiction.
   - Update `OPEN_PROBLEMS.md` Problem 1a header from "OPEN" to "**FALSIFIED (r123, 2026-08-23 audit)** — substrate has 1 tracial state, not 9. See `AlphaFromSubstrateKTheory_r123.lean`."

2. **Kernel-clean policy sweep.** Rewrite Collatz + Polignac + Singmaster + OddPerfect + Brocard witnesses from `native_decide` to `decide` (or precomputed `rfl` chains for larger n). Verify axiom budgets on capstones drop `Lean.ofReduceBool`.

### Why this landing has highest global leverage (per DIRECTIVE §XVII)

- **Axes affected:** ALL SIX CLAY. The α-web is the shared mechanism across RH, P-vs-NP, NS, YM, BSD, Hodge. r123 already delivered the negative result about substrate α-forcing. Making it corpus-visible clarifies what every future PF Clay attack must NOT assume.
- **PF centrality:** HIGHEST. Priority 1a from OPEN_PROBLEMS.md — the framework's own central research question.
- **Residual < famous:** YES. Substrate falsification of Conjecture 8.X.2 is a corpus-internal question with a corpus-internal answer, already proved. Not a Millennium residual — a cleanup.
- **Existing kernel infrastructure:** COMPLETE (r113 + r123 already discharged).
- **Literal-theorem yield:** A new negative-existence theorem in Lean, plus a policy-compliance sweep.
- **Falsifiability:** N/A (r123 already delivered a proof).
- **Circularity risk:** ZERO.
- **Formalization cost:** LOW. ~1 day for the falsification theorem + ~1–2 days for `native_decide` → `decide` sweep (some witnesses may need `simp`/reification helpers for larger n).
- **Mathematical novelty:** LOW (the mathematics is r113 + r123).
- **Reusability:** HIGHEST. Every future PF Clay attack must know that the substrate does not force α-values. Explicit corpus statement prevents future circular chains.

### Why NOT the ranked alternatives (short)

- **Rank 2 alone:** Necessary policy cleanup but does not resolve the framework's central research question.
- **Rank 3:** Big work, but Hodge substrate is already known to be dim=1 only. Formalizing type-upgrades won't move the residual meaningfully without mathlib Hodge extensions.
- **Rank 4 (Brun):** Real theorem, worth doing, but tangential — doesn't affect central PF architecture.
- **Rank 5 (Lefschetz 1,1):** Very valuable for Hodge, but multi-month mathlib extension.
- **Rank 11 (HP-operator from substrate):** MOST GLOBALLY VALUABLE if it lands, but the substrate is now KNOWN not to force α-values. Attempting to construct a specific self-adjoint operator whose spectrum matches ζ zeros without smuggling assumptions is exactly RH. Wrong time to attempt without first digesting r123's negative result.

### The doctrine behind the recommendation

DIRECTIVE §XV says: "let the substrate decide." r123 already did. The substrate SAID: I have one tracial state, not nine; my K-theory range is ℤ[1/3]; I do not force the α-values you write down; the ternary reality condition on my own definitions excludes the values you assign; the α-web is external input.

The framework's honest next move is not to attempt another Clay endpoint. It is to **record the substrate's answer**, then **use that answer** to redesign what the α-web means. Every subsequent grand-problem attack must proceed under the new understanding that α-values are external constraints, not substrate-derived quantities.

Rank 1 makes the framework catch up to its own r123.

---

# APPENDIX A — VERIFIED PATHOLOGIES AT HEAD

Grepped at commit `4f7b216d`. Findings that must be addressed on any future load-bearing capstone.

## A.1 `native_decide` on load-bearing witnesses (adds `Lean.ofReduceBool` to axiom budget)

```
PF/NumberTheory/CollatzConjectureFrameworkAttack.lean       — 20+ uses (all 20 concrete witnesses)
PF/NumberTheory/PolignacConjectureFrameworkAttack.lean       — 1 use (k=246 witness at line 143)
PF/NumberTheory/SingmastersConjectureFrameworkAttack.lean    — 3 uses
PF/NumberTheory/OddPerfectNumberFrameworkAttack.lean         — 3 uses
PF/NumberTheory/BrocardProblemFrameworkAttack.lean           — (referenced, needs grep)
```

## A.2 `def X : Prop := True` (definitional recovery, violates §I.5)

```
PF/NS2DGlobalRegularity.lean:318                                                  1×
PF/AlgebraicGeometry/Cohen2025_HodgeConjecture_NamedAnchors_2026_06_19.lean       6×
PF/AlgebraicGeometry/Hodge_Substrate_NamedAnchors_2026_06_19.lean                 7×
PF/AlgebraicGeometry/CycleClassMapAtCodim2Attempt.lean:502                        1×
```

## A.3 Unit-typed placeholder Props

```
PF/NS_SubstrateBulletproofClosure.lean:  NavierStokesGlobalSmoothness : ∀ (_ : Unit), ∃ (_ : Unit), True
```

## A.4 Archived-but-referenced axioms (needs live-tree verification)

`AxiomAudit.lean` at HEAD tags `YM_pillar_axioms`. Live grep should confirm whether `R_f_meromorphic_at_2`, `yang_mills_measure_exists`, `minlos_theorem` etc. are DECLARED as `axiom` in the live tree, or merely REFERENCED in comments. If declared: §I.2 violation. Deferred to future sweep.

---

# APPENDIX B — Xi(15) DISCHARGE STATUS (for the record)

Verified at commit `4f7b216d`:

- `theorem int_lower_15 : (0.004441 : ℝ) ≤ ∫ x in (1 : ℝ)..5, FT_15 x` — `[propext, Classical.choice, Quot.sound]` ✓
- `theorem Xi_15_pos : 0 < Xi 15` — same axiom budget ✓
- `theorem xi_positive_at_15_certified_direct_r120 : Xi_Positive_At_15 := Xi_15_pos` — same ✓
- Zero `sorry`, zero `native_decide`, zero `Lean.ofReduceBool`.
- Panel-generation script `scripts/gen_r120_panels_t15.py` committed.

Xi(15) arc is **FROZEN** per DIRECTIVE §XI.

---

**End of audit.** Awaiting Pabs's explicit go / no-go on the recommended Rank-1 landing before any implementation. Per DIRECTIVE §XVIII: **do NOT automatically implement**.
