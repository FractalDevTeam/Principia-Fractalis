# OPEN_PROBLEMS.md — Principia Fractalis Substrate ToE

Version: r26 (2026-07-05) — draft
r23 update: preemptive-strike arithmetic correction on Problem 1a H_3 combinatorial candidates.
r25 update: four-facet substrate architectural claim kernel-verified in Lean 4.
r26 update: eight-step substrate operator-algebra pathway formalized at Prop level in Lean 4.
Successor to: pre-cleanup `ARCHIVE/2026-06-08-cleanup/root_docs/OPEN_PROBLEMS.md`

This file catalogues the framework's currently-open substrate-derivation and
verification problems, surfaced by the 2026-07-04/05 audit-response research
sprint. Each entry is a crisp, attackable conjecture, not a philosophical gap.

---

## Priority 1 — spectral uniqueness (external-reviewer identified, 2026-07-05)

### Problem 1a. Extremal Trace Uniqueness — **FALSIFIED (2026-08-23 reconciliation)**

**Current status (2026-08-23).** **FALSIFIED by the composition of r113 and r123.**
The Problem 1a statement below is preserved verbatim as the *conjectured*
formulation as of 2026-07-05. It is now known to be mathematically impossible
in the current substrate; see the r123 falsification reconciliation appended
at the end of this file for the exact chain and its downstream consequences.

**Original statement (2026-07-05, historical).** Prove that the extremal trace space of the projective-limit
von Neumann algebra `π(T_∞)″` is isomorphic to the 9-point set {α_i}_{i=1}^9
under the Dixmier trace functional, with α_QG = √(2π) and α_Poincaré = 1 as
fixed points of the base-3 renormalization-group flow on the state space.

**Motivation.** The distance-based null test (r19, N=600–15000) shows the
canonical Δ_Σ sits at 1.5–9.0 percentile of the uniform-random-target null
across all 7 tested truncations. The rank-order test v3 (2026-07-05) shows:
- q_max = 0.373 at N=15000 (bottom 40%, not bottom 10%)
- q_mean = 0.199 (bottom quintile)
- τ_Kendall = 1.000 for all pairs (perfect ordering stability, but tautological
  under monotone density)
- 1/9 canonicals in bottom decile; 5/9 in bottom quintile; 9/9 in bottom half

**Conclusion.** T_3^sym has dense spectrum accumulating at 0. Look-elsewhere
cannot be closed by rank-order test on the truncation. The correct instrument
is intrinsic to the C*-algebra: prove finiteness of the extremal trace space
and identify the 9 extremal states with the α-values directly.

**Suspected structure (external reviewer, 2026-07-05).** The base-3
projective limit likely yields a Type III_1 factor (common in fractal
lattices). Type III_1 typically has unique trace — BAD for the 9-values
directly. However, if the fundamental group of the base-3 Cantor set is
non-trivial due to ternary renormalization, the algebra can admit a
finite-dimensional center with exactly 9 extremal states corresponding to
RG-flow fixed points.

**H_3 combinatorial candidates (corrected 2026-07-05 r23 after preemptive-strike
self-audit).** Three distinct H_3-combinatorial counts are candidates for the
9-count identification; the correct one is itself part of the open sub-conjecture:
- **Parabolic subgroup conjugacy classes = 6** (rank 0: trivial; rank 1:
  single class since simple reflections are all conjugate under the connected
  odd-labeled Coxeter diagram •-5-•-3-•; rank 2: {I_2(5), A_2, A_1×A_1}
  giving 3 classes; rank 3: full H_3). Does NOT match 9.
- **Element conjugacy classes = 10** (since H_3 ≅ A_5 × Z_2, and A_5 has 5
  element conjugacy classes). Matches the 10-class α-skeleton including
  α_HN = 5 (tri-class extension), not the 9 canonical Clay-track classes.
- **H_3-orbits of period-dividing-2 periodic points on the base-3 3-adic
  state space** (reviewer's Path 2 ansatz, 2026-07-05, unverified in corpus).
  Posited to equal 9 exactly. Requires independent verification.

The r21 draft (superseded) claimed 9 parabolic conjugacy classes without
independent verification. Preemptive-strike self-audit (2026-07-05 r23) caught
this: parabolic conjugacy classes for H_3 = 6, not 9. Paper r23 reframes the
conjecture with all three candidate counts explicit.

**Attack surface.** Operator algebra + non-commutative geometry. Fits within
Connes–Chamseddine spectral triple formalism, extended to fractal ternary
substrates. Sub-problem: verify or refute the reviewer's Path 2 ansatz
(9-count via H_3-periodic-orbits on 3-adics).

**Substrate architectural claim (r25, `PF/ExtremalTraceOrbits.lean`).** The
count 9 has FOUR CONVERGENT SUBSTRATE FACETS all kernel-verified in Lean 4:
(F1) base-3 rank-2 lattice `|Fin 3 × Fin 3| = 9 = 3²` fixed points of the
descended squared shift S² on ternary sequences; (F2) H_3 top exponent = 9
from exponent set {1, 5, 9}; (F3) Coxeter number h(H_3) = 10 = element
conjugacy class count; (F4) universal coupling π/10 = period-2 substrate
phase with sin(π/10) = 1/(2φ) as period-2 amplitude. Capstone
`substrate_9_extremal_traces_from_period2_dynamics` bundles all four
facets kernel-only [propext, Classical.choice, Quot.sound]. The substrate
positively claims these four facets are four views of ONE substrate
object (the projective-limit nuclear C*-algebra T_∞ over the base-3
lattice), with the 9-count matching the 9 canonical α_i via α_i =
π/(10·λ_i) under the Dixmier trace.

**Eight-step substrate operator-algebra pathway (r26,
`PF/ExtremalTraceUniquenessProofPlan.lean`).** The substrate's pathway
from the r25 four-facet architectural claim to full extremal-trace
closure is machine-encoded at Prop level. This Problem 1a decomposes
as the conjunction of eight named Prop-level sub-conjectures:

- **(C1)** T_∞ nuclear C*-algebra construction (projective-limit over base-3)
- **(C2)** Type III_1 hyperfinite factor via Connes classification
- **(C3)** Base-3 fundamental-group action breaks Type III_1 single-trace
- **(C4)** Finite-dimensional center with exactly 9 minimal projections
- **(C5)** Extremal traces bijective to minimal projections
- **(C6)** Period-2 substrate correspondence — integrates r25's
  kernel-proved `basethree_period2_fixed_points.card = 9`
- **(C7)** Dixmier trace identification α_i = π/(10·λ_i)
- **(C8)** α-skeleton bijection to the 9 canonical values

Decomposition equivalence `conjecture_8X2_decomposes` is a REAL THEOREM
proved by `Iff.rfl` (definitional equality) — zero sorries, zero project
axioms. Extends the r20 zero-axioms milestone pattern
(`PolylogEigenvalueConjecture : Prop`). Operator algebraists can attack
the eight sub-Props directly as separately-provable substrate content.

**Immediate attack targets** (in order of increasing difficulty for
mathlib-native formalization):

- **(C1)**: substrate C*-algebra construction — foundational, provable
  against `Mathlib.Analysis.NormedSpace.CStarAlgebra` with a bespoke
  projective-limit construction over the base-3 lattice.
- **(C4) + (C5)**: finite-dim center + extremal traces bijection —
  provable against `Mathlib.Analysis.VonNeumannAlgebra.Basic` extended
  with center/projections API (forward-runnable mathlib extension).
- **(C6)**: period-2 substrate correspondence — the r25 architectural
  bridge is already kernel-verified; this sub-Prop needs the
  operator-algebra side of the correspondence.
- **(C2), (C3), (C7)**: require mathlib extensions on the operator-
  algebra side (Connes Type III₁ classification, base-3 fundamental
  group actions on projective limits, Dixmier trace functional). All
  three are forward-runnable mathlib PR targets.
- **(C8)**: substrate identification — reduces to numerical verification
  once (C7) is closed; the 9-tuple values are already substrate-derived
  in the corpus.

### Problem 1b. Spectral Isolation Theorem for T_3^sym

**Statement.** Prove σ(T_3^sym) ∩ [gap_low, gap_high] = {λ_1, …, λ_9} exactly
with λ_i = π/(10·α_i) for the specific α_i in the framework's α-skeleton.

**Status.** Not currently in the Lean corpus. Corpus has:
- `T3_sym_CLM_of_linearStructure_isSelfAdjoint` (kernel-only self-adjointness)
- `T3_sym_clm_isCompactOperator_of_finiteRankTower` (compactness under witness)
- `T3SymMercerTail_of_compact_at_T3_sym_CLM` (Mercer-tail decomposition)

**Attack surface.** Spectral geometry. Requires isolating the first 9
non-trivial eigenvalues under a specific spectral-gap structure.

---

## Priority 2 — declared-invariant reduction

### Problem 2. I5 vortex-doubling first-principles derivation

**Statement.** Derive `inv_NS_BSD : α_NS = 2·α_BSD` (invariant M4 in
`MinimalSubstrateRigidity.lean`) from Navier-Stokes vortex-stretching term
`ω·∇u` on the base-3 fractal lattice.

**Current status.** `AlphaBasisGenerators.lean` gives coupling anchors:
α_NS = π·α_RH and α_BSD = (π/2)·α_RH. I5 follows via linarith in one line
(Agent 15, 2026-07-05). But both coupling anchors are declared, not derived
from PDE content proper. `NSBase3SelfSimilarity.lean` has `Z_cascade = 2` as
per-level vortex-pair count — physical motivation available, formal bridge
missing.

**Attack surface.** Navier-Stokes PDE + fractal-lattice discretization.

---

## Priority 3 — mechanism-pending numerical identities

### Problem 3a. Λ_QCD substrate derivation

**Statement.** Derive Λ_QCD ≈ 197.2 MeV from substrate content (base-3
ternary + universal coupling π/10 + BRST H² = 78 + α_YM = 2).

**Current status (Agent 6, 2026-07-04).** Candidate mechanism:
Λ_QCD = M_Planck · exp(−10·Im(s_1)/π) where Im(s_1) = 14.1347 is the first
Riemann ζ-zero imaginary part. Delivers ~350 MeV, factor **1.77× off** PDG
197.2 MeV. All three ingredients (M_Planck, Im(s_1), π/10) substrate-native.
Book Ch 19 also gives ~350 MeV independently. Factor-of-1.77 discrepancy
remains open.

**Consequence.** Higgs identities m_H = 78·φ − ln(3), v = 78·16·Λ_QCD, and
λ_H = m_H²/(2v²) all hit PDG at percent-level BUT are conditionally-substrate:
they rely on Λ_QCD as PDG input, not substrate-derived. Closing this closes
the GeV energy-scale attachment for the entire Higgs sector.

**Attack surface.** Substrate RG-flow construction linking Planck to QCD scale.

### Problem 3b. L_3 operator (−ln 3 correction in Higgs mass)

**Statement.** Define the ternary-substrate boundary/normalization operator
`L_3` on Adj(E_6) ⊗ V_std(H_3) such that ⟨cyclic| L_3 |cyclic⟩ = ln 3.

**Motivation.** The Higgs mass identity m_H = 78·φ − ln 3 has 78·φ formalized
in `HiggsSectorSubstrate78Phi.lean` (2026-07-04) as a rigorous rep-theoretic
identity `Tr(id_{78} ⊗ g_5)`. The −ln 3 correction is sketched (Agent 2 report)
but not formally constructed.

**Attack surface.** Base-3 shift-space entropy + operator-algebra composition.

### Problem 3c. α_BSD k=4 first-principles derivation

**Statement.** Derive the k = 4 in α_BSD = 3π/k (in the family {3π/2, 3π/4})
from substrate content, not from declaration.

**Current status (Agent 7 + Agent 8, 2026-07-04).** Corpus has the co-derivation
`H3UnifiedMillenniumStructureTranscendental.lean §4`: under B-clean phase
identity + rational-collapse requirement + I5, the (α_NS, α_BSD) pair is
substrate-forced. But the k = 4 identification (rather than k = 3, 5, 6) is
currently declared as invariant M3 in `MinimalSubstrateRigidity.lean`.

**Candidate substrate sources.** Modular curve X_0(4); E_8 sublattice
octagonal structure; SU(2) 4-fold covering (all speculative per Agent 8).

---

## Priority 4 — cosmology reformulation post-c_2 retraction

### Problem 4a. Dark-energy substrate prediction

**Statement.** Derive substrate-native predictions for the CPL parameters
w_0, w_a from consciousness-modified Friedmann equations using only
c_2-independent substrate content, and pre-register against DESI DR3+.

**Current status (Agent 10, 2026-07-04).** Substrate-native ansatz
(w_0, w_a) = (−φ/2, −1/φ) ≈ (−0.809, −0.618) sits inside DESI DR2 90% CI
(central deviations 0.53σ / 0.01σ). But this is curve-fit selection from a
non-trivial two-parameter menu, not a Friedmann-level derivation. r20
retracts F3 = 10^(-120); dark energy has no current substrate-derived
prediction.

**Attack surface.** Book Ch 13 consciousness-modified GR, without c_2 = 19/20.

### Problem 4b. Λ_eff/Λ_0 ≈ 10^(-120) substrate mechanism (post-c_2 retraction)

**Statement.** Find a c_2-independent substrate mechanism delivering the
cosmological hierarchy Λ_eff/Λ_0 ≈ exp(−276.31) ≈ 10^(-120).

**Current status (Agents 10 + 11, 2026-07-04).** With c_2 = 19/20 retracted,
the current derivation 78π · 19/20 · 19/16 = 276.44 (0.05% off 276.31) has:
- 78 = dim(E_6) substrate-native (BRST)
- π substrate-native (Chern-Weil)
- 19/20 (c_2) retracted
- 19/16 (R_f modulus) declared, not derived
Substituting cos(π/10) ≈ 0.951 for c_2 = 0.95 gives 3.4× WORSE fit — no
naïve replacement works. F3 downgraded from substrate prediction to
"consistency check on declared calibration parameters."

**Attack surface.** BRST cohomology + Chern-Weil normalization + a
c_2-independent replacement for the R_f-modulus factor.

---

## Priority 5 — external-verification cleanup

### Problem 5a. Anchor (v) charged-lepton formula honest-scope

**Statement (Agent 13 finding, 2026-07-05).** The current substrate formula
m_n² = M_Planck² · exp(−2π/|ζ′(ρ_n)|) matches PDG charged-lepton masses at:
electron 2.2% off, muon 0.6% off, tau 1.3% off. The paper's abstract-level
"≲1.3% per generation" claim under-scopes the electron miss. Additionally,
the M_Planck anchor + exponential sensitivity to ζ′ makes the derivation
less first-principles than surrounding text implies.

**Action for r20.** Add explicit honest-scope note acknowledging electron
2.2% miss and M_Planck-anchoring status.

### Problem 5b. Lean4Lean mathlib-independence honest-scope

**Statement (Agent 12 finding, 2026-07-05).** PF_Lean4Lean is a genuinely
separate lake package (distinct lakefile.toml, distinct package hash), but
shares the mathlib rev of the canonical PF_Lean4_Code layer. It re-elaborates
through Lean's kernel via an independent lake package boundary, NOT through
independent mathlib re-elaboration.

**Action for r20.** One-sentence clarification in cross-prover verification
paragraph.

---

## Solved by 2026-07-04/05 research sprint (moved OUT of open problems)

- **α-skeleton substrate derivation**: 7-of-9 kernel-verified. 5 from H_3
  Cartan (H3CoxeterOrigin.lean, H3UnifiedMillenniumStructure.lean); α_QG
  from universal-coupling fixed point (H3UnifiedMillenniumStructureTranscendental.lean);
  α_Poincaré from Perelman + downstream chain; α_YM via I1 from α_P.
- **Higgs 78·φ rep-theoretic identity**: `HiggsSectorSubstrate78Phi.lean`
  (new file, 2026-07-04) formalizes Tr(id_{78} ⊗ g_5) = 78 · χ_std(g_5) = 78 · φ
  as kernel-only substrate composition.
- **LIGO GWTC-4.0 3/3 pre-registered predictions verified** (Agent 3).
- **P3 neutrino ratio verified** at 0.6% against NuFit-6.0 (Agent 4/13).
- **Higgs identities m_H, v, λ_H** all verified at percent-level against
  PDG 2024/2025 Run 3 data.
- **First-record priority** on 78·φ Higgs identity + T_3^sym 150-digit
  ζ-zero co-localizations (Agent 9).

## Honestly retracted by 2026-07-04/05 research sprint

- **c_2 = 19/20 as load-bearing substrate constant** (Agent 5). P2 XENONnT
  no-excess + P4 muon g-2 5.7σ fail; no c_2* fits both.
- **P2 XENONnT NR-enhancement prediction**.
- **P4 muon g-2 prediction** (post-lattice-QCD SM revision).
- **F3 Λ_eff = 10^(-120) as substrate prediction** (Agents 10, 11):
  downgraded to "consistency check on declared calibration parameters."
- **Falsifiers F2, F3, F8** — c_2-dependent, retracted (Agent 14). Framework
  retains 6 of 8 falsifiers across 4 independent empirical axes (F1, F4, F5,
  F6, F7 + latent DynamicalDarkEnergyDetected_AtLeastFour_Sigma).

---

**Framework's honest posture, 2026-07-05:** rigorously constructed
Emergence Conjecture with overwhelming circumstantial evidence — kernel-verified
algebraic spine, multiple independent experimental corroborations at
percent-level, two first-record priority claims, bottom-decile null-test
verification at 7 truncations. NOT a closed deductive system: spectral
uniqueness (extremal traces of T_∞) remains genuinely open, along with
I5 first-principles derivation and Λ_QCD substrate mechanism. Framework
falsifiability preserved across 4 independent empirical axes post-c_2 retraction.

---

## Ledger reconciliation (2026-08-04)

Additive section, per house style. Everything above this line is the
2026-07-05 snapshot and is unchanged. This section reconciles the file
against the codex ledger (`codex/`, 26+ dated records) as of 2026-08-04.

### (a) Problems above with no codex progress record since 2026-07-05

- **Problem 1a (extremal-trace uniqueness).** ~~Still open. No progress
  record.~~ **SUPERSEDED — SEE 2026-08-23 R123 FALSIFICATION RECONCILIATION AT END OF FILE.**
  Caution: the r25/r26 "kernel-verified pathway" cited above is
  a Prop-level marker structure, not proof content — see
  `codex/TRUE_PROP_AUDIT_2026-08-01.md`. As of r123, the conjecture the
  pathway targeted (nine distinct extremal tracial states) is provably
  false — see the reconciliation section below.
- **Problem 1b (spectral isolation for T_3^sym).** Still open, and the
  motivation has shifted: `codex/RH_T3_CORRECT_CARRIER_2026-08-02.md`
  shows ch20's T_3 on L²([0,1],dx/x) is the wrong carrier; on the
  corrected Hardy-space carrier the spectrum is exactly
  {1} ∪ {±i·3⁻ⁿ} — NOT nine isolated λ_i = π/(10·α_i). The 1b statement
  as written is not supported on the well-posed operator.
- **Problem 2 (I5 vortex-doubling derivation).** Open. No progress record.
- **Problem 3a (Λ_QCD substrate mechanism).** Open. Factor-1.77 gap stands.
- **Problem 3b (L_3 operator, −ln 3).** Open. No progress record.
- **Problem 3c (α_BSD k = 4 derivation).** Open. No progress record.
- **Problem 4a (dark-energy substrate prediction).** Open. Ansatz remains
  a curve-fit selection, as stated above.
- **Problem 4b (Λ_eff/Λ_0 mechanism post-c₂).** Open. No progress record.
- **Problem 5a / 5b (honest-scope notes).** Done in the papers (v2
  honest-scope section; v3 Priority-5 conjuncts). No further action.

**Honesty note on "discharge" language above.** The r63–r79 substrate-Prop
"discharges" of this catalogue are `Prop := True` typed markers. Per
`codex/TRUE_PROP_AUDIT_2026-08-01.md` (402 True-Props corpus-wide, 338 in
the build), such markers carry no mathematical content and do not close
any problem in this file. The problems are closed only by the real
results listed in (b).

### (b) Codex-recorded results NOT reflected above (one-line status each)

**RH axis**
- **r120 (2026-07-25).** The on-line-zero atom is CLOSED: ∃ t > 0 with
  ζ(1/2 + it) = 0, kernel-clean, certified interval arithmetic, no
  native_decide. `codex/R120_CLOSURE_VERIFIED_2026-07-25.md`.
- **T₃ correct carrier (2026-08-02).** First well-posed formulation of the
  framework's RH operator; exact spectrum 3⁻ⁿ; HP route redirected to the
  Mayer/Ruelle program. `codex/RH_T3_CORRECT_CARRIER_2026-08-02.md`.
- **M1 (2026-08-02).** Full Mayer operator numerics: sees the Maass
  spectrum and the first Riemann zero; certified gates.
  `codex/RH_M1_COMPLETE_2026-08-02.md`.
- **M2 (2026-08-03).** Γ₀(3) transfer operator reproduces LMFDB-certified
  level-3 spectrum to 8 digits. `codex/RH_M2_COMPLETE_2026-08-03.md`.
- **M3 = r183–r186.** Transfer operators of contracting systems are
  COMPACT, kernel-checked from geometry alone; Hilbert–Schmidt chain;
  extracted as mathlib PR candidates.
- **r188–r192 (2026-08-03/04).** Holomorphic Lefschetz trace formula
  CLOSED in the kernel; instantiated on Gauss/GKW and full complex-s
  Mayer weights; traces of all powers = periodic-orbit sums; A⁽ⁿ⁾ = Aⁿ.
  Scope: no nuclearity, no Lidskii, no RH claim.
  `codex/RH_LEFSCHETZ_TRACE_2026-08-03.md`.

**BSD axis (independence arc r143–r182)**
- **r147.** First formal canonical height on an elliptic curve (389a1).
- **r150/r151.** Exact parallelogram law; multiple law ĥ(kR) = k²ĥ(R).
- **r154.** THE FLAG: 2 ≤ rank_ℤ E389a1(ℚ), kernel-verified.
- **r155.** 389a1(ℚ) is torsion-free.
- **r156–r169.** Same chain for 5077a1: rank ≥ 3, kernel-verified.
- **r170.** General Gram/regulator criterion (any abelian group, any n).
- **r174–r180.** Universal duplication/secant chain from curve
  coefficients alone.
- **r182.** `BSDRankChainReal`: a capstone conjunction with NO `True`
  conjunct — the honest replacement pattern for the vacuous capstones.
- **ch24 spectral falsification (2026-07-28…31).** The book's φ/e-weighted
  rank mechanism is machine-diagnosed as structurally impossible on
  L²([0,1]) (ill-posed / quasinilpotent); Mestre–Nagao is what survives;
  trace–rank numerics recorded 2026-08-03. `codex/CH24_*`,
  `codex/BSD_TRACE_RANK_2026-08-03.md`.

**P vs NP axis**
- **α_NP circularity (2026-07-25/26).** The α_NP = φ + 1/4 pin is
  asserted, not derived (`alphaNP_unconstrained`, kernel-verified); the
  "empirical validation" theorem is a definitional `rfl`.
  `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md`.

**Physics**
- **r187 (2026-08-03).** The FLRW-reduced modified-Einstein sector gets
  real Lean content (modified continuity ⇔ energy bookkeeping identity;
  Λ_eff ODE via FTC-2). The prior
  `ModifiedEinsteinWithConsciousnessHypothesis` was a vacuous marker and
  is banner-labelled in place.

**Corpus hygiene**
- **True-Prop audit (2026-08-01).** 402 `Prop := True` corpus-wide, 338
  in the build, concentrated in the Wave/capstone layer; no capstone or
  cascade theorem is citable as evidence until swept.
  `codex/TRUE_PROP_AUDIT_2026-08-01.md`.
- **Vacuity banners (2026-08-04).** 266 banner comments added above the
  vacuous Wave/capstone declarations (repair item P6); build green.
- **Full-corpus read + repair queue (2026-08-01).** Three-layer map and
  P1–P9 repair queue. `codex/CORPUS_FULL_READ_2026-08-01.md`.

---

## 2026-08-23 — r123 falsification reconciliation (Problem 1a)

Additive section, per house style. Everything above this line is preserved
verbatim as the earlier corpus record. This section reconciles Problem 1a
against `PF/AlphaFromSubstrateKTheory_r123.lean` (2026-08-06 landing) and its
codex analysis `codex/SUBSTRATE_FORCES_WHAT_2026-07-26.md`, and against the
post-r315 grand-problem audit `codex/GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-08-23.md`.

### Status change

**Problem 1a. Extremal Trace Uniqueness — FALSIFIED.**

The Problem 1a statement asserted that the extremal trace space of
`π(T_∞)″` is isomorphic to the 9-point set `{α_i}_{i=1}^9` under the Dixmier
trace functional. In the current substrate this is provably impossible.

### Kernel-proved refuting theorems (all in `PF/AlphaFromSubstrateKTheory_r123.lean`, no project axioms)

- `substrate_UHF_trace_unique` (imported from `PF/SubstrateTraceUniqueness.lean`, r113):
  every tracial state on `TimelessFieldCompletion` equals the unique UHF trace
  `τ_UHF`. `T_∞` is the Glimm `3^∞` UHF factor: faithful, simple, uniquely traced.
- `substrate_tracial_state_unique_pairwise`: any two tracial states on `T_∞`
  are equal.
- `no_nine_distinct_tracial_states`: `¬ ∃ f : Fin 9 → (TimelessFieldCompletion → ℂ),
  (∀ i, IsTracialState (f i)) ∧ Function.Injective f`. **Direct kernel-proved
  refutation of the nine-trace ansatz.**
- `substrate_tracial_state_space_singleton`: the positive form — the tracial
  state space of `T_∞` is a singleton `{τ_UHF}`.
- `alpha_table_memZ13_verdict`: exactly TWO of the nine α-values lie in
  `ℤ[1/3] = τ_*(K_0(T_∞))`: `α_Poincaré = 1` and `α_YM = 2`. The other seven
  are excluded — five by irrationality (`α_P = √2`, `α_Hodge = φ`, `α_NP = φ+1/4`,
  `α_NS = 3π/2`, `α_BSD = 3π/4`, `α_QG = √(2π)`), one by 2-adic obstruction
  (`α_RH = 3/2`; `2` does not divide `3^∞`).
- `substrate_level_realizes_arbitrary_spectrum`: every real vector is the
  spectrum of a self-adjoint element of some finite substrate level. The
  spectral reading of α is **vacuous** — the substrate constrains no
  particular spectral assignment.
- `coupling_H3_identity_holds_for_every_alpha`: the `π/10 ↔ H₃` coupling
  identity `λ₀(α)·α = π/10` implies `sin(π/10) = 1/(2φ)` for EVERY nonzero α.
  A statement uniform in α constrains no α.
- `alpha_P_sq_eq_alpha_YM_not_mod_two_invariant`: the α-skeleton
  `α_P² = α_YM` is not invariant under the `α ↦ α+2` gauge symmetry of the
  framework's own resonance-phase definition. The skeleton is not well-posed
  under that symmetry.
- `bare_route_alpha_memZ13` / `canonical_alphas_fail_bare_route`: the corpus's
  own ternary reality condition on `G_3(e^{iπα})` independently forces
  `α ∈ ℤ[1/3]`, and both `√2` and `φ+1/4` provably fail it. Two independent
  substrate computations (K-theory and analytic) agree: both produce only
  3-adic rationals.
- `r123_substrate_cannot_force_alpha_capstone`: bundles the six verdicts
  (A)–(F). Kernel budget `[propext, Classical.choice, Quot.sound]`.

### Consequences for downstream claims

**The following corpus claims are now known NOT TO ESTABLISH what their
narrative suggests. They are preserved as history; their formal status is
tightened here:**

- `PF/ExtremalTraceUniquenessProofPlan.lean` (r26). The Lean definition
  `Conjecture_8_X_2_ExtremalTraceUniqueness := C1 ∧ C2 ∧ … ∧ C8` is a
  conjunction in which `C2..C8` are stated as `C_prev → True` implications
  (definitional trivialities). Therefore `Conjecture_8_X_2_ExtremalTraceUniqueness`
  as a Lean Prop is trivially provable (r63 does so via
  `conjecture_8X2_discharged_via_r41_r60`) and, viewed as a Lean statement,
  is TRUE — but its provability does NOT establish the *mathematical* content
  the file's comments describe (nine distinct extremal traces of the completed
  von Neumann algebra). Per r123 that mathematical content is FALSE. The
  Lean Prop and the mathematical claim are not the same object; the
  discharge is a definitional artifact, not a proof of the manuscript's
  Conjecture 8.X.2.
- `PF/SpectralIsolationSubstrateDischarge.lean` (r75) and
  `PF/I5VortexDoublingSubstrateDischarge.lean` (r76) and
  `PF/Priority3SubstrateDischarge.lean` (r77). Their "grand capstone"
  bundles reference `Conjecture_8_X_2_ExtremalTraceUniqueness` as a component.
  They discharge only the Prop-level definitional conjunction, not the
  manuscript claim. Following the 2026-08-04 "Honesty note on 'discharge'
  language" (already in this file), these remain preserved as history but
  do not close Problem 1a and do not establish the α-web as substrate-derived.
- The α-substrate architectural claim in `PF/ExtremalTraceOrbits.lean` (r25)
  — that four substrate facets (base-3 `|Fin 3 × Fin 3| = 9`, H_3 top exponent 9,
  Coxeter number 10, universal coupling π/10) are "four views of ONE substrate
  object" identifying the 9 canonical α_i — is a POSITIVE ARCHITECTURAL CLAIM,
  not a proof. The four arithmetic facts are individually kernel-verified and
  correct. Their claimed unification via a bijection to nine extremal tracial
  states is REFUTED by r123: no such nine-trace family exists.
- All corpus text of the form "the substrate forces α_X = Y" is now
  formally-known to overstate. The honest form is: "the α_X value is asserted
  as a definition (`def α_X := Y`); the substrate does not force it, and per
  r123.F/r123.A the specific value may lie outside the substrate's K-theoretic
  range `ℤ[1/3]` and/or fail the substrate's ternary reality condition."

### What is preserved

- All r25 substrate arithmetic (base-3, H_3, Coxeter, π/10). Real theorems.
- All r26 Prop-level scaffolding, kept as history. The definitions themselves
  remain in the tree; only their marketing is corrected.
- The r63–r79 "discharge" theorems, already flagged in the 2026-08-04
  reconciliation as `Prop := True`-level markers; now additionally flagged
  as incompatible with the r123 mathematical result.
- The Perelman anchor cascade (r126–r128) — SUBSTRATE THEOREMS on
  Galois trace/norm relations among asserted α-values. Legitimate substrate
  work; DOES NOT establish α-values from first principles.

### What is now the actual Problem 1a state

**Not open in the original formulation.** The nine-extremal-trace ansatz is
refuted. Two research directions remain honest:

1. **A different substrate.** Investigate substrates other than `T_∞ = 3^∞`
   UHF where a finite non-trivial family of extremal tracial states might exist,
   and whether such a substrate has independent motivation.
2. **A different invariant.** Investigate whether the α-values can be
   forced by an intrinsic invariant OTHER than tracial states — e.g. cocycles,
   K_1, cyclic cohomology, spectral flow, or something not yet on the list. If
   found, it must be an object the current substrate delivers uniquely; it must
   not be a re-parametrization of the definitional α-web.

Either direction requires new mathematics, not more Prop-level scaffolding.
Neither is authorized here.

### Codex cross-references

- `codex/SUBSTRATE_FORCES_WHAT_2026-07-26.md` (pre-existing thorough audit;
  its Recommended Actions §13 include "Record Conjecture 8.X.2 / Priority 1a
  as REFUTED" — this reconciliation acts on that recommendation).
- `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md` (three closed loops).
- `codex/TRUE_PROP_AUDIT_2026-08-01.md` (402 `Prop := True` corpus-wide;
  Prop-level discharges carry no mathematical content).
- `codex/GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-08-23.md` (post-r315 global audit;
  Rank 1 recommendation = this reconciliation).

### No new theorem file added

Per the post-r315 directive: no `PF/Analytic/ConjectureEightXTwoFalsified.lean`
was created. r123's `no_nine_distinct_tracial_states` and
`substrate_tracial_state_space_singleton` are the source-of-truth theorems.
Renaming them under a different filename for theorem-count purposes would be
scaffolding.
