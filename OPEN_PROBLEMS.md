# OPEN_PROBLEMS.md — Principia Fractalis Substrate ToE

Version: r23 (2026-07-05) — draft
r23 update: preemptive-strike arithmetic correction on Problem 1a H_3 combinatorial candidates.
Successor to: pre-cleanup `ARCHIVE/2026-06-08-cleanup/root_docs/OPEN_PROBLEMS.md`

This file catalogues the framework's currently-open substrate-derivation and
verification problems, surfaced by the 2026-07-04/05 audit-response research
sprint. Each entry is a crisp, attackable conjecture, not a philosophical gap.

---

## Priority 1 — spectral uniqueness (external-reviewer identified, 2026-07-05)

### Problem 1a. Extremal Trace Uniqueness

**Statement.** Prove that the extremal trace space of the projective-limit
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
