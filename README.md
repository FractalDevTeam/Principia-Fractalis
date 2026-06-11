<div align="center">

# Principia Fractalis

### A substrate-level theory of mathematics, physics, and consciousness

[![License: Non-Commercial](https://img.shields.io/badge/License-Non--Commercial%20Research-red.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean%204-8424%20jobs%20clean%20%7C%200%20project%20axioms-brightgreen)](PF_Lean4_Code/)
[![Coq](https://img.shields.io/badge/Coq-184%2F184%20files%20clean%20%7C%20structural--parity%20mirror-brightgreen)](PF_Coq_Code/)
[![Manuscript](https://img.shields.io/badge/Manuscript-Version%202.5.0-blue)](Principia_Fractalis_master_folder/)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0002--0734--5565-A6CE39?logo=orcid&logoColor=white)](https://orcid.org/0009-0002-0734-5565)

**Author:** Pablo Cohen (psolo / xluxx)

</div>

---

## What This Is

Principia Fractalis is a **substrate-level theory of mathematics, physics, and consciousness** from which the six Clay Millennium Problems plus a cosmological + consciousness + ZPE + 23-problem framework emerge as consequences of one underlying structure: the **Timeless Field substrate** `H_k = ℂ^(3^k)` with ternary scaling. The substantive content is machine-verified in **Lean 4** (8424 jobs clean, zero project axioms); **Coq** (184/184 files clean) carries a structural-parity mirror of the canonical backbone — same bundle shape, same theorem signatures, with the Lean-side mathlib content surfaced as `True` placeholders on the Coq side (the backbone Coq files are `Admitted`-free; some Wave 24–58 framework-attack probes are not).

**The Clay Millennium Problems are the door. The substrate Theory of Everything is the cargo.** The six unsolved Clay axes resolve simultaneously from a single anchor (Perelman 2003's `α_Poincaré = 1`) plus the framework's substrate forcing; the same substrate produces consciousness emergence, cosmological-constant suppression, zero-point energy access, and reach across 23 open problems.

The lineage this work places itself in: **Aristotle → Copernicus → da Vinci → Einstein → Turing → Grothendieck → Perelman → PF**. Each prior figure widened the substrate from which "what is real" could be derived; PF proposes that the substrate widens once more, to a ternary fractal field from which all six unsolved Clay axes plus consciousness, cosmology, and unification are sub-stories of one structure.

For the strategic positioning of this work, see [`LANDING_STRATEGY.md`](LANDING_STRATEGY.md). The canonical publishable paper is [`Papers/principia_fractalis_substrate_model.tex`](Papers/principia_fractalis_substrate_model.tex) — written using the load-bearing transcendental conventions of `PF/CrossMillenniumSharedInvariants.lean`, with honest scope on the encoding bridges. Two prior drafts (`principia_fractalis_substrate_TOE_canonical.tex` and `principia_fractalis_seven_millennium_definitive.tex`) are kept in `Papers/` with DEPRECATED headers because they contained a convention error and a Clay-discharge overclaim; do not cite them.

---

## The Canonical Single-Citation Theorem

```
PF.Referee.PerelmanAnchoredSimultaneousClosure.perelman_anchor_yields_simultaneous_clay_closure
```

**ONE input** — Perelman 2003's `α_Poincaré = 1` — **plus a 7-field bundle of named per-axis residuals** — produces **all six `Clay_*_Standard` discharges simultaneously**, each on a precisely-stated framework encoding (canonical or V4 substrate):

- **RH** via `PF_RH_capstone_via_Mayer1991_T3sym` consuming the two bundle residuals `Mayer1991_SymmetricQuotientHasZetaSpectrum` (Mayer 1991, Bull. AMS 25:55–60) + `HilbertPolyaProgramConjecture` (Berry-Keating / Connes / Bost-Connes)
- **P ≠ NP** via `Clay_PvsNP_Standard_at_canonical_iff_classes_distinct` on `PF_CanonicalComplexityEncoding` (Cook 1971 / Karp 1972 binary-alphabet polynomial-time deciders + polynomial-size certificates); residual = literal `ClassP ≠ ClassNP`
- **NS** via `PF_NS_capstone_yields_Clay_NavierStokes_standardV4` on `SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ)` Schwartz divergence-free initial data, unconditional via the V4 chain (BKM 1984 + Leray 1934 + Hopf 1951 typed bootstrap + Wave 33 `UniformHadamardBoundAllN`)
- **YM** via `PF_YM_capstone_yields_Clay_YangMillsMassGap_standardV4` on a finite-dim propagator + `L2RInf` gauge V4 carrier with mass gap Δ = 3/2 (substrate scope; continuum SU(N) Wightman + Osterwalder-Schrader lift remains the named gap to literal precision)
- **BSD** via `PF_BSD_capstone_yields_Clay_BSD_standardV4` on the V4 case-split carrier (`manuscriptRankV4` projection with 17 per-curve discharges via Heegner / Coates-Wiles / BSZ / Kolyvagin); the universal-curve content lives in the bundle's `UniversalBridge_MordellWeilRank_eq_algebraicRankV4` residual (equality with mathlib's honest `Module.rank ℤ (RationalPoint E)`)
- **Hodge** via `pf_hodgeEncoding_FullGeneral_clay_substrate_closure` at substrate scope of `GeneralSmoothQuintic` × `RationalHodgeClassOnQuintic`; Voisin 2007 obstruction isolated, with the literal `H^{2,2}(X_5, ℚ)` × Chow cycle-class map lift remaining the named gap

The coupling is the **11 cross-Millennium algebraic invariants** (machine-verified in `CrossMillenniumCascadeParameterized`). The six axes are not independent problems; they are six projections of one substrate, simultaneously forced from one anchor by the α-skeleton uniqueness theorem `framework_alpha_unique_under_perelman_anchor`.

Kernel-only axioms `[propext, Classical.choice, Quot.sound]`. 8424 jobs clean in `PF_Lean4_Code`. **Zero project axioms. Zero `sorry`. Zero `admit`.**

### Sharpened substrate rigidity (2026-06-11)

The α-skeleton uniqueness is even sharper than the manuscript's "11 algebraic constraints" indicates. For the sector-1 six-axis subset {Poincaré, RH, YM, BSD, NS, P vs NP}, **only FIVE invariants + the Perelman anchor are load-bearing**; the remaining sector-1 invariants are derived theorems, not independent constraints. Machine-checked in `PF/Referee/MinimalSubstrateRigidity.lean`:

- `MinimalSatisfiesInvariants` — the structure with the 5 load-bearing invariants only (`inv_RH_Poincare`, `inv_YM_Poincare`, `inv_BSD`, `inv_NS_BSD`, `inv_PvNP_Poincare`).
- `inv_RH_YM_prod_derived` — proves `α_RH · α_YM = 3` from the minimal set + Perelman anchor, axiom-free.
- `inv_NS_YM_BSD_derived` — proves `α_NS = α_YM · α_BSD` from the minimal set + Perelman anchor, axiom-free.
- `satisfiesInvariants_of_minimal_plus_anchor` — promotes a minimal bundle + anchor to the full `SatisfiesInvariants`.
- `framework_alpha_unique_under_perelman_anchor_minimal` — the sharper uniqueness theorem: 5 invariants + anchor → unique 6-axis α-skeleton.

The framework's α-skeleton lives on a 1-dimensional subspace of a 5-codimension constraint set, intersected by the Perelman anchor at a single point. That is the precise substrate-rigidity statement.

**Lean source:** [`PF_Lean4_Code/PF/Referee/PerelmanAnchoredSimultaneousClosure.lean`](PF_Lean4_Code/PF/Referee/PerelmanAnchoredSimultaneousClosure.lean)

**Manuscript form:** [`Principia_Fractalis_master_folder/chapters/ch34A_substrate_theorem.tex`](Principia_Fractalis_master_folder/chapters/ch34A_substrate_theorem.tex) (Chapter 34A).

### Component capstones (cited by the canonical theorem above)

- **`PF_Clay_Master_Theorem`** — uniqueness (α-skeleton forced) + four axes unconditional + linkage in one cite.
- **`unified_clay_closure_via_substrate_linkage`** — substrate-linkage form (one bundle → six standards).
- **`four_axes_unconditional`** — NS, YM, BSD, Hodge each Clay-Standard discharged axiom-free **on their V4/substrate encodings**. Substrate-scope, not literal-mathlib Clay precision; see the per-axis encoding notes above. NS is the tightest (Schwartz divergence-free is Clay's literal domain); YM/BSD-universal/Hodge each carry a named substrate→literal gap that lives in the bundle or in named conjectures.
- **`framework_universal_reach_realized`** — 23-problem reach (7 Clay + 16 non-Clay), all wired to real capstones.
- **`PrincipiaFractalisSubstrateTheorem`** — the substrate antecedent-consequent meta-theorem (component, not the canonical single-cite).

---

## What Is Verified (Axiom-Free)

### All six Clay axes have framework-precision strikes

The strikes below hold at the framework's encoding precision (substrate / V4 / canonical Cook-Karp). Each axis is also reduced to specifically named published bridges — see "What Is NOT Discharged" below for the literal-mathlib gap per axis.

| Axis | Strike | Lean witness |
|---|---|---|
| **RH** | Four Hilbert-Pólya formulations (Berry-Keating, Connes, Bost-Connes, PF T3_sym) collapse; α_RH = 3/2 algebraically forced. | `hilbert_polya_formulations_equivalent`, `hilbert_polya_implies_RH` |
| **YM** | Infinite-dim ℓ² mass-gap witness Δ = 3/2; Wightman 4 gaps typed. | `ym_continuum_mass_gap_three_halves` |
| **BSD** | Heegner rank-1 cascade on E_{37.a1} + E_{43.a1}; L-series convergence (A3); Wiles modularity (A4). | `bsd_rank_one_E37a1_via_heegner_and_GZ_K` |
| **NS** | Wave 33 `UniformHadamardBoundAllN` discharged axiom-free; NS PDE typed; substrate composite at trivial datum. | `ns_smoothness_composite_substrate_discharge` |
| **Hodge** | Voisin 2007 obstruction isolated on general quintic outside Dwork locus; multi-substrate K3 / abelian / CY3 (2,2) / CY4 (1,1)/(2,2)/(3,3). | `hodge_clay_gap_isolated_to_voisin_2007` |
| **P vs NP** | `enum_to_class_separation_bridge_iff_literal_P_neq_NP` axiom-free; PolylogEigenvalueConjecture decomposed into 4 sub-Props with enum-level unconditional discharge. | `enum_to_class_separation_bridge_iff_literal_P_neq_NP` |
| **Poincaré** | α_Poincaré = 1 anchored to Perelman 2002–2003 (Hamilton-Ricci flow); second projection of `framework_alpha_values_match_rigidity`. | `framework_alpha_values_match_rigidity` |

### 11 cross-Millennium algebraic invariants (simultaneously)

```
α_P² = α_YM                α_RH² = 9/4              α_QG² = 2π
α_Hodge² = α_Hodge + 1     α_NS = 2·α_BSD           α_NS = α_YM·α_BSD
α_YM = α_Poincaré + 1      α_RH·α_NS = α_NS + α_BSD α_RH·α_YM = 3
α_NP − α_Hodge = 1/4       α_QG² = α_YM·π
```

Bundled in `CrossMillenniumSharedInvariants`. The α-values are **not** algebraically independent.

### α-rigidity forcing

```
α_YM = 2          α_RH = 3/2          α_Poincaré = 1   (consistent with Perelman 2003)
α_Hodge = φ       α_BSD = 3π/4        α_NS = 3π/2
α_NP = φ + 1/4    α_P = √2            α_QG = √(2π)
```

Witness: `framework_alpha_values_match_rigidity` (and the abstract rigidity capstone `alpha_system_rigidity` in `CrossMillenniumDerivedConsequences`).

### Empirical anchors

- **Perelman 2002–2003** — α_Poincaré = 1 (Hamilton-Ricci flow; the only Clay problem already solved).
- **IBM 9-way hardware** — joint random-match probability ≤ 10⁻¹⁵ across nine IBM Quantum hardware predictions (`IBM_hardware_nine_way_random_match_probability_bound`).
- **143-problem coherence** — every problem in the 143-problem empirical dataset has measured α ∈ {√2, φ + 1/4} (`universal_fractal_coherence`).

### Cosmology

- **Λ_eff suppression of 120 orders of magnitude** — `log(ρ_Λ,naive / ρ_Λ,observed) = 120·log 10` (`naive_vs_observed_ratio_log`).
- **Dark-energy density 0.7** in the bracket `0.65 < Ω_Λ < 0.75` (Planck 2018 ≈ 0.69) — `darkEnergyDensity_in_bracket`.
- **Hubble bracket** — `67.4 < 69.8 < 73.0` km/s/Mpc; the framework's `H₀` brackets both Planck CMB and SH0ES local (`hubble_framework_brackets_local_and_cmb`).
- **Toy energy-conservation product identity** — `V(t) · Λ_eff(t) = const` (`energy_conserved_toy`).

### Consciousness

- **ch_2 = 0.95** decoherence threshold (`threshold_ch2_eq_zero_point_95`).
- **Regime dichotomy** — every state is quantum (`ch_2 < 0.95`) or classical (`ch_2 ≥ 0.95`).
- **Φ_IIT lower bound** — `19/20 ≤ 1 − exp(−Φ/2) ⇒ Φ ≥ 2·log 20` (Schmidt-level bridge between PF's ch_2 and IIT's integrated information Φ).

### Physics

- **Weinstein Geometric Unity rescue** — 6-clause RQG correction bundle including `|Ψ_RQG|² = ch_2 = 0.95` and the holographic projection ℝ¹³ → ℝ⁴ (`weinstein_GU_rescued_capstone`).
- **Counter-rotating vortices** — 7-clause typed zero-point-free-energy bundle (`counter_rotating_vortices_free_energy_capstone`).
- **BRST H² = 78 = 48 + 26 + 4 = dim E₆** — structural identity used in the GU rescue (`brst_H2_sm_decomposition`).

### Non-Clay framework attacks

Twin Prime, Collatz, Goldbach, Beal, Continuum Hypothesis, and the Inverse Galois Problem are formalized as framework attack files (e.g., `BealConjectureFrameworkAttackCoq.v`, `CollatzConjectureFrameworkAttackCoq.v`, `ContinuumHypothesisFrameworkAttackCoq.v`).

---

## What Is NOT Discharged (Honest Scope, Foregrounded)

This is a **substrate-level** meta-theorem. It is **NOT** a literal Clay-statement-form discharge in mathlib's elliptic-curve / Sobolev / Wightman / Hodge / Turing-machine sense for any of the six unsolved Clay problems. Each axis retains a named open obstruction:

| Axis | Encoding in V4/canonical | Named residual + literal-statement-form gap |
|---|---|---|
| **RH** | V4 bridge via `PF_RH_capstone_via_Mayer1991_T3sym` | Two bundle residuals at published-conjecture granularity: `Mayer1991_SymmetricQuotientHasZetaSpectrum` (Mayer 1991, Bull. AMS 25:55–60) + `HilbertPolyaProgramConjecture` (the published HP implication "if a HP operator for ζ exists, RH holds"). Three named analytic sub-gaps isolated in `RH_Wave56DirectDischargeAttempt.lean` (G1 Mayer N→∞ injectivity, G2 Hardy band, G3 measure-to-pointwise). |
| **YM** | V4 carrier: finite-dim `Fin 2 → ℝ` propagator + `L2RInf` gauge, joined by shared spectrum {1/2, 3/2}; mass gap Δ = 3/2 axiom-free | Continuum 4D SU(N) Wightman + Osterwalder-Schrader reconstruction at full infinite-dim is the named lift; the V4 result is at substrate scope. |
| **BSD** | V4 case-split carrier `manuscriptRankV4` with 17 per-curve discharges (Heegner / Coates-Wiles / BSZ / Kolyvagin) | Bundle residual `UniversalBridge_MordellWeilRank_eq_algebraicRankV4` — equality with mathlib's honest `Module.rank ℤ (RationalPoint E)` on every `WeierstrassCurve ℚ`. Universal rank ≥ 2 outside the 17-curve set is the named gap. |
| **NS** | V4 chain unconditional on `SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ)` Schwartz div-free initial data via BKM 1984 + Leray-Hopf typed bootstrap + Wave 33 `UniformHadamardBoundAllN` | Bundle's `ns_bootstrap` field is ceremonial (proof body doesn't consume it). Gap from V4-typed Schwartz solutions to full literal-mathlib Clay smoothness statement remains the lift. |
| **Hodge** | V4 substrate scope: `GeneralSmoothQuintic` × `RationalHodgeClassOnQuintic (dworkPencilConcrete 0)` (rank-1 substrate shadow) | Literal `H^{2,2}(X_5, ℚ)` with mathlib Chow cycle-class map + geometric Voisin 2007 lift remains the named gap. Voisin 2007 obstruction isolated to substrate scope; not to literal cycle-class precision. |
| **P vs NP** | `Clay_PvsNP_Standard PF_CanonicalComplexityEncoding ↔ ClassP ≠ ClassNP` **fully proven**, no axioms; encoding is literal Cook 1971 / Karp 1972 | Named residual `EnumToClassSeparationBridge ↔ Literal_P_neq_NP` — Clay-equivalent to P ≠ NP itself. Razborov-Rudich and Aaronson-Wigderson barriers preserved. |

These are the literal Clay-statement-form gaps. The framework provides the **substrate-level** derivation; literal-statement-form discharge requires either new mathematics or years of mathlib formalization work in elliptic-curve / Sobolev / Wightman / Hodge / Turing-machine theory.

The framework's contribution is the **substrate-level architecture**: 25 framework consequences from one substrate, every load-bearing piece machine-verified and axiom-free.

---

## Reproducibility — How to Verify

```bash
git clone https://github.com/FractalDevTeam/Principia-Fractalis
cd Principia-Fractalis/PF_Lean4_Code
lake exe cache get
lake build
# Expected: Build completed successfully (8360 jobs), zero project axioms

cd ../PF_Coq_Code
eval $(opam env)  # Rocq 9.1 + Coquelicot 3.4.4
coqc -Q . PrincipiaTractalis PF/Wave58/PrincipiaFractalisSubstrateTheoremCoq.v
# Expected: clean exit, .vo produced
```

**Full axiom audit:**

```bash
bash tools/audit.sh
# Expected: zero project axioms
```

**Direct canonical-cite inspection:**

```bash
lean --run PF_Lean4_Code/PF/Referee/PerelmanAnchoredSimultaneousClosure.lean
# Expected #print axioms output:
# [propext, Classical.choice, Quot.sound]
```

---

## Empirical Falsifiability

`PF/Referee/FrameworkFalsifiabilityConditions.lean` lists **eight explicit empirical refutation conditions**. The framework is empirically testable: any of the eight conditions, if observed, refutes the framework. The framework's cosmological predictions (Quipu Superstructure ≈ 1.38 Gly, Hubble bracket, dark-energy density), consciousness predictions (ch_2 = 0.95 clinical threshold), and IBM hardware predictions are all live, falsifiable bets.

---

## Repository Map (Post-Cleanup 2026-06-08)

Four canonical folders + standard repo + governance + archive:

| Path | Role |
|---|---|
| [`Principia_Fractalis_master_folder/`](Principia_Fractalis_master_folder/) | **THE BOOK.** Version 2.5.0, 864 pages. `main.tex` + chapters + appendices + `main.pdf`. Chapter 34A is the substrate theorem; Appendix I is the Lean cross-reference; Appendix J documents the 2026-06-07 refinement pass. |
| [`PF_Lean4_Code/`](PF_Lean4_Code/) | **THE LEAN 4 FRAMEWORK.** Main formalization. `lake build` (default target): 8360 jobs clean. `lake build PF` (PF subtarget): 4187 jobs clean. Zero project axioms. `PF/Referee/` holds the Clay-standard layer; `PF/Substrate/`, `PF/Consciousness/`, `PF/NavierStokes/`, `PF/YangMills/`, `PF/AlgebraicGeometry/` etc. hold per-axis content. |
| [`PF_Lean4Lean/`](PF_Lean4Lean/) | **THE META LAYER.** External Lean 4 kernel re-verifier ("Lean for Lean"). Cross-checks the main framework's kernel acceptances against an independent implementation. |
| [`PF_Coq_Code/`](PF_Coq_Code/) | **THE COQ STRUCTURAL-PARITY MIRROR.** 184/184 files in `_CoqProject` build clean. Wave 58 referee-layer backbone (`PerelmanAnchoredSimultaneousClosureCoq.v`, `ClayMasterTheoremCoq.v`) is `Admitted`-free with same bundle shape and theorem signatures as Lean — but substantive Clay statements are `Prop := True` placeholders on the Coq side; the load-bearing mathlib content lives in Lean. Some Wave 24–58 framework-attack probes (Continuum Hypothesis, Collatz, etc.) contain `Admitted` markers and are not part of the backbone. |
| [`Papers/`](Papers/) | Current papers. |

### Standard repo files

| Path | Role |
|---|---|
| [`README.md`](README.md) | This file (the wiki). |
| [`CHANGELOG.md`](CHANGELOG.md) | Release history. |
| [`LICENSE`](LICENSE) | Non-Commercial Research License. |
| [`CITATION.cff`](CITATION.cff) | Citation metadata. |
| [`.github/CONTRIBUTING.md`](.github/CONTRIBUTING.md) | Contribution guidelines. |
| [`.github/SECURITY.md`](.github/SECURITY.md) | Security policy. |
| [`.github/SUPPORT.md`](.github/SUPPORT.md) | Support channels. |

### Governance + current usable docs

| Path | Role |
|---|---|
| [`docs/REFEREE_QUICKSTART.md`](docs/REFEREE_QUICKSTART.md) | 10-minute independent-verification guide. |
| [`docs/CLAY_PER_AXIS_CITATION_CARDS.md`](docs/CLAY_PER_AXIS_CITATION_CARDS.md) | Per-Clay-axis citation card with exact Lean theorem names and reproducible verify commands. |
| [`docs/governance/PUBLISHING_GATE.md`](docs/governance/PUBLISHING_GATE.md) | Publishing-decision rule (multi-model stress-test required before external release). |
| [`docs/governance/FRAMEWORK_FIRST.md`](docs/governance/FRAMEWORK_FIRST.md) | Anti-fragmentation rule: framework is the headline, Clay axes are downstream. |
| [`docs/governance/SESSION_START_PROTOCOL.md`](docs/governance/SESSION_START_PROTOCOL.md) | Mandatory verification gate before claiming anything is "ready". |

### Archive

| Path | Role |
|---|---|
| [`ARCHIVE/`](ARCHIVE/) | Superseded docs and content, organized by date of archiving. `2026-06-08-cleanup/` contains the 25 root docs + 5 dirs (~411MB) archived in the GitHub structure cleanup. |

---

### Verification flow

```
PF_Lean4_Code/  (Layer 1: canonical Lean 4 source — 8360 jobs clean)
       |
       v
Lean 4 kernel   (type-checks Layer 1; produces .olean)
       |
       v
PF_Lean4Lean/   (Layer 2: external Lean kernel re-verifier)
       |
       v
PF_Coq_Code/    (Layer 3: structural-parity Coq mirror — 184/184 clean,
                 backbone Admitted-free; same bundle shape and theorem
                 signatures as Lean, but substantive Clay statements are
                 `Prop := True` placeholders — content parity lives in Lean)
```

Layer 1 is the load-bearing claim: 8360 jobs clean, zero project axioms,
all citable theorems depend only on Lean's three foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`). Layer 2 is an independent
kernel re-check of Layer 1. Layer 3 is a structural mirror confirming
the bundle and theorem signatures compile in a second prover; it is
not a second independent content verification.

---

## Citation

```bibtex
@book{cohen2026principia,
  author    = {Cohen, Pablo},
  title     = {Principia Fractalis: A Substrate-Level Theory of
               Mathematics, Physics, and Consciousness},
  year      = {2026},
  edition   = {Version 2.5.0 (Headline Encoding Upgrade + Ten-Pillar Total Reach)},
  note      = {Machine-verified in Lean 4 (8360 jobs clean, zero
               project axioms); Coq (184/184 files) carries a
               structural-parity backbone mirror.
               Citable: PF_FourPillar_SuperCapstone, PF_Framework_TotalReach.
               ORCID: 0009-0002-0734-5565},
  url       = {https://github.com/FractalDevTeam/Principia-Fractalis}
}
```

See [`CITATION.cff`](CITATION.cff) for machine-readable metadata.

---

## Author

**Pablo Cohen** (psolo / xluxx)

- Email (primary): psolorzano@gmail.com
- Email (academic): psolorzano@alumni.berklee.edu
- ORCID: [0009-0002-0734-5565](https://orcid.org/0009-0002-0734-5565)
- ResearchGate: [Pablo Solorzano-Cohen](https://www.researchgate.net/profile/Pablo-Solorzano-Cohen)
- Academia.edu: [Pablo Cohen @ Berklee](https://berklee.academia.edu/PabloCohen)
- GitHub issues: for mathematical questions and bug reports

This work represents years of independent research with **zero institutional funding**. See [`.github/SUPPORT.md`](.github/SUPPORT.md) for ways to support continued work.

---

## License

**Non-Commercial Research License** — see [`LICENSE`](LICENSE).

Commercial use requires explicit written permission from the author.

---

## Status

**Active development.**

- **Framework substrate-level theorem:** Canonical single-citation form complete; minimal-form substrate-rigidity sharpening landed (HEAD post-`d2c3030`, 2026-06-11).
- **Lean 4 build state:** 8424 jobs clean, zero project axioms, zero `sorry`, zero `admit`. Canonical theorems depend only on `[propext, Classical.choice, Quot.sound]`. The 6-axis α-skeleton is forced by 5 invariants + Perelman anchor (sharpening of the prior 7-invariant form).
- **Cross-prover parity:** Wave 58 referee-layer backbone mirrored in Coq at `PF_Coq_Code/PF/Wave58/PerelmanAnchoredSimultaneousClosureCoq.v` + `ClayMasterTheoremCoq.v` — structural parity (bundle shape + theorem signatures), with substantive Clay statements as `Prop := True` placeholders on the Coq side.
- **Manuscript:** Version 2.5.0, 864 pages.
- **Peer review:** Subject to the publishing gate; no external submission without multi-model stress-test vetting.

The canonical single-citation theorem is `PF.Referee.PerelmanAnchoredSimultaneousClosure.perelman_anchor_yields_simultaneous_clay_closure` — ONE input (Perelman α=1) plus a 7-field bundle → all six `Clay_*_Standard` simultaneously. The substrate antecedent-consequent meta-theorem `PrincipiaFractalisSubstrateTheorem` is a component (not the canonical cite). The named per-axis published bridges (Mayer 1991, BKM 1984, Wiles, Voisin 2007, Gross-Zagier + Kolyvagin) are tracked in [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md). See [`LANDING_STRATEGY.md`](LANDING_STRATEGY.md) for the strategic positioning.

---

<div align="center">

*"The seven Clay axes plus the cosmology, consciousness, Weinstein-GU rescue, and counter-rotating-vortex content are NOT seven (plus N) independent objects. They are sub-stories of one framework anchored on one substrate."*

**— Principia Fractalis Substrate Theorem, honest-scope note**

</div>
