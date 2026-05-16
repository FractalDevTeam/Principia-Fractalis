# Principia Fractalis – Chapter ↔ Lean ↔ PF_L4L Map

This document summarizes how the LaTeX book chapters map to the canonical Lean 4 formalization and the Lean4Lean (L4L) verification layer.

**Path note (post-rev-3, 2026-04-28).** The repository structure has evolved since this document was first written; the path references below for `PF_canonical/...` should be read with the following substitutions:

| Older path label                               | Current canonical path                                                          |
|------------------------------------------------|---------------------------------------------------------------------------------|
| `PF_canonical/1_BOOK_LATEX_SOURCE/chapters/`   | `Principia_Fractalis_master_folder_rev2/chapters/`                              |
| `PF_canonical/2_LEAN_SOURCE_CODE/`             | `PF_Lean4_Code/PF/` (canonical Lean 4 library; **1 axiom**, 0 sorries, 5626 jobs clean)          |
| `PF_L4L/PF_L4L/`                               | `experimental/PF_L4L_future/PF_L4L/` (quarantined; see `L4L_ARCHITECTURAL_DECISION.md` in that directory) |

The empty directory `PF_canonical/` at the repository root is preserved as a path-redirect placeholder pending a full path-rewrite of this document. The chapter ↔ Lean mapping below is still substantively correct; only the path prefixes have moved.

The goal of this document is to show **where to look in code** for the mathematics of each part of the book. For the post-rev-3 audit-document chain, see `AXIOM_AUDIT.md`, `PARITY_REPORT.md`, `RESEARCH_ROADMAP.md`, and `REVISION_GUIDE.md` at the repository root, all current as of 2026-04-28.

---

## Legend

- **ChXX** – Chapter number in the book.
- **LaTeX** – `.tex` files in `1_BOOK_LATEX_SOURCE/chapters`.
- **Canonical Lean** – main Lean modules in `2_LEAN_SOURCE_CODE`.
- **PF_L4L** – contract modules and axiom tags, when present.

---

## Part I–II: Foundations, Resonance, Timeless Field, Consciousness

### [AUX] Ch01–Ch02 – Numbers and Complex Analysis

- **LaTeX**: `ch01_numbers.tex`, `ch02_complex.tex`
- **Canonical Lean**:
  - Background mostly via mathlib; PF does not re-develop elementary theory in detail.
  - Basic helpers appear in:
    - `Basic.lean`
    - `PF/Basic.lean`
- **PF_L4L**: none (background only).

### [CORE] Ch03 – Fractal Resonance

- **LaTeX**: `ch03_resonance.tex`
- **Canonical Lean**:
  - `PF/Resonance.lean`
  - `IntervalArithmetic.lean` (numeric support)
- **PF_L4L**:
  - Indirectly used by all four Millennium contracts via resonance/spectral gap definitions.

### [CORE] Ch04 – Timeless Field

- **LaTeX**: `ch04_timeless_field.tex`
- **Canonical Lean**:
  - `UniversalFramework.lean`
  - `PF/Basic.lean`
- **PF_L4L**:
  - Tags: `UniversalFramework_consciousness`, shared by all pillar contracts.

### [AUX] Ch05 – Peixoto (Foundations of Dynamical Systems)

- **LaTeX**: `ch05_peixoto.tex`
- **Canonical Lean**:
  - Concepts reflected indirectly in `PF/Resonance.lean` (fractal dynamics view).
  - No dedicated `Peixoto.lean` yet.
- **PF_L4L**: none.

### [CORE] Ch06, Ch30–Ch32 – Consciousness Core and Clinical/Neuro/IIT

- **LaTeX**:
  - `ch06_consciousness.tex`
  - `ch30_clinical_consciousness.tex`
  - `ch31_neuroscience_iit.tex`
  - `ch32_consciousness_quantification.tex`
- **Canonical Lean**:
  - `PF/ConsciousnessCore.lean` (ch₂–α relations, thresholds)
  - `ChernWeil.lean` (Chern–Weil/sheaf consciousness model)
  - `UniversalFramework.lean` (clinical and cosmological axioms)
- **PF_L4L**:
  - All contracts depend on these via `PFAxiomTag.UniversalFramework_consciousness`.

### [CORE] Ch07 – Constants

- **LaTeX**: `ch07_constants.tex`
- **Canonical Lean**:
  - `IntervalArithmetic.lean` (φ, √2, spectral constants, λ₀(P), λ₀(NP), W/Z masses, etc.)
- **PF_L4L**:
  - Numeric certificates used by P vs NP and RH contracts.

### [CORE] Ch08 – Field Equations; Ch19 – Physical Applications

- **LaTeX**: `ch08_field_equations.tex`, `ch19_physical_applications.tex`
- **Canonical Lean**:
  - `UniversalFramework.lean`
  - `ChernWeil.lean`
  - YM/NS toy models for concrete examples.
- **PF_L4L**:
  - Indirectly via pillar contracts (YM, NS, cosmology).

---

## Part III–IV: Spectral Unity, Hydrodynamics, Geometry, QFT

### [CORE] Ch09, Ch16 – Spectral Unity and Spectral Foundations

- **LaTeX**: `ch09_spectral_unity.tex`, `ch16_spectral_foundations.tex`
- **Canonical Lean**:
  - `PF/Resonance.lean`
  - `PF/SpectralGap.lean`
  - `PF/SpectralEmbedding.lean`
  - `IntervalArithmetic.lean`
- **PF_L4L**:
  - Used implicitly by P vs NP, RH, YM, BSD contracts.

### [PROBE] Ch10, Ch22 – Hydrodynamics and Navier–Stokes

- **LaTeX**: `ch10_hydrodynamic.tex`, `ch22_navier_stokes.tex`, `ch22_vortex_formation_proof.tex`
- **Canonical Lean**:
  - `NavierStokesConsciousness.lean`
  - `NavierStokesToyModel.lean`
- **PF_L4L**:
  - No dedicated NS contract yet; NS axioms are tagged under `UniversalFramework`.

### [CORE] Ch11–Ch14 – Geometric Unity, QFT Consciousness, Solutions, Symmetries

- **LaTeX**: `ch11_geometric_unity.tex`, `ch12_qft_consciousness.tex`, `ch13_solutions_dynamics.tex`, `ch14_symmetries_conservation.tex`
- **Canonical Lean**:
  - `ChernWeil.lean`
  - `PF/ConsciousnessCore.lean`
  - YM and NS toy models.
- **PF_L4L**:
  - Indirectly via YM and global consciousness tags.

### [AUX] Ch15, Ch33, Ch35 – Computational and Numerical Methods, Software

- **LaTeX**: `ch15_computational_methods.tex`, `ch33_numerical_methods.tex`, `ch35_software.tex`
- **Canonical Lean**:
  - `PF/TuringEncoding.lean`
  - `PF/SpectralGap.lean`
  - `IntervalArithmetic.lean`
- **PF_L4L**:
  - P vs NP contract (`Ch21/PNP.lean`) depends on these via encoding and spectral gap.

### [CORE] Ch17, Ch18 – Operator Theory and Spectral Measures

- **LaTeX**: `ch17_operator_theory.tex`, `ch18_spectral_measures.tex`
- **Canonical Lean**:
  - `PF/SpectralEmbedding.lean`
  - `PF/RH_Equivalence.lean`
  - `NavierStokesConsciousness.lean` (for measure aspects).
- **PF_L4L**:
  - RH, YM, BSD contracts depend on these operator-theoretic frameworks.

---

## Part V: Millennium Problems

### [PROBE] Ch20 – Riemann Hypothesis

- **LaTeX**: `ch20_riemann_hypothesis.tex`
- **Canonical Lean**:
  - `PF/RH_Equivalence.lean`
  - `PF/SpectralEmbedding.lean`
- **PF_L4L**:
  - `PF_L4L/Ch20/RH.lean`
  - Tags: `PFAxiomTag.RH_operator_axioms`, `PFAxiomTag.UniversalFramework_consciousness`.

### [PROBE] Ch21 – P vs NP and Turing Connection

- **LaTeX**: `ch21_p_vs_np.tex`, `ch21_turing_connection_proof.tex`
- **Canonical Lean**:
  - `PF/P_NP_Equivalence.lean`
  - `PF/P_NP_EquivalenceLemmas.lean`
  - `PF/TuringEncoding.lean`
  - `PF/SpectralGap.lean`
  - `Chapter21_Operator_Proof.lean`
- **PF_L4L**:
  - `PF_L4L/Ch21/PNP.lean`
  - Tags: `P_vs_NP_prime_encoding`, `P_vs_NP_resonance_spectrum`, `P_vs_NP_numeric_certificates`, `UniversalFramework_consciousness`.

### [PROBE] Ch23 – Rigorous QFT and Yang–Mills

- **LaTeX**: `ch23_rigorous_qft_construction.tex`, `ch23_yang_mills.tex`
- **Canonical Lean**:
  - `YM_Equivalence.lean`
  - `NavierStokesConsciousness.lean` (shared QFT ideas)
  - `ChernWeil.lean` (gauge/consciousness geometry)
- **PF_L4L**:
  - `PF_L4L/Ch23/YM.lean`
  - Tags: `YM_pillar_axioms`, `UniversalFramework_consciousness`.

### [PROBE] Ch24 – Birch–Swinnerton–Dyer

- **LaTeX**: `ch24_birch_swinnerton_dyer.tex`, `ch24_bsd_theoretical_proof.tex`
- **Canonical Lean**:
  - `PF/BSD_Equivalence.lean`
  - `BSDToyModel.lean`
- **PF_L4L**:
  - `PF_L4L/Ch24/BSD.lean`
  - Tags: `BSD_pillar_axioms`, `UniversalFramework_consciousness`.

### [PROBE] Ch25 – Hodge Conjecture

- **LaTeX**: `ch25_hodge_conjecture.tex`, `ch25_hodge_general_proof.tex`
- **Canonical Lean**:
  - `HodgeToyModel.lean`
  - `HodgeToyMatrix.lean`
- **PF_L4L**:
  - No dedicated Hodge contract yet; Hodge axioms appear via toy models and consciousness tags.

---

## Part VI–VII: Cosmology, Early Universe, Observational Tests

### [PROBE] Ch26–Ch29 – Cosmological Constant, Dark Energy, Early Universe, Observational Tests

- **LaTeX**:
  - `ch26_cosmological_constant.tex`
  - `ch27_dark_energy_expansion.tex`
  - `ch28_early_universe.tex`
  - `ch29_observational_tests.tex`
- **Canonical Lean**:
  - `UniversalFramework.lean`
  - `PF/ConsciousnessCore.lean`
  - `ChernWeil.lean`
  - `IntervalArithmetic.lean` (numeric inputs)
- **PF_L4L**:
  - Cosmology enters all pillar contracts via Timeless Field and consciousness thresholds.

---

## Part VIII–IX: Consciousness, Neuroscience, Verification, Software

### [CORE] Ch30–Ch32 – Clinical, Neuroscience, IIT, Quantification

- **LaTeX**: `ch30_clinical_consciousness.tex`, `ch31_neuroscience_iit.tex`, `ch32_consciousness_quantification.tex`
- **Canonical Lean**:
  - `PF/ConsciousnessCore.lean`
  - `ChernWeil.lean`
  - `UniversalFramework.lean`
- **PF_L4L**:
  - All pillar contracts depend on these via consciousness tags.

### [AUX] Ch33–Ch35 – Numerical Methods, Verification, Software

- **LaTeX**: `ch33_numerical_methods.tex`, `ch34_verification.tex`, `ch35_software.tex`
- **Canonical Lean**:
  - `IntervalArithmetic.lean`
  - `PF/TuringEncoding.lean`
  - `PF/SpectralGap.lean`
  - Meta-level verification rationale is reflected in PF_L4L contracts and `Core/AxiomAudit.lean`.
- **PF_L4L**:
  - Entire PF_L4L layer (contracts + AxiomAudit) realizes the verification story described in these chapters.

---

## How to use this map

- **From book to Lean**: Start from a chapter, locate the LaTeX file, then use the entries above to find the corresponding canonical Lean files and PF_L4L contracts.
- **From Lean to book**: Given a Lean file (e.g. `YM_Equivalence.lean`), locate the LaTeX chapter(s) listed here to find the narrative exposition.
- **For referees**: Use this together with `README.md` and `AXIOM_AUDIT.md` to navigate from:
  - Chapter claims → Lean definitions/theorems/axioms → PF_L4L contracts and axiom tags.

This map is intentionally high-level; finer-grained per-theorem mappings can be added as the formalization expands.