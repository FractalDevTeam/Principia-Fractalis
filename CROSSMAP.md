# CROSSMAP – LaTeX Chapters ↔ Lean Files (Initial Draft)

Canonical roots:

- LaTeX: `1_BOOK_LATEX_SOURCE/chapters/`
- Lean:  `2_LEAN_SOURCE_CODE/`

This is an initial, high‑level mapping by topic. It will be refined
per chapter in `CHAPTER_NN_REPORT.md` files.

## Core Chapters

| Chapter | LaTeX File | Main Lean Files (2_LEAN_SOURCE_CODE) | Notes |
|---------|------------|----------------------------------------|-------|
| 1 | `ch01_numbers.tex` | `Basic.lean`, `IntervalArithmetic.lean` | Numbers, basic real analysis, interval bounds |
| 2 | `ch02_complex.tex` | `IntervalArithmetic.lean`, `RadixEconomy.lean` | Complex plane groundwork (used in later spectral/constant work) |
| 3 | `ch03_resonance.tex` | `FractalResonance` concepts appear in `UniversalFramework.lean` and `TuringEncoding.lean` | Resonance language and qualitative structure |
| 4 | `ch04_timeless_field.tex` | `UniversalFramework.lean` | Timeless field definitions and framework constants |
| 5 | `ch05_peixoto.tex` | (no dedicated Lean file yet) | Dynamical systems background (used conceptually) |
| 6 | `ch06_consciousness.tex` | `ChernWeil.lean`, parts of `UniversalFramework.lean` | Conceptual foundation of ch₂ framework |
| 7 | `ch07_constants.tex` | `RadixEconomy.lean`, `UniversalFramework.lean` | Base‑3 radix economy and π/10 coupling |
| 8 | `ch08_field_equations.tex` | `UniversalFramework.lean` | Field equations underlying the framework |
| 9 | `ch09_spectral_unity.tex` | `SpectralGap.lean`, `UniversalFramework.lean` | Spectral unity ideas, later used in gap/equivalence proofs |
| 10 | `ch10_hydrodynamic.tex` | (no dedicated Lean file in 2_LEAN_SOURCE_CODE) | Navier–Stokes handled in other projects, referenced here |
| 11 | `ch11_geometric_unity.tex` | `ChernWeil.lean`, `UniversalFramework.lean` | Geometric aspects of the framework |
| 12 | `ch12_qft_consciousness.tex` | `UniversalFramework.lean` | QFT‑style field interpretation of ch₂ |
| 13 | `ch13_solutions_dynamics.tex` | `IntervalArithmetic.lean`, `UniversalFramework.lean` | Numerical/solution behaviour |
| 14 | `ch14_symmetries_conservation.tex` | `UniversalFramework.lean` | Symmetry constraints feeding into constants |
| 15 | `ch15_computational_methods.tex` | `TuringEncoding.lean`, `TuringEncoding/Basic.lean`, `TuringEncoding/Complexity.lean` | Turing machines, complexity classes, encodings |
| 16 | `ch16_spectral_foundations.tex` | `SpectralGap.lean`, `TuringEncoding/Operators.lean` | Spectral framework for P vs NP |
| 17 | `ch17_operator_theory.tex` | `Chapter21_Operator_Proof.lean`, `TuringToOperator_PROOFS.lean` | Operator‑theoretic machinery for P ≠ NP |
| 18 | `ch18_spectral_measures.tex` | `RH_Equivalence.lean`, `SpectralEmbedding.lean` | Spectral measures, RH operator construction |
| 19 | `ch19_physical_applications.tex` | `UniversalFramework.lean` | Cross‑domain physical applications |
| 20 | `ch20_riemann_hypothesis.tex` | `RH_Equivalence.lean` | RH spectral/eigenvalue correspondence |
| 21 | `ch21_p_vs_np.tex` | `P_NP_COMPLETE_FINAL.lean`, `P_NP_Proof_COMPLETE.lean`, `P_NP_Equivalence.lean`, `P_NP_EquivalenceLemmas.lean` | P ≠ NP equivalence and spectral gap |
| 22 | `ch21_turing_connection_proof.tex` | `TuringEncoding.lean`, `TuringEncoding/*`, `TuringToOperator_PROOFS.lean` | Full Turing‑to‑operator connection |
| 23 | `ch22_navier_stokes.tex` | (not present in 2_LEAN_SOURCE_CODE) | Navier–Stokes handled in other lean projects |
| 24 | `ch22_vortex_formation_proof.tex` | (not present in 2_LEAN_SOURCE_CODE) | Vortex proofs presently external/numerical |
| 25 | `ch23_rigorous_qft_construction.tex` | `UniversalFramework.lean` | Rigorous QFT framework elements |
| 26 | `ch23_yang_mills.tex` | `YM_Equivalence.lean` | Yang–Mills mass gap and measure construction |
| 27 | `ch24_birch_swinnerton_dyer.tex` | `BSD_Equivalence.lean` | BSD overview and equivalence framing |
| 28 | `ch24_bsd_theoretical_proof.tex` | `BSD_Equivalence.lean` | BSD proof structure and analytic rank arguments |
| 29 | `ch25_hodge_conjecture.tex` | (no dedicated file in 2_LEAN_SOURCE_CODE) | Hodge handled via external Hodge project, referenced here |
| 30 | `ch25_hodge_general_proof.tex` | (no dedicated file in 2_LEAN_SOURCE_CODE) | General Hodge proof beyond current Lean scope |
| 31 | `ch26_cosmological_constant.tex` | `UniversalFramework.lean` | Cosmological constant and π/10 in cosmology |
| 32 | `ch27_dark_energy_expansion.tex` | `UniversalFramework.lean` | Dark energy expansion data/modeling |
| 33 | `ch28_early_universe.tex` | `UniversalFramework.lean` | Early universe dynamics in framework |
| 34 | `ch29_observational_tests.tex` | `UniversalFramework.lean` | Observational constraints on framework constants |
| 35 | `ch30_clinical_consciousness.tex` | `UniversalFramework.lean` | Clinical validation of ch₂ threshold |
| 36 | `ch31_neuroscience_iit.tex` | `UniversalFramework.lean` | Neuroscience/IIT aspects in the framework |
| 37 | `ch32_consciousness_quantification.tex` | `ChernWeil.lean`, `UniversalFramework.lean` | Formal ch₂ quantification and thresholds |
| 38 | `ch33_numerical_methods.tex` | `IntervalArithmetic.lean` | Numerical certification and interval bounds |
| 39 | `ch34_verification.tex` | `check_axioms.lean`, `Main.lean` | Verification harness, axiom checks |
| 40 | `ch35_software.tex` | (outside Lean core: scripts, code/) | Software infrastructure around the proofs |

> This mapping is derived from file names and project documentation and will be
> refined chapter by chapter. When a chapter has no dedicated Lean file listed,
> that means its content is either background (covered by Mathlib) or handled in
> external projects not present in `2_LEAN_SOURCE_CODE`.
