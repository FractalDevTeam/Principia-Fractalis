# Lean 4 ↔ Coq Axiom Parity Report

*Last updated: 2026-04-22 late session, commit `9a0936d`*

## Headline numbers

| System | Files | Axioms / Parameters | Build status |
|---|---|---|---|
| **Lean 4** (`PF_Lean4_Code/PF/*`) | 20 | **9** | `lake build` — 5486 jobs clean |
| **Coq** (`PF_Coq/theories/*`) | 32 | **252** | `make` clean |
| **Lean4Lean** (`PF_L4L/*`) | 9 | 0 | ❌ non-buildable — broken dependency path `PF_canonical/2_LEAN_SOURCE_CODE` (empty dir) |

Change from prior report: Lean 16 → 9 (7 more numerical axioms eliminated via 10-digit √2/√5/φ supporting theorems + classical `log_lt_sub_one_of_pos` for radix_economy_max_at_exp1); Coq 253 → 252 (one latent-unsound axiom deleted).

## Axiom distribution by topic

| Topic / Chapter | Lean axioms | Coq axioms | Gap |
|---|---|---|---|
| IntervalArithmetic (numerical bounds) | 8 | 5 | Lean has extra tight bounds (`lambda_0_*_precise`) |
| TransferOperator (Ch 20, RH) | 2 | 37 | **Huge Coq gap** — Coq axiomatizes many lemmas Lean derives |
| BochnerMinlos | 2 | 5 | Lean eliminated `minlos_sigma_additivity`, `gaussian_is_characteristic`, `nuclearity_essential` tonight |
| CylindricalMeasures | 1 | 6 | Lean eliminated `pos_def_hermitian`, `pos_def_normalized_bounded`, `characteristic_cylindrical_round_trip`, `cylindrical_measure_fourier_is_characteristic` tonight |
| TuringEncoding (Ch 21, P vs NP) | 2 | 13 | Coq gap on encoding-injectivity and complexity lemmas |
| YangMillsMeasure | 0 | 8 | Lean eliminated all 6 tonight; Coq has 8 |
| YM (contracts) | 0 (no file) | 24 | Coq-only — Yang-Mills Millennium contract |
| SpectralEmbedding | 0 | 6 | Lean promoted to structure fields tonight |
| GaussianModel | 0 | 0 | Lean eliminated all tonight |
| SpectralGap | 0 | 8 | Coq-only axioms |
| SpectralBijection | 0 | 1 | Near parity |
| NuclearSpaces | 0 | 1 | Near parity |
| RadixEconomy | 0 | 6 | Coq-only |
| Resonance | — | 6 | Coq-only |
| UniversalFramework | — | 7 | Coq-only |
| ChernWeil | 0 (in PF/) | 1 | Lean has extra-library (orphan) ChernWeil.lean with 3 axioms |
| Hodge | — | 19 | Coq-only (Ch 25) |
| BSD | — | 20 | Coq-only (Ch 24) |
| NavierStokes | — | 23 | Coq-only (Ch 22) |
| ClinicalValidation | — | 21 | Coq-only (Ch 30+) |
| Problems143 | — | 12 | Coq-only |
| ComplexityTheory | — | 4 | Coq-only |
| RH (contract) | — | 5 | Coq-only (Ch 20) |
| PNP (Coq contract) | — | 3 | Coq-only |
| P_NP_Proof (Coq) | — | 7 | Coq-only |
| Zeta | — | 3 | Coq-only |
| FractalOperators | — | 1 | Coq-only |
| P_NP_Complete_Proof | 1 (`operator_collapse_hypothesis`) | 0 | Lean-only |

## What this means

### For parity
1. **Coq axiomatizes ~16× more content than Lean**, much of it covering topics Lean doesn't yet formalize (Hodge, BSD, Navier-Stokes, clinical validation). These aren't Lean shortcomings — they're out of current Lean scope.
2. **Where both have files**, Coq is consistently more axiomatic. Tonight's 25 Lean eliminations have NOT yet been ported to Coq.
3. **Lean4Lean layer is currently broken** — unbuildable due to missing canonical-source directory. Would require separate project work to restore.

### Referee-risk assessment
- The FORMALIZATION, as a referee would encounter it, is **two partially-consistent systems**: a cleaner Lean 4 framework (16 axioms, many proven against honest placeholders with caveats) and a heavily-axiomatized Coq framework (253 axioms covering broader scope).
- The book makes claims (RH, P≠NP, Yang-Mills, Hodge, BSD, Navier-Stokes) that are backed by Coq axioms, not proofs. A rigorous review would note these are AXIOMATIZED, not derived.
- The Yang-Mills placeholder (`yangMillsCovariance := 0`) in Lean is honestly disclosed; corresponding Coq placeholders (if any) should be similarly documented.

### Next actions
1. **Port Lean eliminations to Coq**: specifically, `pos_def_hermitian`, `pos_def_normalized_bounded`, `Q_decreasing_from_4`, the structural promotions (embedding_strictly_monotone, shell_has_natural_frequency) should all be eliminable in Coq via analogous proofs.
2. **Fix Lean4Lean build path** so the meta-verification layer can run.
3. **Coq-only topics** (Hodge, BSD, Navier-Stokes, etc.) need their own axiom elimination pass — each file's axioms are book-critical statements, not scaffolding.
4. **Book sync** (rev2 LaTeX): add a "Formal verification state (rev 2)" note in each relevant chapter indicating which claims are currently axiomatized vs proven.
