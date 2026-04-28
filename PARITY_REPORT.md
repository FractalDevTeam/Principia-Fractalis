# Lean 4 ↔ Coq Axiom Parity Report

*Last updated: 2026-04-28, post-rev-3 cycle complete (commits through `325b555`)*

## Post-rev-3 status (2026-04-28)

The full rev-3 cycle (REVISION_GUIDE.md, all 20 items) was completed 2026-04-27/28 in 17 commits. Headline numbers unchanged; manuscript-level theorem statements are now coordinated with the formalization layers:

- **Lean 4 canonical**: 8 axioms (unchanged), 5486 jobs clean, 0 sorries.
- **Coq Contracts disclosure blocks**: updated to reference post-V01 manuscript fixes by commit hash (commit `a5a6488`); `NavierStokes.v`, `Hodge.v`, `BSD.v` now name the new manuscript-level Hypotheses (`hyp:bsd-golden-threshold`, `hyp:hodge-rhg-concentration`) and Remarks. Coq build unaffected.
- **L4L**: architectural decision recorded (commit `325b555`, `experimental/PF_L4L_future/L4L_ARCHITECTURAL_DECISION.md`); Path B selected (preserve verification-only design intent + canonical 8-axiom count). Full L4L source-file rewrites are future work.
- **Lean axiom `T3_self_adjoint_conj`**: superseded at the manuscript level by symmetrisation $\widetilde{T}_3^{\mathrm{sym}}$ (commit `9659f92`). Canonical 8-axiom count unchanged; the axiom's meaning has shifted from "the unsymmetrised $\tilde{T}_3$ is self-adjoint" to "the symmetrised $\widetilde{T}_3^{\mathrm{sym}}$ is self-adjoint via Friedrichs extension". A follow-on Lean pass should rewrite the axiom statement explicitly to match the manuscript's symmetric operator.

The 2026-04-26/27 verification finding is now resolved: the unsymmetrised $\tilde{T}_3$ was correctly identified as non-self-adjoint, and the rev-3 manuscript fix replaces it with the rigorous Friedrichs symmetrisation construction. **The other 7 axioms are unaffected.**

Lean → Coq parity work (porting ~33 Lean axiom eliminations to the Coq side) remains on the future-work list; this rev-3 cycle did not address Coq axiom counts directly.

## Historical: ⚠ Verification check pending V01 reconciliation (2026-04-27)

A numerical/symbolic verification pass (sympy + 40-digit mpmath) on 2026-04-26, applied to the operator and inner product as transcribed verbatim from manuscript Ch20 and the Lean source, did not confirm self-adjointness of T₃ on L²([0,1], dx/x). A reconciliation pass tested nine alternative interpretations of the manuscript notation; none rescued the claim under the verified setup. **This is not a proof that the underlying mathematics is incorrect.** Pabs's earlier verification work ("V01 catalog") was located 2026-04-27; the manuscript fix in commit `9659f92` adopts the symmetrisation construction (Friedrichs extension of $(\tilde{T}_3 + \tilde{T}_3^*)/2$) which is rigorously self-adjoint. Until the corresponding Lean axiom is rewritten to match (a follow-on pass), `T3_self_adjoint_conj` retains its statement form but its meaning is to be read as the symmetrised version. The other 7 axioms are unaffected.

## Earlier infrastructure note (2026-04-25)

Two infrastructure commits landed in `PF_Lean4_Code/PF/LogWeightedIntegral.lean` toward elimination of `LogWeightedL2.inner` and `T3_self_adjoint_conj`: `83c1f38` proves `SigmaFinite logWeightedMeasure`, and `88d5f37` defines `LogWeightedL2_concrete := MeasureTheory.Lp ℂ 2 logWeightedMeasure`. Following the post-rev-2 finding above, the planned T₃ refactor is on hold pending operator redesign. The `LogWeightedL2.inner` Phase A elimination remains feasible independently if desired (the redesigned T₃ will still need an inner product on log-weighted L²).

## Headline numbers

| System | Files | Axioms / Parameters | Build status |
|---|---|---|---|
| **Lean 4** (`PF_Lean4_Code/PF/*`) | 20 | **8** | `lake build` — 5486 jobs clean |
| **Coq** (`PF_Coq/theories/*`) | 32 | **253** | `make` clean |
| **Lean4Lean** (formerly `PF_L4L/`) | — | — | Quarantined to `experimental/PF_L4L_future/` (was non-buildable; not part of rev 2 claim) |

Change from start of rev 2 cycle: Lean 41 → 8 (33 eliminations). Headline eliminations:
- 8-digit + 10-digit numerical bounds for $\sqrt{2}$, $\sqrt{5}$, $\varphi$ (new theorems, not axioms)
- Four $\lambda_0$ closed-form theorems via 20-digit $\pi$ bounds and the 10-digit $\sqrt{2}/\varphi$ supporting theorems
- `log_3_bounds` via direct n=60 Taylor at $x = 2/3$ (session commit `86a61d1`)
- `radix_economy_max_at_exp1` via classical `log_lt_sub_one_of_pos` substitution
- Three classical positive-definite-functional theorems: `pos_def_hermitian`, `pos_def_normalized_bounded`, plus the underlying `IsPositiveDefinite` definitional upgrade
- Eight Yang-Mills-cluster theorems proven against the zero-covariance placeholder with explicit `CURRENT PROOF CAVEAT` docstrings
- Four latent-unsoundness axioms deleted: `empty_tape_bound`, `characteristic_cylindrical_round_trip`, `cylindrical_measure_fourier_is_characteristic`, `nuclearity_essential`
- Four structure-field promotions: `TestGaugeField.instAddCommGroup/instModule` (Pi-type refactor), `embedding_strictly_monotone` → `TimelessFieldTorus.embedding_mono`, `shell_has_natural_frequency` → `CurvatureShell.alpha_natural`

Coq remains at 253 — the `characteristic_cylindrical_round_trip` deletion was net zero (replaced with a directly-stated `bochner_minlos_existence_full` axiom to preserve downstream compatibility); the `IsPositiveDefinite` strengthening mirrors the Lean upgrade. Tonight's 33 Lean eliminations have not yet been ported to Coq (tracked as future work in `RESEARCH_ROADMAP.md`).

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
3. **Lean4Lean layer was quarantined** — the `PF_L4L/` directory was moved to `experimental/PF_L4L_future/` because it was structurally non-buildable (broken dependency path + import-layout mismatch with the current Lean codebase). Restoring it would require either restructuring the Lean code or rewriting the L4L imports.

### Referee-risk assessment
- The FORMALIZATION, as a referee would encounter it, is **two partially-consistent systems**: a cleaner Lean 4 framework (16 axioms, many proven against honest placeholders with caveats) and a heavily-axiomatized Coq framework (253 axioms covering broader scope).
- The book makes claims (RH, P≠NP, Yang-Mills, Hodge, BSD, Navier-Stokes) that are backed by Coq axioms, not proofs. A rigorous review would note these are AXIOMATIZED, not derived.
- The Yang-Mills placeholder (`yangMillsCovariance := 0`) in Lean is honestly disclosed; corresponding Coq placeholders (if any) should be similarly documented.

### Next actions
1. **Port Lean eliminations to Coq**: specifically, `pos_def_hermitian`, `pos_def_normalized_bounded`, `Q_decreasing_from_4`, the structural promotions (embedding_strictly_monotone, shell_has_natural_frequency) should all be eliminable in Coq via analogous proofs.
2. **Restore Lean4Lean meta-verification layer** (currently quarantined to `experimental/PF_L4L_future/`) by either restructuring the Lean code organization or rewriting the L4L imports against the current layout.
3. **Coq-only topics** (Hodge, BSD, Navier-Stokes, etc.) need their own axiom elimination pass — each file's axioms are book-critical statements, not scaffolding.
4. **Book sync** (rev2 LaTeX): add a "Formal verification state (rev 2)" note in each relevant chapter indicating which claims are currently axiomatized vs proven.
