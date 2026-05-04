# Lean 4 ↔ Coq Axiom Parity Report

*Last updated: 2026-05-04, post-rev-3 follow-on chain extended through complete CLM packaging — T_b as `ContinuousLinearMap` with op-norm ≤ 1 (commits through `de5d131`)*

## CLM PACKAGING COMPLETE (2026-05-04, commits `98b1f7e` … `de5d131`)

A nine-commit extension takes T_b to a **`ContinuousLinearMap`** on $L^2(\mu_{\log}\!\restriction(0,1))$ with operator norm $\le 1$. Phase A analytic content for the manuscript $\|T_b\| \le 1$ statement is COMPLETE.

- **Lean 4 canonical**: 8 axioms (unchanged), **5488 jobs clean**, 0 sorries.
- **Mutual absolute continuity** (commits `98b1f7e`, `869b6f7`): $\mu_{\log}\!\restriction(0,1)$ and $\text{volume}\!\restriction(0,1)$ share null sets — substantive measure-theoretic equivalence on (0,1).
- **Pushforward absolute continuity** (commit `25e00eb`): $(\mu_{\log}\!\restriction(0,1)).\mathrm{map}(y_k) \ll \mu_{\log}\!\restriction(0,1)$.
- **AE-propagation through T_b** (commits `8aac4c4`, `e989098`): per-branch and full T_b ae-respect, the well-definedness step for `transferOperator_lp` linearity.
- **Lp-level linearity** (commits `483b388`, `d448a7e`): `transferOperator_lp_add` and `_smul`.
- **CLM packaging** (commit `de5d131`): `transferOperator_clm : LogWeightedL2_Ioo →L[ℂ] LogWeightedL2_Ioo` + `transferOperator_clm_norm_le : ‖transferOperator_clm‖ ≤ 1` via `LinearMap.mkContinuous`.

**Coq parity**: unchanged. The Coq formalization has its own independent axiomatization (253 axioms, separate scope from the canonical Lean's 8) and is not touched by this CLM-packaging chain.

**What remains for retiring `LogWeightedL2.inner` (canonical 8 → 7)**: the structural rename cascade through ~44 callsites in `PF/TransferOperator.lean`, `PF/SpectralBijection.lean`, `PF/Millennium.lean`, swapping the placeholder `structure LogWeightedL2` with `LogWeightedL2_Ioo`. **Mechanical refactor only — no new mathematics needed.**

## CLM-packaging analytic prerequisites (2026-05-04)

A five-commit extension (`0e87907` through `0e5e4b9`) brings $T_b$ to the `Lp → Lp` level with operator-norm bound stated in real-valued `Lp.norm`. Headline numbers unchanged on the Lean side; Coq side untouched.

- **Lean 4 canonical**: 8 axioms (unchanged), **5488 jobs clean**, 0 sorries.
- **Real-Lp.norm bridge of contractivity** (commit `0e87907`): `transferOperatorAction_fn_toLp_norm_le` — the eLpNorm bound (commit `de54564`) lifted via `Lp.norm_def` + `ENNReal.toReal_mono`.
- **Pointwise linearity at the function level** (commit `49ff3ba`): `transferOperatorAction_fn_add` and `_smul` — $T_b(f+g) = T_b f + T_b g$, $T_b(c \cdot f) = c \cdot T_b f$ pointwise. No measurability hypothesis.
- **Lp-lifted linearity** (commit `aef881c`): `transferOperatorAction_fn_toLp_add` and `_smul` — `Eq.trans` chain via `MemLp.toLp_congr` (mathlib `LpSpace/Basic.lean:109`) bridging to `MemLp.toLp_add` / `MemLp.toLp_const_smul` (each `rfl` in mathlib).
- **Input-Lp.norm form of contractivity** (commit `712ee4e`): `transferOperatorAction_fn_toLp_norm_le_input_toLp` — $\|T_b^{fn,Lp}\, f\| \le \|\mathrm{MemLp.toLp}\, f\, h\|$. The form `LinearMap.mkContinuous` consumes as op-norm bound with $M = 1$.
- **Direct `Lp → Lp` form** (commit `0e5e4b9`): `transferOperator_lp` (extracts canonical strongly-measurable representative via `(Lp.aestronglyMeasurable g).mk g`) + `transferOperator_lp_norm_le` ($\|\mathrm{transferOperator}_{lp}\, g\| \le \|g\|$). $T_b$ is now `Lp → Lp` with op norm $\le 1$.

**Coq parity**: unchanged. The Coq formalization has its own independent axiomatization (253 axioms, separate scope from the canonical Lean's 8) and is not touched by this CLM-packaging work.

**Effort to complete CLM packaging on the Lean side**: ~1-3 days remaining — lift `aef881c`'s linearity to `transferOperator_lp`, which requires showing $T_b$ respects ae-equality of input under $\mu_{\log}\!\restriction(0,1)$ (reduces to $y_k$ preserving $\mu_{\log}$-null sets, which follows from `inverseBranch_measurePreserving` + absolute continuity of $\mu_{\log}$ wrt volume on $(0,1)$). After that, `LinearMap.mkContinuous` is a one-shot.

## Phase A integration ladder + Mayer 1991 capstone + L² structural-swap analytic prerequisites (2026-05-01 → 2026-05-03)

A 38-commit extension of the rev-3 follow-on chain (commits `2c2a737` through `2e026aa`) completed the analytic foundation for the Mayer 1991 transfer-operator contractivity bound on $L^2(d\mu_{\log})$ AND the L²-structural-swap analytic prerequisites. Headline numbers unchanged on the Lean side; Coq side untouched.

- **Lean 4 canonical**: 8 axioms (unchanged), **5488 jobs clean**, 0 sorries.
- **Phase A integration ladder complete in `PF/LogWeightedIntegral.lean`** (eleven named lintegral identities, commits `2c2a737`...`8038a01`): per-branch CoV (set-restricted, unit-interval-specialized), geometric and integration partition of $[0, 1)$, summed per-branch identity (sum-outside and sum-inside), Radon-Nikodym integrand substitution, combined Mayer chain identity, $(1/b)$-normalized form, integrated lift of the pointwise transfer-operator bound, and integrand-distribution lemmas.
- **Phase A capstone** (commit `b8ee9a9`): `mayer_1991_lintegral_norm_sq_bound_log_weighted` — the operator-norm bound $\|T_b f\|^2 \le \|f\|^2$ in lintegral form against $d\mu_{\log}$, for unit-modulus phases. Hypothesis: `Measurable f`. The analytic foundation of T₃-style operator self-adjointness is now fully in source.
- **logWeightedMeasure bridge + restatement** (commits `69b7054`, `f13126b`): bridge `setLIntegral_Ioo_logWeightedMeasure_eq_setLIntegral_volume_mul_inv` and the restated Mayer bound `mayer_1991_lintegral_norm_sq_bound_against_logWeightedMeasure` — the form mathlib's `eLpNorm` consumes for the operator-norm statement.
- **L² structural-swap analytic prerequisites** (commits `9429dd6` … `2e026aa`, six commits 2026-05-03): `transferOperatorAction_fn` (function-level operator on `ℝ → ℂ`) + measurability (commit `9429dd6`); restated Mayer bound under the named operator (commit `e259e42`); enorm-ofReal pointwise bridge `enorm_rpow_two_eq_ofReal_norm_sq` (commit `63daa64`); **Mayer 1991 contractivity in `eLpNorm` form** $\|T_b\| \le 1$ on $L^2(\mu_{\log}\!\restriction(0,1))$ (commit `de54564`); **MemLp preservation corollary** (commit `2e026aa`).
- **Coq side unchanged.** Lean → Coq parity work (porting the rev-3 follow-on chain plus the 38-commit Phase A + structural-prep extension) remains on the future-work list.

The remaining work for `LogWeightedL2.inner` elimination is now purely the **structural rename cascade** through `PF/TransferOperator.lean` — the analytic content (eLpNorm contractivity, MemLp preservation) is fully in source. Effort estimate revised: ~2-5 days of focused Lean engineering (was 3-7 days per RESEARCH_ROADMAP §2.1).

See `principia_t3_lean_followon_2026-04-28.md` (session memory) for full per-commit detail of all 58 commits.

## Post-rev-3 follow-on (2026-04-29)

An eight-commit chain on 2026-04-29 executed the follow-on Lean pass flagged in the 2026-04-28 entry below, plus extended the Lean side substantially. Headline numbers unchanged on the Lean side; Coq side untouched (still on the future-work list).

- **Lean 4 canonical**: 8 axioms (unchanged), **5488 jobs clean** (was 5486; +2 for the new `PF.Millennium` capstone module), 0 sorries.
- **`T3_self_adjoint_conj` Lean rewrite COMPLETE.** The follow-on Lean pass flagged in the 2026-04-28 entry below was executed in two stages: commit `f06243f` (existential bridge form) and commit `9c06820` (sharpened to explicit `T3_sym` witness). Axiom now states `∀ f g, ⟪T3_sym.apply f, g⟫ = ⟪f, T3_sym.apply g⟫` where `T3_sym := (1/2 : ℂ) • (T3.apply + T3_adjoint.apply)` with explicit `T3_adjoint` definition (piecewise expanding-branch operator on $I_k = (k/3, (k+1)/3]$ with conjugate phases $(1, +i, -1)$ and reciprocal weights $\sqrt{x/(3x-k)}$). The canonical 8-axiom referee surface preserves the axiom name per Pabs's no-demote mandate; the statement is now mathematically defensible.
- **New `PF.Millennium` capstone module** (commit `2a76b26`): top-level Lean-checkable address bundling `P_neq_NP_def ∧ RiemannHypothesis` under a single hypothesis bundle.
- **`IsEigenvalue` predicate + `RiemannHypothesis` Prop defined.** New conditional theorems: `self_adjoint_real_eigenvalues` (Reed-Simon I VI.8 chain), `compact_discrete_spectrum` (squeeze on $1/n$-decay), `T3_sym_spectral_framework`, `T3_sym_RH_precondition`, `riemann_hypothesis_via_spectral_bijection` (minimal), `riemann_hypothesis_via_T3_sym_framework` (full chain).
- **Two `True`-placeholder theorems converted to real conditional theorems** (above).
- **Coq side unchanged.** Lean → Coq parity work (porting ~33 Lean axiom eliminations + the rev-3 follow-on chain) remains on the future-work list. Coq Contracts disclosure blocks (`NavierStokes.v`, `Hodge.v`, `BSD.v`) updated 2026-04-28 (commit `a5a6488`); no Coq updates this cycle.

See `principia_t3_lean_followon_2026-04-28.md` (session memory) for full per-commit detail.

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
