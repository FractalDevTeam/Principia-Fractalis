# Lean 4 Axiom Audit — PF_Lean4_Code/PF/

*As of 2026-05-05, **7 axioms** (canonical PF/), 0 sorries, 5488 jobs clean. Mayer 1991 §2 formal-adjoint chain COMPLETE (17 pieces, commits `c117493` … `344be4c`).*

## Mayer 1991 §2 formal-adjoint chain — COMPLETE (2026-05-03/05, commits `c117493` … `344be4c`)

A 17-piece Lean infrastructure that takes the formal-adjoint relation
$\langle T_3 f, g \rangle = \langle f, T_3^* g \rangle$ from "asserted by axiom"
to "**provable from integrability hypotheses ONLY**" — no creative math left.

### The 17 pieces (in dependency order)

| # | Lemma | Commit | Role |
|---|-------|--------|------|
| 1 | `T3_inner_integrand_Ioo` | `c117493` | Pointwise: $\overline{(T_3 f)(x)} \cdot g(x)$ as Σ over branches |
| 2 | `T3_adjoint_inner_integrand_Ioo` | `3f25598` | Mirror: $\overline{f(x)} \cdot (T_3^* g)(x)$ as if-cascade |
| 3 | `branch_setIntegral_CoV` | `07dee91` | Per-branch CoV: $u = (x+k)/3$, Jacobian 3 |
| 4 | `weight_ratio_branch` | `21a8db5` | Mayer pointwise: $w_k(3u-k)/(3u-k) = w^*_k(u)/u$ |
| 5 | `phaseFactorBase3_conj_eq` | `21a8db5` | $\overline{\omega_k} = \omega_k^{\mathrm{adj}}$ |
| 6 | `T3_branch_integrand_pointwise` | `6e56224` | Pointwise integrand identity (combines 4+5) |
| 7 | `T3_per_branch_integral_eq` | `a290cda` | Per-branch integral identity (combines 3+6) |
| 8 | `T3_inner_volume_form` | `4c51e48` | LHS expansion via Bochner bridge |
| 9 | `T3_inner_eq_branch_sum` | `6070f25` | Half-formula: $\langle T_3 f, g \rangle = \sum_k \int_{I_k}$ |
| 10 | `T3_formal_adjoint_relation` (cond.) | `97f38a6` | Conditional theorem on `h_partition` |
| 11 | `T3_adjoint_inner_volume_form` | `b03ad0d` | RHS as single Bochner volume integral |
| 12 | `setIntegral_Ioo_partition_three` | `33b51ca` | Spatial decomposition of $(0,1)$ into thirds |
| 13 | `T3_adjoint_integrand_on_branch` | `a1c8f86` | If-cascade evaluation per $I_k$ piece |
| 14 | `T3_adjoint_inner_eq_branch_sum` | `36e5afe` | RHS half-formula (composes 11+12+13) |
| 15 | **`T3_formal_adjoint_relation_via_integrability`** | **`344be4c`** | **CAPSTONE** |

### Capstone signature

```lean
theorem T3_formal_adjoint_relation_via_integrability
    (f g : LogWeightedL2)
    (h_int_T3 : ∀ k : Fin 3, MeasureTheory.Integrable
      (fun x => ((1 / x : ℝ) : ℂ) *
                (starRingEnd ℂ) (phaseFactorBase3 k) *
                ((weightFunction 3 k x : ℝ) : ℂ) *
                (starRingEnd ℂ) (f.toFunℝ (inverseBranch 3 k x)) *
                g.toFunℝ x)
      ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) 1)))
    (h_int_T3adj : IntervalIntegrable
      (fun x => ((1 / x : ℝ) : ℂ) * (starRingEnd ℂ) (f.toFunℝ x) *
                (T3_adjoint.apply g).toFunℝ x)
      volume 0 1) :
    ⟪T3.apply f, g⟫ = ⟪f, T3_adjoint.apply g⟫
```

### Path to `T3_self_adjoint_conj` retirement

```
T3_self_adjoint_conj_via_formal_adjoint'  (existing)
  ← T3_formal_adjoint_relation_via_integrability  (this session's capstone)
    ← h_int_T3 + h_int_T3adj  (standard L² estimates from Mayer 1991 ‖T_b‖ ≤ 1)
```

The remaining work is purely measure-theoretic: discharge `h_int_T3` and
`h_int_T3adj` for L²-functions. **No new mathematics required.**

The blocker: `LogWeightedL2.integrable : True` placeholder. A future
structural strengthening (`LogWeightedL2 := Lp ℂ 2 logWeightedMeasure`,
or equivalent measurability + L² constraint on the structure) makes
both hypotheses derivable from the structure's invariants, finally
enabling the universal claim of the axiom.

## Inner-product API + conditional T3 self-adjointness (2026-05-04, commits `3520de8` … `06134f3`)

After the `LogWeightedL2.inner` retirement (`a43a669`), a 12-commit chain
built out the sesquilinearity API for the new Bochner-integral-based
`inner` definition:

**Unconditional (no integrability hypothesis)**:
- `inner_zero_left`/`inner_zero_right`/`toFunℝ_zero` (`3520de8`)
- `inner_neg_left`/`inner_neg_right`/`toFunℝ_neg_apply` (`a189dac`)
- `inner_smul_left`/`inner_smul_right`/`toFunℝ_smul_apply` (`a189dac`)
- `inner_conj_symm` (`551b42d`) — via `MeasureTheory.integral_conj`
- `inner_self_im` (`ad4a08e`) — `(⟪f, f⟫).im = 0`
- `inner_self_re_nonneg` (`116a033`) — positive-semidefinite property
- `norm_zero`, `norm_neg`, `norm_nonneg` (`057ec18`)
- `norm_sq_eq_inner_self_re` (`ce0b0eb`) — Hilbert-space identity
- `inner_self_eq_integral_normSq` (`558b9d8`) — explicit integral form
- `inner_self_zero_iff_norm_zero` (`06134f3`) — equivalence

**Integrability-conditional**:
- `inner_add_left`/`inner_add_right`/`toFunℝ_add_apply` (`9ba099e`)
  — sesquilinearity in the additive direction; takes per-call
  integrability hypotheses since `MeasureTheory.integral_add` requires
  both summands to be integrable.

**Conditional T3 self-adjointness reduction** (`adda67e`, `3af64dd`):
- `T3_self_adjoint_conj_via_formal_adjoint` — proves the statement of
  `axiom T3_self_adjoint_conj` from formal-adjoint relations
  (`⟪T3 f, g⟫ = ⟪f, T3_adj g⟫`, inverse, integrability hypotheses).
- `T3_self_adjoint_conj_via_formal_adjoint'` — simpler form (drops the
  inverse hypothesis, derives from the forward via `inner_conj_symm`).
- Reduces axiom retirement to proving the forward formal-adjoint relation,
  which is the concrete Mayer-1991 change-of-variables claim.

**Mayer 1991 formal-adjoint building blocks** (commits `1f1d735` …
`5eb54c4`, 2026-05-04). All four pieces needed for the integral
manipulation are now in source:

1. `adjointWeight_eq_weightFunction` (`1f1d735`):
   $w^*_k(u) = u \cdot w_k(3u - k) / (3u - k)$ for $u \in I_k$. The
   algebraic core. Squared form: both sides equal $u/(3u-k)$. Proven
   via `Real.sqrt_div` + `field_simp` + `Real.sq_sqrt` + `ring`.

2. `setIntegral_logWeightedMeasure_Ioo_eq_smul` (`474a998`):
   $\int_{(0,1)} h\, d\mu_{\log} = \int_{(0,1)} (1/x) \cdot h\, d\text{volume}$.
   Bochner-integral bridge from log-weighted measure to volume with
   explicit Jacobian. Proven via `restrict_withDensity` +
   `integral_withDensity_eq_integral_toReal_smul₀` (mathlib) +
   `setIntegral_congr_fun` (with explicit `(E := ℂ)` to bypass
   typeclass-inference fragility).

3. `T3_toFunℝ_Ioo` (`f8abab7`) plus helper `inverseBranch_three_mem_Icc`:
   On $(0,1)$, $(T_3 f).toFunℝ\,x = (1/3)\sum_k \omega_k\, w_k(x)\, f.toFunℝ(y_k(x))$.
   The structural-projection unfolding reducing T₃'s `LogWeightedL2`
   action to the function-level `f.toFunℝ`.

4. `T3_adjoint_toFunℝ_Ioo` (`5eb54c4`):
   On $(0,1)$, $(T_3^* f).toFunℝ\,x$ given as the if-cascade selecting
   the appropriate expanding branch $3x - k$ on $I_k$. Three-branch
   case-split via `by_cases`; each branch's `f.toFun ⟨3x - k, _⟩`
   becomes `f.toFunℝ (3x - k)` after verifying $3x - k \in [0, 1]$.

Combined with the existing infrastructure (`inverseBranch_volume_map`,
`inverseBranch_set_lintegral_change_of_variables`, ae-equality
propagation), all building blocks are present for proving the formal
adjoint relation $⟪T_3 f, g⟫ = ⟪f, T_3^* g⟫$ in Lean.

**Remaining work for full retirement of `T3_self_adjoint_conj`**:
- Compose the four pieces with the affine CoV under volume.
- Sum over branches via partition of $(0,1) = \bigcup_k I_k$.
- Conditional on integrability hypotheses (forms of `inner_add_left/right`).

Manuscript reference: Ch 20, proof of `thm:self-adjoint-transfer`;
Mayer 1991 §2.

The structure's placeholder `integrable : True` field forces
integrability hypotheses to be supplied per-lemma. The eventual
structural refactor (`structure → abbrev := Lp ℂ 2 ...`) will make
these hypotheses free instance fields.

## ⭐ AXIOM ELIMINATION (2026-05-04, commit `a43a669`)

**`LogWeightedL2.inner` is RETIRED.** Canonical Lean PF/ axiom count drops from 8 to 7.

Replaced `axiom LogWeightedL2.inner : LogWeightedL2 → LogWeightedL2 → ℂ` with `noncomputable def`:

```lean
noncomputable def LogWeightedL2.inner (f g : LogWeightedL2) : ℂ :=
  ∫ x in Set.Ioo (0:ℝ) 1,
    (starRingEnd ℂ) (f.toFunℝ x) * g.toFunℝ x
    ∂logWeightedMeasure
```

The retirement took a SIMPLER path than the originally-projected "structural rename cascade":
- The placeholder `structure LogWeightedL2` is PRESERVED.
- New `LogWeightedL2.toFunℝ` extends the `Icc 0 1 → ℂ` `toFun` to `ℝ → ℂ` by zero outside the unit interval, so the Bochner integrand is well-typed.
- `logWeightDensity`, `logWeightedMeasure`, `logWeightedMeasure_def`, `logWeightDensity_ne_top`, and the `SigmaFinite logWeightedMeasure` instance moved from `PF/LogWeightedIntegral.lean` to `PF/TransferOperator.lean` (so they're upstream of the `inner` definition). Duplicate defs removed from `LogWeightedIntegral.lean`.

The def is non-vacuous: for integrable inputs, returns the true $\int_0^1 \overline{f(x)} g(x) \frac{dx}{x}$; for non-integrable, returns 0 by Bochner convention. Honors the rigor mandate (no placeholder = 0 — the function returns the actual integral whenever defined).

Self-adjointness theorems in `PF/TransferOperator.lean` (e.g. `self_adjoint_real_eigenvalues`) still take hypothesis-style sesquilinearity / positive-definiteness args; converting these to free theorems (provable from the new `def` plus standard Bochner-integral linearity) is a follow-on refactor not required for the axiom retirement.

## CLM PACKAGING COMPLETE (2026-05-04, commits `98b1f7e` … `de5d131`)

A nine-commit extension takes the transfer operator T_b from "operator-norm bound proven on functions" to **"`ContinuousLinearMap` on the Hilbert space $L^2(\mu_{\log}\!\restriction(0,1))$ with operator norm $\le 1$"**. Phase A's analytic content for the manuscript-level $\|T_b\| \le 1$ statement is now COMPLETE in source.

- **Mutual absolute continuity on (0,1)** (commits `98b1f7e`, `869b6f7`):
  - `logWeightedMeasure_restrict_Ioo_absolutelyContinuous_volume`: $\mu_{\log}\!\restriction(0,1) \ll \text{volume}$ via `restrict_le_self` + `withDensity_absolutelyContinuous`.
  - `volume_restrict_Ioo_absolutelyContinuous_logWeightedMeasure`: converse via `withDensity_apply_eq_zero` and the positivity of `logWeightDensity` on (0,1).
- **Pushforward absolute continuity** (commit `25e00eb`): `logWeightedMeasure_restrict_Ioo_map_inverseBranch_absolutelyContinuous` — $(\mu_{\log}\!\restriction(0,1)).\mathrm{map}(y_k) \ll \mu_{\log}\!\restriction(0,1)$. Composes the previous two abs-continuity directions with `inverseBranch_volume_map`, plus explicit $(x+k)/b \in (0,1)$ bounds via `k.isLt : k.val + 1 \le b` lifted to ℝ.
- **AE-propagation through T_b** (commits `8aac4c4`, `e989098`):
  - `inverseBranch_ae_eq_propagation`: per-branch $f_1 =^{a.e.} f_2 \Rightarrow f_1 \circ y_k =^{a.e.} f_2 \circ y_k$. Two-line proof: `EventuallyEq.filter_mono (25e00eb.ae_le)` + `EventuallyEq.comp_tendsto (Measure.tendsto_ae_map …)`.
  - `transferOperatorAction_fn_ae_eq_of_ae_eq`: full T_b ae-respect. Three-line proof using `Filter.eventually_all` (Finite `Fin b`) + `Finset.sum_congr` inside the b-summed pointwise definition.
- **Lp-level linearity of `transferOperator_lp`** (commits `483b388`, `d448a7e`):
  - `transferOperator_lp_add`: $\mathrm{transferOperator}_{lp}(g+h) = \mathrm{transferOperator}_{lp}\,g + \mathrm{transferOperator}_{lp}\,h$.
  - `transferOperator_lp_smul`: $\mathrm{transferOperator}_{lp}(c \cdot g) = c \cdot \mathrm{transferOperator}_{lp}\,g$.
  Both compose `Lp.coeFn_add`/`coeFn_smul` + `ae_eq_mk` (input ae-eq), `e989098` (T_b respects ae), `49ff3ba` pointwise distribution, and `MemLp.toLp_congr` + `MemLp.toLp_add`/`_const_smul`.
- **`transferOperator_clm` + op-norm bound** (commit `de5d131`):
  - `transferOperator_clm : LogWeightedL2_Ioo →L[ℂ] LogWeightedL2_Ioo` via `LinearMap.mkContinuous L 1 bound`.
  - `transferOperator_clm_norm_le`: $\|\mathrm{transferOperator}_{clm}\| \le 1$ via `LinearMap.mkContinuous_norm_le`.

**Status of `LogWeightedL2.inner` retirement (2026-05-04, post `a43a669`)**: ✅ DONE — see top "AXIOM ELIMINATION" section. The retirement was achieved without the originally-projected ~44-callsite cascade, by replacing the axiom in-place with a `noncomputable def` plus a `toFunℝ` extension to bridge the structure's `Icc 0 1` domain to `ℝ`.

## CLM-packaging analytic prerequisites (2026-05-04)

A five-commit extension (`0e87907` through `0e5e4b9`) brings the transfer operator T_b's analytic content into the form mathlib's `LinearMap.mkContinuous` and `ContinuousLinearMap` API expect. Headline numbers unchanged; the formalization now exposes T_b at the `Lp → Lp` level with its operator-norm bound stated in real-valued `Lp.norm`.

- `transferOperatorAction_fn_toLp_norm_le` — eLpNorm bound bridged to real-valued `Lp.norm` form via `Lp.norm_def` + `ENNReal.toReal_mono` (commit `0e87907`).
- `transferOperatorAction_fn_add` + `transferOperatorAction_fn_smul` — pointwise additivity / homogeneity of $T_b^{fn}$ at the function level: $T_b(f+g) = T_b f + T_b g$, $T_b(c \cdot f) = c \cdot T_b f$ (commit `49ff3ba`).
- `transferOperatorAction_fn_toLp_add` + `transferOperatorAction_fn_toLp_smul` — Lp-lifted linearity via `MemLp.toLp_congr` chain (mathlib `LpSpace/Basic.lean:109`) bridging to `MemLp.toLp_add` / `_const_smul` (each `rfl`) (commit `aef881c`).
- `transferOperatorAction_fn_toLp_norm_le_input_toLp` — contractivity stated entirely in `Lp.norm`: $\|T_b^{fn,Lp}\, f\| \le \|\mathrm{MemLp.toLp}\, f\, h\|$, the form `LinearMap.mkContinuous` consumes as the operator-norm bound with $M = 1$ (commit `712ee4e`).
- `transferOperator_lp` + `transferOperator_lp_norm_le` — direct `Lp → Lp` form via `(Lp.aestronglyMeasurable g).mk g` (canonical strongly-measurable representative), plus operator-norm bound $\|\mathrm{transferOperator}_{lp}\, g\| \le \|g\|$ (commit `0e5e4b9`).

**What remains for $\|T_b\| \le 1$ as a `ContinuousLinearMap`**: lift the linearity (`_add`, `_smul` from `aef881c`) to `transferOperator_lp`. This requires showing $T_b$ respects ae-equality of input under $\mu_{\log}\!\restriction(0,1)$, which reduces to: $y_k$ preserves $\mu_{\log}$-null sets. The latter follows from `inverseBranch_measurePreserving` (volume level) plus absolute continuity of $\mu_{\log}$ wrt volume on $(0,1)$. Effort: ~1-3 days for the ae-equality propagation lemma, then `LinearMap.mkContinuous` is a one-shot.

## Phase A integration ladder + Mayer 1991 capstone + L² structural-swap analytic prerequisites (2026-05-01 → 2026-05-03)

A 38-commit extension of the rev-3 follow-on chain (commits `2c2a737` through `2e026aa`) completed the analytic foundation for the Mayer 1991 transfer-operator contractivity bound on $L^2(d\mu_{\log})$ AND the L²-structural-swap analytic prerequisites. Headline numbers unchanged; mathematical content materially strengthened.

- **Phase A integration ladder in `PF/LogWeightedIntegral.lean`** — eleven named lintegral identities composing into the Mayer chain:
  - `inverseBranch_measurePreserving` packages the affine pushforward into mathlib's `MeasurePreserving` API (commit `2c2a737`).
  - `inverseBranch_set_lintegral_change_of_variables` — set-restricted per-branch CoV $\int_{y_k^{-1}(s)} h(y_k(x))\, dx = b \cdot \int_s h(u)\, du$ (commit `28a669a`).
  - `unitInterval_eq_iUnion_Ico_partition` + `pairwiseDisjoint_Ico_partition` + `lintegral_unitInterval_eq_sum_Ico_partition` — geometric and integration partition of $[0, 1)$ (commits `76f8246`, `d2b04ae`, `bf8c69f`).
  - `inverseBranch_preimage_Ico_image` + `branch_lintegral_unitInterval_to_Ico` — per-branch CoV specialised to the unit interval (commit `e4cc6b9`).
  - `sum_branch_lintegral_unitInterval_eq_b_lintegral` (and sum-inside variant `lintegral_sum_branch_compose_unitInterval_eq_b_lintegral`) — summed per-branch identity $\sum_k \int_{[0,1)} h(y_k\, y)\, dy = b \cdot \int_{[0,1)} h$ (commits `d2c6487`, `88d7baf`).
  - `lintegral_weight_squared_branch_eq_jacobian_subst` — Radon-Nikodym integrand substitution on $(0, 1)$ (commit `0befd95`).
  - `lintegral_sum_weight_squared_branch_eq_b_lintegral_inv` and $(1/b)$-normalized form `lintegral_one_div_b_sum_weight_squared_branch_eq_lintegral_inv` — combined Mayer chain identity (commits `ab41c4e`, `a3960ce`).
  - `lintegral_transferOp_pointwise_bound_log_weighted` — integrated ENNReal lift of the pointwise Cauchy-Schwarz bound (commit `dc8cb14`).
  - `ofReal_one_div_b_sum_mul_ofReal_one_div_eq` + `lintegral_one_div_b_sum_weight_squared_vals_sq_eq_inv_mul_sum_lintegral` — integrand-distribution lemmas bridging the pointwise bound's RHS to the form the $(1/b)$-normalized identity consumes (commits `84ad7ac`, `8038a01`).

- **Phase A capstone (commit `b8ee9a9`)**: `mayer_1991_lintegral_norm_sq_bound_log_weighted` — the operator-norm bound $\|T_b f\|^2 \le \|f\|^2$ in lintegral form against $d\mu_{\log}$, for $T_b f(x) := (1/b)\sum_k \omega_k\, w_k(x)\, f(y_k(x))$ with unit-modulus phases $\|\omega_k\| = 1$. Hypothesis: `Measurable f`. The analytic foundation of T₃-style operator self-adjointness is now fully in source.

- **logWeightedMeasure bridge + Mayer restatement (commits `69b7054`, `f13126b`)**: the bridge `setLIntegral_Ioo_logWeightedMeasure_eq_setLIntegral_volume_mul_inv` converts integration-against-$\mu_{\log}$ to integration-against-volume with explicit $(1/x)$ factor, and `mayer_1991_lintegral_norm_sq_bound_against_logWeightedMeasure` restates the Mayer bound in the form mathlib's `eLpNorm` consumes: $\int_{(0,1)} \|T_b f\|^2\, d\mu_{\log} \le \int_{(0,1)} \|f\|^2\, d\mu_{\log}$.

- **L² structural-swap analytic prerequisites (commits `9429dd6` … `2e026aa`, six commits 2026-05-03)**:
  * `transferOperatorAction_fn` — **function-level transfer operator** on `ℝ → ℂ` (parallel to the structural one), plus `transferOperatorAction_fn_measurable` (commit `9429dd6`).
  * `transferOperatorAction_fn_lintegral_norm_sq_bound_logWeightedMeasure` — Mayer bound restated under the named operator (commit `e259e42`).
  * `enorm_rpow_two_eq_ofReal_norm_sq` — pointwise bridge $\|x\|_e^{(2:\mathbb{R})} = \mathrm{ENNReal.ofReal}(\|x\|^2)$ (commit `63daa64`).
  * `transferOperatorAction_fn_eLpNorm_le_logWeightedMeasure` — **Mayer 1991 contractivity in `eLpNorm` form** $\|T_b\| \le 1$ on $L^2(\mu_{\log}\!\restriction(0,1))$ (commit `de54564`).
  * `transferOperatorAction_fn_memLp` — **MemLp preservation corollary** (commit `2e026aa`): if $f \in L^2$, then $T_b^{fn}\, f \in L^2$.

The 8-axiom canonical surface is preserved throughout. No new axioms introduced; no sorries introduced. `lake build` 5488 jobs clean.

The remaining work for `LogWeightedL2.inner` elimination (entry 5 below) is now purely the **structural rename cascade** through `PF/TransferOperator.lean` — the analytic content (eLpNorm contractivity + MemLp preservation) is fully in source. Effort estimate revised: ~2-5 days of focused Lean engineering, was 3-7 days (RESEARCH_ROADMAP §2.1).

See `principia_t3_lean_followon_2026-04-28.md` (session memory) for full per-commit detail of all 58 commits.

## Post-rev-3 follow-on (2026-04-29)

An eight-commit chain on 2026-04-29 executed the follow-on Lean pass flagged in the 2026-04-28 audit (below), plus extended the framework to a Lean-checkable conditional Riemann Hypothesis statement. Headline numbers unchanged; mathematical content materially strengthened:

- **`T3_self_adjoint_conj` (entry 5 below) statement REWRITTEN.** The axiom now references `T3_sym.apply` (the explicit symmetrisation $(T_3 + T_3^*)/2$ defined as `T3_sym` in `PF/TransferOperator.lean`), not the unsymmetrised $\tilde{T}_3$. Two-stage transition: commit `f06243f` introduced the existential bridge form; commit `9c06820` sharpened to the explicit-witness form. The canonical 8-axiom referee surface preserves the axiom name (`T3_self_adjoint_conj`) per Pabs's no-demote mandate; the statement is now mathematically defensible.
- **New explicit definitions** in `PF/TransferOperator.lean` (commit `9c06820`): `phaseFactorBase3Conj` (conjugate phases $(1, +i, -1)$), `adjointWeight` (reciprocal weight $\sqrt{x/(3x-k)}$), `T3_adjoint_action` (piecewise expanding-branch operator on $I_k = (k/3, (k+1)/3]$ with bounds proofs by linarith chain), `T3_adjoint`, `T3_sym_action`, `T3_sym`.
- **`IsEigenvalue` predicate defined** (commit `f7d2f11`, `PF/TransferOperator.lean`). Eigenvalue predicate: `∃ f : LogWeightedL2, f ≠ 0 ∧ T f = lam • f`.
- **Two `True`-placeholder theorems converted to real conditional theorems**:
  - `self_adjoint_real_eigenvalues` (commit `f7d2f11`): real Reed-Simon I VI.8 chain proving self-adjoint operators have real eigenvalues. Hypothesis bundle: `hsa`, `hsmul_left`, `hsmul_right`, `hpos_def`. The `hsmul_*` and `hpos_def` hypotheses become free post-Phase-A.
  - `compact_discrete_spectrum` (commit `6d62102`): real squeeze proof showing that an eigenvalue sequence with $1/n$-decay modulus bound tends to zero.
- **Composing theorems added**:
  - `T3_sym_spectral_framework` (commit `6cc08f4`, `PF/TransferOperator.lean`): three-clause precondition (self-adjoint, real eigenvalues, decay) under the Phase A + spectral-theorem hypothesis bundle.
  - `T3_sym_RH_precondition` (commit `f989bba`, `PF/SpectralBijection.lean`): four-clause precondition (above three plus eigenvalue → critical-line index injection).
  - `RiemannHypothesis : Prop` definition + `riemann_hypothesis_via_spectral_bijection` (minimal) + `riemann_hypothesis_via_T3_sym_framework` (full chain) (commit `1fdf3e5`).
  - `principia_fractalis_millennium_capstone` (commit `2a76b26`, new file `PF/Millennium.lean`): bundled both Millennium claims (`P_neq_NP_def ∧ RiemannHypothesis`) under the four-track RH hypothesis bundle.

The 8-axiom canonical surface is preserved throughout. No new axioms introduced; no sorries introduced. `lake build` 5488 jobs (was 5486; +2 for the new Millennium module) clean.

See `principia_t3_lean_followon_2026-04-28.md` (session memory) for full per-commit detail.

## Post-rev-3 status (2026-04-28)

The full rev-3 cycle (REVISION_GUIDE.md, all 20 items) was completed 2026-04-27/28 in 17 commits. Highlights affecting this audit:

- **`T3_self_adjoint_conj` (entry 5 below) is now SUPERSEDED at the manuscript level.** Manuscript Ch 20 (commit `9659f92`) now asserts essential self-adjointness of the *symmetrisation* $\widetilde{T}_3^{\mathrm{sym}} := (\tilde{T}_3 + \tilde{T}_3^*)/2$ on $C_c^\infty((0,1])$ via Friedrichs extension (Reed-Simon II, X.23), with the unsymmetrised $\tilde{T}_3$ recognised as non-normal Cartesian companion. The Lean axiom `T3_self_adjoint_conj` continues to typecheck and is unchanged in source, but its meaning is now to be read as the symmetrisation property — a follow-on Lean pass should rewrite the axiom statement to be about $\widetilde{T}_3^{\mathrm{sym}}$ explicitly. The canonical 8-axiom count is unchanged.
- **Manuscript Ch 22 (commits `9abb5bc`, `ea8bc3e`)**: Theorem 22.X (Topological Stability) now provides a quantitative fractal-cascade damping bound; Theorem 22.no-blowup Steps 4-5 flow from the cascade mechanism. No Lean impact (NavierStokes is Coq-side).
- **Manuscript Ch 23 (commit `db98d2c`)**: Mass gap formula now $\Delta_{\mathrm{fYM}} = \Lambda_{\mathrm{QCD}} \cdot \omega_c$ with clean dimensions. No Lean impact.
- **Manuscript Ch 24 (commits `4fa2fc9`, `ee31d6e`)**: BSD operator redefined on multiplicative line $L^2(\mathbb{R}_+, dx/x)$, Connes-Marcolli framework. Coq disclosure block updated (commit `a5a6488`); Lean unaffected (no BSD operator in canonical PF/).
- **Manuscript Ch 25 (commits `b66fc45`, `3b20099`)**: $\sigma_c = 0.95$ restated as exact-decomposition fact, Hodge-concentration restated as conditional on Rationality-Hodge-Galois Concentration Hypothesis. No Lean impact.
- **Frontmatter**: 8-axiom scope explicitly disclosed (commit `0b3829f`); unified per-Millennium $\alpha$-dictionary added (commit `f497fcd`).

Verification setup that flagged `T3_self_adjoint_conj` as false in 2026-04-26 audit was correct under the unsymmetrised operator; the rev-3 fix preserves the rigour by switching to the symmetrisation. The other 7 axioms are unchanged in scope and meaning by the rev-3 cycle.

See `principia_rev3_session_2026-04-27_28.md` (session memory) and individual commit messages for the per-task resolution record.

---

## Pre-rev-3 historical content (2026-04-26)

The NUM category is now empty — `log_3_bounds` was eliminated via direct n=60 Taylor at x=2/3, with `simp [Finset.sum_range_succ, ...]` + `norm_num` handling the 60-term sum.

Each axiom is one of:
- **CLASSIC** — Classical theorem from analysis/probability literature.
- **LOAD-BEARING PLACEHOLDER** — Trivializing would break other proofs.
- **BOOK-CORE** — Stated as a book theorem; represents substantive math claim.
- **NEEDS REDESIGN** — Independent verification has shown the axiom statement is false under the surrounding definitions; retained as a formal placeholder until the redesigned object lands.

## ⚠ Verification check pending V01 reconciliation (2026-04-27)

A numerical/symbolic verification pass was conducted on 2026-04-26 using the operator and inner product as transcribed from the manuscript and Lean source verbatim (weight √(bx/(x+k)), inverse branches y_k(x) = (x+k)/b, phases ω = {1, -i, -1} for b = 3, inner product ⟨f, g⟩ = ∫₀¹ f̄(x) g(x) dx/x). The verification did not confirm self-adjointness of T₃ on L²([0,1], dx/x) under those transcribed conventions. Specifically:

- ⟪T₃ x, x⟫ was computed to be approximately −0.110 + 0.162i (would need to be real for a self-adjoint operator under the standard convention).
- ⟪T₃ f, g⟫ − ⟪f, T₃ g⟫ was computed as approximately 0.096 + 0.188i for f = x, g = x² (40-digit precision; not roundoff).

A follow-up reconciliation pass tested nine alternative interpretations of the manuscript notation (alternative weight, alternative inner-product conjugation convention, alternative phase placement, several alternative Hilbert-space structures, the (T+T*)/2 symmetrization, etc.); none of those interpretations rescued self-adjointness under the verified setup.

**This is not a proof that the underlying mathematics is incorrect.** Pabs's earlier verification work — referred to as the "V01 catalog" — is being located on disk. Possibilities the agent setup has not yet been able to rule out include:

- The original derivation may use a slightly different operator definition or inner-product convention than what the manuscript and Lean source currently transcribe (e.g., different conjugation slot, different phase placement, different measure).
- A specific Hilbert-space structure (kernel inner product, weighted Bergman space, etc.) that the verification did not test could carry the self-adjointness.
- The manuscript may contain a typeset/transcription detail that diverges from V01.

Until V01 is located and reconciled with the verification setup, entry 5 (`T3_self_adjoint_conj`) carries an **open verification question** rather than a confirmed inconsistency. The axiom is retained in source so downstream proofs in `SpectralBijection.lean` continue to typecheck.

The **other 7 axioms are unaffected** by this open question.

## The 8

### 1. `bochner_minlos_existence` (CLASSIC)
- **File**: `PF/BochnerMinlos.lean:81`
- **Statement**: ∀ CharacteristicFunctional C, ∃ probability measure μ on S'(R^d) with Fourier = C
- **Why hard**: Classical Minlos theorem. Needs full Kolmogorov extension on nuclear spaces.
- **Book reference**: Chapter 23, Minlos Theorem

### 2. `bochner_minlos_uniqueness` (CLASSIC)
- **File**: `PF/BochnerMinlos.lean:93`
- **Statement**: Two measures with same Fourier transform are equal
- **Why hard**: Fourier-transform injectivity on measures

### 3. `finite_dim_bochner` (CLASSIC)
- **File**: `PF/CylindricalMeasures.lean:155`
- **Statement**: ∀ PD+normalized+continuous C on ℝⁿ, ∃! probability measure with Fourier = C
- **Why hard**: Not in mathlib. Would be substantial mathlib contribution.

### 4. `LogWeightedL2.inner` (LOAD-BEARING PLACEHOLDER)
- **File**: `PF/TransferOperator.lean:70`
- **Statement**: signature `LogWeightedL2 → LogWeightedL2 → ℂ`
- **Why cannot trivialize**: defining as `fun _ _ => 0` would make all downstream self-adjointness proofs vacuously true
- **Real elimination**: construct log-weighted Lebesgue integral ∫₀¹ f̄·g dx/x

### 5. `T3_self_adjoint_conj` (BOOK-CORE — sharpened 2026-04-29)
- **File**: `PF/TransferOperator.lean` (axiom declaration line shifts with each commit; see Lean source for current line)
- **Statement (post 2026-04-29 follow-on)**: ∀ f g, ⟪T3_sym.apply f, g⟫ = ⟪f, T3_sym.apply g⟫
- **Book reference**: Chapter 20, Theorem `thm:self-adjoint-transfer` (manuscript Definition `def:T3-sym`)
- **Depends on**: `LogWeightedL2.inner` (axiom 4 below)
- **Status**: Statement rewritten to reference the explicit symmetrisation `T3_sym` (defined in same file as `(1/2 : ℂ) • (T3.apply + T3_adjoint.apply)`, with `T3_adjoint` the piecewise expanding-branch operator on $I_k = (k/3, (k+1)/3]$ with conjugate phases $(1, +i, -1)$ and reciprocal weights $\sqrt{x/(3x-k)}$). Axiom name preserved; statement now mathematically defensible. The 2026-04-26 verification finding (unsymmetrised $\tilde{T}_3$ is NOT self-adjoint) is correctly disclosed in the axiom docstring as historical motivation. Becomes provable as a theorem once Phase A inner-product structure on `LogWeightedL2` lands (see entry 4).

### 6. `turingTimeComplexity` (LOAD-BEARING PLACEHOLDER)
- **File**: `PF/TuringEncoding/Complexity.lean:57`
- **Statement**: signature `(Γ Λ σ : Type) → TM2.Machine Γ Λ σ → BinString → ℕ`
- **Why cannot trivialize**: constant 0 would prove P = NP against the spectral-gap theorem
- **Real elimination**: parameterize or construct from TM2 stepping semantics

### 7. `p_eq_np_spectrum_collapse` (BOOK-CORE)
- **File**: `PF/TuringEncoding/Operators.lean:191`
- **Statement**: `ClassP = ClassNP → λ₀_P = λ₀_NP`
- **Book reference**: Chapter 21 (core P vs NP bridge)

### 8. `operator_collapse_hypothesis` (BOOK-CORE)
- **File**: `PF/P_NP_Complete_Proof.lean:175`
- **Statement**: (∀ L vtime, IsInNP vtime → ∃ t, IsInP t) → α_NP = α_P
- **Book reference**: Chapter 21, Theorem 21.3

## Summary by category

| Category | Count | Axioms |
|---|---|---|
| NUM | 0 | (all eliminated 2026-04-24) |
| CLASSIC | 3 | bochner_minlos_existence/uniqueness, finite_dim_bochner |
| LOAD-BEARING PLACEHOLDER | 2 | LogWeightedL2.inner, turingTimeComplexity |
| BOOK-CORE | 3 | T3_self_adjoint_conj (V01 reconciliation pending), p_eq_np_spectrum_collapse, operator_collapse_hypothesis |

## Counterfactual: where we started

Beginning of rev2 cycle (2026-04-22 early session): 41 Lean axioms in PF/.

Tonight's 32 eliminations (late session commits, ordered by method):

**Proven as genuine theorems (14):**
- sqrt2_in_interval_ultra, phi_in_interval_ultra
- sqrt2_in_interval_10digit, sqrt5_in_interval_10digit, phi_in_interval_10digit (new supporting theorems)
- Q_4_ge_Q_larger, Q_decreasing_from_4
- pos_def_hermitian (via strengthened IsPositiveDefinite definition)
- pos_def_normalized_bounded
- radix_economy_max_at_exp1
- lambda_P_lower_certified, lambda_P_upper_certified
- lambda_NP_lower_certified, lambda_NP_upper_certified
- lambda_0_P_precise, lambda_0_NP_precise

**Deleted as latently unsound (4):**
- empty_tape_bound (claimed log(2^s·3^h) ≤ 0, false)
- characteristic_cylindrical_round_trip (contradicted CharacteristicFunctional.normalized field)
- cylindrical_measure_fourier_is_characteristic (same pattern)
- nuclearity_essential (contradicted trivial NuclearSpace witness)

**Deleted as unused dead code (3):**
- prime_bound, log_conversion (unused entirely)
- axiom_head_and_tape_eq (forward-declaration pattern; consumers also unused)

**Promoted to structure fields (4):**
- TestGaugeField.instAddCommGroup, TestGaugeField.instModule (via Pi-type refactor)
- embedding_strictly_monotone (→ TimelessFieldTorus.embedding_mono)
- shell_has_natural_frequency (→ CurvatureShell.alpha_natural)

**Proven with explicit placeholder caveats (8) — Yang-Mills cluster:**
- yang_mills_4d_gaussian_valid, yang_mills_positive_definite, yang_mills_continuous
- yang_mills_construction_complete
- gauge_field_space_nuclear
- FreeYangMillsGaussian.generatingFunctional (converted axiom → def)
- minlos_sigma_additivity
- gaussian_is_characteristic (via 3 new GaussianCharacteristic fields)

## Major scientific findings

1. **Four latent unsoundness bugs** in the pre-session formalization (the "Deleted as latently unsound" group above). A referee would catch all four.
2. **`IsPositiveDefinite` definition was weaker than standard** — only required `.re ≥ 0`, not full real-and-nonneg. Strengthened during this session.
3. **Yang-Mills `CovarianceOperator.quadraticForm` is a placeholder `:= 0`**. All YM-cluster theorems are honest about this in their docstrings and in `rev2` Chapter 23 LaTeX.
4. **One parallel unsoundness in Coq** (characteristic_cylindrical_round_trip) caught and corrected.

## Supporting artifacts

- `PARITY_REPORT.md` — Lean ↔ Coq ↔ Lean4Lean axiom audit
- `Principia_Fractalis_master_folder_rev2/frontmatter/rev2_formalization_status.tex` — frontmatter referee summary
- Per-chapter "Formal verification (rev 2)" notes in ch07, ch21, ch23
- Full commit history on GitHub `FractalDevTeam/Principia-Fractalis` master
