# CHURN χ_k EEG-BRIDGE — SYNTHETIC MEASUREMENT-VALIDITY BENCHMARK CHARTER

Date: 2026-09-13 (correction revision, following independent-audit
rejection of prior HEAD `5ceaea9c`).

Branch: r331b-provenance.

**STATUS: DOCUMENTATION ONLY. IMPLEMENTATION-READINESS IS SCOPED
PER DECLARED BENCHMARK CELL, NOT GLOBAL.**
§13 lists the specification gaps that must be closed by labelled
amendment commits before implementation of any given cell may
proceed. §14 defines the **Phase-1 cell** (M19 + P.LAP + Benchmark
B) and lists the exact subset of §13 gaps that must close for that
cell. Gaps outside the Phase-1 subset (in particular G1 M64/M128,
G7 Benchmark-A source reconstruction, and the P.REST / P.SRC-
specific parts of G6) remain deferred and MUST NOT be represented
as completed by any Phase-1 amendment.

This charter is the U15 dependency named in
`codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md` §13.

**What passing this benchmark can and cannot mean.**
Passing this benchmark **qualifies a declared operationalization**
(one representation, one set of pinned estimator parameters, one
head-model realization) **for advancement to a pilot preregistration
of the χ_k program.** It does NOT:

- close Ring 4 of the ring map (a synthetic benchmark cannot close
  the physical measurement ring; only physical measurements against
  independent ground-truth can do that);
- validate the Timeless-Field ontology (Rings 1–2);
- validate any identification of χ_k with a measure of
  consciousness (Ring 5);
- validate that clinical human EEG is well-approximated by the
  head model, source model, or noise model used here.

---

## §1. Definitions (locked)

| Symbol | Meaning |
|---|---|
| `M` | number of latent dipole sources |
| `N_ch` | number of scalp electrodes in the montage |
| `S_lat(f)` | Hermitian PSD latent cross-spectrum, `M × M`, at frequency or band `f` |
| `ρ_lat = ρ_lat(f) = S_lat(f) / Tr(S_lat(f))` | analytic per-band normalized latent state, `M × M`, at band `f` |
| `S_full` | full latent cross-spectrum aggregated across the §7 band set (including cross-band blocks); its executable construction (block layout, aggregation rule, trace normalisation) remains part of §13 G3 |
| `ρ_full = S_full / Tr(S_full)` | full-spectrum normalized latent state used ONLY by S5; executable construction PENDING §13 G3 |
| `Π_band` | block-diagonal-by-band projector on `S_full` that retains within-band blocks and zeroes cross-band blocks; the block layout is fixed by the §7 band set, its executable specification PENDING §13 G3 |
| `ρ_proj := Π_band(S_full) / Tr(Π_band(S_full))` | projected/operational state used ONLY by S5; consistent with the per-band `ρ_lat` view because its non-zero blocks are exactly the per-band `ρ_lat(f)` reweighted by `Tr(S_lat(f)) / Tr(Π_band(S_full))` |
| `G` | forward operator (leadfield), `N_ch × M` |
| `η` | additive sensor-noise term (spec in §13 G2) |
| `V = G · s + η` | scalp potential vector (with `s` the vectorised source amplitude) |
| `P` | representation map (P.LAP, P.REST, P.SRC.sLORETA, P.SRC.LCMV) |
| `S_rep(f) = P(V)` | representation-space cross-spectrum |
| `ρ_rep = S_rep / Tr(S_rep)` | representation-space normalized state |
| `R_P` | reconstruction map from representation-space back to latent-source space, where defined (§3.A only) |
| `χ_lat(ρ_A, ρ_B) = (1/2) · ‖ρ_A − ρ_B‖²_F` | Frobenius churn on the latent M×M state pair (identified with the Layer-1 χ_k via the isometric lift, per Layer-2 charter §3.5) |
| `χ_rec(P; ρ_A, ρ_B) = (1/2) · ‖R_P(ρ_rep_A) − R_P(ρ_rep_B)‖²_F` | reconstructed-latent churn (Benchmark A only) |
| `χ_op(P; ρ_A, ρ_B) = (1/2) · ‖ρ_rep_A − ρ_rep_B‖²_F` | operational (representation-space) churn (Benchmark B) |

All three churn definitions inherit Layer-1 T1–T4 (non-negativity,
symmetry, zero-iff-eq, unitary invariance) on their respective
spaces. **χ_op is NOT claimed to equal χ_lat** except under the
unitary special case; see §2.

---

## §2. Load-bearing mathematical caveat

Independent audit correctly identified the following defect in the
prior HEAD `5ceaea9c`:

> For a non-unitary representation map A, the mapping
> `ρ ↦ A ρ A† / Tr(A ρ A†)` does not in general preserve
> Hilbert–Schmidt / Frobenius distance.

Concretely, for representation `P` acting on scalp signals via a
linear operator `A_P` (Laplacian derivative, rREST re-referencing,
regularised inverse operator, or their composition with the
cross-spectrum construction), the induced map on cross-spectra
```
S_rep = A_P S_sensor A_P^H
```
is not isometric on the Frobenius norm unless `A_P` is unitary.
None of P.LAP, P.REST, or regularised P.SRC is unitary. Therefore:

- `χ_op(P; ρ_lat_A, ρ_lat_B) ≠ χ_lat(ρ_lat_A, ρ_lat_B)` in general.
- Requiring near-exact recovery `χ_op ≈ χ_lat` to `1e-6` tolerance
  (as HEAD `5ceaea9c` E2 did) is scientifically unjustified. That
  requirement is retracted.
- Layer-1 T4 (unitary invariance) does NOT rescue χ_k here.

Consequence: the benchmark must separate two estimands.

**Benchmark A — Latent-source recovery.** Applicable only where an
explicit reconstruction map `R_P` maps representation-space back
into the same latent M-dim space. Compares `χ_rec` (churn on the
reconstructed latent state pair) against `χ_lat` (churn on the true
latent state pair). Tolerances must be justified by the
reconstruction model's identifiability assumptions, not by
machine precision.

**Benchmark B — Operational observable.** Applicable to any
representation. `χ_op` is treated as an operational quantity DEFINED
on representation-space cross-spectra, NOT as a recovery of χ_lat.
Tests are limited to (i) exact internal invariances of the
representation-space map (E-family: reference-swap, scalar
amplitude, global phase, isometric-embedding, symmetry),
(ii) monotone response to latent structural change (χ_op should
increase when χ_lat increases across a swept parameter, but the
proportionality is representation-dependent), (iii) nuisance
robustness (χ_op should be small when latent state is unchanged),
(iv) stability of χ_op under estimator-parameter perturbations.

**A and B are not combined into a single ranking.** Their outcomes
are reported separately. A representation may pass B without
passing A (P.LAP is the canonical case — it has no defined
reconstruction map `R_P.LAP`). No representation may pass A without
passing B.

---

## §3. Applicability of each estimand per representation

| Representation | Benchmark A (latent-recovery) | Benchmark B (operational) | Rationale for A applicability |
|---|---|---|---|
| P.LAP | NOT APPLICABLE | applicable | Surface Laplacian is a spatial derivative on scalp; no natural inverse to the source grid; no `R_P.LAP` defined. |
| P.REST | NOT APPLICABLE | applicable | rREST reconstructs "potentials at infinity" on the sensor manifold, not source-space activity; identifying that with the latent M-dim space would require an additional post-hoc inverse step, which is P.SRC territory. |
| P.SRC.sLORETA | CANDIDATE / PENDING G7 | applicable | sLORETA reconstructs standardised source amplitudes on a declared grid, but its Benchmark-A applicability is NOT established until §13 G7 explicitly defines `R_P.SRC.sLORETA` as a map into the same M-dim latent basis used to define `ρ_lat` and states its identifiability assumptions. |
| P.SRC.LCMV | CANDIDATE / PENDING G7 | applicable | LCMV beamformer reconstructs source amplitudes on the same grid, but its Benchmark-A applicability is NOT established until §13 G7 explicitly defines `R_P.SRC.LCMV` as a map into the same M-dim latent basis and states its identifiability assumptions (adaptive-covariance case included). |

For A, applicability itself is CANDIDATE. `R_P.SRC.*` must be
defined by §13 G7 as an explicit map into the same M-dim latent
basis used by `ρ_lat`, and its identifiability assumptions must be
stated, before P.SRC.sLORETA or P.SRC.LCMV can be treated as
applicable to Benchmark A. Until then, both are labelled PENDING G7
in §8.A and in the manifest.

---

## §4. Fault list corrected by this revision

| # | Prior defect (in `5ceaea9c`) | Correction |
|---|---|---|
| D1 | E2 demanded `χ_op ≈ χ_lat = 1/4` to `1e-6` relative tolerance across all three representations. Mathematically unjustified for non-unitary A. | E2 is retracted for Benchmark B. A latent-recovery version of E2 is retained in Benchmark A only (§5.A), applicable only to P.SRC.sLORETA and P.SRC.LCMV, with tolerances declared per §13 G7. |
| D2 | Acceptance rule "95% CI LOWER bound ≤ 5%" is failure-to-prove-failure, not evidence of acceptance. | Replaced with three-outcome logic: **PASS** iff 95% CI UPPER ≤ threshold; **FAIL** iff 95% CI LOWER > threshold; **INCONCLUSIVE** iff CI straddles the threshold (§6.1). |
| D3 | Nuisance ratio used LOWER-bound acceptance for the same reason. | Same three-outcome upper-bound convention applied (§6.5). |
| D4 | S7.a, S7.b, S7.c null distributions were pooled into a single per-representation null band. | Each S7 sub-scenario now yields its OWN per-representation null band. No pooling. |
| D5 | S6 sub-scenarios contributed to both the null-family false-positive aggregate AND to the nuisance-ratio gate (double-counting). | S6 contributes ONLY to the nuisance-ratio gate (§6.5) and is NOT part of the §6.2 null decision set. The §6.2 null decision set is S1, S7.a, S7.b, S7.c, each with its OWN per-scenario calibration and PASS/FAIL/INCONCLUSIVE decision. Any S1 ∪ S7.* aggregate is descriptive-only (§6.2) and never participates in PASS/FAIL. |
| D6 | "Wishart-like," "approximately 5000 sources," and unnamed 10-10 / 10-5 subsets were not implementable. | Marked as specification gaps G1, G3, G5 in §13. Charter is NOT IMPLEMENTATION-READY until those are closed by labelled amendments. |
| D7 | Sensor-noise, artifact templates, forward-model implementation, and inverse-operator implementation were named but not specified. | Marked as specification gaps G2, G4, G5, G6 in §13. Charter is NOT IMPLEMENTATION-READY. |
| D8 | Layer-2 charter §5 declares `Δt = N · Δ_stft = 8 × 250 ms = 2 s` as the super-window length, but §3.2 declares `T_stft = 500 ms` STFT windows with `Δ_hop = 250 ms`. Actual signal span of N=8 segments is `T_stft + (N-1) · Δ_hop = 500 + 7 × 250 = 2250 ms`, not 2000 ms. | Benchmark adopts explicit `T_super = T_stft + (N_seg − 1) · Δ_hop`. For the Layer-2 charter's declared `T_stft = 500 ms`, `Δ_hop = 250 ms`, `N_seg = 8`, this gives `T_super = 2.25 s`. Layer-2 charter §5 is flagged for follow-up amendment (§13 G8); it is not amended in this commit. |
| D9 | Exact-test tolerances (`1e-10`, `1e-6`, `1e-4`) and stochastic thresholds (5× SNR margin, `R_nuis ≤ 0.5`, false-positive ≤ 5%) were pinned without justification and without sensitivity analysis. | All thresholds are labelled ★ PF design choices. §6.7 mandates a sensitivity analysis on a **metric-specific feasible grid** (see §6.7 table): bounded-range metrics such as the Spearman rank threshold use their own feasible grid (`{0.8, 0.9, 0.95}` for rank, preserved from §7), and no uniform `× {0.5, 1, 2}` multiplier is applied to bounded metrics. If any threshold flips the outcome across its feasible grid on a disqualifying metric, the decision is INCONCLUSIVE-BY-SENSITIVITY. |
| D10 | "Closes Ring 4" was overclaimed. | Replaced throughout with "qualifies this operationalization for a pilot." A synthetic benchmark cannot close the physical measurement ring. |

---

## §5. Test scenarios

Two disjoint families (deterministic vs stochastic) applied
separately to Benchmark A and Benchmark B.

### §5.1 Family E — EXACT tests (deterministic, closed-form χ_gt)

E-family tests are the ONLY ones with mathematically closed-form
answers. They probe the noiseless correctness of the map. Except
where §5.A explicitly promotes E2 into Benchmark A, exact tests
belong to Benchmark B and use `χ_op`.

| ID | Applies to | Test | Ground-truth answer | Tolerance basis |
|---|---|---|---|---|
| E0 | B, all P | Reference-swap invariance: same latent V(t), two synthetic scalp recordings under different references (Cz vs linked mastoids), both passed through the same P. `χ_op(P; ρ_rep_A, ρ_rep_B)` computed on the two recordings. | 0 | PF choice per representation (§13 G8); MUST be justified as the numerical/regularisation floor of that representation's implementation, NOT set to machine precision arbitrarily |
| E1 | B, fixed-and-scale-equivariant P only | Scalar-amplitude scaling null: `S_lat(t_1, f) = α · S_lat(t_0, f)` for scalar `α > 0`. `ρ_lat` invariant. | `χ_op = 0` under fixed, scale-equivariant preprocessing (representation acts as a fixed linear map on `V` so `S_rep` scales by `α` and cancels through `S / Tr(S)`) | Machine precision — but ONLY for representations whose implementation (per §13 G6) is a fixed linear operator and scale-equivariant on `S`. E1 is PENDING for any pipeline whose §13 G6 algorithm has not yet established scale equivariance; in particular, adaptive-covariance LCMV and any data-dependent regularisation whose regulariser is a function of `α · S` are not automatically fixed linear maps and their E1 outcome is PENDING G6 |
| E2.A | A, P.SRC.* only | Analytic redistribution recovery: `ρ_lat(t_0) = diag(1/4, 3/4)`, `ρ_lat(t_1) = diag(3/4, 1/4)` on `M = 2` sources; `χ_lat = 1/4`. Compute `χ_rec = (1/2)‖R_P(ρ_rep_0) − R_P(ρ_rep_1)‖²_F`. | `χ_rec` compared to `χ_lat = 1/4` | Bounded by declared identifiability error of `R_P` (§13 G7); NOT a machine-precision bound |
| E3.a | B, all P | Global-phase invariance: signal at t_0 and t_1 differs by scalar `e^{iφ}` applied everywhere. `χ_op` computed. | 0 | Machine precision (`(e^{iφ} X)(e^{iφ} X)^H = X X^H` identically) |
| E3.b | B, all P | Isometric-embedding invariance: two distinct isometric maps `V, V′` with `V†V = V′†V′ = I_D`; `χ_op` computed under both. | Equal (Layer-2 charter §3.5 identity) | Machine precision |
| E3.c | B, all P | Numerical symmetry: `χ_op(ρ_A, ρ_B)` compared to `χ_op(ρ_B, ρ_A)`. | Equal (Layer-1 T2) | Machine precision |

Note on E2.A: this is the only exact test that participates in
Benchmark A. Benchmark B does NOT contain any analytic-value
recovery test — because χ_op is not claimed equal to χ_lat.

### §5.2 Family S — STOCHASTIC scenarios (seeded, CI-based)

Family S has the same structural placement as E within each
benchmark. Latent ensembles and noise models are specification gaps
(§13 G3, G2); this section defines the SCIENTIFIC INTENT of each
scenario without pinning implementation choices.

| ID | Contributes to | Latent construction (INTENT; executable spec pending §13) | Metric |
|---|---|---|---|
| S1 | Own per-scenario calibration + PASS/FAIL/INCONCLUSIVE (§6.2); contributes to a §6.2 descriptive-only aggregate | Same latent at both windows (scalar-scaling null with seed-driven noise realizations) | Own `p_null(P, S1)` and own decision per §6.2 |
| S2 | Benchmark A monotonicity/recovery; Benchmark B monotonicity | Latent redistribution parameterized by a scalar `θ` swept over `{θ_1, ..., θ_K}`; χ_lat computed analytically per draw and θ | A: `χ_rec` vs `χ_lat` scatter, Spearman rank correlation, RMSE (per θ). B: `χ_op` monotone in θ (Spearman); NO recovery-of-χ_lat claim |
| S3 | Benchmark B monotonicity (flag-only) | Latent inter-band redistribution at constant total power; χ_lat analytic under a declared ρ construction | Same as S2 but with a caveat: block-diagonal-by-frequency ρ discards cross-band content by design (Layer-2 charter §3.3) |
| S4 | Benchmark B (flag-only) | Latent lagged inter-source phase change with fixed marginal auto-spectra | Response of `χ_op` vs latent phase parameter; magnitude-only ρ constructions will not respond (design blind spot, flagged not disqualified) |
| S5 | Implementation-correctness check | Latent cross-frequency coupling change with unchanged within-frequency structure. The genuine latent state on the full cross-spectrum `ρ_full` (§1) changes between windows; the full-spectrum churn on `ρ_full` is NOT zero. The Layer-2 §3.3 projector `Π_band` (§1; executable construction PENDING §13 G3) discards cross-band content by construction, so the projected/operational state `ρ_proj` (§1) is unchanged and `χ_op` computed on `ρ_proj` is zero by construction. S5 is a test of the projection-implementation, not a claim that latent churn is zero | `χ_op` on `ρ_proj` must equal 0 under the declared ρ construction (implementation correctness of the `Π_band` projection). The full-spectrum churn on `ρ_full` is not claimed zero here. `ρ_full`, `Π_band`, and `ρ_proj` are §1-declared objects whose executable construction remains part of §13 G3 |
| S6.a | Nuisance gate (§6.5); NOT in the §6.2 null decision set | Latent unchanged; scalp montage rotated between windows (yaw ∈ {2°, 5°, 10°}) | `R_nuis(S6.a)` (§6.5) |
| S6.b | Nuisance gate; NOT in the §6.2 null decision set | Latent unchanged; electrode subset displaced 5 mm ({5%, 10%} of electrodes) | `R_nuis(S6.b)` |
| S6.c | Nuisance gate; NOT in the §6.2 null decision set | Latent unchanged; {5%, 10%} channels bad-marked and interpolated | `R_nuis(S6.c)` |
| S6.d | Nuisance gate; NOT in the §6.2 null decision set | Latent unchanged; leadfield perturbation of 5% Frobenius norm applied to t_1 only | `R_nuis(S6.d)` |
| S6.e | Nuisance gate; NOT in the §6.2 null decision set | Latent unchanged; artifact template added at t_1 (spec §13 G4) | `R_nuis(S6.e)` |
| S7.a | Own per-scenario calibration + PASS/FAIL/INCONCLUSIVE (§6.2); contributes to a §6.2 descriptive-only aggregate | Latent = independent white-noise sources at both windows | Own null band and own decision per §6.2 |
| S7.b | Own per-scenario calibration + PASS/FAIL/INCONCLUSIVE (§6.2); contributes to a §6.2 descriptive-only aggregate | Latent = single distant deep source (volume-conduction pattern) at both windows | Own null band and own decision per §6.2 |
| S7.c | Own per-scenario calibration + PASS/FAIL/INCONCLUSIVE (§6.2); contributes to a §6.2 descriptive-only aggregate | No latent source; sensor noise only | Own null band and own decision per §6.2 |

**Explicit no-double-counting rule (D5).** S6 contributes ONLY to
the nuisance-ratio gate (§6.5). S6 is NOT part of the §6.2 null
per-scenario decision set. The §6.2 decision set is S1, S7.a,
S7.b, S7.c — each with its OWN calibration and OWN PASS/FAIL/
INCONCLUSIVE decision (per the no-pooling rule below). A
descriptive-only aggregate across S1 ∪ S7.* MAY be reported (§6.2)
but is NOT a decision statistic.

**Explicit no-pooling rule (D4, strengthened).** S1, S7.a, S7.b,
and S7.c each yield their OWN per-representation null band, their
OWN margin, their OWN 95% CI on false-positive rate, and their OWN
three-outcome PASS/FAIL/INCONCLUSIVE decision (§6.2). Their draws
and their false-positive events are NOT combined into a single
per-representation pass/fail statistic and no maximum margin is
formed across S7 sub-scenarios. Any single disqualifying scenario
(S1, S7.a, S7.b, or S7.c) failing at §6.2 blocks advancement of
that representation independently. A representation-level aggregate
across S1 ∪ S7.* MAY be reported descriptively in the manifest, but
it is NOT a decision statistic.

---

## §5.A Benchmark A test set

Applies to `P.SRC.sLORETA` and `P.SRC.LCMV` as **CANDIDATE /
PENDING G7** — see §3. Applicability itself is not established
until §13 G7 defines `R_P.SRC.*` as a map into the same M-dim
latent basis used by `ρ_lat` and states its identifiability
assumptions. Until G7 closes for a given `P.SRC.*`, its §5.A gate
outcome is PENDING G7 and no PASS may be recorded.

- E-family: `E2.A` only.
- S-family: `S2` (monotonicity + `χ_rec` vs `χ_lat` recovery per θ).
- Tolerances: PF design choice per §13 G7, justified by declared
  identifiability assumptions of the inverse operator, not by
  machine precision.

Pass/fail per §6, four-outcome PASS/FAIL/INCONCLUSIVE/PENDING G7.

## §5.B Benchmark B test set

Applies to all four representations (P.LAP, P.REST,
P.SRC.sLORETA, P.SRC.LCMV).

- E-family: E0, E1, E3.a, E3.b, E3.c.
- S-family: S1, S2 (monotonicity only, no recovery-of-χ_lat claim),
  S3 (flag), S4 (flag), S5 (implementation), S6.* (nuisance), S7.*
  (null bands).

Pass/fail per §6.

---

## §6. Metrics and three-outcome decisions

All CIs at 95% confidence, computed by bootstrap over `N_eval`
seeds (see §7 for draw counts, PF design choice).

**Three-outcome convention (D2, D3):**

| Situation | Outcome |
|---|---|
| 95% CI **upper** bound ≤ threshold | PASS |
| 95% CI **lower** bound > threshold | FAIL |
| CI straddles threshold | INCONCLUSIVE |

INCONCLUSIVE is a distinct outcome, not a pass or fail. A
representation with any INCONCLUSIVE decision on a disqualifying
metric cannot advance to a pilot until that decision is resolved
(either by increasing draw counts or by amending the threshold via
§10).

### §6.1 Draw separation (retained from prior revision)

- `N_cal`: per-scenario calibration seeds (PF choice; §7).
- `N_eval`: per-scenario evaluation seeds, DISJOINT from `N_cal`.
- Bootstrap resamples `B` on the `N_eval` set (PF choice; §7).

Calibration is used to construct null bands and to size CI widths;
pass/fail decisions use only `N_eval`.

### §6.2 Null-scenario false-positive rate (Benchmark B, per scenario)

Scenarios evaluated: S1, S7.a, S7.b, S7.c (S6 NOT included, D5).
Each scenario is decided INDEPENDENTLY. Draws are NOT combined
across scenarios into a single decision statistic, and no maximum
margin is formed across S7 sub-scenarios.

For each scenario `x ∈ {S1, S7.a, S7.b, S7.c}` and each
representation `P`:

1. **Own calibration distribution.** Compute the empirical null
   distribution of `χ_op(P; x)` on that scenario's `N_cal` draws
   (disjoint from `N_eval`).
2. **Own margin.** `margin_null(P, x) := ` the 95th-percentile
   upper endpoint of a 95% CI on the null distribution's chosen
   quantile (PF choice per §13 G8; candidate: the 95th percentile
   of the `N_cal` empirical null).
3. **Own point estimate.**
   `p_null(P, x) := ` fraction of that scenario's `N_eval` draws
   with `χ_op > margin_null(P, x)`.
4. **Own confidence interval.** Bootstrap 95% CI on
   `p_null(P, x)` over `B` resamples of the `N_eval` draws of
   scenario `x` (each scenario resampled independently).
5. **Own three-outcome decision** against threshold
   `p_null ≤ 5%` (PF choice, sensitivity per §6.7), using the
   generic upper-bound rule of §6 for a lower-is-better metric:
   PASS iff CI upper ≤ 5%; FAIL iff CI lower > 5%; INCONCLUSIVE
   otherwise.

**Disqualifying-scenario rule.** FAIL on ANY of S1, S7.a, S7.b, or
S7.c independently disqualifies representation `P` for advancement.
INCONCLUSIVE on any of these scenarios blocks advancement per §6
until resolved.

**Descriptive-only aggregate.** A pooled or maximum
`p_null_aggregate(P) := max_x p_null(P, x)` (or its bootstrap CI)
MAY be reported in the manifest for descriptive purposes only. It
is NOT a decision statistic and cannot substitute for any of the
four per-scenario decisions above.

### §6.3 Monotonicity and recovery (Benchmarks A and B)

Population: S2 sweep over `θ ∈ {θ_1, ..., θ_K}`.

**Confidence-interval procedure.** For both Spearman and RMSE, the
95% CI is computed by direct paired-seed nonparametric bootstrap
over the `N_eval` seed set with `B` resamples (§7). Each bootstrap
resample draws seeds jointly across the swept `θ` grid so that
within-seed paired structure is preserved. The Spearman CI is the
empirical **percentile** 95% CI of the bootstrap distribution of
the Spearman rank coefficient itself, clipped to the closed
interval `[-1, 1]`; the Fisher z-transform is NOT used, since it
is singular at `±1` and both endpoints are attainable with the
declared five-point `θ` grid. The RMSE CI is the empirical
percentile 95% CI of the bootstrap distribution of
`RMSE(χ_rec, χ_lat)` (Benchmark A) or, where applicable, of the
analogous residual (Benchmark B, not required).

**Undefined-metric handling for Spearman.** The Spearman
coefficient is undefined when either ranked vector (`θ` on one
side; median `χ_op(θ)` or `χ_rec(θ)` on the other) is constant on
the sample under evaluation:
- **Point-estimate case.** If the point estimate of the Spearman
  coefficient on the full `N_eval` set is undefined (either
  ranked vector constant), the monotonicity gate is FAIL for that
  representation. It is not INCONCLUSIVE — a constant response is
  a definitive failure of monotonicity.
- **Bootstrap-replicate case.** If any bootstrap replicate yields
  an undefined coefficient (because the resampled median on that
  replicate is constant across `θ`), that replicate is NOT
  silently dropped. The fraction of undefined replicates
  `undef_frac(P)` is computed on `B` replicates and reported in
  the manifest. If `undef_frac(P) > 0`, the monotonicity gate
  outcome is INCONCLUSIVE-METRIC-UNDEFINED and the representation
  cannot advance until either the metric is redefined by
  amendment (§10) or the point estimate and every bootstrap
  replicate are well-defined at increased `N_eval`. No arbitrary
  acceptable-undefined-fraction threshold is introduced.

**Direction-specific three-outcome rules (metric-by-metric).**

Spearman rank correlation is a **higher-is-better** metric against
threshold `r_thr` (PF choice; §7 candidate `r_thr = 0.9`):
- PASS iff 95% CI **lower** bound ≥ `r_thr`.
- FAIL iff 95% CI **upper** bound < `r_thr`.
- INCONCLUSIVE otherwise (CI straddles `r_thr`).

RMSE is a **lower-is-better** metric against bound `RMSE_bound`
(Benchmark A: declared identifiability bound of `R_P` per §13 G7):
- PASS iff 95% CI **upper** bound ≤ `RMSE_bound`.
- FAIL iff 95% CI **lower** bound > `RMSE_bound`.
- INCONCLUSIVE otherwise.

For Benchmark B: Spearman rank correlation between `θ` and median
`χ_op(θ)` decided by the higher-is-better rule above. No recovery
claim is made and no RMSE test is applied.

For Benchmark A: Spearman rank correlation between `χ_lat(θ)` and
median `χ_rec(θ)` decided by the higher-is-better rule above; AND
RMSE `‖χ_rec − χ_lat‖` per θ (pooled across θ into a single RMSE
statistic) decided by the lower-is-better rule above. Both
sub-decisions must PASS for the §6.3 gate to PASS; any FAIL is a
gate FAIL; any INCONCLUSIVE that is not overridden by a FAIL yields
gate INCONCLUSIVE.

These direction-specific rules SUPERSEDE the generic upper-bound
convention of the §6 table for the metrics named in this section.

### §6.4 Minimum signal recovery (Benchmark B only)

Population: S2 at smallest swept magnitude `θ_1`.

Metric: median `χ_op(P; S2, θ_1)`.
Threshold: median 95% CI LOWER bound ≥ `f_SNR × margin_null` for a
PF-declared SNR margin `f_SNR` (candidate: `f_SNR = 5`; §7
sensitivity range `{2.5, 5, 10}`).

Outcome: PASS iff 95% CI LOWER ≥ threshold; FAIL iff 95% CI UPPER
< threshold; INCONCLUSIVE otherwise.

Note: for this floor test, the direction of the CI comparison is
inverted (we WANT the lower bound to exceed the floor). The
three-outcome logic is applied consistently: PASS requires
confidence that the true value is above the floor; FAIL requires
confidence that it is below.

For Benchmark A: no minimum-signal-recovery test; recovery quality
is captured entirely in §6.3 RMSE.

### §6.5 Nuisance-ratio gate (Benchmark B)

Population per sub-scenario: S6.a, S6.b, S6.c, S6.d, S6.e.
```
R_nuis(P; S6.x) = median χ_op(P; S6.x) / median χ_op(P; S2, θ_ref),
```
with `θ_ref` a PF-declared mid-sweep magnitude (§7).

**Joint resampling.** The 95% CI on `R_nuis(P; S6.x)` is computed
by nonparametric bootstrap over `B` resamples in which the
numerator draws (S6.x) and the denominator draws (S2 at `θ_ref`)
are BOTH resampled per bootstrap replicate. The ratio-of-medians is
recomputed on each jointly resampled replicate; the empirical
percentile 95% CI of that ratio-of-medians distribution is the
reported CI. This propagates denominator uncertainty rather than
treating the denominator as a fixed point estimate.

**Denominator uncertainty statistic.** The bootstrap distribution
of `median χ_op(P; S2, θ_ref)` on the denominator side is also
summarised (point estimate + 95% percentile CI) and recorded in the
per-scenario metric block of §9 alongside `R_nuis` itself.

**Denominator-stability threshold (PENDING G8).** `χ_op` is a
dimensionless Frobenius churn on trace-normalised states, so the
denominator-stability threshold must itself be dimensionless. No
fixed numerical floor is declared in this charter — in particular
the prior formula `χ_op_floor := max(1e-12, ε_min · Tr(S_baseline))`
is retracted as dimensionally invalid (`ε_min · Tr(S_baseline)` is
a spectrum-scale regularisation quantity, not a churn magnitude).
In its place, introduce a per-representation dimensionless
denominator-stability threshold `δ_den(P)` on
`median χ_op(P; S2, θ_ref)`, marked **PENDING §13 G8**. §13 G8
must define `δ_den(P)` as a labelled ★ PF design choice — with
justification and a feasible sensitivity grid — before
implementation may proceed. Until G8 closes for `P`, the §6.5 gate
is PENDING G8 for that `P`.

**Ratio-decision admissibility.** A ratio-of-medians decision on
`R_nuis(P; S6.x)` is admissible **only** when BOTH of the
following hold on the denominator side:
- the point estimate `median χ_op(P; S2, θ_ref) > δ_den(P)`, AND
- the bootstrap **lower** 95% percentile bound on
  `median χ_op(P; S2, θ_ref)` (the same denominator bootstrap
  distribution summarised above) is `> δ_den(P)`.

If either condition fails, the S6.x gate outcome is
INCONCLUSIVE-DENOMINATOR-UNSTABLE (§6.7 sensitivity analysis is
not consulted; the denominator is the load-bearing failure) and
the representation cannot advance until the denominator is
re-established above `δ_den(P)` — e.g. by re-selection of `θ_ref`
via labelled amendment (§10).

**Bootstrap-replicate rule (executable).** For each bootstrap
replicate `b`, compute the replicate ratio
`R_nuis^{(b)} := median χ_op(P; S6.x)^{(b)} / median χ_op(P; S2, θ_ref)^{(b)}`
ONLY when the replicate denominator
`median χ_op(P; S2, θ_ref)^{(b)}` is strictly positive. If the
replicate denominator is exactly zero, the replicate is neither
dropped nor assigned `+∞`; instead the fraction of zero-denominator
replicates `zero_den_frac(P; S6.x)` is computed over `B` and
reported in the manifest. If `zero_den_frac(P; S6.x) > 0`, the
ratio 95% CI is not defined and the S6.x gate outcome is
INCONCLUSIVE-METRIC-UNDEFINED (analogous to the §6.3 rule); no
arbitrary acceptable-fraction threshold is introduced.

Replicate denominators that are strictly positive but below
`δ_den(P)` still produce well-defined ratios and are retained in
the bootstrap distribution. Their stability is controlled by the
point-estimate + lower-CI admissibility rule above, which operates
on the summary denominator statistics and is the authoritative
stability gate. There is no claim that the point/CI rule
automatically handles every individual bootstrap replicate; the
executable rule for replicates is the one stated in this
paragraph.

Ratio values are never defined as `+∞`. `u_frac` is removed from
the decision logic and is no longer reported.

**Outcomes (when admissible).** The ratio's 95% percentile CI is
compared to the threshold `R_nuis ≤ 0.5` (PF choice; §7
sensitivity range) by the standard lower-is-better rule of §6:
PASS iff 95% CI upper ≤ 0.5; FAIL iff 95% CI lower > 0.5;
INCONCLUSIVE otherwise.

Applied to each S6.x separately. FAIL on any S6.x disqualifies P.
INCONCLUSIVE (any variant, including PENDING G8) on any S6.x
blocks advancement until resolved.

For Benchmark A: no nuisance-ratio gate against latent-recovery;
Benchmark B's nuisance ratio is the sole nuisance measure. This
means Benchmark A is a NECESSARY-BUT-NOT-SUFFICIENT filter — a
representation passing A must also pass B to advance.

### §6.6 Implementation-correctness gate

E-family failures within Benchmark B and S5 non-zero response are
both implementation-correctness failures (numerical / coding fault),
disqualifying independent of §6.2–§6.5.

### §6.7 Threshold sensitivity analysis (D9)

Every PF-declared threshold in §6.2–§6.5 is recomputed on a
**metric-specific feasible grid** — a uniform `× {0.5, 1.0, 2.0}`
multiplier is not applied to bounded-range metrics because it can
produce infeasible values (e.g. `2 × 0.9 = 1.8` is not a valid
rank correlation). The grids below preserve §7's declared ranges
and are the authoritative sensitivity set:

| Threshold | Feasible sensitivity grid | Source |
|---|---|---|
| Null false-positive `p_null` ≤ 5% (§6.2) | `{2.5%, 5%, 10%}` | §7 |
| Monotonicity Spearman rank ≥ 0.9 (§6.3) | `{0.8, 0.9, 0.95}` | §7 (PRESERVED — no uniform multiplier) |
| RMSE bound (§6.3, Benchmark A) | `{0.5, 1.0, 2.0} × RMSE_bound(§13 G7)` | §7 |
| Minimum-signal floor factor `f_SNR` (§6.4) | `{2.5, 5, 10}` | §7 |
| Nuisance ratio `R_nuis` ≤ 0.5 (§6.5) | `{0.25, 0.5, 1.0}` | §7 |
| Denominator-stability threshold `δ_den(P)` (§6.5) | PENDING §13 G8; feasible grid supplied by G8 | §13 G8 |
| E-family tolerances (§5.1 per representation) | `× {0.1, 1.0, 10}` | ★ PF |

Any historical or downstream reference to a "uniform `×{0.5,1,2}`
sensitivity multiplier" is superseded by this table. The three-
outcome decision under each perturbation on this table is reported
in the manifest.

**Robustness rule.** If ANY threshold's perturbation changes a
representation's PASS/FAIL/INCONCLUSIVE decision on a disqualifying
metric, that decision is downgraded to INCONCLUSIVE-BY-SENSITIVITY
and the representation cannot advance to a pilot until the
threshold is either narrowed to a range that yields a stable
decision, or amended by §10.

---

## §7. Pinned parameters (bounded PF design choices)

All values below are PF design choices, subject to §6.7 sensitivity
analysis. They are NOT claimed as primary-source-derived. Any
implementation must instantiate them explicitly.

| Parameter | Value | Note |
|---|---|---|
| `N_cal` | 2000 | ★ PF |
| `N_eval` | 5000 | ★ PF; disjoint seed range from N_cal |
| Bootstrap resamples `B` | 5000 | ★ PF |
| Master seed `SEED_MASTER` | 20260913 | ★ PF |
| `N_cal` seed range | `[SEED_MASTER, SEED_MASTER + N_cal)` | disjoint from evaluation range |
| `N_eval` seed range | `[SEED_MASTER + 10^6, SEED_MASTER + 10^6 + N_eval)` | |
| Bootstrap seed | `SEED_MASTER + 2·10^6` | |
| Frequency-band set | δ [0.5, 4], θ [4, 8], α [8, 13], β [13, 30], γ [30, 45] Hz | Consistent with Layer-2 charter §3.2 |
| STFT window `T_stft` | 500 ms | Layer-2 charter §3.2 |
| STFT hop `Δ_hop` | 250 ms | Layer-2 charter §3.2 |
| Segments per super-window `N_seg` | 8 | Layer-2 charter §5 |
| Super-window signal span `T_super` | `T_stft + (N_seg − 1) · Δ_hop = 500 + 7 × 250 = 2250 ms` | D8 correction; Layer-2 §5 inconsistency flagged in §13 G8 |
| ε_min for ρ definition | `1e-12 · median Tr(S)` | Layer-2 charter §3.4 |
| Head model | 3-shell concentric spherical | Radii and conductivities in §13 G5 (executable spec required) |
| Montages | M19 (10-20, listed below) | ★ PF; M64 and M128 gaps §13 G1 |
| P.LAP (m, λ) grid | m ∈ {3, 4, 5}, λ ∈ {1e-6, 1e-5, 1e-4} | ★ PF |
| P.REST regularisation ε_REST | {1e-4, 1e-3, 1e-2} | ★ PF |
| P.SRC.* λ_SRC | {1e-3, 1e-2, 1e-1} · max singular value of leadfield | ★ PF |
| P.SRC.* source grid | §13 G5 executable spec required | not-implementation-ready |
| S2 sweep set | `θ ∈ {0.05, 0.10, 0.20, 0.40, 0.80} rad` | ★ PF |
| S2 reference magnitude `θ_ref` for §6.5 | 0.20 rad | ★ PF |
| Sensitivity SNR margin `f_SNR` | 5 | ★ PF; §6.7 range {2.5, 5, 10} |
| Nuisance ratio threshold | 0.5 | ★ PF; §6.7 range {0.25, 0.5, 1.0} |
| Null false-positive threshold | 5% | ★ PF; §6.7 range {2.5%, 5%, 10%} |
| Monotonicity rank threshold | 0.9 | ★ PF; §6.7 range {0.8, 0.9, 0.95} |
| Numerical absolute floor | 1e-14 | ★ PF |
| Numerical relative floor | 1e-12 | ★ PF |

**M19 electrode set (International 10-20).** Fp1, Fp2, F7, F3, Fz,
F4, F8, T3, C3, Cz, C4, T4, T5, P3, Pz, P4, T6, O1, O2. (19
labels.) This montage is fully specified.

**M64 and M128 are NOT specified in this charter.** See §13 G1.

---

## §8. Selection procedure

Per representation, per montage (M19 only until §13 G1 closes),
per parameter cell (P.LAP: per (m, λ); P.REST: per ε_REST;
P.SRC: per λ_SRC and forward-model mismatch condition):

### §8.A Benchmark A (P.SRC.sLORETA, P.SRC.LCMV — both PENDING G7)

Applicability itself is CANDIDATE / PENDING G7 per §3. Until G7
lands, the §8.A gate outcome for both P.SRC.sLORETA and P.SRC.LCMV
is PENDING G7 and no PASS may be recorded. After G7 closes:

1. E2.A within declared identifiability tolerance (§13 G7).
2. S2 Spearman rank correlation decided by the higher-is-better
   rule of §6.3 against threshold `r_thr` (§7).
3. S2 RMSE decided by the lower-is-better rule of §6.3 against the
   declared identifiability bound (§13 G7).

Outcomes reported: {PASS, FAIL, INCONCLUSIVE, PENDING G7}.

### §8.B Benchmark B (all representations)

1. E0, E1, E3.a, E3.b, E3.c within §5.1 tolerances. E1 is PENDING
   G6 for any representation whose §13 G6 algorithm has not yet
   established scale equivariance (§5.1); no PASS may be recorded
   for E1 on such a representation until G6 closes for it.
2. S5 within numerical zero on the block-diagonal-projected state
   (implementation-correctness gate; the projected `χ_op` is zero
   by construction, latent `χ_lat` is NOT claimed zero — §5.2).
3. Per-scenario null false-positive decisions under §6.2:
   independent PASS/FAIL/INCONCLUSIVE decisions on S1, S7.a, S7.b,
   and S7.c. Each disqualifying scenario failure blocks
   advancement independently. The S1 ∪ S7.* aggregate is
   descriptive only and NOT a decision statistic.
4. S2 monotonicity Spearman rank decided by §6.3's higher-is-
   better rule against threshold `r_thr` (§7).
5. Sensitivity floor (§6.4) at smallest θ.
6. Nuisance ratio (§6.5) for every S6.x — including the joint-
   resampling CI, denominator-uncertainty summary, and
   `u_frac`/stability-floor handling.
7. §6.7 sensitivity analysis stable on the metric-specific feasible
   grid.

Outcomes reported: {PASS, FAIL, INCONCLUSIVE,
INCONCLUSIVE-DENOMINATOR-UNSTABLE, INCONCLUSIVE-BY-SENSITIVITY,
PENDING G6}.

### §8.C No cross-representation aggregation

Each representation is evaluated independently. There is no
cross-representation agreement rule (C4 correction retained).

### §8.D Global outcome

A representation "qualifies for a pilot" iff:
- Benchmark B outcome is PASS on all §8.B filters (no PENDING G6
  on E1 for that representation, no INCONCLUSIVE of any variant,
  no FAIL).
- Benchmark A outcome is either NOT APPLICABLE (P.LAP, P.REST) or
  PASS on all §8.A filters (P.SRC.*). A P.SRC.* whose §8.A outcome
  is PENDING G7 does NOT qualify until G7 closes and Benchmark A
  is re-evaluated to PASS.

If ≥ 1 representation qualifies, the Layer-2 charter §3.1
provisional primary designation is testable against this set, and
the pilot preregistration is unblocked.

If NO representation qualifies at any montage, Ring 4 remains open
under the current operationalization. Amendments to the Layer-2
charter (narrower claim or different representation catalog) are
required.

**"Qualifies for a pilot" is not "Ring 4 is closed."** Ring 4
closure requires physical measurement against independent ground
truth; synthetic benchmarks cannot supply that.

---

## §9. Reproducibility manifest

Not implementation-ready per §13. When implementation lands, the
manifest requirements below apply.

Output artifact per run: single directory
`benchmark_results/YYYY-MM-DD_HHMMSS_<git-sha>/` containing:

| Path | Contents |
|---|---|
| `manifest.json` | git sha of this charter and any implementation; §7 pinned values echoed as literals; §13-gap-closure amendment SHAs; per-scenario seed ranges; hostname; timestamp; library versions |
| `latent_truth/<scenario>.parquet` | analytic `ρ_lat(t_0)`, `ρ_lat(t_1)`, `χ_lat` per draw (Benchmark A also stores `R_P` reconstructed states) |
| `measured/<representation>/<montage>/<param_cell>/<scenario>.parquet` | `χ_op` or `χ_rec` per draw; ρ hashes only (not full matrices) |
| `metrics/<representation>/<montage>/<param_cell>/<scenario>.json` | per-scenario per-representation metric block (columns per §6.7 sensitivity grid) |
| `sensitivity_grid/<representation>/<montage>/<param_cell>.json` | §6.7 outcomes across the perturbation grid |
| `selection.json` | per-representation per-montage per-cell §8 outcomes {PASS, FAIL, INCONCLUSIVE} |
| `disqualifications.log` | one line per FAIL or INCONCLUSIVE outcome with (representation, montage, cell, filter, value, bound) |
| `sha256.txt` | sha256 of every emitted file |

Determinism: rerunning with the same manifest MUST reproduce every
file byte-for-byte. Verification requires an independently
computed `sha256.txt` and comparison against a pre-committed
expected-hash file.

---

## §10. Governance

- This charter lives on `r331b-provenance`. Master unchanged.
- No Lean, no book, no Layer-3 content.
- Any change to §5 scenarios, §6 metrics, §7 pinned values, or §8
  selection procedure requires a labelled amendment commit that
  (i) identifies the paragraph, (ii) states the reason, (iii) does
  NOT touch results or logs. Post-hoc silent threshold changes are
  prohibited.
- Specification gaps §13 G1–G8 must each be closed by their own
  labelled amendment commit before implementation of any cell that
  depends on that gap may proceed. **Cell-scoped closure is
  authoritative.** §14 declares the Phase-1 cell (M19 + P.LAP +
  Benchmark B) and its dependency subset of §13 gaps; a Phase-1
  amendment CANNOT represent gaps outside that subset (in
  particular G1 M64/M128, G7 Benchmark-A source reconstruction,
  and the P.REST / P.SRC-specific parts of G6) as completed.
- New representations added only by amendment adding a §7 block
  plus a §3 applicability entry, evaluated on the same scenario
  set, and their own cell declaration in §14.

---

## §11. Disclaimer (D10)

Passing this benchmark **qualifies a declared operationalization
for advancement to a pilot preregistration.**

Passing does NOT:
- Close Ring 4 (a synthetic benchmark cannot close the physical
  measurement ring).
- Validate the Timeless-Field ontology (Rings 1–2).
- Validate any identification of χ_k with a measure of
  consciousness (Ring 5).
- Validate that clinical human EEG is well-approximated by the
  head model, source model, or noise model instantiated by §7 and
  §13.

Failure of a representation to qualify under this benchmark
disqualifies THAT representation, under THESE assumptions, from
advancing to pilot. It does NOT disqualify Layer 1 (kernel-verified
Frobenius churn on H_k), the underlying mathematical construction,
or the χ_k program at other Layer-2 operationalizations.

---

## §12. Cross-references

- Layer-2 charter `codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md`:
  §3.1 (provisional primary/sensitivity designation this benchmark
  exists to test), §3.2 (STFT parameters), §3.3 (block-diagonal-by-
  band ρ; drives S5 ground-truth), §3.4 (ε_min), §3.5 (isometric-
  embedding invariance; drives E3.b), §5 (χ_k definition;
  arithmetic inconsistency flagged §13 G8), §9 (robustness axes),
  §11 (D1/D2/D3 surrogate constructions), §13 U11–U15 (load-bearing
  assumptions this benchmark resolves).
- Bridge audit `codex/CHURN_CHI_K_EEG_BRIDGE_AUDIT_2026-09-13.md`:
  §7 (A/B/C decomposition of the pipeline claim).
- Layer-1 kernel `PF_Lean4_Code/PF/Consciousness/FrobeniusChurn.lean`:
  unchanged; χ_k, T1–T5 as proven there. Unitary invariance is NOT
  invoked to protect χ_k from the non-unitary preprocessing under
  evaluation.

---

## §13. Specification gaps (cell-scoped implementation-blockers)

The gaps below are implementation-blocking on a **per-cell** basis.
No cell of §14 is implementation-ready until every gap in that
cell's declared dependency subset is closed by its own labelled
amendment commit on `r331b-provenance`. Gaps outside a cell's
subset MUST NOT be represented as completed by any amendment
serving that cell.

### G1 — Electrode label sets for M64 and M128

Required contents of the amendment:
- Exact ordered list of electrode labels for M64.
- Exact ordered list of electrode labels for M128.
- Reference to the naming convention (10-10, 10-5, or vendor
  scheme) with citation to whichever primary source or
  documentation defines the layout.
- Corresponding electrode positions on the pinned 3-shell head
  model (§13 G5) as `(x, y, z)` coordinates in metres.

### G2 — Sensor-noise model

Required contents:
- Distribution family (candidate: Gaussian, i.i.d. across channels
  and time samples).
- Numerical scale (candidate: `σ = 0.5 μV`).
- Correlation structure (candidate: none, i.i.d.).
- Coupling to the seed hierarchy (§7).
- Justification of the choice or a labelled ★ PF-design-choice tag
  with sensitivity range.

### G3 — Latent-source ensemble per stochastic scenario

Required contents for S1, S2, S3, S4, S6.*, S7.*:
- Distribution family from which `S_lat(f)` is drawn per draw
  (candidate: complex Wishart on `M × M` Hermitian PSD, `ν` degrees
  of freedom, scale matrix `Σ`).
- Numerical parameters (candidate: `ν = 2M`, `Σ = I_M`).
- Trace normalization and any additional constraints.
- Coupling to the seed hierarchy.

Additionally, for **S5**:
- Executable construction of the full latent cross-spectrum
  `S_full`, including the block layout across the §7 band set,
  aggregation rule from per-band `S_lat(f)`, cross-band block
  populations that make S5's cross-frequency coupling change
  nontrivial, and trace normalisation.
- Executable specification of the block-diagonal-by-band projector
  `Π_band` on `S_full`.
- Definition of `ρ_full` and `ρ_proj` consistent with §1.

The prior-charter phrase "Wishart-like distribution" is retracted;
executable specification required.

### G4 — Artifact template for S6.e

Required contents:
- Time-domain template shape for the eye-blink artifact
  (candidate: parametric alpha-function).
- Amplitude scaling relative to background RMS.
- Spatial projection to scalp electrodes (candidate: fixed frontal
  weight vector).
- Muscle-artifact template if required.

### G5 — Forward-model implementation

Required contents:
- Head-model geometry (radii; §7 pins three-shell concentric
  spherical) with numerical values in metres.
- Tissue conductivities in S/m (candidate: scalp 0.33, skull
  0.0165, brain 0.33; skull:brain 1:20; requires primary-source
  attribution or explicit ★ PF design-choice tag).
- Leadfield algorithm: analytical (Berg-Scherg 1994 series with
  truncation order) OR numerical (BEM/FEM with mesh spec).
- Source grid: exact number of source dipoles, positions in metres,
  orientations. The prior-charter phrase "approximately 5000 sources"
  is retracted.
- Implementation library (if any) with version pin, or full
  algorithmic pseudocode.

### G6 — Inverse-operator implementation

Required contents:
- sLORETA: algorithmic definition with regularisation formula,
  standardisation step, and orientation handling.
- LCMV beamformer: constraint (unit-gain), covariance regularisation
  rule, orientation handling.
- Implementation library with version pin OR full algorithmic
  pseudocode.

### G7 — Reconstruction map `R_P.SRC.*` and identifiability

Required contents:
- Definition of `R_P` for each `P.SRC.*`: composition of the
  inverse operator with any projection into the M-dim latent space
  used for `χ_rec`.
- Identifiability assumptions (candidate: `rank(G) = M`, no sources
  outside the modelled grid, no dipole-orientation error, no
  spatial mismatch between head model and generator).
- Analytic or simulated tolerance bound for E2.A recovery under
  those assumptions.
- Recovery-error decomposition (bias, variance, regularisation
  residual) as a checklist for the RMSE floor in §6.3.

### G8 — Threshold justification and Layer-2 charter §5 reconciliation

Required contents:
- Justification (or explicit ★ PF-design-choice tag) for every §7
  threshold: `p_null ≤ 5%`, rank ≥ 0.9, `f_SNR = 5`,
  `R_nuis ≤ 0.5`, E0 numerical floors (`1e-10`, `1e-6`), E2.A
  identifiability bound.
- Definition and justification of the per-representation
  dimensionless denominator-stability threshold `δ_den(P)` on
  `median χ_op(P; S2, θ_ref)` used by §6.5, as a labelled ★ PF
  design choice with a feasible sensitivity grid. The threshold
  MUST be dimensionless on the χ_op scale (no `ε_min · Tr(S)`
  or other spectrum-scale surrogate).
- Amendment to Layer-2 charter §5 to reconcile the arithmetic
  inconsistency between `Δt = N · Δ_stft = 2 s` and the actual
  super-window span `T_super = T_stft + (N_seg − 1) · Δ_hop
  = 2.25 s` under the declared `T_stft = 500 ms`, `Δ_hop = 250 ms`,
  `N_seg = 8`. Either (a) change `N_seg`, (b) change `Δ_hop`, or
  (c) redefine `Δt` to reference stride rather than span. This
  amendment must land on the Layer-2 charter, NOT on this benchmark
  charter.

---

**Correction commit lineage.** This revision replaces HEAD
`5ceaea9c` on `r331b-provenance`. The independent audit rejected
`5ceaea9c` on the load-bearing mathematical defect stated in §2
plus nine additional defects catalogued in §4. No implementation,
Lean, book, or Layer-3 work is authorised for a given cell until
the §13 gaps in that cell's dependency subset (§14) close and the
resulting revised charter is itself independently audited.

---

## §14. Cell declarations and Phase-1 scope

A **benchmark cell** is a triple `(Montage, Representation, Bench)`
that fully determines which §13 gaps must close before the cell is
implementation-ready. Cell declarations are additive: adding a
cell requires a §14 amendment and does not authorise work on any
other cell.

### §14.1 Phase-1 cell — the executable surface authorised now

**Phase-1 cell = (M19, P.LAP, Benchmark B).**

Rationale: this is the smallest scientifically honest executable
surface that lets the χ_k program's Layer-2 measurement side
advance to a synthetic-validity pass/fail decision without
overclaiming source-space reconstruction (Benchmark A) or larger
montages (M64/M128). Choice of P.LAP as the Phase-1 representation
mirrors the Layer-2 charter §3.1 provisional primary designation
(★ PF), whose supporting sources — Sitt 2014 (spatial Laplacian /
CSD for the target UWS/MCS population) and Tenke & Kayser 2015
(reference-freedom + parameter-dependence documentation of surface
Laplacian) — are recorded in the bridge audit §3 and the Layer-2
charter §3.1 as PF design justification, NOT as a mandate.

**Phase-1 dependency subset of §13.** Only the following gaps are
implementation-blocking for the Phase-1 cell:

| Gap | Required for Phase-1? | Phase-1 scope |
|---|---|---|
| G1 M64/M128 | NO (deferred) | Phase-1 uses M19 only |
| G2 Sensor-noise model | YES | Full spec required |
| G3 Latent-source ensemble | YES | Only for scenarios used by Phase-1 Benchmark B (S1, S2, S3-flag, S4-flag, S5, S6.a–e, S7.a–c). S5 must include the `S_full` / `Π_band` / `ρ_full` / `ρ_proj` executable construction (§1). |
| G4 Artifact template | YES | S6.e is a Phase-1 nuisance scenario |
| G5 Forward-model implementation | YES, restricted | Only geometry, conductivities, and the P.LAP-adjacent scalp-potential generation are Phase-1-blocking. Source-grid parameters that only feed Benchmark A (`R_P.SRC.*`) are NOT Phase-1-blocking. |
| G6 Inverse-operator implementation | NO for Phase-1's decision path | Phase-1 uses no inverse operator. sLORETA and LCMV specifications remain deferred and MUST NOT be represented as completed by any Phase-1 amendment. |
| G7 Reconstruction map `R_P.SRC.*` | NO (deferred) | Phase-1 uses no `R_P`. Benchmark A remains deferred. |
| G8 Threshold justification + Layer-2 §5 reconciliation | YES, restricted | Only the thresholds and estimator specifications actually used by the Phase-1 cell (`p_null`, monotonicity, `f_SNR`, `R_nuis`, `δ_den(P.LAP)`, E-family tolerances for P.LAP, null quantile/CI estimator, Spearman/RMSE bootstrap behaviour, Layer-2 §5 timing reconciliation) are Phase-1-blocking. Justifications of thresholds that only apply to representations outside Phase-1 remain deferred. |

**Phase-1 readiness rule.** The Phase-1 cell is implementation-
ready when — and only when — every "YES" row above is closed by a
labelled amendment commit that (i) declares which gap and which
Phase-1 scope it closes, (ii) does not touch code, Lean, book,
Layer-3, master, or results, and (iii) either supplies a primary-
source-verified specification or a labelled ★ PF preregistered
design choice with a feasible sensitivity grid per §6.7.

### §14.2 Explicitly deferred surfaces (NOT implementation-ready)

The following cells are declared but **NOT** implementation-ready
under this charter revision. Any claim of readiness for them is
scope-violating:

- `(M64, *, *)` and `(M128, *, *)` — pending G1.
- `(*, P.REST, *)` — pending the P.REST-specific parts of G6
  (rREST estimator/regularisation).
- `(*, P.SRC.sLORETA, *)` and `(*, P.SRC.LCMV, *)` — pending the
  P.SRC-specific parts of G6 (inverse operator) and, for
  Benchmark A, G7 (`R_P.SRC.*` definition + identifiability).
- `(*, *, Benchmark A)` — pending G7 for the applicable
  representations.

A cell moves from "deferred" to "implementation-ready" only via a
new §14 sub-section declaration.

### §14.3 What passing the Phase-1 cell can and cannot mean

Passing the Phase-1 cell means: the (M19, P.LAP, Benchmark B)
operationalization is qualified to advance to a **pilot
preregistration** of the χ_k program on that specific
operationalization.

Passing the Phase-1 cell does NOT:
- Close Ring 4 (only physical measurements against independent
  ground truth can do that; §11).
- Validate the Timeless-Field ontology (Rings 1–2).
- Validate any identification of χ_k with a measure of
  consciousness (Ring 5). Ring 5 identification is a separate
  epistemic layer from Layer-2 measurement validity.
- Qualify any other cell (M64/M128, P.REST, P.SRC.*, Benchmark A).
- Validate that clinical human EEG is well-approximated by the
  Phase-1 head model or noise model.
- Establish that P.LAP is the correct or unique operationalization
  for the χ_k program; the Layer-2 charter §3.1 designation
  remains a PF provisional choice subject to §9 robustness checks
  and to future cell declarations.

### §14.4 Cross-references

- Layer-2 charter §3.1: PF-provisional-primary rationale for P.LAP
  and the sources supporting it (not a mandate).
- Layer-2 charter §5: super-window / stride timing (subject to
  §13 G8 reconciliation).
- Bridge audit §3: P.LAP verified claims and unverified aspects.
- Bridge audit §7: A/B/C decomposition — Phase-1 addresses A
  (algebraic well-formedness) and the estimator side of B
  (statistical assumptions), but explicitly does NOT resolve C
  (physical interpretation as intrinsic brain-state change).
- Source audit: full-text verification records for Sitt 2014 and
  provenance/inaccessibility records for other primary sources.
- Layer-1 kernel `PF_Lean4_Code/PF/Consciousness/FrobeniusChurn.lean`:
  unchanged. Phase-1 does not touch Lean or the book.
