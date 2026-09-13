# CHURN χ_k EEG-BRIDGE — SYNTHETIC MEASUREMENT-VALIDITY BENCHMARK CHARTER

Date: 2026-09-13 (executable-spec revision)
Branch: r331b-provenance
Status: DOCUMENTATION ONLY. No implementation code, no simulation
runs, no human data. This charter is the U15 dependency named in
`codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md` §13.

Scope: define the sole filter through which each of the three
candidate representations (P.LAP, P.REST, P.SRC) must independently
pass before it may be used as the Layer-2 EEG → ρ_EEG(t) → χ_k
bridge in a human-subjects pilot preregistration.

**What passing means.** Passing this benchmark validates ONLY that
the synthetic measurement map from a simulated latent state to χ_k
recovers the analytic ground-truth χ within calibrated error under
the stated forward/inverse models and estimator parameters. Passing
does NOT validate: (i) the Timeless-Field ontology, (ii) any
consciousness interpretation, (iii) that the true biophysical
generator of clinical EEG is described by this simulation family.
Those are separate rings. This benchmark closes Ring 4 for a
declared operationalization; nothing more.

---

## §1. Definitions (locked)

| Symbol | Meaning |
|---|---|
| `M` | number of latent dipole sources in the head model |
| `N_ch` | number of scalp electrodes in the montage |
| `S_lat(f)` | Hermitian PSD latent cross-spectrum, `M × M`, at frequency `f` or band |
| `ρ_lat = S_lat / Tr(S_lat)` | analytic normalized latent state |
| `G` | fixed forward operator (leadfield), `N_ch × M` |
| `X = G S_lat G^H + N` | scalp cross-spectrum with additive sensor noise `N` |
| `P.LAP, P.REST, P.SRC` | candidate representations (see §7 for pinned parameters) |
| `S_rep(f) = P(X)` | representation-space cross-spectrum after applying `P` |
| `ρ_rep = S_rep / Tr(S_rep)` | representation-space normalized state |
| `χ_gt(ρ_A, ρ_B) = (1/2) · ‖ρ_A − ρ_B‖²_F` | Frobenius churn on H_k (Layer-1 definition, applied to the D-space Hermitian trace-1 matrix pair; isometric lift into H_k is invariant per Layer-2 charter §3.5, so χ_gt on D-space equals χ_k on H_k) |
| `χ_meas(P; L_0, L_1)` | measured χ from applying representation `P` end-to-end on scenarios generated from latent states `L_0, L_1` |
| `err(P; scen) = χ_meas − χ_gt` | measurement error for representation `P` on scenario `scen` |
| `N_cal, N_eval` | independent random-seed draws for null-band calibration and for evaluation (see §6.1) |

χ_gt is computed on the LATENT state, not on any representation
output. Every metric in §6 references this analytic ground truth,
NOT a representation-space empirical band.

---

## §2. Test architecture

Two disjoint families. Every scenario belongs to exactly one.

**Family E — EXACT (noiseless, deterministic).** Latent PSD is
declared analytically; `χ_gt` is a closed-form number; the only
tolerance permitted is floating-point / numerical-solver tolerance;
no random seeds. An EXACT-family failure is disqualifying with a
tolerance table (§4). EXACT tests verify that the map is
CORRECT AS A MATHEMATICAL OPERATION on ideal inputs.

**Family S — STOCHASTIC (sampled, seeded).** Latent PSD is drawn
from a declared random ensemble with sensor noise; `χ_gt` is still
computed analytically on the LATENT state; measured χ has sampling
variance. Metrics use independent calibration/evaluation draws with
CI-based false-positive control (§6). STOCHASTIC tests characterize
the map's BEHAVIOR UNDER REALISTIC MEASUREMENT NOISE AND NUISANCE.

An EXACT-family failure is disqualifying independent of any
STOCHASTIC-family results. This ordering is deliberate: a
representation that cannot pass exact noiseless tests has no basis
for being characterized under noise.

Family membership per representation is not automatic. E0
(reference-swap null) becomes an EXACT test only for representations
that are analytically reference-invariant (P.LAP is; P.REST is under
declared regularization; P.SRC is under declared inverse). Where
the mapping is analytically reference-dependent, E0 promotes to S0
in Family S with a declared numerical tolerance and CI. Which
family a given (representation, scenario) pair belongs to is fixed
in §4/§5 tables.

---

## §3. Fault list this revision corrects

Numbered so amendment-audit is unambiguous:

| # | Prior charter fault | Correction |
|---|---|---|
| C1 | S0 tested only that the SAME reference applied at both windows produced ≈0 churn. That is a tautology (identity of a fixed function), not a reference-invariance test. | S0 replaced by E0: two DIFFERENT synthetic recording references at t_0 and t_1 both passed through the SAME candidate canonicalization; χ must be within a declared representation-specific tolerance. This is the real reference-swap null. |
| C2 | S1 "uniform amplitude scaling" and S2 "total-power change with unchanged normalized structure" were structurally identical (both reduced to `S(t_1) = c · S(t_0)` for scalar c > 0). | Merged into E1 (exact analytic scalar-scaling null with closed-form ρ identity). No stochastic redundant duplicate. |
| C3 | Null band was defined as the 95th-percentile envelope of measured χ on S8 (a representation-space band), and pass conditions referenced that band, so an oversmoothing representation could pass by driving its own band to zero. | Every metric references ANALYTIC χ_gt computed from the LATENT state. Null band retained only for calibration of `err` CIs, never as the pass criterion. |
| C4 | "100% pairwise ordinal agreement" across P.LAP/P.REST/P.SRC could disqualify a correct representation because a second one was broken. | Removed. Each representation is evaluated INDEPENDENTLY against latent truth. |
| C5 | "Tightest sampling-noise band on S8" was step (b) of the selection tiebreaker and rewarded oversmoothing. | Removed. Tiebreaker replaced by minimum RMSE against χ_gt across the combined test set (§8). |
| C6 | Sensitivity had no minimum floor; a representation with p_null under threshold but negligible signal response could pass. | §6.4 adds a MINIMUM SIGNAL RECOVERY threshold: sensitivity 25%-quantile must exceed 5× null-band 95%-CI upper. |
| C7 | Draws for null-band construction and pass/fail evaluation were the same set (implicit selection bias). | §6.1 mandates independent seeds for `N_cal` (calibration) and `N_eval` (evaluation). |
| C8 | Nuisance ratio, null false-positive rate, and sensitivity were reported as point estimates and compared against fixed thresholds. | Replaced by bootstrap 95% CI comparisons: null false-positive rate is disqualifying only if its 95% CI LOWER bound exceeds 5%; sensitivity floor is met only if its 95% CI LOWER bound exceeds 5× null-band 95%-CI upper. |
| C9 | Latent PSD matrices, ground-truth ρ, and ground-truth χ were never written down. | §4 supplies at least one worked closed-form example per exact test. |
| C10 | Montages, forward/inverse models, parameter grids, seeds, and output paths were labelled "to be pinned" and never pinned. | §7 pins all of them by numeric value. |

---

## §4. Family E — EXACT tests

Every EXACT test is stated with (i) explicit latent construction,
(ii) closed-form ρ, (iii) closed-form χ_gt, (iv) representation-
specific numerical tolerance. Failure of any single EXACT test is
disqualifying for the representation on that test.

### §4.1 E0 — Reference-swap null (mandatory, disqualifying)

Latent construction: `M = 2` unit-orientation radial dipoles at
fixed positions `p_1 = (0, 0, 0.06 m)`, `p_2 = (0.03, 0, 0.05 m)`
inside the pinned 3-shell head model (§7.2). Latent PSD is fixed
analytically as:
```
S_lat(f) = diag(2, 1)   for f in the pinned band F_test = [8, 13] Hz.
```
Time-domain generator: bandpass-limited Gaussian source with the
declared cross-spectrum, propagated through `G`.

Manipulation. Two synthetic recordings are formed from IDENTICAL
scalp potentials `V(t)`:
- Recording A: referenced to Cz.
- Recording B: referenced to linked mastoids.

Both recordings pass through the SAME candidate canonicalization
`P` at both t_0 and t_1 (which are the same window; the "reference
swap" here is between recordings, not between windows). Compute
`ρ_rep_A` and `ρ_rep_B`; compare via χ_meas.

Ground truth: `χ_gt = 0` (identical scalp potentials, identical
canonicalization).

Tolerance table:

| Representation | Family | Tolerance on χ_meas | Rationale |
|---|---|---|---|
| P.LAP | E (exact) | ≤ 1e-10 | Surface Laplacian is analytically reference-independent by construction; only floating-point noise remains |
| P.REST | E (exact) | ≤ 1e-6 | Reference-independent at infinite conditioning; pinned regularization ε_REST introduces a bounded numerical residual |
| P.SRC | E (exact) | ≤ 1e-6 | Reference is absorbed into the inverse; pinned inverse-operator regularization λ_SRC introduces a bounded numerical residual |

**Disqualification.** Any representation whose χ_meas exceeds its
tolerance on E0 is disqualified.

### §4.2 E1 — Scalar-scaling null (mandatory, disqualifying)

Latent construction: same 2-dipole geometry as E0.
```
S_lat(t_0, f) = diag(2, 1);   S_lat(t_1, f) = α · S_lat(t_0, f),  α = 7.0.
```
Analytic identity: `ρ_lat(t_0) = ρ_lat(t_1) = diag(2/3, 1/3)`.
`χ_gt = 0` by trace normalization.

Manipulation: none other than latent PSD amplitude change.

Tolerance: ≤ 1e-12 for all three representations (independent of
representation choice, because ρ_lat is literally invariant).

**Disqualification.** χ_meas > tolerance ⇒ disqualified for the
representation.

### §4.3 E2 — Analytic redistribution (mandatory, disqualifying)

Latent construction: same 2-dipole geometry.
```
S_lat(t_0, f) = diag(1, 3);        ρ_lat(t_0) = diag(1/4, 3/4).
S_lat(t_1, f) = diag(3, 1);        ρ_lat(t_1) = diag(3/4, 1/4).
```
Ground truth:
```
Δρ = diag(−1/2, +1/2);   ‖Δρ‖²_F = 1/2;   χ_gt = 1/4 = 0.25.
```

Manipulation: none other than latent PSD change.

Tolerance:

| Representation | Tolerance | Rationale |
|---|---|---|
| P.LAP | ≤ 1e-6 relative | Non-unitary spatial derivative + spline interpolation introduces a bounded, deterministic mixing that must nevertheless recover the exact χ_gt to 6 sig figs on this noiseless input |
| P.REST | ≤ 1e-6 relative | rREST inverse under fixed λ_REST is deterministic; must match |
| P.SRC | ≤ 1e-4 relative | Inverse-model regularization is looser; wider tolerance permitted |

**Disqualification.** Relative error > tolerance ⇒ disqualified.

### §4.4 E3 — Analytic invariance identities (mandatory, disqualifying)

Three sub-tests, all with closed-form χ_gt:

| ID | Test | χ_gt | Tolerance (all P) |
|---|---|---|---|
| E3.a | Global phase invariance: recording B = e^{iφ} · recording A at both windows, latent identical | 0 | ≤ 1e-14 |
| E3.b | Isometric-embedding invariance: apply Layer-2 charter §3.5 V and V' (two distinct isometries with V†V = V'†V' = I_D); recompute χ on both | equal to χ_gt within numerical tolerance | ≤ 1e-12 relative |
| E3.c | Symmetry: χ(ρ_A, ρ_B) = χ(ρ_B, ρ_A) | proven at Layer 1 (T2); test only for numerical implementation | ≤ 1e-14 |

**Disqualification.** Any E3 sub-test failure ⇒ disqualified. E3.b
in particular verifies that the implementation of V does not silently
break the Layer-2 charter §3.5 Frobenius invariance.

### §4.5 EXACT-family summary table

| ID | Purpose | χ_gt | Failure ⇒ disqualified? |
|---|---|---|---|
| E0 | Reference-swap invariance under same canonicalization | 0 | Yes |
| E1 | Trace-normalization eats scalar amplitude scaling | 0 | Yes |
| E2 | Analytic redistribution recovered to closed-form χ | 0.25 | Yes |
| E3.a | Global-phase invariance | 0 | Yes |
| E3.b | Isometric-embedding invariance | invariant | Yes |
| E3.c | Numerical symmetry | equal | Yes |

---

## §5. Family S — STOCHASTIC scenarios

Every stochastic scenario is stated with (i) latent ensemble,
(ii) sensor-noise model, (iii) analytic χ_gt (per draw or per
ensemble), (iv) evaluation metric with 95% CI.

Draws are seeded per §7.4. Every scenario runs on `N_cal` seeds for
calibration and a DISJOINT `N_eval` seeds for evaluation. Metrics
in §6 always reference `N_eval` for pass/fail; `N_cal` sets any
required null bands and bootstrap parameters only.

### §5.1 S1 — Stochastic scalar-scaling null (characterization)

Purpose: quantify how sampling noise on ρ estimation inflates χ_meas
under the E1 latent (same ρ at both windows). χ_gt = 0 per draw.
Failure not itself disqualifying (E1 already carries the
disqualifying test); S1 provides the null band used to calibrate
false-positive rates for signal scenarios.

### §5.2 S2 — Redistribution signal recovery (mandatory)

Latent ensemble: `S_lat(t_0)` drawn from a Wishart-like distribution
on `M × M` Hermitian PSD, scaled to fixed trace. `S_lat(t_1)` obtained
by unitary conjugation `U_θ · S_lat(t_0) · U_θ^H` where `U_θ` is a
one-parameter Givens rotation with parameter `θ` swept over
`{0.05, 0.10, 0.20, 0.40, 0.80}` radians.

Analytic χ_gt per draw:
`χ_gt(θ) = (1/2) · ‖ρ_lat(t_0) − U_θ ρ_lat(t_0) U_θ^H‖²_F`,
computed on each drawn ρ_lat before any measurement noise.

Metrics: bias `E[χ_meas − χ_gt]`, RMSE, Spearman(θ, χ_meas).
Sensitivity floor per §6.4.

### §5.3 S3 — Band redistribution (mandatory, band-scheme dependent)

Latent ensemble: multiband `S_lat(f)` with power moved between the
pinned bands (δ, θ, α, β, γ; §7.1) at constant total power, with
parameter sweep controlling the fraction moved. χ_gt computed
analytically per draw.

Metrics per §6. Representations that band-collapse in a way that
destroys S3 sensitivity are FLAGGED in output (not disqualified),
because band-collapse is a declared PF operational choice at
Layer-2 charter §3.3.

### §5.4 S4 — Lagged inter-source phase (mandatory)

Latent ensemble: fix marginal auto-spectra; sweep the LAGGED
cross-phase parameter `φ` over `{0, π/8, π/4, π/2}`. χ_gt computed
analytically per draw.

Purpose: verify off-diagonal (imaginary) cross-spectral sensitivity
is preserved end-to-end. Representations that zero out phase (e.g.,
magnitude-only ρ) will fail S4 with high error; flagged, not
disqualified by S4 alone.

### §5.5 S5 — Cross-frequency coupling change (blind-spot documentation)

Latent ensemble: identical marginal within-frequency structure at
both windows; only cross-frequency coupling differs. Under the
Layer-2 charter §3.3 block-diagonal-by-frequency ρ construction,
`χ_gt = 0` (the ρ construction discards the cross-frequency
information). Under a full time-frequency ρ (a §9 alternate),
`χ_gt > 0` computed analytically.

Purpose: document the blind spot the PF construction has by design.
The measured χ_meas must match the ρ-construction-specific χ_gt;
mismatch is a bug (disqualifying implementation-correctness fault),
not a scientific caveat.

### §5.6 S6 — Nuisance suite (mandatory)

Sub-scenarios, each with `L_0 = L_1` at the latent level and only
the nuisance changed between windows. χ_gt = 0 per draw; the
metric is the nuisance ratio `R_nuis` (§6.5).

| ID | Nuisance |
|---|---|
| S6.a | Rigid head rotation: yaw ∈ {2°, 5°, 10°} between windows |
| S6.b | Electrode displacement: fraction ∈ {5%, 10%} of electrodes moved by 5 mm |
| S6.c | Bad-channel replacement: fraction ∈ {5%, 10%} channels marked bad and interpolated |
| S6.d | Instantaneous linear mixing perturbation: independent 5% Frobenius-norm perturbation to G at t_1 only |
| S6.e | Additive artifact: eye-blink template scaled to {1×, 3×} background RMS added to t_1 |

Threshold per §6.5.

### §5.7 S7 — Pure-null controls (calibration)

| ID | Latent | Purpose |
|---|---|---|
| S7.a | Independent white-noise sources at both windows | Baseline null band |
| S7.b | Single deep source projecting broadly (volume-conduction pattern) | Null band under diffuse latent |
| S7.c | No latent source; sensor noise only | Instrument-only null band |

χ_gt = 0 in all three. Used to construct the per-representation
null band under noise for calibration purposes only. Pass/fail is
NOT tested against this band (that is C3); the band is used only to
size CIs and check that the representation is not silently
degenerate.

### §5.8 STOCHASTIC-family summary table

| ID | Family role | χ_gt per draw | Contributes to disqualification via |
|---|---|---|---|
| S1 | Null band (scalar-scaling) | 0 | §6.2 |
| S2 | Signal recovery (redistribution) | analytic per θ | §6.3, §6.4 |
| S3 | Signal recovery (band) | analytic per sweep | §6.3, §6.4 (flag only, per band-collapse note) |
| S4 | Signal recovery (lagged phase) | analytic per φ | §6.3, §6.4 (flag only for magnitude-only ρ) |
| S5 | Blind-spot check (XFC) | 0 for block-diag ρ | §6.6 implementation-correctness |
| S6 | Nuisance robustness (5 sub-scenarios) | 0 | §6.5 |
| S7 | Null-band calibration (3 sub-scenarios) | 0 | Calibration only |

---

## §6. Metrics with CI-based control

All metrics reported per representation independently; no
cross-representation aggregation (C4). All 95% CIs computed by
bootstrap over `N_eval` seeds with `B = 5000` resamples unless
otherwise specified.

### §6.1 Independent draws (C7)

- `N_cal = 2000` seeds: null-band construction, bootstrap
  distribution priors, calibration-only.
- `N_eval = 5000` seeds, drawn from a DISJOINT seed range: all
  pass/fail metrics.
- Seed ranges pinned in §7.4.

### §6.2 Null-band false-positive rate (mandatory, C8 CI form)

For each representation and each null-family stochastic scenario in
{S1, S6.*, S7.*} where χ_gt = 0:
```
p_null(P; scen) = fraction of N_eval draws with χ_meas > χ_gt + margin,
                  margin = null-band 95% CI upper on S7 (per-representation),
p̂_null 95% CI computed by bootstrap.
```
**Disqualification.** For null-family aggregate over S1 + S6 + S7,
if the 95% CI LOWER bound of `p_null` exceeds 5%, the
representation is disqualified. Reporting the point estimate alone
does not trigger disqualification (C8).

### §6.3 Latent-truth error (mandatory, replaces "tightest band")

For every scenario (E-family and S-family alike):
```
err(P; scen, draw) = χ_meas(P; scen, draw) − χ_gt(scen, draw).
```
Reported per scenario:
- Median `err` and 95% CI (bootstrap).
- RMSE of `err` and 95% CI.

The AGGREGATE latent-truth RMSE across the combined
S1 ∪ S2 ∪ S3 ∪ S4 ∪ S6 ∪ S7 test set is used as the primary
representation-quality metric (§8 selection). It penalizes both
false positives (large positive err on null scenarios) AND
oversmoothing (large negative err on signal scenarios). C5.

### §6.4 Sensitivity floor (mandatory, C6)

For each signal-family scenario (S2, S3, S4) and each swept
magnitude:
```
sens(P; scen, magnitude) = median χ_meas(P; scen, magnitude) over N_eval.
```
**Sensitivity floor requirement.** For S2 at the SMALLEST magnitude
sweep point (θ = 0.05 rad), the 95% CI LOWER bound of `sens` must
exceed `5 × (null-band 95% CI upper on S7)`. This binds the
representation to actually detect the smallest scripted signal at a
factor-of-5 SNR margin. Failure ⇒ disqualified as primary
(sensitivity-limited).

S3 and S4 sensitivity are reported but not tied to disqualification
thresholds (band collapse and phase-loss are declared design
choices at Layer-2 charter §3.3, §11).

### §6.5 Nuisance ratio (mandatory, C8 CI form)

For each S6 sub-scenario:
```
R_nuis(P; S6.x) = median χ_meas(P; S6.x) / median sens(P; S2 at θ = 0.20 rad).
```
Reference signal magnitude is fixed at θ = 0.20 rad (mid-sweep) so
the denominator does not drift with representation.

**Disqualification.** For any S6 sub-scenario, if the 95% CI LOWER
bound of `R_nuis` exceeds 0.5, the representation is disqualified.

### §6.6 Implementation-correctness checks (mandatory)

Any deviation from analytic ground truth on E-family tests beyond
the §4 tolerance is an implementation-correctness failure and
blocks any further reporting for that representation. Similarly for
S5 mismatch against ρ-construction-specific χ_gt.

### §6.7 Reported per representation, per scenario

Minimum output columns (§9 manifest for full spec):
`representation, scenario, magnitude_param, N_eval, chi_gt,
median_chi_meas, ci_lo_chi_meas, ci_hi_chi_meas, median_err,
rmse_err, p_null_lo, p_null_hi, R_nuis_lo, R_nuis_hi,
sens_ci_lo, disqualifying_flag`.

---

## §7. Pinned parameters (C10)

All values below are numerical; downstream implementation reads
them as literal constants. Any change requires a labelled amendment
commit per §10.

### §7.1 Frequency bands

```
δ = [0.5, 4.0] Hz
θ = [4.0,  8.0] Hz
α = [8.0, 13.0] Hz     (F_test in §4.1)
β = [13.0, 30.0] Hz
γ = [30.0, 45.0] Hz
```

### §7.2 Head model (forward)

- Geometry: 3-shell concentric spheres.
- Radii (outer): scalp 0.092 m, skull 0.085 m, brain 0.080 m.
- Conductivities (S/m): scalp 0.33, skull 0.0165, brain 0.33.
  (Skull:brain conductivity ratio 1:20 per Oostendorp 2000 style;
  pinned here as literal numbers; primary-source verification is
  NOT claimed by this charter.)
- Dipole positions and orientations per scenario (§4 fixes E-family
  positions; S-family positions drawn per §7.4 seed).

### §7.3 Montages

Three pinned montages; each scenario is run on all three.

| Label | N_ch | Layout |
|---|---|---|
| M19  | 19 | International 10-20 |
| M64  | 64 | Extended 10-10 subset |
| M128 | 128 | Extended 10-5 subset |

### §7.4 Random seeds

- Master seed: `SEED_MASTER = 20260913`.
- Per-scenario seed: `SEED_MASTER + scenario_index`, where
  `scenario_index` is the ordinal position in the §5 table.
- Calibration seeds: `range(SEED_MASTER, SEED_MASTER + N_cal)`.
- Evaluation seeds: `range(SEED_MASTER + 10^6,
  SEED_MASTER + 10^6 + N_eval)`. Disjoint by construction.
- Bootstrap resample seed: `SEED_MASTER + 2·10^6`.

### §7.5 Estimator parameters (LAYER-2 CHARTER-CONSISTENT)

- STFT window: 500 ms Hamming.
- STFT overlap: 50%.
- Super-window: 8 segments, Δt = 2 s (Layer-2 charter §5).
- ε_min: `10^{−12} · median Tr(S)` (Layer-2 charter §3.4).
- Block-diagonal-by-band ρ construction (Layer-2 charter §3.3);
  S5 uses this ρ construction, hence χ_gt = 0 for S5 under this
  spec.

### §7.6 P.LAP parameter grid

- Spline order `m` ∈ {3, 4, 5}.
- Smoothing `λ` ∈ {1e-6, 1e-5, 1e-4}.
- All (m, λ) cells reported. A cell is disqualifying for that
  (m, λ) only, not for P.LAP as a family. P.LAP passes if AT LEAST
  ONE (m, λ) cell passes at each montage.

### §7.7 P.REST parameters

- Method: rREST (Hu-Yao 2018-style) under the pinned 3-shell head
  model (§7.2).
- Regularization ε_REST: {1e-4, 1e-3, 1e-2} (Tikhonov on the
  leadfield SVD).
- Sensor lead field: computed from §7.2 forward model.

### §7.8 P.SRC parameters

- Inverse operators: {sLORETA, LCMV beamformer}. Reported
  separately (`P.SRC.sLORETA`, `P.SRC.LCMV`).
- Inverse regularization λ_SRC: {1e-3, 1e-2, 1e-1} · max singular
  value of the leadfield.
- Source grid: 5-mm cortical grid inside the innermost sphere,
  approximately 5000 candidate sources.
- Forward-model mismatch condition (mandatory characterization):
  ONE additional run per representation with the assumed head-model
  skull conductivity perturbed by ±20% relative. Reported as
  `P.SRC.*.mismatch`.

### §7.9 Draw counts

- `N_cal = 2000`, `N_eval = 5000`.
- Bootstrap resamples `B = 5000`.

### §7.10 Numerical tolerance floors

Applied to all χ_meas outputs before comparison to χ_gt:
- Absolute floor: `1e-14`.
- Relative floor: `1e-12`.

---

## §8. Selection procedure (per representation, no aggregation)

Applied INDEPENDENTLY to each representation `P` in `{P.LAP,
P.REST, P.SRC.sLORETA, P.SRC.LCMV}` (and, for P.LAP, per (m, λ)
cell; for P.REST per ε_REST; for P.SRC per λ_SRC and mismatch
condition).

**Filters (any single failure ⇒ disqualified):**
1. EXACT-family E0, E1, E2, E3.a, E3.b, E3.c all within §4
   tolerance.
2. §6.2 null-family false-positive rate 95% CI LOWER ≤ 5%.
3. §6.5 nuisance ratio 95% CI LOWER ≤ 0.5 for every S6.*.
4. §6.4 sensitivity floor met: S2 at θ = 0.05 rad, 95% CI LOWER
   of median χ_meas ≥ 5 × (S7 null-band 95% CI upper).
5. §6.6 implementation-correctness (E3.b, S5) satisfied.

**Ranking of survivors (per representation, per montage):**
Minimum §6.3 aggregate latent-truth RMSE across
S1 ∪ S2 ∪ S3 ∪ S4 ∪ S6 ∪ S7.

**Global outcome:**
- If ≥ 1 representation survives at ≥ 1 montage: report the
  surviving set; the Layer-2 charter §3.1 provisional primary
  designation is testable against this set.
- If NO representation survives at ANY montage: the χ_k pilot is
  NOT preregistrable under the current Layer-2 charter, and Ring 4
  is reported as OPEN. An amendment to the Layer-2 charter (either
  narrower scientific claim or a different representation catalog)
  is required. No advancement to Ring 5.

No cross-representation aggregation rule. No "100% pairwise
agreement" (C4). No "tightest band" tiebreaker (C5).

---

## §9. Reproducibility manifest

Output artifact per run: single directory
`benchmark_results/YYYY-MM-DD_HHMMSS_<git-sha>/` containing:

| Path | Contents |
|---|---|
| `manifest.json` | git sha of this charter, git sha of any implementation, all §7 pinned values echoed as literals, per-scenario seed ranges, hostname, timestamp, Python / library versions |
| `latent_truth/<scenario>.parquet` | analytic ρ_lat(t_0), ρ_lat(t_1), χ_gt per draw |
| `measured/<representation>/<montage>/<scenario>.parquet` | χ_meas per draw plus intermediate ρ_rep(t_0), ρ_rep(t_1) hashes (not full matrices) |
| `metrics/<representation>/<montage>/<scenario>.json` | all §6.7 columns |
| `selection.json` | per-representation, per-montage: pass/fail per §8 filter, ranking, final disposition |
| `disqualifications.log` | one line per disqualification with (representation, montage, filter, value, bound) |
| `sha256.txt` | sha256 of every emitted file |

Determinism requirement: rerunning with the same manifest MUST
reproduce every parquet and json file byte-for-byte.

Verification requirement: `sha256.txt` MUST be independently
computed post-run and compared against a pre-committed expected-
hash file when the implementation lands.

---

## §10. Governance

- This charter lives on `r331b-provenance`. Master unchanged.
- No Lean, no book, no Layer-3 content is authored under this
  charter.
- Any change to §4 tolerances, §5 scenarios, §6 metrics,
  §7 pinned values, or §8 selection procedure requires a labelled
  amendment commit that (i) identifies the paragraph changed,
  (ii) states the reason, (iii) does NOT touch results or run
  logs. Post-hoc silent threshold changes are prohibited.
- New candidate representations may be added ONLY by amendment
  commit adding a §7.x block, and MUST be evaluated on the same
  scenario set at the same tolerances.

---

## §11. Explicit disclaimer (C10)

Passing this benchmark validates one thing and one thing only:

**The measurement map from the declared synthetic latent-source
family through the declared forward/reference/inverse pipeline into
χ_k recovers the analytic ground-truth χ_gt within calibrated
error, under the pinned montages and estimator parameters.**

Passing does NOT validate:
- The Timeless-Field ontology of Rings 1–2.
- The identification of χ_k on ρ_EEG(t) with any measure of
  consciousness (Ring 5).
- That the biophysical generator of clinical human EEG is
  well-approximated by the pinned 3-shell head model, the pinned
  dipole geometry, or the pinned noise model.
- That any human-pilot preregistration hypothesis is likely to hold.

The benchmark closes Ring 4 for the declared operationalization by
providing a go/no-go verdict on whether EEG → ρ_EEG → χ_k is an
identifiable measurement map under those assumptions. Nothing more.

---

## §12. Cross-references

- Layer-2 charter `codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md`:
  §3.1 (provisional primary/sensitivity designation this benchmark
  exists to test), §3.3 (block-diagonal-by-band ρ; drives S5
  ground-truth), §3.4 (ε_min), §3.5 (isometric-embedding
  invariance; drives E3.b), §5 (χ_k definition), §9 (robustness
  axes), §11 (D1/D2/D3 surrogate constructions), §13 U11–U15
  (load-bearing assumptions this benchmark resolves).
- Bridge audit `codex/CHURN_CHI_K_EEG_BRIDGE_AUDIT_2026-09-13.md`:
  §7 (A/B/C decomposition of the pipeline claim).
- Layer-1 kernel `PF_Lean4_Code/PF/Consciousness/FrobeniusChurn.lean`:
  unchanged; χ_k definition and unitary-invariance theorem used
  here are as proven there. Unitary invariance is NOT invoked to
  protect χ_k from the non-unitary preprocessing under evaluation.
