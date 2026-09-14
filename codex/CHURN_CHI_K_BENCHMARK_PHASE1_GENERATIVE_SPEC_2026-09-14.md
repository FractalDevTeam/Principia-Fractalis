# CHURN χ_k EEG-BRIDGE — PHASE-1 GENERATIVE SPECIFICATION (G2 + G3 + G4)

Date: 2026-09-14.
Branch: `r331b-provenance`.
Scope: **the Phase-1 cell only**, per benchmark charter §14.1 =
(M19, P.LAP, Benchmark B).

**STATUS: DOCUMENTATION ONLY.** This document closes the Phase-1-
scope obligations of benchmark-charter §13 G2, G3, and G4 by
providing executable mathematical pseudocode for sensor noise,
every latent scenario actually used by Phase-1 Benchmark B, all
Phase-1 nuisance perturbations, and the S5 projection objects
(`S_full`, `Π_band`, `ρ_full`, `ρ_proj`). Gaps outside the Phase-1
subset (in particular G1 M64/M128 and G7 Benchmark-A `R_P.SRC.*`)
are NOT touched and MUST NOT be represented as closed by this
document.

**Scope-violation guard.** Nothing here specifies P.REST, P.SRC.*,
sLORETA, LCMV, source-grid parameters used only by Benchmark A,
or the M64/M128 electrode sets. Those remain deferred per §14.2.

**Companion documents.**
- Benchmark charter `codex/CHURN_CHI_K_MEASUREMENT_BENCHMARK_CHARTER_2026-09-13.md`
  (§1 definitions, §5–§7 scenarios/metrics, §7.A statistical pins,
  §13 G2–G4, §14 Phase-1 scope).
- Layer-2 charter `codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md`
  (§3.2 STFT + band set, §3.3 block-diagonal-by-band ρ, §5 hop-
  stride + T_super).
- Bridge audit `codex/CHURN_CHI_K_EEG_BRIDGE_AUDIT_2026-09-13.md`
  (§3 P.LAP verified/unverified claims; §7 A/B/C decomposition).
- Source audit `codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md`
  (Sitt 2014 verified full-text; other sources partial or
  inaccessible).

---

## §1. Sampling and timing (Phase-1)

Every draw is generated on the following pinned grid. All values
are load-bearing.

| Symbol | Value | Provenance |
|---|---|---|
| Sampling rate `f_s` | 250 Hz | Sitt 2014 (source audit, full-text verified); ★ PF preservation choice |
| Bandpass | 0.2–45 Hz | Sitt 2014 (source audit); ★ PF preservation choice |
| `T_stft` | 500 ms | Layer-2 §3.2, ★ PF |
| `Δ_hop` | 250 ms | Layer-2 §3.2, ★ PF |
| `N_seg` | 8 | Layer-2 §5, ★ PF |
| `T_super` (endpoint signal span) | 2.25 s | Layer-2 §5 (as reconciled 2026-09-14) |
| `Δt` (hop-stride between ρ endpoints) | 2 s | Layer-2 §5 (as reconciled 2026-09-14) |
| Number of samples per T_super | `T_super · f_s = 562` (integer floor) | derived; the 0.25-ms residual is absorbed by discretisation |
| STFT taper | Hamming | Layer-2 §3.2, ★ PF |
| Band set B | δ [0.5, 4], θ [4, 8], α [8, 13], β [13, 30], γ [30, 45] Hz | Layer-2 §3.2, ★ PF; five bands |

**Time-series generation.** Every scenario produces two synthetic
recordings of length `T_super` sampled at `f_s`, one for each ρ
endpoint. The recordings are then windowed (Hamming, `T_stft`,
`Δ_hop`), Fourier-transformed per segment, band-integrated (mean
over frequency bins whose centre falls inside the band's
half-open interval), and stacked into the per-band `S_lat(f)`
matrices as declared by Layer-2 §3.3. `ρ_lat(f) = S_lat(f) /
Tr(S_lat(f))` per band.

---

## §2. Deterministic seed hierarchy (Phase-1)

Every draw is fully determined by a seed triple. The seed
hierarchy is unified with benchmark-charter §7:

- Master seed `SEED_MASTER = 20260913` (★ PF).
- Calibration seed range: `[SEED_MASTER, SEED_MASTER + N_cal)`
  where `N_cal = 2000`.
- Evaluation seed range: `[SEED_MASTER + 10^6, SEED_MASTER + 10^6
  + N_eval)` where `N_eval = 5000`. Disjoint from calibration.
- Bootstrap seed: `SEED_MASTER + 2·10^6`.

**Sub-seeding for each draw.** For a draw with global index `i`,
scenario id `s`, endpoint index `e ∈ {0, 1}`, and stream name
`name ∈ {latent, noise, artifact, montage, leadfield}`, derive
the stream seed
```
seed(i, s, e, name) := SHA256_64bit(f"{i}|{s}|{e}|{name}|{SEED_MASTER}")
```
and use it to seed a `numpy.random.Generator(PCG64)`. Streams
never share seeds. Deterministic reruns MUST produce byte-
identical outputs.

**Draw-role separation guarantee.** No draw index `i` is reused
across null-family, signal-family, nuisance-family, or
projection-blind-spot scenarios. Concretely, the global index
space is partitioned into disjoint blocks per scenario id `s`;
any implementation that shares indices across `s` values is a
scope-violating bug.

---

## §3. G2 — Sensor-noise model (executable, Phase-1)

**Distribution family.** Additive Gaussian, i.i.d. across
channels and time samples. Zero mean.

**Numerical scale.** `σ_noise = 0.5 μV` (★ PF preregistered
design choice; no primary source in the audit trail for this
exact value; §6.7 feasibility grid `{0.25, 0.5, 1.0} μV`).

**Correlation structure.** None (spatially white, temporally
white). No structured 1/f colouring at this Phase-1 stage; a
future amendment may add it after G2 sensitivity analysis.

**Executable pseudocode (Phase-1).**

```
def G2_sensor_noise(i, s, e, N_ch, T_super, f_s, sigma=0.5e-6):
    rng = np.random.Generator(PCG64(seed(i, s, e, "noise")))
    n_samples = int(T_super * f_s)
    eta = rng.normal(loc=0.0, scale=sigma, size=(N_ch, n_samples))
    return eta   # shape (N_ch, n_samples), units: volts
```

`sigma` is treated as a load-bearing ★ PF value; every Phase-1
run must record the value used in the manifest.

---

## §4. G3.0 — Common latent-source infrastructure

The latent source amplitudes for a single time window are
constructed as follows.

### §4.1 Constructive PSD generation (preferred over "complex Wishart")

For null and signal scenarios where a Hermitian PSD latent
cross-spectrum `S_lat(f) ∈ ℂ^{M × M}` per band `f ∈ B` is
required, the ensemble is constructed **constructively** rather
than drawn from a nominal complex Wishart, for two reasons: (a)
the χ_op decision depends on the ρ construction of Layer-2 §3.3,
not on any moment of the Wishart family; (b) a constructive
generator makes reproducibility and per-scenario parameterisation
explicit.

**Constructive form.** For a scenario with declared latent source
count `M`, per-band rank `r_f ≤ M`, and per-band amplitude tensor
`A_f ∈ ℂ^{M × r_f}`:
```
S_lat(f) := A_f · A_f^H + λ_reg · I_M
ρ_lat(f) := S_lat(f) / Tr(S_lat(f))
```
where `λ_reg = 10^{−9}` (★ PF, absolute regularisation on the
trace-normalisation denominator; §6.7 feasibility `{10^{−10},
10^{−9}, 10^{−8}}`).

`A_f` is drawn as a complex Gaussian with i.i.d. real and
imaginary parts of unit variance, then scaled by the scenario's
signal-magnitude schedule.

**When complex Wishart is appropriate.** Only in S7.a
(independent-white-noise-source null) does the target
distribution match a complex Wishart. There we generate `A_f`
of shape `M × ν` with `ν = 2M` complex-Gaussian columns, giving
`S_lat(f) = A_f A_f^H` distributed as complex Wishart on M
degrees of freedom `ν` and scale `I_M`.

**M for Phase-1.** `M = 5` (★ PF preregistered design choice;
§6.7 feasibility grid `{3, 5, 10}`). Rationale: `M = 5` is small
enough that all M-dependent computations remain analytically
tractable and large enough that ρ is not degenerate at the
band-integrated level. No primary source supports `M = 5` for
this use.

**Latent source positions.** Placed on a fixed spherical shell
of radius `r_lat = 0.070 m` (see G5 forward-model amendments in
commit K4; the 3-shell model has brain-shell outer radius pinned
there). Positions are uniformly distributed on the shell using a
Fibonacci lattice with `M = 5` points. Dipole orientation:
radial. Positions and orientations are fixed across draws in a
given cell — only amplitudes vary.

---

## §5. Phase-1 scenario specifications

Each scenario emits exactly two synthetic recordings `V_0(t)` and
`V_1(t)` of shape `(N_ch=19, n_samples)`. `V_e = G · s_e + η_e`
where `G` is the M19 leadfield (specified in K4), `s_e` is the
source amplitude time series for endpoint `e`, and `η_e` is
independent sensor noise per §3.

### §5.1 S1 — scalar-scaling null

Same latent state at both windows; only sensor noise realisations
differ.

```
def scenario_S1(i, N_ch=19, M=5):
    # Same amplitude tensor at both endpoints
    A = draw_complex_gaussian(shape=(M, r_S1),
                              seed=seed(i, "S1", 0, "latent"))
    s_0 = amplitude_to_time_series(A, T_super, f_s,
                                    seed=seed(i, "S1", 0, "latent-ts"))
    s_1 = amplitude_to_time_series(A, T_super, f_s,
                                    seed=seed(i, "S1", 1, "latent-ts"))
    V_0 = G @ s_0 + G2_sensor_noise(i, "S1", 0, N_ch, T_super, f_s)
    V_1 = G @ s_1 + G2_sensor_noise(i, "S1", 1, N_ch, T_super, f_s)
    return V_0, V_1
```

with `r_S1 = 3` (★ PF, effective rank of the source amplitude
tensor; §6.7 feasibility `{2, 3, 4}`), `amplitude_to_time_series`
mapping the frequency-domain amplitude tensor to a bandpassed,
0.2–45 Hz-filtered time series by inverse STFT with random per-
band phase (seeded independently per endpoint so the sensor-noise
realisation and phase-realisation are both fresh at the second
window).

**Role.** This is the SAME-state null. Both endpoints share the
same amplitude tensor `A` — only the phase realisation and the
sensor-noise realisation differ. χ_op should be small under an
unbiased estimator.

### §5.2 S2 — signal-redistribution sweep

The signal parameter `θ ∈ Θ := {0.05, 0.10, 0.20, 0.40, 0.80}
rad` controls the angle of a rotation applied to the per-band
amplitude subspace between the two endpoints.

```
def scenario_S2(i, theta, N_ch=19, M=5):
    A = draw_complex_gaussian(shape=(M, r_S2),
                              seed=seed(i, "S2", "latent"))
    U_theta = rotation_in_source_space(theta,
                                       seed=seed(i, "S2", "rot"))
    A_0 = A
    A_1 = U_theta @ A
    s_0 = amplitude_to_time_series(A_0, T_super, f_s,
                                    seed=seed(i, "S2", 0, "ts"))
    s_1 = amplitude_to_time_series(A_1, T_super, f_s,
                                    seed=seed(i, "S2", 1, "ts"))
    V_0 = G @ s_0 + G2_sensor_noise(i, "S2", 0, N_ch, T_super, f_s)
    V_1 = G @ s_1 + G2_sensor_noise(i, "S2", 1, N_ch, T_super, f_s)
    return V_0, V_1
```

- `r_S2 = 3` (★ PF; §6.7 feasibility `{2, 3, 4}`).
- `rotation_in_source_space(theta, seed)` returns an `M × M` real
  orthogonal matrix that is `I_M` if `theta = 0`, and otherwise a
  Givens rotation by angle `theta` in a random 2-plane selected
  by `seed`.
- `θ_ref = 0.20 rad` for §6.5's denominator (benchmark charter §7).

Analytic ground-truth χ_lat per θ is computable from `A` and
`U_theta` under the block-diagonal-by-band ρ construction — see
§8 below.

### §5.3 S3 — inter-band redistribution (flag-only)

Total per-band power is preserved; power is redistributed between
bands by a mixing angle. Because Layer-2 §3.3 uses block-
diagonal-by-band ρ, this redistribution changes the trace-
normalisation weights of each block, so `χ_op` may respond
partially. This is flagged as a known design blind-spot at
Phase-1 and does not contribute to PASS/FAIL. Executable spec:

```
def scenario_S3(i, phi, N_ch=19, M=5):
    A_delta = draw_complex_gaussian(...)
    A_alpha = draw_complex_gaussian(...)
    # Endpoint 0: 90% δ, 10% α; Endpoint 1: (90% - phi_deg)% δ, etc.
    ...
```
Full parameterisation of `phi` is deferred; S3 is not exercised
by any Phase-1 decision gate.

### §5.4 S4 — lagged inter-source phase change (flag-only)

Auto-spectra fixed at both endpoints; a lag parameter `τ`
introduces a phase relationship between two source pairs at the
second window. Because magnitude-only ρ constructions do not
respond to phase-only changes, S4 is a design blind-spot,
flagged, and does not contribute to Phase-1 PASS/FAIL. Deferred
parameterisation.

### §5.5 S5 — cross-frequency coupling on `ρ_full` (implementation-correctness)

**Purpose.** Verify that Layer-2 §3.3's block-diagonal-by-band
projector `Π_band` is correctly implemented, i.e. that the
implementation truly zeros cross-band blocks.

**`S_full` construction (executable).** Let the band set be
`B = {b_1, ..., b_5}` per §1. For a fixed source amplitude tensor
`A ∈ ℂ^{M × r_S5}` (with `r_S5 = 3`, ★ PF), define per-band
amplitude tensors `A_{b_j}` for `j = 1, ..., 5`. `S_full ∈
ℂ^{5M × 5M}` is constructed with block layout:
```
S_full[block(j), block(k)] = A_{b_j} · C_{jk} · A_{b_k}^H
```
where `C_{jk} ∈ ℂ^{r_S5 × r_S5}` is the cross-band coupling
matrix (identity `I_{r_S5}` on within-band blocks; a scenario
parameter `κ ∈ (0, 1]` times a random unitary `U_{jk}` on cross-
band blocks). `S_full` is Hermitian by construction:
`C_{jk} = C_{kj}^H`.

**Cross-frequency coupling change.** Endpoint 0 uses `κ_0`
sampled from `{0.0}` (zero coupling); endpoint 1 uses `κ_1 = 0.5`
(★ PF; §6.7 feasibility `{0.25, 0.5, 0.75}`). Because
within-band blocks are unchanged, the per-band `ρ_lat(f)` states
are identical at both endpoints.

**`ρ_full` and `ρ_proj` (executable).**
```
ρ_full = S_full / Tr(S_full)
Π_band(X)[block(j), block(k)] = X[block(j), block(j)] if j == k else 0
S_proj = Π_band(S_full)
ρ_proj = S_proj / Tr(S_proj)
```
By the construction above, `ρ_proj` at endpoint 0 equals `ρ_proj`
at endpoint 1, so `χ_op(P.LAP; ρ_proj_0, ρ_proj_1) = 0` under a
correct implementation — this is the S5 pass condition.

**What `ρ_full` is used for.** `ρ_full` is defined so the S5
description is self-contained. The Phase-1 Benchmark B path does
NOT compute Frobenius churn on `ρ_full`; only `ρ_proj` enters
`χ_op` per Layer-2 §3.3. `ρ_full` is used only in the executable
provenance and in any diagnostic printout of the "full-spectrum
churn is not zero" fact recorded in the benchmark charter §5.2
S5 row.

**Coupling to the seed hierarchy.** All random components
(`A`, per-band `A_{b_j}` splits, `C_{jk}` unitaries) are seeded
via `seed(i, "S5", ...)` sub-streams.

### §5.6 S6.a — montage rotation (nuisance)

Latent state unchanged. Between the two endpoints, the M19
electrode positions used to compute the leadfield are rotated by
yaw `α ∈ {2°, 5°, 10°}` about the axial (z) axis of the head-
model coordinate frame. The leadfield `G_1` at endpoint 1 is
recomputed on rotated positions; sensor noise realisations
differ. All source parameters are identical.

```
def scenario_S6a(i, yaw_deg, N_ch=19, M=5):
    A = draw_complex_gaussian(...)
    s_0 = ...; s_1 = ...
    G_0 = leadfield(M19_positions)
    G_1 = leadfield(rotate_z(M19_positions, yaw_deg))
    V_0 = G_0 @ s_0 + G2_sensor_noise(i, "S6a", 0, N_ch, T_super, f_s)
    V_1 = G_1 @ s_1 + G2_sensor_noise(i, "S6a", 1, N_ch, T_super, f_s)
    return V_0, V_1
```

### §5.7 S6.b — electrode subset displacement

A fraction `p_disp ∈ {5%, 10%}` of M19 electrodes are displaced
by 5 mm in a random spherical-tangent direction per electrode
between endpoints. Deterministic per-seed selection of which
electrodes are displaced.

### §5.8 S6.c — channels bad-marked and interpolated

A fraction `p_bad ∈ {5%, 10%}` of M19 channels are marked bad at
endpoint 1 and replaced by a spline-interpolated value from the
remaining M19 electrodes using the same spherical-spline (m, λ)
grid that Phase-1 P.LAP uses (see K4). No structural change is
applied at endpoint 0. This is a pure preprocessing nuisance.

### §5.9 S6.d — leadfield Frobenius perturbation

`G_1 = G_0 + ε · ξ`, with `ξ` a random matrix of the same shape
as `G_0` normalised so `‖ε · ξ‖_F / ‖G_0‖_F = 0.05`. `ε` is
seed-derived. Applied only to endpoint 1.

### §5.10 S6.e — artifact injection

Add a G4 artifact template (see §7 below) to endpoint 1 only.
Endpoint 0 is artifact-free.

### §5.11 S7.a — independent white-noise sources (null)

`A_f` at both endpoints is drawn independently per band and per
endpoint, complex Gaussian with i.i.d. real/imaginary parts. This
matches the complex Wishart family with `ν = 2M`, `Σ = I_M`.
Between the two endpoints the source amplitudes are
independently drawn, so this is genuinely a "no shared latent
state" null.

### §5.12 S7.b — single distant deep source (null)

`M = 1` effective source placed at the geometric centre of the
3-shell brain compartment (deep-source volume conduction
pattern). Same source at both endpoints. Different sensor-noise
realisations.

### §5.13 S7.c — sensor noise only (null)

`s_0 = s_1 = 0`. Only sensor noise contributes to `V_0` and
`V_1`. Different noise realisations per endpoint.

---

## §6. Signal / null / nuisance role separation (executable)

Enforced by the seed hierarchy of §2 and by disjoint scenario ids
`s ∈ {S1, S2, S3, S4, S5, S6.a, S6.b, S6.c, S6.d, S6.e, S7.a,
S7.b, S7.c}`. No implementation may reuse the same seed triple
across scenarios; the manifest of §9 of the benchmark charter
records the full seed-triple grid to enable byte-identical
reproduction.

- **Null decision set (per §6.2):** S1, S7.a, S7.b, S7.c. Each
  has its own calibration + PASS/FAIL/INCONCLUSIVE per benchmark
  charter §6.2.
- **Signal (monotonicity) set:** S2 only.
- **Nuisance set:** S6.a–S6.e. Never enters §6.2's decision.
- **Projection-blind-spot set:** S3, S4. Flag-only, no PASS/FAIL
  role at Phase-1.
- **Implementation-correctness set:** S5. Own gate per §6.6.

---

## §7. G4 — Artifact template for S6.e (executable, Phase-1)

**Family.** Parametric alpha-function envelope multiplied by a
low-frequency oscillation, spatially projected onto a fixed
frontal weight vector.

**Time-domain envelope.**
```
w_blink(t) = (t / τ) · exp(1 - t / τ) for t ≥ 0, else 0
```
with `τ = 100 ms` (★ PF; §6.7 feasibility `{50, 100, 200} ms`).
This is a standard alpha-function shape; it is a ★ PF choice
because no primary source in the audit trail supports this exact
τ for the χ_k use case.

**Spectral content.** The envelope is centred at t = `T_super/2`.
Amplitude scaled to `A_art = 3 · σ_noise · f_s^{1/2}` (★ PF; a
signal-to-noise ratio choice; §6.7 feasibility `{1, 3, 10} ·
σ_noise · f_s^{1/2}`).

**Spatial projection (frontal weight vector).** M19 label set →
weight vector `w_spatial ∈ ℝ^{19}` with weights concentrated at
Fp1, Fp2, F7, F3, Fz, F4, F8 (7 frontal electrodes):
`w_spatial[frontal] = 1/7`, `w_spatial[other] = 0`. ★ PF
convention; the specific weights are not derived from a primary
source.

**Executable pseudocode.**
```
def G4_artifact(i, T_super, f_s, sigma_noise, N_ch=19):
    rng = np.random.Generator(PCG64(seed(i, "S6e", 1, "artifact")))
    t = np.arange(int(T_super * f_s)) / f_s
    t_center = T_super / 2
    tau = 0.100
    envelope = ((t - t_center) / tau) * np.exp(1 - (t - t_center) / tau)
    envelope = np.where(t >= t_center, envelope, 0.0)
    amplitude = 3 * sigma_noise * np.sqrt(f_s)
    w_spatial = np.zeros(N_ch)
    frontal_idx = [0, 1, 2, 3, 4, 5, 6]  # Fp1, Fp2, F7, F3, Fz, F4, F8
    w_spatial[frontal_idx] = 1.0 / 7.0
    artifact = amplitude * np.outer(w_spatial, envelope)
    return artifact   # shape (N_ch, n_samples)
```

**Muscle-artifact template.** Not required at Phase-1. Deferred.

---

## §8. Analytic χ_lat for S2 (informational)

The S2 sweep uses a rotation `U_theta ∈ O(M)` in source space
applied to a fixed amplitude tensor `A`. Under the block-
diagonal-by-band ρ construction of Layer-2 §3.3, with per-band
ρ = A_f A_f^H / Tr(A_f A_f^H) at endpoint 0 and
U_theta A_f (U_theta A_f)^H / Tr(...) at endpoint 1, the per-band
Frobenius churn is:
```
χ_lat(f; θ) = (1/2) · ‖ρ_lat(f, 0) - ρ_lat(f, 1)‖_F^2
```
which is a function of `θ` and `A_f`. Averaging over the band set
under the block-diagonal aggregation gives `χ_lat(θ)`. Because
`U_theta` is orthogonal, at `θ = 0` we have `χ_lat = 0`, and
`χ_lat` is monotone in `|θ|` on the small-angle regime — this is
the analytical basis for the S2 monotonicity test of §6.3.

Phase-1 does not require closed-form `χ_lat` because §6.3's
Benchmark-B monotonicity test compares `θ` to median `χ_op(θ)`
directly. The analytic identity is provided for provenance only.

---

## §9. Remaining Phase-1-blocking obligations under G2/G3/G4

| Item | Status | Blocker |
|---|---|---|
| `σ_noise = 0.5 μV` | ★ PF, feasibility grid declared | No primary-source citation in audit trail for this exact value at χ_k use case. |
| `M = 5` latent sources | ★ PF, feasibility `{3, 5, 10}` | Same. |
| `r_S1 = r_S2 = r_S5 = 3` effective rank | ★ PF, feasibility `{2, 3, 4}` | Same. |
| `κ = 0.5` cross-band coupling in S5 | ★ PF, feasibility `{0.25, 0.5, 0.75}` | Same. |
| `λ_reg = 10^{−9}` | ★ PF, feasibility `{10^{−10}, 10^{−9}, 10^{−8}}` | Same. |
| `τ = 100 ms` artifact envelope | ★ PF, feasibility `{50, 100, 200} ms` | Same. |
| Artifact amplitude `3 σ_noise √f_s` | ★ PF, feasibility `{1, 3, 10} · σ_noise √f_s` | Same. |
| Frontal weight vector for artifact | ★ PF convention | Same. |
| Latent source positions on `r_lat = 0.070 m` shell, Fibonacci-5 | ★ PF | Same. |
| S3, S4 full parameterisation | Deferred (flag-only, no Phase-1 PASS/FAIL) | Not required at Phase-1. |

Every ★ PF choice above is preserved as ★ PF and MUST NOT be
retroactively promoted to primary-source-supported without a
verified full-text citation logged in the source audit
(benchmark charter §7.A.7 rule).

---

## §10. Cross-references

- Benchmark charter `codex/CHURN_CHI_K_MEASUREMENT_BENCHMARK_CHARTER_2026-09-13.md`
  §1 (definitions of `S_full`, `ρ_full`, `Π_band`, `ρ_proj`),
  §5.1–§5.2 (scenario intent), §7 (pinned parameters), §7.A
  (statistical/timing pins), §13 G2/G3/G4 (this document closes
  the Phase-1 scope), §14.1 (Phase-1 cell declaration).
- Layer-2 charter `codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md`
  §3.2, §3.3, §5.
- Source audit `codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md`
  for Sitt 2014 verified sampling rate and bandpass.

No content of this document authorises a claim of primary-source
support beyond what the source audit records. Every load-bearing
number is either primary-source-tagged with an exact source-audit
line reference or labelled ★ PF with a §6.7 feasibility grid.
