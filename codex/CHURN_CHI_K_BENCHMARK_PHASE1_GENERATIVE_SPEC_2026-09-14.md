# CHURN χ_k EEG-BRIDGE — PHASE-1 EXECUTABLE SPECIFICATION (G2 + G3 + G4 + G5 + G6-P.LAP)

Date: 2026-09-14. Original title
"PHASE-1 GENERATIVE SPECIFICATION (G2 + G3 + G4)" retained in the
K3 commit provenance; K4 broadens the scope to include Phase-1-
restricted G5 (forward-model geometry) and G6-P.LAP (P.LAP
algorithm). Filename unchanged for K3 provenance continuity.

Branch: `r331b-provenance`.
Scope: **the Phase-1 cell only**, per benchmark charter §14.1 =
(M19, P.LAP, Benchmark B).

**STATUS: DOCUMENTATION ONLY.** This document closes the Phase-1-
scope obligations of benchmark-charter §13 G2, G3, G4 (K3
commit), and — with two named blockers — G5 (Phase-1 restricted
to P.LAP-adjacent geometry) and G6 (Phase-1 restricted to
P.LAP; sLORETA/LCMV deferred) via K4. Gaps outside the Phase-1
subset (in particular G1 M64/M128, G7 Benchmark-A `R_P.SRC.*`,
and the sLORETA/LCMV portions of G6) are NOT touched and MUST
NOT be represented as closed by this document.

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

## §10. Cross-references (Phase-1 G2/G3/G4 scope)

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

---

## §11. G5 — Phase-1 forward-model geometry (executable, restricted)

Closes the Phase-1-scope obligations of benchmark-charter §13 G5
for the (M19, P.LAP, Benchmark B) cell. Only geometry,
conductivities, and the P.LAP-adjacent scalp-potential generation
are addressed; source-grid parameters used only by Benchmark A
(`R_P.SRC.*`) remain deferred per §14.1 and §14.2.

### §11.1 M19 electrode coordinates — PF spherical convention

**Load-bearing honesty note.** The International 10-20 system
(Jasper 1958, as re-standardised by the American EEG Society
Guideline 1994) specifies electrode positions **topographically**,
as percentages of the four skull landmarks (nasion, inion, left
and right preauricular points). It does NOT specify exact 3D
Cartesian coordinates on a specific spherical or realistic head
model — a mapping convention is required. Software vendors
(FieldTrip `elec1005.mat`, MNE-Python `standard_1020`, EEGLAB
built-in coords, Brainstorm defaults) each publish their own
mapping conventions, which differ at millimetre level.

**No such vendor file has been verified full-text in the source
audit for this branch.** Therefore Phase-1 declares its own
mapping and labels it ★ PF preregistered design choice. Any
future amendment claiming primary-source support for the M19
coordinates MUST record a full-text citation in the source audit.

**PF spherical M19 convention (★ PF).** Coordinates given in
spherical `(θ_zen, φ_az)` on a unit sphere, with `θ_zen` measured
from the +z (vertex) axis and `φ_az` measured from the +x axis
in the x-y plane, right-handed, x toward nasion, y toward left
preauricular. To convert to Cartesian on the scalp shell of
radius `r_scalp` (§11.2), multiply by `r_scalp`.

| Label | θ_zen (deg) | φ_az (deg) |
|---|---|---|
| Fp1 | 72 | 108 |
| Fp2 | 72 | 72 |
| F7 | 72 | 144 |
| F3 | 51 | 129 |
| Fz | 45 | 90 |
| F4 | 51 | 51 |
| F8 | 72 | 36 |
| T3 | 90 | 180 |
| C3 | 45 | 180 |
| Cz | 0 | 0 (degenerate — placed at +z axis) |
| C4 | 45 | 0 |
| T4 | 90 | 0 |
| T5 | 108 | 144 |
| P3 | 51 | 231 |
| Pz | 45 | 270 |
| P4 | 51 | 309 |
| T6 | 108 | 36 |
| O1 | 108 | 252 |
| O2 | 108 | 288 |

This table is a ★ PF convention that reproduces the 10-20
topographic ordering (frontal/central/parietal/occipital rows;
midline column at φ_az ∈ {90°, 0°/degenerate, 270°}; left/right
symmetry). It is NOT claimed to match any vendor file. Any
consumer of Phase-1 outputs comparing to physical EEG must
declare its own coordinate convention and note the mismatch.

**Sensitivity.** The §6.7 sensitivity grid does NOT vary M19
coordinates; a mismatch at the millimetre level is fully absorbed
into the S6.a montage-rotation and S6.b electrode-displacement
nuisance scenarios by construction.

### §11.2 Three-shell head model — radii and conductivities

**Load-bearing honesty note.** Canonical three-shell radii and
conductivities (brain / skull / scalp) appear in Rush & Driscoll
1968, Berg & Scherg 1994, and Nunez & Srinivasan 2006, among
others. None of these papers has been verified full-text in the
source audit for this branch. Skull:brain conductivity ratios in
the literature span 1:15 to 1:80 with the modern literature
converging near 1:20 to 1:50; the source audit does not adjudicate
this. Phase-1 therefore declares:

| Parameter | Value | Status |
|---|---|---|
| Scalp outer radius `r_scalp` | 0.092 m | ★ PF (nominal adult head; no primary source verified) |
| Skull outer radius `r_skull` | 0.086 m | ★ PF |
| Brain outer radius `r_brain` | 0.080 m | ★ PF |
| Scalp conductivity | 0.33 S/m | ★ PF (nominal saline-like value widely cited but not verified in source audit for this exact use) |
| Skull conductivity | 0.0165 S/m | ★ PF (skull:brain ratio 1:20, one of the widely cited values; not verified) |
| Brain conductivity | 0.33 S/m | ★ PF |

**§6.7 sensitivity grid.**
- Radii: `× {0.95, 1.0, 1.05}` on each of r_scalp, r_skull,
  r_brain (nested-shell constraint `r_brain < r_skull <
  r_scalp` must hold; grid points violating it are discarded).
- Conductivity ratios: skull:brain ∈ `{1:15, 1:20, 1:50}` at
  fixed brain and scalp conductivities.

Every one of these is a Phase-1-blocking obligation ONLY at the
level of "each value must have either a verified primary source
in the source audit, or a ★ PF label with the feasibility grid
above." Phase-1 opts for the ★ PF path for every row above; no
row is claimed to be primary-source-supported.

### §11.3 Latent source shell

Latent sources placed on a fixed spherical shell of radius
`r_lat = 0.070 m` (★ PF; §6.7 feasibility `{0.060, 0.070, 0.075}
m`, all strictly inside `r_brain`). Fibonacci-`M` lattice with
`M = 5` points; positions and orientations fixed across draws in
a given cell.

Dipole orientations: **radial** (pointing outward along the
source's radial direction from head-model origin). Tangential
dipoles are NOT modelled at Phase-1; they remain a G5 amendment
obligation for future cells.

### §11.4 Leadfield `G` (M19 × M) — analytical form

**K5 amendment (2026-09-14) — mis-attribution correction.** The
K4 wording of this section attributed a schematic Legendre series
to Berg-Scherg 1994 and Rush-Driscoll 1968. That attribution was
WRONG on two counts: (1) Berg-Scherg 1994 is a **fast-computation
approximation** (three homogeneous-sphere dipoles reproducing a
multishell dipole potential), NOT the primary source for the
analytical Legendre-series multishell EEG solution. (2) Rush &
Driscoll's original three-sphere work (their 1968/1969 papers) is
an important predecessor but is not the compact multishell series
now standard in the literature. The correct primary source for the
analytical Legendre-polynomial multishell EEG series is Zhang
(1995) *Phys Med Biol* 40(3):335–349, extending de Munck (1988)
*J Appl Phys* 64:464–470. Both remain paywalled at IOPscience and
the AIP publisher respectively; see source audit §7.2.

**Executable form (corrected to the Zhang 1995 / Mosher-Leahy-Lewis
1999 kernel form).** For a dipole with moment `q` located at
`r_q` inside the innermost shell of an M-shell concentric-sphere
head model with conductivities `σ_1, ..., σ_M` and radii
`r_1 < r_2 < ... < r_M`, the scalp potential at observation point
`r` (on the outer shell) is:

```
v^M(r; r_q, q) = (q / (4π σ_M r²)) · Σ_{n=1}^{∞} ((2n+1)/n)
              · (r_q / r)^{n−1}
              · f_n
              · ( n · cos α · P_n(cos γ) + cos β · sin α · P_n^1(cos γ) )
```

where
- `P_n` is the Legendre polynomial of order `n` and `P_n^1` is
  the associated Legendre polynomial (radial-dipole vs
  tangential-dipole angular structure);
- `α` is the angle between `q` and the radial direction at `r_q`
  (so `q_r = q cos α` is the radial dipole component and
  `q_t = q sin α` is the tangential component);
- `γ` is the angle between `r_q` and `r`;
- `β` is the angle between the plane `(r_q, q)` and the plane
  `(r_q, r)`;
- `f_n = n / (n · m_22 + (n+1) · m_21)` (Mosher-Leahy-Lewis Eq. 16);
- `[m_11, m_12; m_21, m_22]` is the 2×2 shell-recursion matrix
  from Mosher-Leahy-Lewis Eq. (17), a non-commuting product over
  `M−1` boundaries with the highest-index matrix applied first:
  ```
  [m_11 m_12]                          M-1  [ n + (n+1)σ_k/σ_{k+1}                (n+1)(σ_k/σ_{k+1} − 1)(r_q/r_k)^{2n+1} ]
  [         ] = (1/(2n+1)^{M-1}) · Π k=1   [                                                                              ]
  [m_21 m_22]                              [ n(σ_k/σ_{k+1} − 1)(r_k/r_q)^{2n+1}   (n+1) + n σ_k/σ_{k+1}                    ]
  ```

For M = 3 (brain, skull, scalp), the product has two matrix
factors (`k = 1` and `k = 2`) and the outermost conductivity
`σ_M = σ_scalp` appears in the normalisation.

**Provenance of this equation form.** Transcribed verbatim from
Mosher, Leahy & Lewis 1999 *IEEE Trans. Biomed. Eng.* 46(3):245–
259, equations (15)–(17) on page 248, PDF openly accessible at
https://neuroimage.usc.edu/paperspdf/IEEEBME99.pdf. Mosher-Leahy-
Lewis attribute the compact series form to Zhang 1995
(reference [52] in their paper), which is the PRIMARY source and
remains paywalled and unverified full-text on this branch (source
audit §7.2). Mosher-Leahy-Lewis is an AUTHORITATIVE CROSS-CHECK
but not primary provenance for Phase-1 §14 blocker-closure
purposes.

**Truncation.** `N_trunc = 40` (★ PF; §6.7 feasibility grid
`{20, 40, 80}`). Convergence at Phase-1 spatial scales must be
verified at implementation time against this grid.

**Berg-Scherg 1994 fast approximation (RECORDED for future
Benchmark-A cells; NOT used at Phase-1).** Mosher-Leahy-Lewis
Eq. (18): `v^M ≈ v^1(r; μ_1 r_q, λ_1 q) + v^1(r; μ_2 r_q, λ_2 q)
+ v^1(r; μ_3 r_q, λ_3 q)`, three single-shell evaluations at
scaled dipole locations and moments (the "Berg parameters"
`{μ_i, λ_i}`, tabulated in Mosher-Leahy-Lewis [3] = Berg-Scherg
1994 and [52] = Zhang 1995). This approximation is NOT used by
the Phase-1 (M19, P.LAP, Benchmark B) cell — Phase-1 uses the
exact truncated series above.

**PHASE-1-BLOCKING OBLIGATION (updated at K5).** Implementation of
this leadfield form still requires primary-source verification of
Zhang 1995 (or de Munck 1988) with the exact form of Eq. (15)–
(17) quoted verbatim in the source audit. Alternative
resolutions:
(a) direct access to Zhang 1995 primary full text;
(b) a numerical BEM implementation with fully pinned library and
    version, whose output is regression-tested against
    Mosher-Leahy-Lewis Eq. (15)–(17) evaluated at a fixed set of
    test dipole configurations, with agreement at machine
    precision on radial dipoles and at declared tolerance on
    tangential dipoles;
(c) an alternative primary source that independently derives the
    same closed form (e.g., de Munck 1988; Cuffin & Cohen 1979).

Pending this blocker, no Phase-1 implementation may run. The
equations above are conditional on that resolution. The K5
cross-check via Mosher-Leahy-Lewis 1999 downgrades the severity
of the blocker (the equations are now anchored in an accessible
peer-reviewed IEEE journal article) but does NOT close it.

---

## §12. G6 — P.LAP algorithm (executable, restricted)

Closes the Phase-1-scope obligations of benchmark-charter §13 G6
for the (M19, P.LAP, Benchmark B) cell. sLORETA and LCMV
specifications remain deferred per §14.1 and MUST NOT be
represented as completed by Phase-1.

### §12.1 P.LAP algorithm — spherical-spline surface Laplacian

**Family.** Spherical-spline surface Laplacian per Perrin et al.
1989 with regularisation and spline-order parameters per
Tenke & Kayser 2015. Neither Perrin 1989 nor Tenke & Kayser 2015
is verified full-text in the source audit for this branch; the
bridge audit records secondary quotations from Tenke & Kayser
2015 (reference-independence, sensitivity to spline flexibility)
that support the choice of spherical-spline family, but does NOT
supply the primary equation forms. Phase-1 therefore uses the
general form as documented across the CSD literature and flags
each primary-equation dependency as a Phase-1-blocking obligation
requiring source-audit verification before implementation.

**K5 amendment (2026-09-14) — cross-check without closure.** An
authoritative arXiv preprint (Carvalhaes CG & de Barros JAdB, *The
Surface Laplacian Technique in EEG: Theory and Methods*,
arXiv:1406.0458v2, Nov 8, 2014, openly accessible at
https://arxiv.org/pdf/1406.0458) independently reproduces the
Perrin 1989 spherical-spline construction with clear attribution
to Perrin et al. 1989. The kernels defined in §12.2 below MATCH
Carvalhaes-de Barros Eq. (33a), (33b), and (36) as follows:
- Eq. (33a) p. 17: `f_sph(r) = Σ c_i g_m(r, r_i) + d`.
- Eq. (33b) p. 18: `g_m(r, r_i) = (1/(4π)) Σ_{ℓ=1}^{∞}
  ((2ℓ+1)/(ℓ^m(ℓ+1)^m)) P_ℓ(r̂ · r̂_i)`.
- Eq. (36) p. 18: `Lap_s(f(r)) = -(1/r²) Σ c_i g_{m-1}(r, r_i)`
  for `m > 1`.

The §12.2 `g_m` matches Eq. (33b) exactly. The §12.2 `h_m` is
algebraically equal to `-(1/r_scalp²) · g_{m-1}` (since
`n(n+1)/(n^m(n+1)^m) = 1/(n^{m-1}(n+1)^{m-1})`), matching
Eq. (36).

Carvalhaes-de Barros 2014 is a REVIEW paper and IS NOT PRIMARY
PROVENANCE for Perrin's equations. This cross-check downgrades
the severity of Blocker A but does NOT close it. See source audit
§7.1 for the full access-attempt log and rule preservation.

### §12.2 P.LAP — mathematical form (executable pseudocode)

Given:
- Electrode positions `x_i ∈ ℝ^3`, `i = 1, ..., N_ch = 19`, on
  the scalp shell of radius `r_scalp` (§11.2).
- Scalp potentials `V_i(t) ∈ ℝ`.
- Spline order `m ∈ {3, 4, 5}` (benchmark charter §7 ★ PF grid).
- Regularisation parameter `λ ∈ {10^{-6}, 10^{-5}, 10^{-4}}`
  (benchmark charter §7 ★ PF grid).

Step 1 — geodesic angles between electrodes:
```
cos γ_{ij} = (x_i · x_j) / (‖x_i‖ · ‖x_j‖),   i, j = 1..N_ch
```

Step 2 — spherical-spline kernel `g_m(cos γ)`:
```
g_m(cos γ) = (1 / (4π)) · sum_{n=1}^{N_g_trunc}
             ((2n + 1) / (n^m · (n + 1)^m)) · P_n(cos γ)
```
with `N_g_trunc = 50` (★ PF; §6.7 feasibility `{25, 50, 100}`).
This is the canonical form of the spline kernel documented in the
Perrin 1989 spherical-spline construction; the primary-source
verification is a Phase-1-blocking obligation.

Step 3 — assemble `N_ch × N_ch` kernel matrix `K_m[i, j] =
g_m(cos γ_{ij})` and add regularisation:
```
K_m_reg = K_m + λ · I_{N_ch}
```

Step 4 — spline coefficients:
```
c(t) = K_m_reg^{-1} · V(t)     ∈ ℝ^{N_ch}
```
where `V(t) = (V_1(t), ..., V_{N_ch}(t))^T`.

Step 5 — surface Laplacian kernel `h_m(cos γ)`:
```
h_m(cos γ) = -(1 / (4π · r_scalp^2)) · sum_{n=1}^{N_h_trunc}
              ((2n + 1) · n · (n + 1) / (n^m · (n + 1)^m))
              · P_n(cos γ)
```
with `N_h_trunc = 50` (★ PF; §6.7 feasibility `{25, 50, 100}`).
The `n(n+1)/r_scalp^2` factor is the eigenvalue of the spherical
Laplacian for order-`n` spherical harmonics on a sphere of
radius `r_scalp`; this is a standard result. Primary-source
verification of the Perrin 1989 exact coefficient is a
Phase-1-blocking obligation.

Step 6 — evaluate surface Laplacian at each electrode:
```
Lap V(x_i, t) = sum_{j=1}^{N_ch} h_m(cos γ_{ij}) · c_j(t)
```
so `Lap V(t) = H_m · K_m_reg^{-1} · V(t)`, where `H_m[i, j] =
h_m(cos γ_{ij})`. Define the P.LAP operator:
```
A_{LAP}(m, λ) := H_m · (K_m + λ · I_{N_ch})^{-1}
```
`A_{LAP}` is an `N_ch × N_ch` fixed matrix that depends on
(m, λ) and on the electrode geometry only. It is FIXED across
draws (no data-dependent regularisation), which satisfies the
scale-equivariance condition of benchmark charter §7.A.6 for E1
in Phase-1.

### §12.3 Reference handling

P.LAP is reference-independent by construction: applying `A_{LAP}`
to `V(t) + c · 1` (with `1` the all-ones vector) gives
`A_{LAP} · (V + c · 1) = A_{LAP} · V + c · A_{LAP} · 1`, and
`A_{LAP} · 1 = 0` by the structure of the surface-Laplacian
kernel on a closed sphere (the constant function has zero
Laplacian). This is the Layer-2 §3.1 reference-freedom claim,
sourced to Tenke & Kayser 2015 in the bridge audit. Phase-1
implementation MUST verify `‖A_{LAP} · 1‖_∞ ≤ 10^{-10}` as a
build-time check.

### §12.4 Cross-spectral estimator (from P.LAP output)

Given P.LAP output `X(t) = A_{LAP} · V(t) ∈ ℝ^{N_ch}` sampled at
`f_s = 250 Hz` (§1), the per-band cross-spectrum is computed by
Welch's method with the Layer-2 §3.2 STFT parameters
(T_stft = 500 ms Hamming, Δ_hop = 250 ms 50% overlap, FFT length
next power of 2 ≥ window samples):

```
For each STFT segment k = 1, ..., N_seg:
    Y_k(f) = FFT(w_Hamming * X(segment k))       # (N_ch, N_freq)
For each band b ∈ B:
    F_b = { frequency bins whose centre ∈ b }
    S_b = (1 / N_seg) · sum_k mean_{f ∈ F_b} [Y_k(f) · Y_k(f)^H]
```
`S_b ∈ ℂ^{N_ch × N_ch}` is Hermitian PSD. Trace-normalise per
band:
```
ρ_b = S_b / Tr(S_b)     if Tr(S_b) > ε_min · median_b Tr(S_b);
      UNDEFINED         otherwise
```
with `ε_min = 10^{-12}` per Layer-2 §3.4 (★ PF).

The block-diagonal-by-band ρ per Layer-2 §3.3:
```
ρ_full_op = block_diag(ρ_δ, ρ_θ, ρ_α, ρ_β, ρ_γ) ∈ ℂ^{D × D}
```
with `D = N_ch · |B| = 19 · 5 = 95`. This is the Benchmark-B
operational ρ.

### §12.5 Channel ordering and feature ordering

Channel ordering follows the M19 label list of benchmark charter
§7 verbatim: `[Fp1, Fp2, F7, F3, Fz, F4, F8, T3, C3, Cz, C4, T4,
T5, P3, Pz, P4, T6, O1, O2]`. Feature ordering per Layer-2 §3.2:
channel-major within each band; band order `[δ, θ, α, β, γ]`.

### §12.6 Regularisation and data-dependence

`λ ∈ {10^{-6}, 10^{-5}, 10^{-4}}` is a fixed parameter grid; it
is NOT selected by any data-dependent procedure. Each (m, λ)
cell is evaluated independently. The scale-equivariance condition
of benchmark charter §7.A.6 (E1 IN-SCOPE for P.LAP) is
established for every (m, λ) cell precisely because `A_{LAP}` is
independent of the data.

---

## §13. P.LAP scale-equivariance (E1 in Phase-1)

Claim: for every (m, λ) in the Phase-1 grid, `χ_op` on P.LAP
outputs is exactly zero on the scalar-amplitude scaling null (E1)
up to the E-family tolerance of §7.A.5, under a correct fixed-
operator implementation.

Proof sketch (fixed linear operator on sensor cross-spectrum):
- If `V(t)` is replaced by `α · V(t)`, then `X(t) = A_{LAP} · V(t)`
  becomes `α · X(t)`.
- The Welch cross-spectral estimator scales by `|α|²`: for any
  segment `k`, `Y_k → α · Y_k`, so `Y_k Y_k^H → |α|² · Y_k Y_k^H`.
- Band integration is linear; `S_b → |α|² · S_b`.
- Trace normalisation cancels: `ρ_b = S_b / Tr(S_b) → (|α|² S_b)
  / (|α|² Tr(S_b)) = ρ_b`.
- Block-diagonal aggregation preserves per-band ρ; therefore
  `ρ_full_op` is invariant under `V ↦ α · V`.
- `χ_op = (1/2) · ‖ρ_full_op_0 − ρ_full_op_1‖_F^2 = 0` exactly.

Any implementation that violates this identity has introduced
data-dependent regularisation or a numerical instability that is
disqualifying under §6.6. E1 remains IN-SCOPE for P.LAP in
Phase-1.

---

## §14. Remaining Phase-1-blocking obligations under G5/G6/P.LAP

| Item | Status | Blocker |
|---|---|---|
| M19 spherical `(θ_zen, φ_az)` table | ★ PF convention | No primary source for exact coordinates. Convention is reproducible; nuisance scenarios S6.a/S6.b absorb millimetre-level mismatch. |
| Head-model radii (r_scalp, r_skull, r_brain) | ★ PF | Nominal adult values; no primary-source verification recorded. |
| Head-model conductivities (0.33, 0.0165, 0.33 S/m) | ★ PF | Skull:brain 1:20 is one of the widely-cited ratios; no primary-source verification recorded for this exact use. |
| Multishell EEG analytical Legendre series (K4 §11.4, corrected at K5) | **PHASE-1-BLOCKING** | K5 correction (2026-09-14): the correct primary source is Zhang 1995 *Phys Med Biol* 40(3):335–349 (paywalled, NOT accessed). Prior K4 attribution to Berg-Scherg 1994 was WRONG — Berg-Scherg 1994 is a fast approximation, NOT the primary series. Mosher-Leahy-Lewis 1999 IEEE TBME 46(3):245–259 Eq. (15)–(17) supplies the exact form as an accessible peer-reviewed CROSS-CHECK (openly at https://neuroimage.usc.edu/paperspdf/IEEEBME99.pdf) but is not primary provenance. §11.4 equations are now the corrected Mosher-Leahy-Lewis form; blocker remains OPEN pending Zhang 1995 primary verification or a BEM regression-test alternative. |
| Truncation order `N_trunc = 40` for leadfield series | ★ PF | Convergence at Phase-1 spatial scales must be verified at implementation time against the §6.7 grid `{20, 40, 80}`. |
| Perrin 1989 spline kernel `g_m` and Laplacian kernel `h_m` closed forms | **PHASE-1-BLOCKING** | Primary-source verification of the exact Perrin-1989 spline construction is required before implementation. Secondary quotations exist in the bridge audit. K5 addition (2026-09-14): the Carvalhaes-de Barros 2014 arXiv:1406.0458v2 REVIEW paper (openly accessible) reproduces the kernels as Eq. (33b) and (36) with clear Perrin-1989 attribution, mathematically matching §12.2 exactly. This cross-check downgrades the blocker severity but does NOT close it under the primary-source rule. See source audit §7.1. |
| Truncation orders `N_g_trunc = N_h_trunc = 50` | ★ PF | Convergence must be verified at implementation time against the §6.7 grid `{25, 50, 100}`. |
| Reference-freedom check `‖A_{LAP} · 1‖_∞ ≤ 10^{-10}` | Build-time check | Required as a Phase-1 unit test before any benchmark run. |
| Radial-only dipole orientations | ★ PF | Tangential dipoles deferred to a future cell. |

**Cumulative Phase-1 readiness verdict (K4, 2026-09-14; K5
amendment, 2026-09-14).** The Phase-1 cell (M19, P.LAP, Benchmark
B) is DOCUMENTED but NOT IMPLEMENTATION-READY. Two load-bearing
primary-source verifications remain blocking:

1. **Multishell EEG analytical Legendre series** — correct
   primary source is Zhang 1995 *Phys Med Biol* 40(3):335–349
   (paywalled, NOT accessed at K5). K5 correction retracts the
   K4 mis-attribution to Berg-Scherg 1994 (which is a fast
   approximation, not the analytical series). Mosher-Leahy-Lewis
   1999 IEEE TBME 46(3):245–259 Eq. (15)–(17) is an accessible
   peer-reviewed CROSS-CHECK that supplies the exact form now
   recorded in §11.4; the K4 schematic form has been replaced
   with the Mosher-Leahy-Lewis form. Blocker OPEN pending
   Zhang-1995 primary verification or BEM regression-test
   alternative.
2. **Perrin et al. 1989 spherical-spline kernel `g_m` and
   Laplacian kernel `h_m`** — primary text NOT accessed at K5.
   Carvalhaes-de Barros 2014 arXiv:1406.0458v2 Eq. (33a, 33b,
   36) is an accessible open-preprint CROSS-CHECK that matches
   §12.2 exactly with Perrin-1989 attribution. Blocker OPEN
   pending Perrin-1989 primary verification.

K5 does NOT promote either cross-check into primary provenance;
the "primary source rule" is preserved. Both blockers can still be
resolved only by (a) a full-text verified reading of the actual
primary paper (Zhang 1995 and Perrin 1989) recorded in the source
audit with the exact equations quoted, or (b) an alternative
equivalent numerical implementation with primary-source-backed
regression tests. Doing (a) requires external primary-source
access that is not authorised as implementation and properly
belongs in a future audit step.

All other Phase-1-blocking obligations under G2/G3/G4 (§9) and
G5/G6/P.LAP (this section) are closed to the ★ PF standard with
feasibility grids per §6.7. No content of this document
authorises a primary-source claim beyond what the source audit
records.

---

## §15. Cross-references (K4 additions)

- Benchmark charter `codex/CHURN_CHI_K_MEASUREMENT_BENCHMARK_CHARTER_2026-09-13.md`
  §7 (M19 label list, P.LAP (m, λ) grid, head-model row), §7.A.5–§7.A.6
  (E1 scope for P.LAP, scale-equivariance), §13 G5, §13 G6 (Phase-1
  closure via this document), §14.1 (Phase-1 cell declaration).
- Layer-2 charter `codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md`
  §3.1 (P.LAP as PF provisional primary, sourced to Sitt 2014 +
  Tenke & Kayser 2015), §3.2 (STFT parameters), §3.3 (block-
  diagonal-by-band ρ).
- Bridge audit `codex/CHURN_CHI_K_EEG_BRIDGE_AUDIT_2026-09-13.md`
  §3 (P.LAP verified claims from Tenke & Kayser 2015 quotations;
  edge-electrode behaviour flagged unknown).
- Source audit `codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md`
  (Sitt 2014 verified; Perrin 1989 and Berg-Scherg 1994 not in
  verified-full-text set as of this commit).
