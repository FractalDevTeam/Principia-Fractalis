# CHURN χ_k EEG-BRIDGE — SYNTHETIC MEASUREMENT-VALIDITY BENCHMARK CHARTER

Date: 2026-09-13 (correction revision, following independent-audit
rejection of prior HEAD `5ceaea9c`).

Branch: r331b-provenance.

**STATUS: DOCUMENTATION ONLY. NOT IMPLEMENTATION-READY.**
§13 lists the specification gaps that must be closed by labelled
amendment commits before implementation may proceed.

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
| `ρ_lat = S_lat / Tr(S_lat)` | analytic normalized latent state |
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
| P.SRC.sLORETA | applicable | applicable | sLORETA explicitly reconstructs standardised source amplitudes on a declared grid; `R_P.SRC.sLORETA` is the inverse operator itself. |
| P.SRC.LCMV | applicable | applicable | LCMV beamformer explicitly reconstructs source amplitudes on the same grid; `R_P.SRC.LCMV` is the beamformer output. |

For A, identifiability assumptions of `R_P.SRC.*` must be declared
per §13 G7 before any latent-recovery tolerance is honoured.

---

## §4. Fault list corrected by this revision

| # | Prior defect (in `5ceaea9c`) | Correction |
|---|---|---|
| D1 | E2 demanded `χ_op ≈ χ_lat = 1/4` to `1e-6` relative tolerance across all three representations. Mathematically unjustified for non-unitary A. | E2 is retracted for Benchmark B. A latent-recovery version of E2 is retained in Benchmark A only (§5.A), applicable only to P.SRC.sLORETA and P.SRC.LCMV, with tolerances declared per §13 G7. |
| D2 | Acceptance rule "95% CI LOWER bound ≤ 5%" is failure-to-prove-failure, not evidence of acceptance. | Replaced with three-outcome logic: **PASS** iff 95% CI UPPER ≤ threshold; **FAIL** iff 95% CI LOWER > threshold; **INCONCLUSIVE** iff CI straddles the threshold (§6.1). |
| D3 | Nuisance ratio used LOWER-bound acceptance for the same reason. | Same three-outcome upper-bound convention applied (§6.5). |
| D4 | S7.a, S7.b, S7.c null distributions were pooled into a single per-representation null band. | Each S7 sub-scenario now yields its OWN per-representation null band. No pooling. |
| D5 | S6 sub-scenarios contributed to both the null-family false-positive aggregate AND to the nuisance-ratio gate (double-counting). | S6 contributes ONLY to the nuisance-ratio gate (§6.5). Null-family aggregate is S1 ∪ S7.* only (§6.2). |
| D6 | "Wishart-like," "approximately 5000 sources," and unnamed 10-10 / 10-5 subsets were not implementable. | Marked as specification gaps G1, G3, G5 in §13. Charter is NOT IMPLEMENTATION-READY until those are closed by labelled amendments. |
| D7 | Sensor-noise, artifact templates, forward-model implementation, and inverse-operator implementation were named but not specified. | Marked as specification gaps G2, G4, G5, G6 in §13. Charter is NOT IMPLEMENTATION-READY. |
| D8 | Layer-2 charter §5 declares `Δt = N · Δ_stft = 8 × 250 ms = 2 s` as the super-window length, but §3.2 declares `T_stft = 500 ms` STFT windows with `Δ_hop = 250 ms`. Actual signal span of N=8 segments is `T_stft + (N-1) · Δ_hop = 500 + 7 × 250 = 2250 ms`, not 2000 ms. | Benchmark adopts explicit `T_super = T_stft + (N_seg − 1) · Δ_hop`. For the Layer-2 charter's declared `T_stft = 500 ms`, `Δ_hop = 250 ms`, `N_seg = 8`, this gives `T_super = 2.25 s`. Layer-2 charter §5 is flagged for follow-up amendment (§13 G8); it is not amended in this commit. |
| D9 | Exact-test tolerances (`1e-10`, `1e-6`, `1e-4`) and stochastic thresholds (5× SNR margin, `R_nuis ≤ 0.5`, false-positive ≤ 5%) were pinned without justification and without sensitivity analysis. | All thresholds are labelled ★ PF design choices. §6.7 mandates a sensitivity analysis: the three-outcome decision must be recomputed with each threshold multiplied by `{0.5, 1.0, 2.0}` and the full grid reported. If any threshold flips the outcome across this grid, the decision is INCONCLUSIVE. |
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
| E1 | B, all P | Scalar-amplitude scaling null: `S_lat(t_1, f) = α · S_lat(t_0, f)` for scalar `α > 0`. `ρ_lat` invariant. | `χ_op = 0` (representation is linear in S; scalar cancels through S/Tr(S)) | Machine precision (representations preserve this exactly by linearity + trace normalization) |
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
| S1 | Null-band calibration; §6.2 aggregate | Same latent at both windows (scalar-scaling null with seed-driven noise realizations) | `p_null` per representation (§6.2) |
| S2 | Benchmark A monotonicity/recovery; Benchmark B monotonicity | Latent redistribution parameterized by a scalar `θ` swept over `{θ_1, ..., θ_K}`; χ_lat computed analytically per draw and θ | A: `χ_rec` vs `χ_lat` scatter, Spearman rank correlation, RMSE (per θ). B: `χ_op` monotone in θ (Spearman); NO recovery-of-χ_lat claim |
| S3 | Benchmark B monotonicity (flag-only) | Latent inter-band redistribution at constant total power; χ_lat analytic under a declared ρ construction | Same as S2 but with a caveat: block-diagonal-by-frequency ρ discards cross-band content by design (Layer-2 charter §3.3) |
| S4 | Benchmark B (flag-only) | Latent lagged inter-source phase change with fixed marginal auto-spectra | Response of `χ_op` vs latent phase parameter; magnitude-only ρ constructions will not respond (design blind spot, flagged not disqualified) |
| S5 | Implementation-correctness check | Latent cross-frequency coupling change with unchanged within-frequency structure; under Layer-2 §3.3 block-diagonal-by-band ρ, `χ_lat = 0` by construction | `χ_op` must equal 0 under the declared ρ construction (implementation correctness) |
| S6.a | Nuisance gate (§6.5); NOT in null aggregate | Latent unchanged; scalp montage rotated between windows (yaw ∈ {2°, 5°, 10°}) | `R_nuis(S6.a)` (§6.5) |
| S6.b | Nuisance gate; NOT in null aggregate | Latent unchanged; electrode subset displaced 5 mm ({5%, 10%} of electrodes) | `R_nuis(S6.b)` |
| S6.c | Nuisance gate; NOT in null aggregate | Latent unchanged; {5%, 10%} channels bad-marked and interpolated | `R_nuis(S6.c)` |
| S6.d | Nuisance gate; NOT in null aggregate | Latent unchanged; leadfield perturbation of 5% Frobenius norm applied to t_1 only | `R_nuis(S6.d)` |
| S6.e | Nuisance gate; NOT in null aggregate | Latent unchanged; artifact template added at t_1 (spec §13 G4) | `R_nuis(S6.e)` |
| S7.a | Null aggregate (§6.2); own null band | Latent = independent white-noise sources at both windows | Own null band; contributes to §6.2 aggregate |
| S7.b | Null aggregate; own null band | Latent = single distant deep source (volume-conduction pattern) at both windows | Own null band; contributes to §6.2 aggregate |
| S7.c | Null aggregate; own null band | No latent source; sensor noise only | Own null band; contributes to §6.2 aggregate |

**Explicit no-double-counting rule (D5).** S6 contributes ONLY to
the nuisance-ratio gate. Null-family aggregate `p_null` is
computed over S1 ∪ S7.a ∪ S7.b ∪ S7.c ONLY.

**Explicit no-pooling rule (D4).** S7.a, S7.b, S7.c yield THREE
distinct per-representation null bands. They are not averaged into a
single band. §6.2's aggregate `p_null` is computed by combining
false-positive events across S1 + S7.* draws, but the null-band
CALIBRATION for each S7.x is done independently on that sub-
scenario's own `N_cal` draws.

---

## §5.A Benchmark A test set

Applies to `P.SRC.sLORETA` and `P.SRC.LCMV` only.

- E-family: `E2.A` only.
- S-family: `S2` (monotonicity + `χ_rec` vs `χ_lat` recovery per θ).
- Tolerances: PF design choice per §13 G7, justified by declared
  identifiability assumptions of the inverse operator, not by
  machine precision.

Pass/fail per §6, three-outcome PASS/FAIL/INCONCLUSIVE.

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

### §6.2 Null-family false-positive rate (Benchmark B)

Population: draws from S1 ∪ S7.a ∪ S7.b ∪ S7.c (S6 NOT
included, D5).
```
p_null(P) = fraction of null-family draws with χ_op > margin_null,
```
where `margin_null` is a PF design choice per §13 G8 (candidate:
per-S7.x calibrated 95% CI upper on `N_cal`, combined as the maximum
across S7.x, PF choice).

Threshold: `p_null ≤ 5%` (PF choice, sensitivity per §6.7).

Outcome: PASS / FAIL / INCONCLUSIVE per §6.

### §6.3 Monotonicity (Benchmarks A and B)

Population: S2 sweep over `θ ∈ {θ_1, ..., θ_K}`.

For Benchmark B: Spearman rank correlation between `θ` and median
`χ_op(θ)`. Threshold: rank correlation ≥ 0.9 (PF choice).

For Benchmark A: Spearman rank correlation between `χ_lat(θ)` and
median `χ_rec(θ)`, PLUS RMSE `‖χ_rec − χ_lat‖` per θ.
Threshold: rank correlation ≥ 0.9 AND RMSE within declared
identifiability bound of `R_P` (§13 G7).

Outcome: PASS / FAIL / INCONCLUSIVE per §6.

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

Threshold: `R_nuis ≤ 0.5` (PF choice; §7 sensitivity range).

Outcome per §6: PASS iff 95% CI UPPER ≤ 0.5; FAIL iff 95% CI
LOWER > 0.5; INCONCLUSIVE otherwise.

Applied to each S6.x separately. FAIL on any S6.x disqualifies P.

For Benchmark A: no nuisance-ratio gate against latent-recovery;
Benchmark B's nuisance ratio is the sole nuisance measure. This
means Benchmark A is a NECESSARY-BUT-NOT-SUFFICIENT filter — a
representation passing A must also pass B to advance.

### §6.6 Implementation-correctness gate

E-family failures within Benchmark B and S5 non-zero response are
both implementation-correctness failures (numerical / coding fault),
disqualifying independent of §6.2–§6.5.

### §6.7 Threshold sensitivity analysis (D9)

Every PF-declared threshold in §6.2–§6.5 (`p_null ≤ 5%`, monotonicity
rank ≥ 0.9, minimum-signal floor factor `f_SNR = 5`, nuisance ratio
`≤ 0.5`, and the E-family tolerances of §5.1 per representation)
is recomputed with the threshold multiplied by `{0.5, 1.0, 2.0}`
(and E-family tolerances by `{0.1, 1.0, 10}`). The three-outcome
decision under each perturbation is reported in the manifest.

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

### §8.A Benchmark A (P.SRC.sLORETA, P.SRC.LCMV only)

1. E2.A within declared identifiability tolerance (§13 G7).
2. S2 rank correlation ≥ 0.9 (three-outcome).
3. S2 RMSE within declared identifiability bound (§13 G7).

Outcomes reported: {PASS, FAIL, INCONCLUSIVE}.

### §8.B Benchmark B (all representations)

1. E0, E1, E3.a, E3.b, E3.c within §5.1 tolerances.
2. S5 within numerical zero (implementation-correctness gate).
3. `p_null` (S1 ∪ S7.*, §6.2) three-outcome ≤ 5%.
4. S2 monotonicity rank ≥ 0.9 (§6.3).
5. Sensitivity floor (§6.4) at smallest θ.
6. Nuisance ratio (§6.5) ≤ 0.5 for every S6.x.
7. §6.7 sensitivity analysis stable.

Outcomes reported: {PASS, FAIL, INCONCLUSIVE}.

### §8.C No cross-representation aggregation

Each representation is evaluated independently. There is no
cross-representation agreement rule (C4 correction retained).

### §8.D Global outcome

A representation "qualifies for a pilot" iff:
- Benchmark B outcome is PASS on all §8.B filters.
- Benchmark A outcome is either NOT APPLICABLE (P.LAP, P.REST) or
  PASS on all §8.A filters (P.SRC.*).

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
  labelled amendment commit before implementation may proceed.
- New representations added only by amendment adding a §7 block
  plus a §3 applicability entry, evaluated on the same scenario
  set.

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

## §13. Specification gaps (implementation-blocking)

Charter is NOT IMPLEMENTATION-READY until every gap below is closed
by its own labelled amendment commit on `r331b-provenance`.

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
Lean, book, or Layer-3 work is authorised until §13 gaps close and
this revised charter is itself independently audited.
