# CHURN χ_k EEG-BRIDGE — SYNTHETIC MEASUREMENT-VALIDITY BENCHMARK CHARTER

Date: 2026-09-13
Branch context: r331b-provenance
Status: DRAFT CHARTER. NOT implementation-ready. No implementation code
is prescribed by this document; it defines only the specification of
the benchmark to be built and the pass/fail criteria that a candidate
representation must satisfy before it may be used as a Layer-2 bridge
in any human-subjects pilot.

This charter is the U15 dependency named in
`codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md` §13. It exists
because the Layer-2 charter designates P.LAP (spherical-spline
surface Laplacian, spatial CSD) as a **provisional** primary
representation and P.REST / P.SRC as pre-registered sensitivity
representations, with an explicit acknowledgement (bridge audit §7)
that (A) algebraic validity on H_k, (B) statistical-estimation
soundness, and (C) physical interpretability are three separable
conditions, and only (A) is presently established. This benchmark
addresses (B) and (C).

Nothing in this charter may be construed as evidence FOR any
representation. Its role is to define a filter that the candidate
representations must pass; passing does not confer positive validity,
only survival of a disqualifying test.

---

## §0. Scope and non-goals

### In scope
- Specification of synthetic latent-source scenarios S0–S8 under
  which candidate EEG-to-ρ_EEG(t) representations are evaluated.
- Specification of the forward/reference models under which those
  latent sources are projected to simulated scalp signals.
- Specification of the pipeline that the candidate representations
  are applied to the simulated signals to produce ρ_EEG(t_0) and
  ρ_EEG(t_1) and compute χ_k(ρ_EEG(t_0), ρ_EEG(t_1)).
- Quantitative selection criteria: false-churn rate under null
  scenarios; sensitivity under signal scenarios; representation
  agreement; electrode-count dependence; spline-parameter
  stability.
- A disqualification rule: failure of a candidate representation
  on any of the null scenarios (S0, S1, S2) is disqualifying for
  that representation as a Layer-2 bridge, independent of
  sensitivity on signal scenarios.

### Not in scope
- Actual simulation code or numerical results. This charter is a
  specification, not an experiment.
- Human-subjects data of any kind.
- Any Layer-3 (consciousness-interpretation) content.
- Any change to Layer-1 (kernel-verified Frobenius churn on H_k) or
  its unitary-invariance theorem.
- Any modification to Lean sources or the book manuscript.

---

## §1. Definitions and notation

Fixed for the duration of this charter:

- **Latent source space.** A configurable number `M` of latent dipole
  sources with fixed positions and orientations inside a head volume
  conductor model. Their time courses are the ground truth against
  which measured χ_k values are judged.
- **Latent state.** A configuration of the latent sources at a
  specified time window: joint spectral density, cross-source phase
  relations, and total power. Two latent states `L_0` and `L_1` are
  compared per scenario. In some scenarios `L_0 = L_1` (null
  scenarios).
- **Forward model.** A specified head model (spherical or realistic
  BEM) that maps latent dipole activity to scalp electrode signals.
  Volume-conductor assumptions are stated per experiment; the
  forward model is treated as GIVEN for the purpose of generating
  simulated signals — the candidate representations DO NOT know
  it exactly.
- **Reference / representation.** A choice of pipeline that converts
  simulated scalp signals into channel-space or source-space
  time-frequency data from which S(f, t) and thence ρ_EEG(t) are
  formed. Three candidates:
  - **P.LAP.** Spherical-spline surface Laplacian (spatial CSD) at
    specified `m` (spline flexibility) and `λ` (smoothing).
  - **P.REST / P.rREST.** Reference Electrode Standardization
    Technique / regularized variant, at a specified lead field.
  - **P.SRC.** Source-space reconstruction under a specified
    inverse operator (e.g., minimum-norm class or beamformer class)
    and forward model that may or may not match the generation
    forward model.
- **S(f, t).** Hermitian PSD cross-spectral density matrix of the
  representation-space signals at time window `t` and frequency `f`
  or band `[f_lo, f_hi]`, constructed as the outer-product
  cross-spectrum on rank-corrected channels (bridge audit §Q.A).
- **ρ_EEG(t).** Trace-normalized S(f, t) (or band-integrated
  variant) treated as a density matrix on the representation space.
- **χ_k(ρ_0, ρ_1).** Frobenius churn on the Layer-1 space H_k, as
  proven in `PF/Consciousness/FrobeniusChurn.lean`, applied via a
  fixed lift of ρ_EEG(t) into H_k. The lift used here is exactly
  the one specified in the Layer-2 charter §5 and must not vary
  across scenarios.
- **Nominal expected χ.** The value χ_k is DESIGNED to return under
  a given scenario. For null scenarios the nominal expected value
  is 0 (or arbitrarily small under sampling noise); for signal
  scenarios the nominal expected value is strictly positive with
  a scenario-specific direction of change.

---

## §2. Design principles

1. **Ground truth is the LATENT state**, not the representation-space
   reconstruction. A representation that manufactures apparent
   churn where none exists in the latent state (S0, S1, S2) is
   producing false positives at the physical layer, even if the
   channel-space or source-space signals do change.
2. **Nuisance changes must not be confused with signal.** Electrode
   displacement, missing channels, interpolation, and instantaneous
   mixing changes MUST produce χ_k values that are quantitatively
   below scenario-signal responses.
3. **Multiple representations must agree ON SCENARIOS WHERE THE
   PHYSICAL ANSWER IS UNAMBIGUOUS.** Disagreement on ambiguous
   scenarios is informative and must be reported; disagreement on
   S0–S2 flags at least one representation as unusable.
4. **Parameter dependence must be exercised, not hidden.** For
   P.LAP the (`m`, `λ`, electrode count) grid is explored; for
   P.REST the regularization is exercised; for P.SRC the choice of
   inverse and any forward-model mismatch is exercised.
5. **All decisions are pre-committed.** Scenario definitions,
   pass/fail thresholds, and reporting format are fixed in this
   charter before any code is written. Post-hoc threshold
   adjustment is not permitted.

---

## §3. Scenarios

Each scenario defines: (i) the latent configuration at `t_0` and
`t_1`; (ii) the forward and reference models used to project to
scalp; (iii) any nuisance transformation applied between `t_0` and
`t_1`; (iv) the nominal expected χ_k response; (v) the pass
condition.

Scenarios split into three families:
- **Null family (S0, S1, S2):** nominal expected χ_k ≈ 0.
- **Signal family (S3, S4, S5, S6):** nominal expected χ_k > 0
  with a scenario-specific structure.
- **Nuisance/control family (S7, S8):** measure false-positive rates
  under changes that are physically real but not "brain-state"
  changes.

### S0 — Reference-swap null (mandatory pass)
**Latent.** `L_0 = L_1`; identical latent joint dynamics at both
windows.
**Manipulation.** Between `t_0` and `t_1` the ONLY thing that
changes is the choice of reference/representation applied to the
recorded signals — the underlying scalp potentials are held
identical.
**Nominal expected χ_k.** 0.
**Pass condition.** For the SAME candidate representation applied
consistently at both windows, χ_k(ρ_0, ρ_1) must be within the
sampling-noise band established by pure-null resampling on `L_0` at
`t_0` (see §4.1). This is a self-consistency check: representation
choice, held fixed within a pair, cannot manufacture churn.
**Disqualification.** Failure of any candidate representation on
S0 is disqualifying for that representation.

### S1 — Uniform amplitude scaling (mandatory pass)
**Latent.** Latent dynamics at `t_1` are those at `t_0` multiplied
by a fixed scalar `α > 0` (same across all sources).
**Manipulation.** Uniform gain change only. No structural change
in the latent state.
**Nominal expected χ_k.** 0 (trace normalization removes overall
scaling).
**Pass condition.** χ_k(ρ_0, ρ_1) within the S0 sampling-noise band
for the representation.
**Disqualification.** Failure is disqualifying.

### S2 — Total-power change with unchanged normalized structure
(mandatory pass)
**Latent.** Latent spectral matrix at `t_1` is `β · S_latent(t_0)`
for a spatially non-uniform but proportional scaling `β` that
preserves the normalized (trace-1) form of `S_latent`.
**Manipulation.** Total power differs between windows; normalized
spatial-spectral STRUCTURE is preserved.
**Nominal expected χ_k.** 0 (normalization by trace removes total
power).
**Pass condition.** χ_k(ρ_0, ρ_1) within the S0 sampling-noise band.
**Disqualification.** Failure is disqualifying.

### S3 — Redistribution across channels/sources at constant power
**Latent.** Total power held constant across windows. Normalized
spatial-spectral structure changed by an explicit rotation or
mixing of source power among the `M` latent sources.
**Manipulation.** Structural change of type explicitly targeted by
Frobenius churn on H_k.
**Nominal expected χ_k.** > 0, and monotonically increasing with
the magnitude of the redistribution (parameterized in the scenario).
**Pass condition.** χ_k(ρ_0, ρ_1) is (a) strictly above the S0
sampling-noise band, and (b) monotonic in the redistribution
parameter across a swept set of magnitudes, with a rank correlation
threshold specified in §4.
**Non-disqualifying.** A representation that passes S0–S2 but has
low sensitivity on S3 is not disqualified; it is characterized as
insensitive.

### S4 — Frequency-band redistribution
**Latent.** Total power constant. Power moves between named
frequency bands (e.g., δ, θ, α, β, γ) among a shared set of sources.
Within-band spatial-spectral structure at `t_1` differs from `t_0`
because the band-integrated cross-spectra differ.
**Manipulation.** Signal that a band-integrated ρ_EEG can see;
signal that a full time-frequency ρ_EEG can also see.
**Nominal expected χ_k.** > 0 IF the representation retains
frequency structure; response depends on band-integration choice.
**Pass condition.** Response > S0 band under the band scheme
declared in the Layer-2 charter. Any representation that
band-collapses in a way that destroys S4 sensitivity must be
FLAGGED in reporting, not disqualified.

### S5 — Change only in cross-frequency coupling
**Latent.** Marginal within-frequency structure identical between
windows; cross-frequency coupling structure changes.
**Manipulation.** Deliberate blind-spot test.
**Nominal expected χ_k.** 0 for a block-diagonal-by-frequency
ρ_EEG (because block-diagonal ρ discards cross-frequency terms);
> 0 for a full time-frequency ρ_EEG that retains cross-frequency
blocks.
**Pass condition.** The measured response MUST match the
theoretically nominal value for the ρ construction actually used;
any discrepancy is a bug. This scenario also serves to DOCUMENT
the blind spot for whichever ρ construction the Layer-2 charter
adopts. It does not by itself disqualify.

### S6 — Change in lagged inter-source phase
**Latent.** Marginal source amplitudes and within-source spectra
identical between windows. Only the LAGGED cross-source phase
structure changes.
**Manipulation.** Test whether the cross-spectral (imaginary
component) sensitivity is preserved end-to-end.
**Nominal expected χ_k.** > 0, because Hermitian cross-spectra
carry off-diagonal phase information.
**Pass condition.** Response > S0 band. A representation that
zeros out phase information (e.g., magnitude-only ρ) will fail S6;
this is diagnostic, not disqualifying by itself, but MUST be
reported.

### S7 — Nuisance changes (mandatory characterization)
Sub-scenarios. Each is a change applied between `t_0` and `t_1`
with latent state held identical:
- **S7.a** Small rigid rotation/translation of the electrode
  montage (simulating head movement).
- **S7.b** Displacement of a specified fraction of electrodes
  (e.g., 5%, 10%) by a specified magnitude.
- **S7.c** A specified fraction of channels marked bad and
  interpolated by the same spherical spline as P.LAP (using
  representative parameters).
- **S7.d** Change of instantaneous mixing only (e.g., a linear
  volume-conduction-like transformation applied to the scalp
  signals at `t_1` but not `t_0`; latent sources unchanged).
- **S7.e** Additive artifact (e.g., simulated eye blink, muscle
  activity) at `t_1` only.
**Nominal expected χ_k.** Small but not identically zero. The
purpose is to CHARACTERIZE the false-churn magnitude under
realistic nuisance, not to require it be exactly zero.
**Pass condition.** For each nuisance sub-scenario, the ratio
`χ_k(S7.x) / χ_k(S3 at reference magnitude)` must be BELOW a
declared threshold (see §4). A representation that produces
nuisance-induced χ_k comparable to signal-induced χ_k is unusable
in practice, even if it technically passed S0–S2.

### S8 — Pure-null controls (mandatory characterization)
Sub-scenarios. Each has NO latent signal of interest between `t_0`
and `t_1` — the latent state is either identical or entirely
noise/artifact:
- **S8.a** Latent state = white noise sources at both windows,
  drawn independently but from identical distributions.
- **S8.b** Latent state = pure volume-conduction pattern (e.g.,
  a single distant deep source that projects broadly) at both
  windows.
- **S8.c** Recorded signal = pure electrode noise only (no latent
  source active).
**Nominal expected χ_k.** ~0 (with a well-defined sampling-noise
distribution).
**Pass condition.** The empirical distribution of χ_k values
under S8.a–c defines the SAMPLING-NOISE BAND (§4.1) used to judge
S0, S1, S2, S3, S6.

---

## §4. Quantitative selection criteria

All thresholds below are declared in this charter and MUST NOT be
revised post-hoc without a labelled amendment commit.

### §4.1 Sampling-noise band
The sampling-noise band for a candidate representation is the
95th-percentile envelope of χ_k values under S8 (all sub-scenarios
combined) across a pre-specified number of independent draws.
All null-scenario pass conditions reference this band.

### §4.2 False-churn rate (mandatory)
For each candidate representation, the false-churn rate is defined
as the fraction of S0 + S1 + S2 + S7 trials for which
`χ_k > sampling-noise-band 95th percentile`.
**Threshold.** A candidate representation is disqualified as
primary if the false-churn rate on the combined S0 + S1 + S2 trials
exceeds 5% at the declared draw count.
S7 (nuisance) is characterized but does not itself trigger
disqualification; instead, nuisance ratios per §4.4 apply.

### §4.3 Sensitivity (characterization, not disqualification)
For S3, S4 (under the declared band scheme), S6 the sensitivity of
a representation is quantified as:
- The empirical median χ_k across the swept magnitude range.
- The Spearman rank correlation between the swept magnitude
  parameter and the measured χ_k.
**Reporting requirement.** Both quantities must be reported per
representation, per scenario. No hard threshold; a representation
with markedly lower sensitivity than others is characterized as
"insensitive" and its use as primary must be explicitly justified.

### §4.4 Nuisance ratio (mandatory)
For each S7 sub-scenario and each representation, the nuisance
ratio is:
`R_nuis = median χ_k(S7.x) / median χ_k(S3 at reference magnitude)`.
**Threshold.** A candidate representation is disqualified as
primary if `R_nuis > 0.5` for any S7 sub-scenario. In plain terms:
if realistic nuisance produces half or more of the churn produced
by an explicit target-signal redistribution, the representation
cannot distinguish signal from movement/artifact.

### §4.5 Representation-agreement criterion (mandatory)
Across S0, S1, S2, S3, S6, S8: the three candidate representations
must AGREE on the ordinal ranking (null vs signal) they assign to
each scenario. Quantitative agreement is reported as the pairwise
Spearman correlation of median χ_k across scenarios.
**Threshold.** Pairwise agreement on ordinal null/signal
classification must be 100% (i.e., all three representations must
label each null scenario as null and each signal scenario as
signal). Failure indicates at least one representation is
unsuitable; the failing representation is disqualified as primary
but may be retained as a sensitivity axis if S0–S2 are still
passed.

### §4.6 Electrode-count dependence (mandatory characterization)
Every scenario is run at multiple electrode counts drawn from a
declared set `{N_1, N_2, N_3}` (specific counts to be fixed in
the accompanying pre-registered protocol, spanning at minimum
`10–20` sparse, `64` typical, and `128` dense).
**Reporting requirement.** χ_k statistics are reported per
electrode count. A representation whose null-scenario false-churn
rate crosses the §4.2 threshold at any declared count is
disqualified at that count and above/below (specify which).

### §4.7 Spline-parameter stability (mandatory for P.LAP)
For P.LAP the (`m`, `λ`) grid must be swept over the declared
grid (specific grid fixed in the pre-registered protocol; must
include the Tenke & Kayser 2015 recommended pairing and at least
two flanking values on each axis).
**Reporting requirement.** Null-scenario false-churn rate reported
per (`m`, `λ`) cell. A representation whose false-churn behavior
varies wildly with (`m`, `λ`) is flagged as parameter-fragile;
if any cell exceeds §4.2 the cell is disqualified. The pilot may
proceed only with cells that pass everywhere.

---

## §5. Cross-representation comparison and decision procedure

At completion of the benchmark:

1. For each candidate representation (P.LAP, P.REST, P.SRC) compute
   the sampling-noise band per §4.1.
2. Compute false-churn rate per §4.2. Representations exceeding
   the threshold are DISQUALIFIED AS PRIMARY.
3. Compute nuisance ratios per §4.4. Representations exceeding the
   threshold are DISQUALIFIED AS PRIMARY.
4. Compute pairwise agreement per §4.5. Representations that fail
   agreement are DISQUALIFIED AS PRIMARY but retained as
   sensitivity axes if S0–S2 pass.
5. Report sensitivity per §4.3 and electrode-count / parameter
   stability per §4.6, §4.7.
6. **Primary selection rule.** From the surviving set choose the
   representation with (a) the widest range of electrode counts
   over which §4.2 is satisfied, then (b) the tightest sampling-
   noise band on S8, then (c) the highest sensitivity rank
   correlation on S3.
7. **Sensitivity axes.** All representations surviving S0–S2 but
   not selected as primary become pre-registered sensitivity
   representations to be reported in the pilot alongside the
   primary.
8. If NO representation passes §4.2 and §4.4, the χ_k pilot is not
   preregistrable under the current Layer-2 charter. A charter
   amendment is required — either revisiting the representation
   catalog or explicitly narrowing the scientific claim.

---

## §6. Reporting requirements

The benchmark run produces a single audit artifact:
`codex/CHURN_CHI_K_MEASUREMENT_BENCHMARK_RESULTS_YYYY-MM-DD.md`.

Minimum contents:
- Scenario definitions actually run (with any deviations from this
  charter explicitly labelled).
- Software version and dependencies used.
- Sampling-noise bands per representation.
- False-churn rates per representation per null scenario.
- Nuisance ratios per representation per S7 sub-scenario.
- Sensitivity statistics per representation per signal scenario.
- Pairwise representation-agreement statistics.
- Electrode-count dependence tables.
- Spline-parameter stability tables (P.LAP).
- The decision reached under §5 and the identity of the selected
  primary representation and sensitivity axes (or, if none pass,
  the disqualification statement).

The results document is added to the codex on the same branch and
tagged so that the Layer-2 charter §3.1 primary/sensitivity
designation can be updated by reference.

---

## §7. Governance

- This charter lives on `r331b-provenance`. Master unchanged.
- No Lean, no book, no Layer-3 content is authored under this
  charter.
- Amendments to §3 (scenarios) or §4 (thresholds) require a
  labelled amendment commit that explicitly identifies which
  paragraph changes and why. Post-hoc silent threshold changes are
  prohibited.
- If a candidate representation not currently listed (P.LAP,
  P.REST, P.SRC) is proposed for evaluation, it must be added to
  the charter FIRST and evaluated under the same scenario set and
  criteria as the existing candidates.

---

## §8. Cross-references

- Layer-2 charter: `codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md`
  (see §3.1 for the provisional primary/sensitivity designation
  this benchmark exists to test, and §13 U11–U15 for the load-
  bearing assumptions this benchmark is intended to resolve).
- Source audit: `codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md`.
- Bridge audit: `codex/CHURN_CHI_K_EEG_BRIDGE_AUDIT_2026-09-13.md`
  (see §7 for the (A)/(B)/(C) decomposition; this benchmark
  addresses (B) and, indirectly through the S0/S1/S2/S7 filters,
  (C)).
- Layer-1 kernel: `PF_Lean4_Code/PF/Consciousness/FrobeniusChurn.lean`
  (unchanged; the Frobenius churn definition and unitary-invariance
  theorem used here are the ones proved there; unitary invariance
  is NOT invoked to protect χ_k from the non-unitary preprocessing
  steps under evaluation).
