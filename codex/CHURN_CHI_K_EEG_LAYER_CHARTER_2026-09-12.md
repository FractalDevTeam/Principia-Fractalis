# Layer 2 (EEG → ρ(t)) Measurement-Model Charter — 2026-09-12

*Charter for Layer 2 of the churn program per user directive
2026-09-12. Designs a candidate operational bridge from EEG data to a
normalized state matrix ρ(t) on H_k, feeding the Layer-1 observable
χ_k(t). NO Lean is written by this charter. NO consciousness claim is
made. Stopping condition: after charter + source audit, Layer 2
implementation and Layer 3 (interpretation) require explicit further
approval.*

## ★ Epistemic-status banner ★

Three quantities MUST remain separately labelled throughout this
charter, any downstream document, any paper, and any public
communication:

**Q1 — Chapter 32's clinical ch₂.** A scalar in [0,1] computed via
band power → digitize → base-3 digit sum → phase factor
`exp(iπ√2·D(n))` → weighted sum across bands → `|Σ|²`. Defined
pipeline in `ch32_consciousness_quantification.tex` lines 191–322.
Existing PF construction.

**Q2 — Linear entropy of ρ.** `S_L(ρ) := 1 - Tr(ρ²)` for any density
matrix ρ. Standard quantum-information measure of mixedness. Bounded
in [0, 1 − 1/d] where d = dim H. Recovered in ch06:517 as `ch₂` in
the bipartite-pure-state case, but the identity ch₂ = 1 − Tr(ρ²) is
book language for a specific mathematical object, not for the ch32
clinical scalar Q1.

**Q3 — Frobenius churn χ_k(t).** `χ_k(t) := ½ ‖ρ(t+Δt) − ρ(t)‖²_F` on
H_k = ℂ^{3^k}. Layer 1 mathematical object. Formalized in
`PF/Consciousness/FrobeniusChurn.lean:churnFrobenius`.

**No definitional identification among Q1, Q2, Q3 is made by this
charter.** Any relationship among them is a testable empirical
hypothesis, not a definitional collapse. In particular, the ch32
clinical ch₂ (Q1) and the density-matrix ρ(t) constructed here are
independent operationalizations that happen to share a common
inspiration in the PF framework; they are NOT reducible to each
other.

## §0. What this charter does and does not do

**DOES:**
- Specify one complete candidate pipeline
  `EEG data → ρ(t) on H_k → χ_k(t)`.
- Cite primary sources for every established signal-processing step.
- Enumerate every new modelling choice specific to Principia
  Fractalis and flag it explicitly.
- Provide type-level bookkeeping so Hermiticity, PSD, and trace-1
  properties can be discharged in a future Lean or Python
  implementation.
- Design a preregistered falsification protocol for the
  `χ_k ⇔ conscious/unresponsive` hypothesis.
- Provide sensitivity analyses, negative controls, and rejection
  criteria.

**DOES NOT:**
- Implement the estimator (deferred: post-approval, separate arc).
- Claim EEG directly measures the Timeless Field.
- Claim χ_k measures consciousness.
- Claim H_k = ℂ^{3^k} is empirically established as the correct
  substrate space.
- Modify the book or any Lean file.
- Begin Layer 3 (consciousness interpretation).
- Correlate the pipeline output against Q1, Q2, or established
  consciousness indices except as a preregistered secondary outcome.

## §1. What Layer 1 proves; what Layer 2 assumes

### §1.1 What Layer 1 has proven (kernel-verified at HEAD `cfe64dee`)

Given ANY complex matrix ρ, σ ∈ Matrix (Fin (3^k)) (Fin (3^k)) ℂ:

- `frobeniusSqDist ρ σ := ∑_i ∑_j ‖ρ_{ij} − σ_{ij}‖²` is nonnegative,
  symmetric, and vanishes iff ρ = σ.
- `churnFrobenius ρ σ := (1/2) · frobeniusSqDist ρ σ` inherits these
  properties.
- `churnFrobenius` is invariant under simultaneous unitary
  conjugation `ρ ↦ UρUᴴ, σ ↦ UσUᴴ` (both `U Uᴴ = 1` AND `Uᴴ U = 1`
  as explicit hypotheses).
- `digitAncillaLift k ρ` is the digit-compatible pure-ancilla lift
  from level `k` to level `2k`, and:
  - **T5a:** `partialTraceMorphism k (2k) (dvd_two_mul_self k)
    (digitAncillaLift k ρ) = ρ` (substrate round-trip).
  - **T5b:** `churnFrobenius (digitAncillaLift k ρ) (digitAncillaLift
    k σ) = churnFrobenius ρ σ` (invariance under the lift).

Layer 1 does NOT require:
- ρ, σ to be Hermitian, PSD, trace-1, or in any way "density-matrix-like".
- Any physical interpretation of H_k.
- Any connection to EEG, brain, or consciousness.

Layer 1 is pure finite-dimensional linear algebra with the substrate's
ternary index structure.

### §1.2 What Layer 2 introduces as new assumptions

Layer 2 introduces the following as NEW ASSUMPTIONS not proven in
Layer 1:

**A1. There exists a well-defined mapping**
`M : EEG(window) → Matrix (Fin (3^k)) (Fin (3^k)) ℂ`
such that `M(EEG(t))` is Hermitian, PSD, trace-1 whenever it is
defined. The specific construction is §3–§4 below.

**A2. The specific choice of `k` in `H_k = ℂ^{3^k}` is scientifically
justifiable.** In particular: the ternary substrate structure is a
Principia Fractalis modelling choice, not an empirically established
feature of EEG. The choice of k is a hyperparameter of the model.

**A3. The Layer-1 pure-ancilla lift is distinct from the Layer-2
zero-padding embedding** (proven in §4 below). Any claim of "T5
compatibility" requires the specific digit-order alignment specified
in §4; naive zero-padding does NOT automatically satisfy T5.

**A4. The three quantities Q1, Q2, Q3 are computationally distinct
and empirically comparable.** No identification is assumed by
construction.

**A5. The `χ_k ⇔ conscious/unresponsive` claim is a testable
empirical hypothesis, not a definition.** Layer 3 (consciousness
interpretation) requires empirical validation via the preregistered
protocol of §10.

## §2. Established EEG signal processing (primary sources)

This section restates standard practice with citations. NONE of §2 is
a Principia Fractalis invention.

### §2.1 Recording, montage, filtering

**Reference standards:**
- Nunez, P. L., & Srinivasan, R. (2006). *Electric Fields of the
  Brain: The Neurophysics of EEG* (2nd ed.). Oxford University Press.
  Chapters 1, 6, 7 (recording physics; reference montage; volume
  conduction).
- Michel, C. M., & Brunet, D. (2019). "EEG Source Imaging: A
  Practical Review of the Analysis Steps." *Frontiers in Neurology*
  10:325. doi:10.3389/fneur.2019.00325 (preprocessing pipeline).
- Bigdely-Shamlo, N., Mullen, T., Kothe, C., Su, K. M., & Robbins,
  K. A. (2015). "The PREP pipeline: standardized preprocessing for
  large-scale EEG analysis." *Frontiers in Neuroinformatics* 9:16.
  doi:10.3389/fninf.2015.00016 (reproducible reference/rereference
  standard).

**Reference montage sensitivity:**
- Yao, D., Qin, Y., Hu, S., Dong, L., Vega, M. L. B., & Sosa, P. A. V.
  (2019). "Which reference should we use for EEG and ERP practice?"
  *Brain Topography* 32:530–549. (Common-average vs Laplacian vs
  linked-mastoid; effect on covariance-based metrics.)

**Filtering conventions (primary):**
- Widmann, A., Schröger, E., & Maess, B. (2015). "Digital filter
  design for electrophysiological data — a practical approach."
  *Journal of Neuroscience Methods* 250:34–46.

### §2.2 Artifact rejection

**Independent component analysis:**
- Jung, T. P., Makeig, S., Humphries, C., Lee, T. W., McKeown, M. J.,
  Iragui, V., & Sejnowski, T. J. (2000). "Removing
  electroencephalographic artifacts by blind source separation."
  *Psychophysiology* 37:163–178.
- Chaumon, M., Bishop, D. V., & Busch, N. A. (2015). "A practical
  guide to the selection of independent components of the
  electroencephalogram for artifact correction." *Journal of
  Neuroscience Methods* 250:47–63.

### §2.3 Complex feature extraction

The three canonical routes from real-valued EEG to complex features:

**Route R1 — Hilbert-transformed analytic signal:**
For real signal `s_c(t)` on channel `c`,
`x_c(t) := s_c(t) + i · H[s_c](t)`
where `H` is the discrete Hilbert transform. Reference:
- Cohen, M. X. (2014). *Analyzing Neural Time Series Data: Theory and
  Practice*. MIT Press. Chapter 14 (Hilbert transform for
  instantaneous phase and amplitude).

**Route R2 — Short-time Fourier transform (STFT):**
`X_c(t, f) := ∑_{τ} s_c(τ) · w(τ − t) · e^{−2π i f τ}`
where `w` is a window function.

**Route R3 — Complex Morlet wavelet transform:**
`X_c(t, f) := (s_c ⋆ ψ_f)(t)` where `ψ_f` is the complex Morlet
wavelet at centre frequency `f`.

Cross-references for all three: Cohen (2014) chapters 12–14.

The charter's Layer-2 pipeline uses **Route R2 (STFT)** as the primary
feature construction, with **R1** and **R3** as alternates in the
sensitivity analysis (§9).

### §2.4 Cross-spectral matrix estimation

Standard definition (short-time cross-spectral density matrix at
window centred on t):
```
S_{cc'}(t, f) := (1/N) ∑_{s=1}^{N} X_c^{(s)}(t, f) · [X_{c'}^{(s)}(t, f)]*
```
where `(s)` indexes epochs, trials, or non-overlapping/overlapping
subwindows inside a longer window. `*` denotes complex conjugation.

References:
- Welch, P. D. (1967). "The use of Fast Fourier Transform for the
  estimation of power spectra: A method based on time averaging over
  short, modified periodograms." *IEEE Trans. Audio Electroacoust.*
  15:70–73.
- Bendat, J. S., & Piersol, A. G. (2010). *Random Data: Analysis and
  Measurement Procedures* (4th ed.). Wiley-Interscience.
  Chapters 5–6 (auto- and cross-spectral estimation).
- Rosenberg, J. R., Amjad, A. M., Breeze, P., Brillinger, D. R., &
  Halliday, D. M. (1989). "The Fourier approach to the identification
  of functional coupling between neuronal spike trains." *Progress in
  Biophysics and Molecular Biology* 53:1–31.

Established properties (proven in Bendat & Piersol 2010):
- `S(t, f) ∈ ℂ^{D×D}` for D channels.
- `S(t, f)` is Hermitian by construction (`S = Sᴴ`).
- `S(t, f)` is positive semidefinite: for any `v ∈ ℂ^D`,
  `v^H S v = (1/N) ∑_s |v^H X^{(s)}|² ≥ 0`.
- `Tr(S(t, f)) = (1/N) ∑_s ‖X^{(s)}‖² ≥ 0`, and `= 0` iff
  `X^{(s)} = 0` for all `s`.

### §2.5 Consciousness-state EEG study design

**Preregistered benchmark studies:**
- Sitt, J. D., King, J. R., El Karoui, I., Rohaut, B., Faugeras, F.,
  Gramfort, A., Cohen, L., Sigman, M., Dehaene, S., & Naccache, L.
  (2014). "Large scale screening of neural signatures of
  consciousness in patients in a vegetative or minimally conscious
  state." *Brain* 137:2258–2270. (Standard multi-feature classifier
  for MCS vs UWS.)
- Casali, A. G., Gosseries, O., Rosanova, M., Boly, M., Sarasso, S.,
  Casali, K. R., Casarotto, S., Bruno, M. A., Laureys, S., Tononi, G.,
  & Massimini, M. (2013). "A theoretically based index of
  consciousness independent of sensory processing and behavior."
  *Science Translational Medicine* 5:198ra105. (Perturbational
  Complexity Index — PCI, established benchmark.)
- Sarasso, S., Boly, M., Napolitani, M., Gosseries, O., Charland-Verville,
  V., Casarotto, S., Rosanova, M., Casali, A. G., Brichant, J. F.,
  Boveroux, P., Rex, S., Tononi, G., Laureys, S., & Massimini, M.
  (2015). "Consciousness and complexity during unresponsiveness
  induced by propofol, xenon, and ketamine." *Current Biology*
  25:3099–3105.
- King, J. R., Sitt, J. D., Faugeras, F., Rohaut, B., El Karoui, I.,
  Cohen, L., Naccache, L., & Dehaene, S. (2013). "Information sharing
  in the brain indexes consciousness in noncommunicative patients."
  *Current Biology* 23:1914–1919.

**Preregistration standard:**
- Nosek, B. A., et al. (2018). "The preregistration revolution."
  *PNAS* 115:2600–2606.
- OSF preregistration template: https://osf.io/prereg/

## §3. The Layer-2 candidate pipeline

### §3.1 Preprocessing (standard)

Fixed preregistered choices (any variant explored under §9 sensitivity):

1. **Recording:** 64-channel EEG at ≥ 500 Hz sampling. Nunez-standard
   10–20 or 10–10 electrode placement.
2. **Reference montage:** Common average reference (CAR) computed
   over all channels after artifact rejection. Rationale: canonical
   for cross-spectral analysis (Nunez & Srinivasan 2006, Chapter 7).
3. **Bandpass filter:** 0.5 − 45 Hz, zero-phase FIR Hamming window
   (Widmann et al. 2015, §5).
4. **Notch filter:** IIR notch at line frequency (50 or 60 Hz
   depending on jurisdiction), Q = 30.
5. **Artifact rejection:** ICA (extended Infomax) with automated
   selection via ADJUST or ICLabel (Chaumon et al. 2015). Manual
   review flagged.
6. **Epoching:** T_win = 2 s non-overlapping epochs; discard epochs
   with any channel |amplitude| > 200 µV after ICA.

**None of §3.1 is a PF-specific choice.** All from cited sources.

### §3.2 Feature construction (STFT primary; Route R2)

For each retained epoch and each channel `c ∈ {1, ..., D_ch}`,
compute the STFT with:
- Window: Hamming, length T_stft = 500 ms.
- Overlap: 250 ms (50%).
- FFT length: next power of 2 ≥ window samples.

Output per epoch: `X_c(t_i, f_j) ∈ ℂ` for `t_i` centred at STFT
window positions, `f_j` at Fourier frequencies.

Then restrict to a preregistered frequency-band set
`B = {b_1, ..., b_{D_bd}}` (default: δ 0.5–4, θ 4–8, α 8–13, β 13–30,
γ 30–45 Hz; other choices explored in §9).

Band-average per epoch:
```
Y_{c, b}(t_i) := (1/|F_b|) ∑_{f_j ∈ F_b} X_c(t_i, f_j) ∈ ℂ
```
where `F_b` is the discrete Fourier bins inside band `b`.

**Feature vector at time `t_i`:**
```
x(t_i) := vec[Y_{c, b}(t_i)]_{c ∈ [D_ch], b ∈ [D_bd]} ∈ ℂ^{D}
```
where `D = D_ch × D_bd`.

**PF-specific note:** The feature ordering `vec[Y_{c,b}]` is a
modelling choice (channel-major vs. band-major). Default:
channel-major (all bands for channel 1, then all bands for channel 2,
etc.). This choice is fixed preregistered. Sensitivity in §9.

### §3.3 Cross-spectral / covariance matrix S(t)

Within a moving super-window of `N` STFT windows (default `N = 8`,
covering `≈ 2 s` at 50% overlap), compute:

```
S(t) := (1/N) ∑_{s=0}^{N−1} x(t − s · Δ_stft) · [x(t − s · Δ_stft)]^H
     ∈ ℂ^{D × D}
```

where `Δ_stft = 250 ms` is the STFT hop.

**Established properties (proven in Bendat & Piersol 2010, §2.4
above):**
- `S(t)` is Hermitian by construction.
- `S(t)` is PSD: `v^H S(t) v = (1/N) ∑_s |v^H x(t − s Δ_stft)|² ≥ 0`.
- `Tr(S(t)) = (1/N) ∑_s ‖x(t − s Δ_stft)‖² ≥ 0`.

### §3.4 Normalization ρ(t) = S(t) / Tr(S(t))

**Definition (defined regime):**
```
ρ(t) := S(t) / Tr(S(t))     when Tr(S(t)) ≥ ε_min
```

**Zero-power exclusion rule (fixed a priori):**
- Set `ε_min := 10^{−12} · Tr(S̄)` where `Tr(S̄)` is the recording-wise
  median of `Tr(S(t))` computed on the artifact-cleaned data
  BEFORE any Layer-2 analysis.
- If `Tr(S(t)) < ε_min`: `ρ(t) := UNDEFINED`. The time window is
  EXCLUDED from all downstream analysis. No default matrix (identity,
  maximally-mixed, or otherwise) is substituted.
- Excluded-window fraction is reported per recording; any recording
  with > 5% excluded windows is flagged and re-preprocessed OR
  excluded from the primary analysis (choice preregistered).

**Properties of ρ(t) when defined:**
- Hermitian: `ρ = ρ^H` (division of Hermitian by positive real
  preserves Hermiticity).
- PSD: `v^H ρ v = (v^H S v) / Tr(S) ≥ 0`.
- Unit trace: `Tr(ρ) = Tr(S)/Tr(S) = 1`.

**PF-specific note:** The zero-power exclusion IS a modelling choice.
It could equivalently be handled by substituting the maximally-mixed
state `I/D`, but that would introduce a systematic bias toward the
maximally-mixed reference under low-power conditions (e.g., low-amp
sleep, deep anesthesia burst suppression). Excluding is the honest
choice; the resulting missing-data rate is itself a scientific
readout.

### §3.5 Dimensional embedding into H_k = ℂ^{3^k}

The empirical dimension is `D = D_ch × D_bd`. To situate ρ(t) in
`H_k = ℂ^{3^k}`, one of the following modelling choices must be made
(and fixed preregistered):

**Option (i) — Exact match by design:**
Choose `(D_ch, D_bd)` such that `D = 3^k` exactly. Example:
`D_ch = 9, D_bd = 3, D = 27 = 3^3`, so `k = 3`. This constrains the
electrode subset and band choice a priori.

**Option (ii) — Isometric embedding (zero-padding):**
Choose `3^k > D`, embed via
`V : ℂ^D → ℂ^{3^k}, x ↦ (x, 0, 0, ..., 0)`
(zero-pad the extra `3^k − D` positions). Then define
`ρ̃(t) := V · ρ(t) · V^H ∈ ℂ^{3^k × 3^k}` — the D×D block of ρ in the
upper-left, zero elsewhere.

**Option (iii) — Truncation:**
Choose `3^k < D`; project via `P : ℂ^D → ℂ^{3^k}, x ↦ (x_1, ..., x_{3^k})`
using a preregistered basis choice. This DISCARDS information; not
recommended unless a specific PF-substrate argument compels a
particular k.

**Charter default: Option (i)** with a preregistered choice of
`(D_ch, D_bd)`. If a specific electrode set or band structure is
impossible to construct with `D = 3^k`, fall back to Option (ii) with
the caveat below.

### §4. Zero-padding is NOT T5-compatible

**Claim.** The isometric embedding of §3.5 Option (ii) is
mathematically DISTINCT from the Layer-1 pure-ancilla lift
`digitAncillaLift k : Matrix (Fin (3^k)) _ ℂ → Matrix (Fin (3^{2k})) _ ℂ`.

**Proof.** Layer 1's lift is defined so that
`digitAncillaLift k ρ` places ρ in the "matter" block (first-k digit
positions), with the ancilla projector `|0⟩⟨0|` on the last-k digit
positions. Non-zero entries of `digitAncillaLift k ρ` occur at
positions `(p, q)` where BOTH the last-k digits of p and the last-k
digits of q are the zero digit function.

Zero-padding on the other hand is: for `x ∈ ℂ^D`, `x̃ ∈ ℂ^{3^k}` has
`x̃_i = x_i` for `i < D` and `x̃_i = 0` for `i ≥ D`. Then
`(V x)(V x)^H` has non-zero entries at positions `(p, q)` where BOTH
`p < D` and `q < D`.

The two are the SAME iff "positions with all-zero last-k digits"
coincides with "positions with index < D". This holds iff the
digit-encoding of `Fin (3^k)` is chosen so that indices `[0, D)`
correspond EXACTLY to digit patterns with all-zero last-k digits —
which is NOT the case for `finFunctionFinEquiv` unless `D = 3^{k'}`
for some `k' ≤ k` and the padding places `x` on precisely those
digit indices.

**Consequence.** Under §3.5 Option (ii), the resulting `ρ̃(t)` is NOT
generally the image of any `ρ(t)` on `H_{k'}` under `digitAncillaLift`
for any `k' < k`. Any downstream claim that "χ_k on ρ̃ equals χ_{k'}
on ρ" via T5 is INVALID under naive zero-padding.

**Sufficient condition for T5-compatibility of the embedding:**
Choose `D = 3^{k'}` for some `k' < k`, and construct the embedding
via the digit-encoding
`V : ℂ^{3^{k'}} → ℂ^{3^k}, ψ ↦ ψ ⊗ |0^{(k-k')}⟩`
(pure tensor product with the zero state on the added digits).
Under this construction, `V ρ V^H = digitAncillaLift^{k-k'}` applied
appropriately, and χ_k(ρ̃) = χ_{k'}(ρ) by T5.

Charter default explicitly uses Option (i) precisely to sidestep this
issue. If Option (ii) is used, the T5-compatible construction above
must be followed EXPLICITLY, or T5 invariance must be re-proven for
the specific non-tensor embedding used.

**This is a substantive scientific constraint on Layer 2, not a
Lean-engineering footnote.**

## §5. Defining χ_k(t) at Layer 2

Given the pipeline of §3 with `k` fixed by §3.5, define:
```
χ_k(t) := (1/2) · ‖ρ(t + Δt) − ρ(t)‖²_F
       = (1/2) · ∑_{i,j} ‖ρ(t+Δt)_{ij} − ρ(t)_{ij}‖²
```

**Fixed preregistered parameters:**
- `Δt := N · Δ_stft = 8 × 250 ms = 2 s` (one super-window step).
- ρ super-window length: `2 s` (matches Δt for non-overlapping ρ
  computation).
- Feature ordering: channel-major (see §3.2).
- k: as chosen in §3.5.

**Undefined regime:** If either `ρ(t)` or `ρ(t + Δt)` is UNDEFINED
per §3.4 zero-power rule, then `χ_k(t) := UNDEFINED`.

**Property inheritance from Layer 1:** Whenever both ρ(t) and
ρ(t+Δt) are defined, `χ_k(t)` inherits from Layer 1's proven
properties: nonnegative (T1); zero iff `ρ(t) = ρ(t + Δt)` (T3); unitary
invariance (T4, if both states are transformed by the same U);
digit-compatible pure-ancilla lift invariance (T5b, only under §4's
T5-compatible embedding).

## §6. Three-quantity separation (Q1, Q2, Q3)

For every recording, EACH of the three quantities Q1, Q2, Q3 is
computed INDEPENDENTLY:

**Q1(t) — ch32 clinical ch₂:** Computed exactly per
`ch32_consciousness_quantification.tex` lines 191–322. Uses band
powers per channel per band, base-3 digit sums, phase factors
`exp(iπ√2·D(n))`, weighted sum, `|Σ|²`. Output is a scalar in [0, 1].
DOES NOT go through a density matrix.

**Q2(t) — Linear entropy of ρ(t):**
```
S_L(ρ(t)) := 1 − Tr(ρ(t)²)     ∈ [0, 1 − 1/D_k]
```
where `D_k = 3^k`. Purely a function of ρ(t) constructed in §3.

**Q3(t) — Frobenius churn χ_k(t):** Per §5.

**Analysis discipline:**
- Report Q1, Q2, Q3 as independent per-recording time series.
- Do NOT define any of them in terms of the others.
- Test empirical relationships (Pearson, Spearman correlation between
  time-averaged Q_i values across recordings) as SECONDARY outcomes.
- Any strong correlation is a SCIENTIFIC finding, not a definitional
  identity.

## §7. Dimensional / type ledger

| Symbol | Type | Domain | Range | Reference |
|---|---|---|---|---|
| `s_c(t)` | function | `[c ∈ [D_ch], t ∈ [T]]` | `ℝ` | Raw EEG (§3.1) |
| `x_c(t)` (R1) | function | `[c, t]` | `ℂ` | Hilbert transform, §2.3 R1 |
| `X_c(t, f)` (R2) | function | `[c, t, f]` | `ℂ` | STFT, §3.2 |
| `Y_{c,b}(t_i)` | function | `[c, b, t_i]` | `ℂ` | Band average, §3.2 |
| `x(t_i)` | vector | — | `ℂ^{D}` | Feature vector, §3.2 |
| `S(t)` | matrix | — | `ℂ^{D × D}` | Cross-spectral, §3.3 |
| `Tr(S(t))` | scalar | — | `ℝ_{≥ 0}` | §3.3 |
| `ρ(t)` | matrix (or ⊥) | — | `ℂ^{D × D}` or `UNDEFINED` | §3.4 |
| `V` | isometry | `ℂ^D → ℂ^{3^k}` | — | §3.5 Option (ii) |
| `ρ̃(t)` | matrix (or ⊥) | — | `ℂ^{3^k × 3^k}` or `UNDEFINED` | §3.5 |
| `χ_k(t)` | scalar (or ⊥) | — | `ℝ_{≥ 0}` or `UNDEFINED` | §5 |
| Q1(t) | scalar | — | `ℝ ∈ [0, 1]` | §6 (ch32) |
| Q2(t) | scalar | — | `ℝ ∈ [0, 1 − 1/D_k]` | §6 |
| Q3(t) | scalar (or ⊥) | — | `ℝ_{≥ 0}` or `UNDEFINED` | §6 (= χ_k) |

## §8. Proof obligations for ρ(t)

A future Lean or Python implementation must discharge, for the
constructed `ρ(t)` whenever defined:

**PO1 (Hermiticity).** `ρ(t)^H = ρ(t)`. 
*Proof sketch:* `S(t) = (1/N) ∑_s x^{(s)} x^{(s)H}` is Hermitian by
construction; dividing by real positive `Tr(S(t))` preserves this.

**PO2 (Positive semi-definiteness).** For all `v ∈ ℂ^D`,
`v^H ρ(t) v ≥ 0`.
*Proof sketch:* `v^H S(t) v = (1/N) ∑_s |v^H x^{(s)}|² ≥ 0`; division
by positive `Tr(S(t))` preserves the inequality.

**PO3 (Unit trace).** `Tr(ρ(t)) = 1`.
*Proof sketch:* `Tr(ρ(t)) = Tr(S(t)) / Tr(S(t)) = 1` when
`Tr(S(t)) > 0`.

**PO4 (Undefined-regime disjunction).** If `Tr(S(t)) < ε_min` then
`ρ(t) = UNDEFINED`; otherwise PO1–PO3 hold. Never both.

**PO5 (Embedding preservation of PO1–PO3).** Under §3.5 Option (i),
PO1–PO3 for `ρ(t) ∈ ℂ^{3^k × 3^k}` hold identically (D = 3^k).

Under §3.5 Option (ii) with `V` as defined,
`ρ̃(t) = V ρ(t) V^H` inherits PO1 (Hermitian) and PO2 (PSD) directly;
`Tr(ρ̃(t)) = Tr(V^H V ρ(t)) = Tr(I_D ρ(t)) = Tr(ρ(t)) = 1` (PO3
preserved) since `V^H V = I_D`.

PO5 for Option (iii) requires the projector `P` to satisfy
`P P^H = I_{3^k}` (an orthogonal projection onto a `3^k`-dim
subspace), in which case PO1–PO2 preserved but `Tr(P ρ P^H) ≤ Tr(ρ) = 1`
with equality iff ρ's support lies in the projected subspace. Under
strict inequality PO3 fails and Layer 2 must renormalize; this is
another modelling caveat.

## §9. Sensitivity analyses (all preregistered)

The Layer-2 pipeline's dependence on each choice below must be
reported as a sensitivity analysis. If ANY dimension of variation
reverses or eliminates the primary effect, the primary hypothesis is
DOWNGRADED to "found only under specific choices of X".

**Sensitivity axes:**
1. **Reference montage:** CAR (default) vs. Laplacian vs. linked
   mastoids (Yao et al. 2019).
2. **Feature route:** STFT R2 (default) vs. Hilbert R1 vs. Morlet R3.
3. **Band selection:** 5 canonical bands (default) vs. individualized
   α-peak-centred bands vs. narrow-band decomposition (1 Hz bins in
   δ–β).
4. **Window length T_win:** 2 s (default) vs. 1 s vs. 4 s.
5. **STFT window T_stft:** 500 ms (default) vs. 250 ms vs. 1000 ms.
6. **N super-window count:** 8 (default) vs. 4 vs. 16.
7. **Regularization for near-singular S(t):** none (default) vs.
   Ledoit-Wolf shrinkage (Ledoit & Wolf 2004) vs. minimum-eigenvalue
   floor at `10^{−6} · Tr(S)`.
8. **k choice:** default per §3.5 vs. next power of 3 up vs. next
   down.
9. **Embedding option:** (i) default vs. (ii) with T5-compatible
   tensor structure vs. (iii) with orthogonal projector.
10. **Feature ordering:** channel-major (default) vs. band-major.
11. **Δt for χ_k:** 2 s (default) vs. 1 s vs. 4 s (implicit in super-
    window step).
12. **Zero-power ε_min:** `10^{−12} · Tr(S̄)` (default) vs.
    `10^{−9} · Tr(S̄)` vs. `10^{−15} · Tr(S̄)`.

Each sensitivity is run as an ablation on the primary analysis
dataset; effects reported as `(effect at default, effect at each
alternative, sign preservation, magnitude ratio)`.

## §10. Preregistered falsification design

**Hypothesis (primary, testable):**
`H1_Layer2: mean_t χ_k(t) differs between conscious and unresponsive
conditions with effect size Cohen's d > 0.5 (moderate) at α = 0.05
after multiple-comparison correction across sensitivity axes of §9.`

**Groups (preregistered inclusion criteria):**
- **Group A — Wakefulness:** Healthy adults, eyes-closed resting
  state, Karolinska Sleepiness Scale ≤ 3 at recording. Target
  `n_A ≥ 40`.
- **Group B — Non-REM sleep (N2/N3):** Polysomnographically confirmed
  Stage N2 or N3 per AASM 2007 criteria. Target `n_B ≥ 40`.
- **Group C — Propofol anesthesia (unresponsive):** Bispectral index
  (BIS) 20–40, target-controlled propofol infusion at surgical plane;
  behaviorally unresponsive to name-calling and pain. Target
  `n_C ≥ 30`.
- **Group D — Unresponsive wakefulness syndrome (UWS):** Coma
  Recovery Scale — Revised (CRS-R) score ≤ 6; behaviorally
  unresponsive. Target `n_D ≥ 20`.

**Primary contrast:** `(A ∪ B_N2) vs (C ∪ D)` — behaviorally-verified
conscious/aware vs unresponsive.

*Note on Group B:* Sleep is included cautiously: N2 sleepers are
behaviorally unresponsive but neurally likely to have some
consciousness of sensory environment (dream reports on awakening).
Group B is a diagnostic "intermediate" group; if χ_k assigns B to
neither pole cleanly, that is a preregistered secondary finding
(consistency with the neural correlates literature).

**Secondary contrasts:**
- Wakefulness eyes-closed vs. eyes-open (control for arousal).
- Propofol vs. sevoflurane (drug-class robustness).
- UWS vs. MCS (minimally conscious state per CRS-R > 6).

**Statistical model:**
`χ_k(t)` time-averaged per recording → `χ̄_k` per subject.
Mixed-effects linear model: `χ̄_k ~ Group + (1 | Site) + covariates
(age, sex, montage version)`. Group A vs (C ∪ D) contrast is the
primary test.

**Sample size and power:**
Based on Sitt et al. (2014) which reported classifier AUC ≈ 0.78 for
conscious vs unconscious discrimination with n ≈ 200 patients. For
Cohen's d = 0.5 (equivalent to AUC ≈ 0.64), α = 0.05, β = 0.20,
required n ≈ 64 per group. Our targets (n_A = 40, n_C = 30, n_D = 20)
are DELIBERATELY conservative for a first-look; achieved effect size
must be `d > 0.5` OR the design is scaled up to n ≈ 100 per group
before rejection.

**Preregistration:**
- Preregister on Open Science Framework (OSF) BEFORE data collection.
- Locked analysis pipeline hash before any group-level analysis.
- Data collection sites, ethics approvals, and analysis scripts
  archived at preregistration time.

**Multiple comparisons:**
- Bonferroni correction across the 12 sensitivity axes of §9.
- Family-wise error rate α_family = 0.05 → per-axis α = 0.05/12 ≈ 0.004.

## §11. Negative controls and null models

**Negative controls (must be recorded and analyzed alongside primary):**

**NC1 — Recording noise floor:** 5-minute recording with electrodes
short-circuited (no subject). Expected: χ_k dominated by amplifier
noise; if χ_k ≠ 0 well above shot noise, subject-independent artifact
must be characterized. Threshold: recording χ_k > 10× short-circuit
χ_k for any subject data to be considered non-artifactual.

**NC2 — Time-shuffled surrogates:** For each real recording, shuffle
epoch order to destroy temporal structure. Recompute χ_k. Expected:
distribution centered near a specific null (time-independent
covariance floor).

**NC3 — Phase-randomized surrogates (Theiler et al. 1992):** Preserve
per-channel power spectrum but destroy cross-channel phase
relationships. Expected: distribution centered near a null that
reflects power-only similarity between windows.

**NC4 — Isolated single-channel recordings:** Recompute χ_k from
only 1 channel (`D_ch = 1`). Cross-spectral matrix degenerates to a
1×1 scalar; ρ(t) = 1 identically; χ_k = 0. This is a sanity check:
the pipeline must return 0 in this limit.

**NC5 — Independent Gaussian channels:** Simulate D channels of
independent Gaussian white noise. Compute χ_k. Expected: χ_k
converges to a specific asymptotic distribution predicted by random
matrix theory (Marčenko–Pastur, adjusted for the trace-normalization).

**Null models (for hypothesis testing):**

**NM1 — AR(p) per channel:** Fit an autoregressive model of order
p = 8 per channel independently; simulate surrogate multichannel EEG
that preserves per-channel autocorrelation but has no cross-channel
structure. χ_k on surrogates gives null distribution.

**NM2 — Group-permutation null:** Shuffle group labels (A vs C ∪ D)
across subjects; recompute the primary contrast statistic. Repeat
5000 times to build a null distribution.

**NM3 — Bootstrap over epochs:** Resample epochs within each
recording with replacement to estimate the sampling distribution of
per-recording χ̄_k.

## §12. Rejection criteria for the χ_k ⇔ consciousness hypothesis

**H1_Layer2 is REJECTED if ANY of the following holds:**

**R1.** Primary contrast `mean_t χ_k` between Group A and (Group C ∪
Group D) is NOT significant at Bonferroni-corrected α (per-axis 0.004)
across the majority (≥ 7 of 12) of sensitivity axes.

**R2.** Effect direction reverses (conscious > unresponsive vs.
conscious < unresponsive) between ANY two sensitivity axes for
which the effect is significant.

**R3.** Primary contrast survives on the raw pipeline but fails on
ALL three surrogate null models (NM1, NM2, NM3), indicating the
observed effect is fully attributable to noise structure preserved by
the surrogates.

**R4.** χ_k of any subject in the conscious group falls within the
95% CI of the short-circuit recording noise (NC1) — indicating the
pipeline is not physically probing brain state at all.

**R5.** χ_k on Group A does not exceed the surrogate null NC2 by at
least 2σ — indicating χ_k adds no information beyond spectral density
already captured.

**R6.** χ_k fails to correlate (Spearman |ρ| > 0.3) with ANY of the
established consciousness measures (PCI Casali et al. 2013; Sitt et
al. 2014 classifier; behavioral CRS-R for UWS/MCS). Non-correlation
does not disprove χ_k intrinsically, but it disqualifies the claim
that χ_k is measuring "consciousness" in the sense established by
prior literature — and per this charter's Layer-3 stipulation, the
consciousness interpretation would be unsupported.

**R7.** The estimator required to compute χ_k is not reproducibly
implementable from the charter specification alone (e.g., turns out
to depend on undocumented parameters that alter effect sign).

**R8.** Q1, Q2, Q3 (per §6) are found to be linearly dependent by
construction upon detailed reanalysis, indicating the three-quantity
separation was illusory — collapsing the charter to a redundant
restatement of ch32.

Any of R1–R8 requires publication of the negative result and
withdrawal of the Layer-3 consciousness interpretation.

## §13. Unresolved choices requiring further deliberation

The following are DELIBERATELY LEFT OPEN by this charter; they
require empirical exploration or theoretical justification BEFORE
Layer 2 implementation:

**U1. Choice of `k` when D ≠ 3^{k'}:**
If natural EEG dimension (e.g., 64 channels × 5 bands = 320) does not
factor as 3^k, which embedding option to choose? Option (i) forces a
non-standard channel/band selection; Option (ii) forfeits T5
invariance guarantee unless done via tensor structure; Option (iii)
loses information. RECOMMENDATION: Option (i) with pre-approved
electrode subset.

**U2. Reference montage impact on cross-spectral structure:**
Different montages induce different degrees of spurious coherence
from volume conduction (Nunez & Srinivasan 2006, Chapter 7). CAR is
standard but adds anti-correlations to all pairs. Alternatives (e.g.,
Reference Electrode Standardization Technique, REST; Yao 2001) are
credited with reducing this artifact but are less established.
Sensitivity analysis in §9 will report the impact.

**U3. Complex feature route:**
STFT (R2) is standard for spectral analysis but has fixed
time-frequency resolution. Morlet wavelets (R3) provide adaptive
resolution but introduce a wavelet-parameter (`ω_0` centre frequency
constant) as an extra hyperparameter. Hilbert (R1) requires
pre-band-pass filtering. Default R2 chosen for reproducibility;
sensitivity in §9.

**U4. Feature-ordering convention:**
Channel-major vs. band-major changes which entries of ρ(t) are
"nearby" but does NOT change any invariants (trace, spectrum,
linear entropy). Affects only entry-labelling in visualizations.
Default: channel-major.

**U5. Handling of near-singular S(t):**
When `N < D`, `S(t)` is rank-deficient. `ρ(t) = S(t) / Tr(S(t))` is
still well-defined mathematically (PSD is preserved by non-negative
scalar division), but the resulting ρ may have zero eigenvalues,
making `S_L(ρ) = 1 − Tr(ρ²)` close to 1 (highly mixed) even for
low-power windows. Whether to regularize (Ledoit-Wolf shrinkage;
Ledoit & Wolf 2004) or leave raw is a preregistered choice.

**U6. Definition of "conscious" ground truth:**
Behavioral CRS-R for UWS/MCS; BIS for anesthesia; polysomnography
for sleep. These are all imperfect. Preregister a hierarchy of
ground-truth definitions and analyze robustness across them.

**U7. Cross-site replication:**
Any positive result must be replicated at ≥ 2 recording sites with
different hardware. Preregister multi-site plan before analysis.

## §14. Sources (primary literature)

**Signal processing:**
- Bendat, J. S., & Piersol, A. G. (2010). *Random Data: Analysis and
  Measurement Procedures* (4th ed.). Wiley-Interscience.
  ISBN 978-0-470-24877-5.
- Welch, P. D. (1967). *IEEE Trans. Audio Electroacoust.* 15:70–73.
- Widmann, A., Schröger, E., & Maess, B. (2015). *J. Neurosci. Methods*
  250:34–46. doi:10.1016/j.jneumeth.2014.08.002.

**EEG physics and analysis:**
- Nunez, P. L., & Srinivasan, R. (2006). *Electric Fields of the
  Brain* (2nd ed.). Oxford University Press. ISBN 978-0-19-505038-7.
- Michel, C. M., & Brunet, D. (2019). *Frontiers in Neurology* 10:325.
  doi:10.3389/fneur.2019.00325.
- Cohen, M. X. (2014). *Analyzing Neural Time Series Data*. MIT Press.
  ISBN 978-0-262-01987-3.
- Bigdely-Shamlo, N., Mullen, T., Kothe, C., Su, K.-M., & Robbins,
  K. A. (2015). *Frontiers in Neuroinformatics* 9:16.
  doi:10.3389/fninf.2015.00016.
- Yao, D., Qin, Y., Hu, S., Dong, L., Vega, M. L. B., & Sosa, P. A. V.
  (2019). *Brain Topography* 32:530–549.
  doi:10.1007/s10548-019-00707-x.

**Cross-channel coupling / cross-spectral estimation:**
- Rosenberg, J. R., Amjad, A. M., Breeze, P., Brillinger, D. R., &
  Halliday, D. M. (1989). *Prog. Biophys. Mol. Biol.* 53:1–31.
- Pascual-Marqui, R. D. (2007). "Coherence and phase synchronization:
  generalization to pairs of multivariate time series, and removal of
  zero-lag contributions." arXiv:0706.1776.

**Artifact rejection:**
- Jung, T. P., et al. (2000). *Psychophysiology* 37:163–178.
- Chaumon, M., Bishop, D. V., & Busch, N. A. (2015).
  *J. Neurosci. Methods* 250:47–63.

**Consciousness studies:**
- Sitt, J. D., et al. (2014). *Brain* 137:2258–2270.
  doi:10.1093/brain/awu141.
- Casali, A. G., et al. (2013). *Sci. Transl. Med.* 5:198ra105.
  doi:10.1126/scitranslmed.3006294.
- Sarasso, S., et al. (2015). *Curr. Biol.* 25:3099–3105.
  doi:10.1016/j.cub.2015.10.014.
- King, J. R., et al. (2013). *Curr. Biol.* 23:1914–1919.
  doi:10.1016/j.cub.2013.07.075.

**Statistical / null-model methods:**
- Theiler, J., Eubank, S., Longtin, A., Galdrikian, B., & Farmer, J. D.
  (1992). "Testing for nonlinearity in time series: the method of
  surrogate data." *Physica D* 58:77–94.
- Ledoit, O., & Wolf, M. (2004). "A well-conditioned estimator for
  large-dimensional covariance matrices." *J. Multivariate Anal.*
  88:365–411.
- Nosek, B. A., et al. (2018). *PNAS* 115:2600–2606.
  doi:10.1073/pnas.1708274114.

**Density-matrix quantum information (mathematical framework):**
- Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and
  Quantum Information* (10th anniv. ed.). Cambridge University Press.
  ISBN 978-1-107-00217-3. Chapters 2 (density operators), 8 (open
  systems).
- Kliesch, M., & Roth, I. (2021). "Theory of Quantum System
  Certification." *PRX Quantum* 2:010201. doi:10.1103/PRXQuantum.2.010201.

## §15. What separates this charter from Chapter 32

Ch32 (`ch32_consciousness_quantification.tex`) supplies a fully
specified operational pipeline (Q1) that yields a scalar via
band-power → digit-sum → phase-factor construction. Its physical
justification within the PF framework is a preregistered
consciousness measure.

Layer 2 (this charter) supplies a DIFFERENT operational pipeline (Q3
= χ_k) that yields a scalar via cross-spectral matrix → normalized
density matrix → temporal Frobenius distance. Its mathematical
foundation is Layer 1's proven-clean structural theorems on the
Timeless Field substrate.

**Q1 and Q3 are independently specified operationalizations.** They
may or may not correlate empirically. If they correlate, that would
be a scientifically interesting convergent finding (two distinct
constructions arriving at similar readings of the same brain-state
axis). If they do not correlate, both may still be individually valid
readouts of DIFFERENT axes.

**Neither by itself measures consciousness.** Layer 3 requires the
preregistered protocol of §10 to bring either Q1 or Q3 (or a
combination) into contact with behaviorally-verified consciousness
states.

## §16. Charter stopping conditions

Layer 2 implementation MUST pause and reconsult if any of the
following:

**S1.** The chosen scientific reference for a step in §3.1–§3.4 is
found on primary-source verification to be misquoted or unsupportive
of the claimed step. In particular: any equation in this charter that
does not appear verbatim (or up to trivial notation change) in the
cited source must be flagged and rederived.

**S2.** The `D → 3^k` embedding cannot be constructed for any
preregistered electrode/band selection, forcing Option (ii) or (iii)
of §3.5. In that case, the T5-compatible embedding of §4 must be
implemented and re-verified, OR the T5 claim must be dropped.

**S3.** A negative control (NC1–NC5) shows that the χ_k pipeline is
dominated by artifact under conditions where subject data are
similar. In particular: if χ_k on short-circuit recording (NC1) ≥ χ_k
on Group A recordings, the pipeline is measuring the amplifier, not
the brain.

**S4.** Preregistration on OSF is unable to be completed before the
first data collection (e.g., due to ethics-approval delays for a
specific site). Data collection at that site is delayed until
preregistration is on record.

**S5.** Any of the sensitivity axes (§9) is discovered post hoc to
have been fixed to a specific value by an unstated preprocessing
step; requires re-running the primary analysis with the discovered
degree of freedom exposed.

**S6.** During data analysis, a proof obligation PO1–PO5 (§8) is
found violated on any recording. Requires debugging the pipeline;
NO fallback to "approximate ρ" that violates the proof obligations
is permitted (per §3.4 zero-power discipline).

## §17. Ready-state for implementation

Ready for Layer 2 IMPLEMENTATION (a separate arc, requiring further
approval) when:
- [ ] This charter is committed and reviewed.
- [ ] Every primary source in §14 is inspected on the specific
      equation cited; discrepancies flagged.
- [ ] OSF preregistration document drafted from this charter's §10.
- [ ] Ethics approvals for Group A–D recordings obtained at ≥ 2 sites.
- [ ] Software implementation plan drafted (Python + MNE-Python
      standard EEG toolkit + PyTorch or NumPy for matrix operations).
- [ ] Reproducibility contract signed: analysis scripts published
      alongside preregistration; hashed prior to data unblinding.

Layer 3 (consciousness interpretation) does NOT begin until Layer 2
data collection and analysis are complete and the primary hypothesis
of §10 has been either supported or REJECTED per §12.

---

*Charter opened 2026-09-12. Companion documents:
`codex/CHURN_CHI_K_CHARTER_2026-09-12.md` (Layer 1 charter);
`PF/Consciousness/FrobeniusChurn.lean` (Layer 1 Lean, HEAD `cfe64dee`).
Layer 2 remains a design document; no code, no data, no consciousness
claim. Awaits explicit approval before proceeding to implementation.*
