# Layer 2 (EEG → ρ_EEG(t)) Measurement-Model Charter — 2026-09-12 (Revised 2026-09-13)

*Design-intent document for Layer 2 of the churn program. **This
charter is NOT implementation-ready.** Its S1 stopping condition
triggered on 2026-09-13; the accompanying source audit
`codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md` records that the
original citations of commit `1cabde90` were assembled without
full-text verification. This revision applies user-directed
corrections A–M and marks every unverified specific choice as a
Principia-Fractalis preregistered design choice pending
primary-source justification.*

**Layer 2 implementation and Layer 3 initiation both require:**
1. Full-text verification of all citation-per-claim mappings by a
   qualified reader with source access. (Sitt et al. 2014 was
   full-text-verified 2026-09-13; other citations remain pending.)
2. A χ_k-specific power analysis derived from the χ_k pilot's own
   variance and an independently chosen smallest effect size of
   interest. Do NOT transfer Sitt 2014's classifier AUC into a
   χ_k Cohen's d.
3. Ethics approvals for Groups A–D at ≥ 2 recording sites.
4. Explicit further approval by Pablo per the standing collaboration
   discipline.

## ★ Epistemic-status banner ★

Three quantities MUST remain separately labelled throughout this
charter, any downstream document, any paper, and any public
communication:

**Q1 — Chapter 32's clinical ch₂.** A scalar in [0,1] computed via
band power → digitize → base-3 digit sum → phase factor
`exp(iπ√2·D(n))` → weighted sum across bands → `|Σ|²`. Defined
pipeline in `ch32_consciousness_quantification.tex` lines 191–322.
Existing PF construction.

**Q2 — Linear entropy of ρ_EEG.** `S_L(ρ_EEG) := 1 - Tr(ρ_EEG²)`
for the EEG-derived normalized PSD state matrix ρ_EEG defined in §3.
Standard mathematical quantity on any Hermitian PSD trace-1 matrix.
NOT necessarily interpretable as consciousness in itself.

**Q3 — Frobenius churn χ_k(t).** `χ_k(t) := ½ ‖ρ_EEG(t+Δt) −
ρ_EEG(t)‖²_F` on `H_k = ℂ^{3^k}` (via the isometric map of §3.5).
Layer 1 mathematical object; the Layer-1 file
`PF/Consciousness/FrobeniusChurn.lean:churnFrobenius` computes
this on ANY Hermitian matrix, not just density matrices.

**No definitional identity or algebraic dependence between Q1 and
Q2/Q3 has been established. Their relationship is presently unknown
and empirically testable.** Q2 and Q3 are algebraically LINKED via
the Frobenius identity (§6) but Q3 carries information not in Q2
alone. Empirical relationships beyond that Frobenius identity are
testable hypotheses, not definitional identities.

## §0. What this charter does and does not do

**DOES:**
- Specify ONE candidate pipeline `EEG data → ρ_EEG(t) on H_k → χ_k(t)`
  as a design intent, WITH every unverified specific choice labelled
  a PF preregistered design choice per point B.
- Reference the background literature that motivates the general
  practice, with source-type labels distinguishing textbook / review /
  primary methods paper / experimental paper / preprint.
- Enumerate every new modelling choice specific to Principia
  Fractalis and flag it explicitly.
- Provide type-level bookkeeping so Hermiticity, PSD, and trace-1
  properties can be discharged in a future implementation.
- Design a preregistered falsification protocol for the
  `χ_k ⇔ conscious/unresponsive` hypothesis, with explicit
  distinction between primary and secondary/exploratory content.

**DOES NOT:**
- Implement the estimator (deferred).
- Claim EEG directly measures the Timeless Field.
- Claim χ_k measures consciousness.
- Claim H_k = ℂ^{3^k} is empirically established as the correct
  substrate space.
- Modify the book or any Lean file.
- Begin Layer 3 (consciousness interpretation).
- Correlate the pipeline output against Q1, Q2, or established
  consciousness indices except as a preregistered secondary outcome.
- Claim any citation has been verified against its full text by the
  current auditor.

## §1. What Layer 1 proves; what Layer 2 assumes

### §1.1 What Layer 1 has proven (kernel-verified at HEAD `cfe64dee`)

Given ANY complex matrices ρ, σ ∈ Matrix (Fin (3^k)) (Fin (3^k)) ℂ:

- `frobeniusSqDist ρ σ := ∑_i ∑_j ‖ρ_{ij} − σ_{ij}‖²` is nonnegative,
  symmetric, and vanishes iff ρ = σ.
- `churnFrobenius ρ σ := (1/2) · frobeniusSqDist ρ σ` inherits these
  properties.
- `churnFrobenius` is invariant under simultaneous unitary
  conjugation `ρ ↦ UρUᴴ, σ ↦ UσUᴴ` (both `U Uᴴ = 1` AND `Uᴴ U = 1`
  as explicit hypotheses).
- `digitAncillaLift k ρ` is a digit-compatible pure-ancilla lift
  from level `k` to level `2k`, and:
  - **T5a:** `partialTraceMorphism k (2k) (dvd_two_mul_self k)
    (digitAncillaLift k ρ) = ρ`.
  - **T5b:** `churnFrobenius (digitAncillaLift k ρ) (digitAncillaLift
    k σ) = churnFrobenius ρ σ`.

Layer 1 does NOT require:
- ρ, σ to be Hermitian, PSD, trace-1, or in any way "density-matrix-like".
- Any physical interpretation of H_k.
- Any connection to EEG, brain, or consciousness.

Layer 1 is pure finite-dimensional linear algebra with the substrate's
ternary index structure.

### §1.2 What Layer 2 introduces as new assumptions

**A1.** There exists a well-defined mapping
`M : EEG(window) → Matrix (Fin (3^k)) (Fin (3^k)) ℂ` such that
`M(EEG(t))` is Hermitian, PSD, trace-1 whenever it is defined. The
specific construction is §3–§4.

**A2.** The specific choice of `k` in `H_k = ℂ^{3^k}` is a Principia
Fractalis modelling choice, NOT an empirically established feature of
EEG.

**A3.** The isometric map `V : ℂ^D → ℂ^{3^k}` used to embed the
scientifically-selected feature dimension `D` into `H_k` is a NEW
explicit modelling map. `V†V = I` preserves Frobenius churn under
`A ↦ V A V†` but does NOT establish any physical Timeless-Field
ontology and does NOT witness the Layer-1 pure-ancilla `T5`
compatibility unless the tensor construction of §4 is followed
explicitly. NO Lean implementation of this V or of any Layer-2
estimator is included in this charter.

**A4.** The three quantities Q1, Q2, Q3 have the algebraic relations
proven in §6; empirical relationships beyond those algebraic facts
are testable hypotheses.

**A5.** The `χ_k ⇔ conscious/unresponsive` claim is a testable
empirical hypothesis, NOT a definition. Layer 3 (consciousness
interpretation) requires empirical validation per §10 AND requires
Layer 2 to be successfully implemented and preregistered first.

## §2. Background references (auditor-inaccessible; pending full-text verification)

**⚠ CRITICAL AUDIT NOTE.** The auditor of the source list did NOT
open the full text of any cited work when drafting the original
charter. The corrections here reflect (a) user-directed rework of
specific citations, and (b) downgrading of all textbook/review
citations to background-only. See
`codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md` for the per-item
verdict table.

### §2.1 Recording, montage, filtering — background references

- **Nunez, P. L., & Srinivasan, R. (2006).** *Electric Fields of the
  Brain* (2nd ed.). Oxford University Press. ISBN 978-0-19-505038-7.
  **BACKGROUND TEXTBOOK.** Cited for EEG recording physics and volume
  conduction only. Does NOT establish any specific reference
  montage as canonical.
- **Michel, C. M., & Brunet, D. (2019).** *Frontiers in Neurology*
  10:325. doi:10.3389/fneur.2019.00325. **BACKGROUND REVIEW.** Cited
  as a general preprocessing review. Notes explicitly (per
  auditor-directed correction) that **sensor-level connectivity is
  reference- and volume-conduction-sensitive**.
- **Yao, D., Qin, Y., Hu, S., Dong, L., Vega, M. L. B., & Sosa,
  P. A. V. (2019).** *Brain Topography* 32:530–549.
  doi:10.1007/s10548-019-00707-x. **BACKGROUND REVIEW, DIRECTLY
  CORRECTED.** Yao et al. establishes reference dependence and
  favors REST / rREST over CAR. Charter's earlier attribution of "CAR
  canonical" to this review is REMOVED.
- **Widmann, A., Schröger, E., & Maess, B. (2015).** *J. Neurosci.
  Methods* 250:34–46. doi:10.1016/j.jneumeth.2014.08.002. **METHODS
  PAPER, INACCESSIBLE TO AUDITOR.** Cited for general practice of
  zero-phase FIR EEG filtering.
- **Bigdely-Shamlo, N., et al. (2015).** *Frontiers in
  Neuroinformatics* 9:16. doi:10.3389/fninf.2015.00016. **METHODS
  PAPER (PREP pipeline), INACCESSIBLE TO AUDITOR.**
- **Channel-level covariance interpretation** (per point C): "The
  cross-spectral matrix S(t) computed at electrode level is a
  MEASUREMENT PROXY on scalp signals. It cannot by itself be
  interpreted as cortical connectivity or intrinsic brain state;
  volume-conduction and reference-choice artifacts contribute to it."

### §2.2 Artifact rejection — background references (corrected)

- **Jung, T. P., et al. (2000).** *Psychophysiology* 37:163–178.
  **METHODS PAPER, INACCESSIBLE.** Cited as canonical reference for
  ICA-based EEG artifact removal.
- **Chaumon, M., Bishop, D. V., & Busch, N. A. (2015).** *J.
  Neurosci. Methods* 250:47–63. **METHODS PAPER, DIRECTLY CORRECTED
  per point D.** Chaumon et al. do NOT describe ICLabel; they in fact
  caution against unsupervised automated component rejection.
- **Pion-Tonachini, L., Kreutz-Delgado, K., & Makeig, S. (2019).**
  "ICLabel: An automated electroencephalographic independent component
  classifier, dataset, and website." *NeuroImage* 198:181–197.
  **METHODS PAPER, INACCESSIBLE TO AUDITOR.** Correct citation for
  ICLabel per user directive.
- **Mognon, A., Jovicich, J., Bruzzone, L., & Buiatti, M. (2011).**
  "ADJUST: An automatic EEG artifact detector based on the joint use
  of spatial and temporal features." *Psychophysiology* 48:229–240.
  **METHODS PAPER, INACCESSIBLE TO AUDITOR.** Correct citation for
  ADJUST per user directive.
- **Blinded human quality review of ICA components is REQUIRED per
  point D.** Automated classifiers (ICLabel, ADJUST) may propose
  labels, but the preregistered pipeline includes human confirmation
  on a blinded subset.

### §2.3 Complex feature extraction — background references

- **Cohen, M. X. (2014).** *Analyzing Neural Time Series Data*. MIT
  Press. ISBN 978-0-262-01987-3. **BACKGROUND TEXTBOOK.** Cited for
  the three complex-feature routes (Hilbert transform R1; STFT R2;
  Morlet wavelet R3).

The three routes:
- **R1 — Hilbert analytic signal:** `x_c(t) := s_c(t) + i·H[s_c](t)`.
- **R2 — Short-Time Fourier Transform:**
  `X_c(t, f) := Σ_τ s_c(τ) · w(τ − t) · e^{−2πifτ}` where `w` is a
  window function.
- **R3 — Complex Morlet wavelet:** `X_c(t, f) := (s_c ⋆ ψ_f)(t)`.

Charter defaults to R2 for the primary pipeline; R1 and R3 appear in
the §9 robustness checks.

### §2.4 Cross-spectral estimation — background references and note

- **Welch, P. D. (1967).** *IEEE Trans. Audio Electroacoust.*
  15:70–73. **PRIMARY METHODS PAPER (univariate PSD), INACCESSIBLE
  TO AUDITOR.** Welch's method is UNIVARIATE PSD estimation; the
  multichannel cross-spectral extension is a separate development.
- **Bendat, J. S., & Piersol, A. G. (2010).** *Random Data* (4th
  ed.). Wiley-Interscience. **BACKGROUND TEXTBOOK, INACCESSIBLE.**
- **Rosenberg, J. R., et al. (1989).** *Prog. Biophys. Mol. Biol.*
  53:1–31. **REVIEW about Fourier analysis of neuronal SPIKE-TRAIN
  data** (per correction 2026-09-13 point CC; previously miscategorized
  as a methods paper on cross-spectral estimation). NOT a primary EEG
  cross-spectral methods paper. Not usable to justify the charter's
  §3.3 EEG estimator; do not treat as origin of any construction here.
- **Pascual-Marqui, R. D. (2007).** arXiv:0706.1776. **PREPRINT,
  INACCESSIBLE.** Downgraded — do not cite as primary evidence.

**Note (per point E):** The corrected charter uses a specific
cross-spectral estimator defined in §3.3. That specific construction
is NOT attributed to Welch, Bendat–Piersol, or Rosenberg unless
full-text verification confirms it. It is written out explicitly
here as a PF-declared estimator subject to (a) verification against
standard multitaper / multichannel spectral estimation literature by
a qualified reader with access, or (b) treatment as a new PF choice.

### §2.5 Consciousness-state EEG study design — background references (corrected)

- **Sitt, J. D., et al. (2014).** *Brain* 137:2258–2270.
  doi:10.1093/brain/awu141. **PRIMARY EXPERIMENTAL PAPER,
  FULL-TEXT-VERIFIED 2026-09-13** via
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC4610185/?report=printable`.
  Sample: 173 initial patient recordings, 6 discarded (<200 non-
  artefacted trials), 167 valid recordings from 113 distinct patients,
  patients recorded 1–6 times; 75 VS + 68 MCS + 24 brain-injured
  conscious (CS) + 14 healthy controls = 181 recordings total.
  Acquisition: 256-electrode EGI geodesic sensor net, 250 Hz sampling,
  vertex reference during recording, 0.2–45 Hz bandpass, Local-Global
  auditory protocol, ±150 µV voltage / ±80 µV eye-movement / ±150 µV
  eye-blink rejection, >20% electrode rejection interpolated, trials
  with >20 corrected electrodes rejected, average reference AFTER
  cleaning. Classifier: linear Support Vector Classifier (Pedregosa
  et al. 2011), stratified nested cross-validation. Best single measure
  AUC = 71 ± 4% for VS-MCS. Whole-feature-set AUC = 78 ± 4% (P < 0.001)
  for VS-MCS. Diagnostic agreement: 67% (50/75) of VS-diagnosed and
  76% (52/68) of MCS-diagnosed recordings classified in their respective
  clinical categories. Generalisation: 89% (34/38) of CS/healthy
  recordings classified as MCS (conscious side).
  **Cross-validation patient grouping: UNKNOWN.** Manuscript documents
  "stratified nested cross-validation" but does not explicitly state
  whether repeated recordings from the same patient (1–6 recordings
  per patient) were kept in the same CV fold. Possible subject-level
  leakage is FLAGGED as a caveat on the reported AUCs (per correction
  J and 2026-09-13 verification pass).
  **Correct interpretation of AUC = 78 ± 4%.** This is the multivariate
  (whole feature set) classifier AUC for **VS-versus-MCS** comparison
  ONLY. It is NOT a generic conscious-vs-unconscious result spanning
  wakefulness, sleep, anesthesia, and UWS. It does NOT validate χ_k.
  Do NOT convert this classifier AUC into a Cohen's d for a χ_k power
  calculation. 167 valid recordings must NOT be treated as 167
  independent patients (113 distinct patients contributed).
  Sitt's acquisition settings (256-ch EGI, 250 Hz, vertex ref then
  average-rereferencing after cleaning, 0.2–45 Hz, Local-Global
  auditory protocol, ±150 µV threshold) are those of one experimental
  protocol; they are NOT adopted as universal recommendations for the
  χ_k pipeline of §3.
  **Paradigm mismatch (load-bearing).** Sitt used a TASK-EVOKED
  Local-Global auditory protocol (evoked responses time-locked to
  auditory stimuli); the proposed χ_k pipeline (§3, §5) is a
  CONTINUOUS/windowed spectral-change construction with NO stimulus
  time-locking. The two paradigms probe different neural regimes.
  Sitt therefore supplies NEITHER direct validation NOR a power
  prior for χ_k.
  **Representation mismatch (load-bearing).** Sitt applied average
  rereferencing after cleaning for spectral analyses BUT used a
  surface Laplacian (Current Source Density) transformation for
  connectivity measures — verified verbatim from the High-density
  scalp section: "Connectivity measures were based on a spatial
  Laplacian transformation of the EEG—a computation also known as
  the Current Source Density estimate." This means Sitt does NOT
  endorse CAR sensor-level cross-spectral matrices as the primary
  representation for connectivity-adjacent quantities. The charter's
  §3.3 sensor-level cross-spectral matrix on CAR-rereferenced data
  is therefore NOT justified by Sitt; the choice among CAR vs
  REST/rREST vs surface Laplacian/CSD vs source-space remains an
  open load-bearing decision (see charter §13 U2 and the focused
  bridge audit `codex/CHURN_CHI_K_EEG_BRIDGE_AUDIT_2026-09-13.md`
  when produced).
- **Casali, A. G., et al. (2013).** *Sci. Transl. Med.* 5:198ra105.
  **PRIMARY EXPERIMENTAL PAPER (PCI), INACCESSIBLE.** Cited only for
  PCI as measured within the primary paper.
- **Sarasso, S., et al. (2015).** *Curr. Biol.* 25:3099–3105.
  **PRIMARY EXPERIMENTAL PAPER, INACCESSIBLE.** Cited only for
  propofol/xenon/ketamine PCI within the primary paper.
- **King, J. R., et al. (2013).** *Curr. Biol.* 23:1914–1919.
  **PRIMARY EXPERIMENTAL PAPER (wSMI), INACCESSIBLE.** Cited only
  for wSMI within the primary paper.

**Preregistration standard:**
- **Nosek, B. A., et al. (2018).** *PNAS* 115:2600–2606.
  **META-SCIENCE ESSAY, SECONDARY.**
- OSF preregistration template: https://osf.io/prereg/

## §3. Candidate pipeline (design intent, unverified specific choices)

**⚠ Every specific numerical choice below is a PRINCIPIA FRACTALIS
preregistered design choice PENDING primary-source justification per
point B. No specific value below has been supported by a
full-text-verified passage of any cited primary source. Where a value
is claimed to be "standard," that claim itself is a background
reference to typical EEG-research practice.**

### §3.1 Preprocessing (PF design choices per point B)

Fixed pre-Layer-2 choices (each is a **PF preregistered design
choice**, marked ★ per point B, subject to primary-source
verification and to the §9 robustness checks):

1. ★ Recording: 64-channel EEG at ≥500 Hz sampling. Nunez-standard
   10–20 or 10–10 electrode placement. Rationale: consistent with
   common practice in the consciousness literature (background:
   Nunez–Srinivasan 2006).
2. ★ Reference montage: **PENDING DECISION**. Per point C, CAR is
   NOT established as canonical. The primary choice among {CAR, REST,
   Laplacian, linked mastoids} is a PF design choice pending: (a)
   full-text verification of the specific montage-choice recommendation
   from Yao et al. 2019 for cross-spectral applications, and (b)
   pilot analysis of reference-montage impact on the primary pipeline
   under §9. Recorded default (for pipeline specification, not
   endorsement): CAR, with REST as a mandatory sensitivity axis in
   §9.
3. ★ Bandpass filter: 0.5 − 45 Hz, zero-phase FIR Hamming window.
4. ★ Notch filter: IIR notch at line frequency (50 or 60 Hz per
   site), Q = 30.
5. ★ Artifact rejection: ICA (extended Infomax) followed by
   AUTOMATED component labelling (ICLabel per Pion-Tonachini et al.
   2019 OR ADJUST per Mognon et al. 2011) with MANDATORY BLINDED
   HUMAN REVIEW (per point D) of a preregistered stratified subset
   of flagged components. No fully unsupervised pipeline is
   permitted.
6. ★ Epoching: `T_win = 2 s` non-overlapping epochs; discard epochs
   with any channel `|amplitude| > 200 µV` after ICA.

**No specific value in the list above has been supported by a
verbatim primary-source passage from any cited work.** All are
labelled PF preregistered design choices per point B.

### §3.2 Feature construction (PF design choices, Route R2 primary)

For each retained epoch and each channel `c ∈ {1, ..., D_ch}`,
compute the STFT with PF-preregistered parameters:
- Window: Hamming, length ★ `T_stft = 500 ms`.
- Overlap: ★ 250 ms (50%).
- FFT length: next power of 2 ≥ window samples.

Output per epoch: `X_c(t_i, f_j) ∈ ℂ` for `t_i` centred at STFT
window positions, `f_j` at Fourier frequencies.

Restrict to a preregistered frequency-band set
`B = {b_1, ..., b_{D_bd}}` (★ default: δ 0.5–4, θ 4–8, α 8–13, β
13–30, γ 30–45 Hz; alternatives in §9).

Feature ordering (★ PF choice): channel-major, i.e.
`(c, b) → c · D_bd + b`. This ordering is arbitrary from the physics
side; it determines how the (channel, band) pair is embedded into
the D-dimensional feature vector.

**Feature dimension:** `D := D_ch · D_bd`. This D is preserved per
point G; NO channels or bands are discarded to force `D = 3^k`.

### §3.3 Cross-spectral / covariance estimator (corrected per point E)

**★ Corrected per point E.** The estimator does NOT average complex
amplitudes across a band before forming a single outer product
(which would invite phase-cancellation). It forms outer products at
each `(segment, frequency)` sample and averages the outer products:

**Per-band block estimator:**
```
S_b(t) := (1/(N · |F_b|)) · Σ_{s=0}^{N-1} Σ_{f ∈ F_b}
             X^{(c)}(t − s · Δ_stft, f) · [X^{(c')}(t − s · Δ_stft, f)]*
                                   for each channel pair (c, c').
```

That is, for each fixed band `b`, `S_b(t)` is a Hermitian PSD matrix
in `ℂ^{D_ch × D_ch}` estimated by averaging outer products of channel
vectors `(X^{(1)}, ..., X^{(D_ch)})` over both the super-window
segments `s ∈ [0, N)` and the frequency samples `f ∈ F_b`.

**★ Block-diagonal cross-band matrix:**
```
S(t) := block_diag(S_{b_1}(t), S_{b_2}(t), ..., S_{b_{D_bd}}(t))
      ∈ ℂ^{D × D}, D = D_ch · D_bd.
```
Each block is the within-band cross-channel Hermitian PSD matrix. The
off-block-diagonal blocks (cross-band coupling) are set to zero in
this primary construction, with the caveat below.

**★ Caveat on cross-band coupling.** Including nonzero cross-band
blocks (e.g., via `X^{(c, b)}(t) := band-averaged complex amplitude in
band b`, then `S = ⟨X X^H⟩`) would require a separate cross-frequency
coherence estimator. That is a distinct modelling choice that is NOT
adopted here in the primary construction. If required for a specific
scientific hypothesis, it must be specified with its own primary-
source justification and treated as an alternate pipeline in §9.

**Properties (proven from the construction; no primary source
required):**
- Each `S_b(t)` is Hermitian: `S_b(t) = S_b(t)^H` (sum of outer
  products `X X^H` is Hermitian).
- Each `S_b(t)` is PSD: for any `v ∈ ℂ^{D_ch}`,
  `v^H S_b(t) v = (1/(N|F_b|)) Σ_{s,f} |v^H X(t-sΔ, f)|² ≥ 0`.
- `Tr(S_b(t)) = (1/(N|F_b|)) Σ_{s,f} ‖X(t-sΔ, f)‖² ≥ 0`.
- The block-diagonal `S(t)` inherits all three: Hermitian, PSD,
  `Tr(S(t)) = Σ_b Tr(S_b(t))`.

**Reference honesty.** The above construction is written out
explicitly here as a PF-declared estimator. It is NOT attributed to
Welch (univariate PSD), Bendat–Piersol (textbook), or Rosenberg
(coherence framework) as the origin of this specific band-block
form. Full-text verification against multichannel-multitaper /
cross-spectral MEG-EEG literature by a qualified reader is a
pre-implementation obligation.

### §3.4 Normalization ρ_EEG(t) = S(t) / Tr(S(t)) (per point F)

**Definition (defined regime):**
```
ρ_EEG(t) := S(t) / Tr(S(t))     when Tr(S(t)) ≥ ε_min
```

**★ Zero-power exclusion rule (PF design choice per point B):**
- `ε_min := 10^{−12} · Tr(S̄)` where `Tr(S̄)` is the recording-wise
  median of `Tr(S(t))` computed on the artifact-cleaned data BEFORE
  any Layer-2 analysis. The `10^{−12}` factor is a **PF choice**.
- If `Tr(S(t)) < ε_min`: `ρ_EEG(t) := UNDEFINED`. The time window is
  EXCLUDED. NO default matrix substituted.
- ★ Excluded-window fraction reported per recording; any recording
  with > 5% excluded windows is flagged (the 5% threshold is a PF
  choice).

**Naming rationale (per point F):** The constructed object is renamed
`ρ_EEG(t)`, the "EEG-derived normalized PSD state matrix." Its
mathematical properties (Hermitian, PSD, trace-1) are proven from the
construction. **It is NOT an empirically established quantum density
operator of any physical system.** Nielsen–Chuang and Kliesch–Roth
supply the density-operator MATHEMATICAL FORMALISM but do NOT
supply an EEG-to-quantum bridge; that bridge is not claimed here.

### §3.5 Isometric embedding into H_k = ℂ^{3^k} (corrected per point G)

**Per point G, the naturally selected feature dimension `D` is NOT
altered to fit `3^k`.** Instead, an explicit isometric map `V` is
introduced as a NEW modelling map:

```
V : ℂ^D → ℂ^{3^k}     is an isometric linear map, i.e. V† V = I_D.
```

Choose `3^k ≥ D`. Specific construction of `V` is a PF design choice;
default: extend the standard basis of `ℂ^D` to a chosen `D`-subset of
the standard basis of `ℂ^{3^k}`. This is one specific `V`; other
isometries into `ℂ^{3^k}` are permissible but must be preregistered.

Define the embedded matrix:
```
ρ̃_EEG(t) := V · ρ_EEG(t) · V†     ∈ Matrix (Fin (3^k)) (Fin (3^k)) ℂ.
```

**Properties of ρ̃_EEG (proven from V† V = I_D and properties of
ρ_EEG):**
- Hermitian: `ρ̃† = (V ρ V†)† = V ρ† V† = V ρ V† = ρ̃`.
- PSD: `w† ρ̃ w = (V† w)† ρ (V† w) ≥ 0` for any `w ∈ ℂ^{3^k}`.
- Unit trace: `Tr(ρ̃) = Tr(V ρ V†) = Tr(V† V ρ) = Tr(ρ) = 1` (cyclicity,
  `V† V = I`).
- **Frobenius invariance under the isometric map:** for any Hermitian
  A, B ∈ ℂ^{D × D}, `‖V A V† − V B V†‖²_F = ‖V (A−B) V†‖²_F =
  Tr((V(A−B)V†)† V(A−B)V†) = Tr(V (A−B)† V† V (A−B) V†) = Tr((A−B)†
  (A−B) V† V) = Tr((A−B)² · I_D) = Tr((A−B)²) = ‖A − B‖²_F` (using
  Hermiticity of A−B and `V† V = I`). So:
  ```
  ‖ρ̃_EEG(t + Δt) − ρ̃_EEG(t)‖²_F = ‖ρ_EEG(t + Δt) − ρ_EEG(t)‖²_F
  ```

**IMPORTANT (per point G):** `V† V = I` preserves Frobenius churn
under `A ↦ V A V†`. But this does NOT establish:
- Any Timeless-Field ontology.
- Any T5 (digit-ancilla pure-state lift) compatibility. The T5
  invariance proven in Layer 1 concerns the SPECIFIC
  `digitAncillaLift` map, which is defined by digit decomposition; the
  isometry `V` used here is generally NOT equal to `digitAncillaLift`
  applied to any lower-level state, unless `V` is chosen with the
  specific tensor-product structure of §4.
- Any physical significance of `3^k` as the "correct" dimension.

**NO Lean implementation of `V`, of `ρ_EEG`, or of any Layer-2
estimator is included in this charter.**

## §4. Zero-padding is NOT automatic T5-compatibility

**Claim (unchanged from prior version).** Naive first-D zero-padding
of an EEG feature vector to `ℂ^{3^k}` is mathematically DISTINCT from
the Layer-1 pure-ancilla lift `digitAncillaLift`.

**Sufficient condition for T5-compatibility of an isometric
embedding** (as before): choose `D = 3^{k'}` for some `k' < k`, and
construct
`V : ℂ^{3^{k'}} → ℂ^{3^k}, ψ ↦ ψ ⊗ |0^{(k-k')}⟩`
(pure tensor product with the zero state on the added digits).
Under this construction, `V ρ V†` corresponds to `digitAncillaLift`
applied `(k - k')` times, and χ_k invariance follows from Layer 1
T5b.

For any other `V`, T5b does not automatically hold on `V ρ V†` unless
re-proven. **The Frobenius-preservation identity of §3.5 does NOT
imply T5-compatibility;** it only establishes that χ_k is unchanged
when both states are conjugated by the same isometry. The
Layer-1 result is stronger (partial trace recovers ρ; §T5a) and
requires the specific digit-decomposition structure.

## §5. Defining χ_k(t) at Layer 2

Given the pipeline of §3, define:
```
χ_k(t) := ½ · ‖ρ̃_EEG(t + Δt) − ρ̃_EEG(t)‖²_F
```

By §3.5's isometric-invariance identity, this equals
`½ · ‖ρ_EEG(t + Δt) − ρ_EEG(t)‖²_F`, so the χ_k value is invariant
under the choice of isometric embedding `V` (any V with `V† V = I`).

★ Fixed PF preregistered parameters:
- `Δt := N · Δ_stft = 8 × 250 ms = 2 s` — a PF choice.
- ρ super-window length matches Δt for non-overlapping steps.
- Feature ordering: channel-major (§3.2).
- `k`: PF choice, subject to `3^k ≥ D` per point G.

**Undefined regime:** If either `ρ_EEG(t)` or `ρ_EEG(t + Δt)` is
UNDEFINED per §3.4, then `χ_k(t) := UNDEFINED`.

## §6. Three-quantity separation Q1, Q2, Q3 — algebraic check (per point M)

For every recording, EACH of the three quantities is computed
INDEPENDENTLY:

**Q1(t) — ch32 clinical ch₂.** Per `ch32_consciousness_quantification.tex`
lines 191–322. Scalar in [0, 1]. Uses only real-valued band powers per
(channel, band), digitized to base-3, digit-summed, phase-factored,
weighted-summed, squared. NO cross-channel phase or covariance
information.

**Q2(t) — Linear entropy of ρ_EEG(t).**
```
S_L(ρ_EEG(t)) := 1 − Tr(ρ_EEG(t)²)     ∈ [0, 1 − 1/D].
```
Purely a function of `ρ_EEG(t)`.

**Q3(t) — Frobenius churn.** Per §5.

### §6.1 What is and is not established about Q1, Q2, Q3

**Established facts (only):**

- **Fact 1 — Q1 discards specified information.** The Q1 pipeline
  (band power → base-3 digit sum → phase factor → weighted sum →
  squared magnitude) uses only real-valued band powers per (channel,
  band). It does NOT use complex cross-channel phase or the
  cross-channel outer-product structure that Q2 and Q3 use.
- **Fact 2 — Q2 and Q3 both use the cross-spectral matrix.** Both are
  functionals of `ρ_EEG(t)` (Q2 single-time; Q3 two-time).
- **Fact 3 — No Q1 ↔ Q2/Q3 algebraic dependence or independence
  theorem has been proved.** Different computational formulas do NOT
  by themselves prove algebraic independence, and Q1's lossiness does
  NOT by itself establish that Q2 or Q3 varies across Q1's fibers.
  Neither direction has been formally shown; the Q1 ↔ Q2/Q3
  relationship is presently UNKNOWN and empirically testable.
- **Fact 4 — Q2 and Q3 obey the Frobenius identity.** By the
  Frobenius identity for Hermitian matrices,
  ```
  ‖A − B‖²_F = Tr(A²) + Tr(B²) − 2 Re Tr(A B).
  ```
  Applying with `A = ρ_EEG(t)`, `B = ρ_EEG(t + Δt)`:
  ```
  Q3(t) = (1/2)·[Tr(ρ_EEG(t)²) + Tr(ρ_EEG(t+Δt)²)] − Re Tr(ρ_EEG(t) ρ_EEG(t+Δt))
       = 1 − (1/2)·[Q2(t) + Q2(t+Δt)] − Re Tr(ρ_EEG(t) ρ_EEG(t+Δt)).
  ```
  So Q3 is DETERMINED by the triple
  `(Q2(t), Q2(t+Δt), Re Tr(ρ_EEG(t) · ρ_EEG(t+Δt)))`. The first two
  are single-time linear entropies; the third is the cross-time
  Frobenius inner product, a quantity NOT captured by Q2 alone.

**No further algebraic conclusions are drawn here.** In particular
the charter does NOT claim:
- Q1 is algebraically independent of Q2 or Q3.
- Q1 is not derivable from Q2/Q3 by any polynomial identity.
- Q1's lossiness suggests non-derivability in either direction.

Any empirical relation among Q1, Q2, Q3 is a testable hypothesis.
- Q2 and Q3 are algebraically LINKED via the Frobenius identity
  above.
- Q3 carries information about the cross-time overlap
  `Re Tr(ρ_EEG(t) ρ_EEG(t+Δt))` that Q2(t) and Q2(t+Δt) individually
  do NOT capture. This is why the charter's design is not reducible
  to reporting Q2 at two times.
- Any empirical claim that Q3 tracks a phenomenon DIFFERENT from
  what the Q2 pair `(Q2(t), Q2(t+Δt))` tracks is a claim about the
  cross-time overlap, and must be tested as such.

## §7. Dimensional / type ledger

| Symbol | Type | Domain | Range | Reference |
|---|---|---|---|---|
| `s_c(t)` | function | `[c ∈ [D_ch], t ∈ [T]]` | `ℝ` | Raw EEG |
| `x_c(t)` (R1) | function | `[c, t]` | `ℂ` | Hilbert |
| `X_c(t, f)` (R2) | function | `[c, t, f]` | `ℂ` | STFT |
| `S_b(t)` | matrix | — | `ℂ^{D_ch × D_ch}` | §3.3 per-band |
| `S(t)` | matrix | — | `ℂ^{D × D}`, `D = D_ch · D_bd` | §3.3 block-diag |
| `Tr(S(t))` | scalar | — | `ℝ_{≥ 0}` | §3.3 |
| `ρ_EEG(t)` | matrix (or ⊥) | — | `ℂ^{D × D}` or `UNDEFINED` | §3.4 |
| `V` | isometry | `ℂ^D → ℂ^{3^k}` | (linear, `V† V = I`) | §3.5 |
| `ρ̃_EEG(t)` | matrix (or ⊥) | — | `ℂ^{3^k × 3^k}` or `UNDEFINED` | §3.5 |
| `χ_k(t)` | scalar (or ⊥) | — | `ℝ_{≥ 0}` or `UNDEFINED` | §5 |
| Q1(t) | scalar | — | `ℝ ∈ [0, 1]` | ch32 |
| Q2(t) | scalar | — | `ℝ ∈ [0, 1 − 1/D]` | §6 |
| Q3(t) | scalar (or ⊥) | — | `ℝ_{≥ 0}` or `UNDEFINED` | §6 (= χ_k) |

## §8. Proof obligations for ρ_EEG(t) and ρ̃_EEG(t)

Whenever `ρ_EEG(t)` is defined (per §3.4):

- **PO1** Hermiticity: `ρ_EEG(t)† = ρ_EEG(t)`.
- **PO2** PSD: `v† ρ_EEG(t) v ≥ 0` for all `v ∈ ℂ^D`.
- **PO3** Unit trace: `Tr(ρ_EEG(t)) = 1`.
- **PO4** Undefined-regime disjunction: if `Tr(S(t)) < ε_min` then
  `ρ_EEG(t) = UNDEFINED`; else PO1–PO3 hold. Never both.
- **PO5** Isometric-embedding preservation: for `ρ̃_EEG(t) := V ρ_EEG(t) V†`
  with `V† V = I`, PO1 and PO2 are preserved directly. PO3 preserved
  since `Tr(V ρ V†) = Tr(V† V ρ) = Tr(ρ) = 1`.
- **PO6** Frobenius invariance under `V` (per §3.5):
  `‖ρ̃_EEG(t+Δt) − ρ̃_EEG(t)‖²_F = ‖ρ_EEG(t+Δt) − ρ_EEG(t)‖²_F`.

## §9. Robustness checks (secondary; NOT Bonferroni-corrected primary hypotheses)

**Per point L,** the following are SECONDARY sensitivity / robustness
checks, NOT independent primary hypotheses. The primary pipeline of
§3 is the ONE preregistered primary; each of the following axes is
varied around the primary defaults, and the primary contrast of §10
is reported unchanged. If any axis reverses or eliminates the primary
effect, that observation is a QUALIFIER on the primary result, not a
separate hypothesis.

**Robustness axes:**
1. Reference montage: CAR default vs. REST vs. Laplacian vs.
   linked-mastoids (per point C; primary choice pending §3.1 item 2).
2. Feature route: STFT R2 default vs. Hilbert R1 vs. Morlet R3.
3. Band selection: 5 canonical bands vs. individualized α-peak-centred
   vs. narrow-band (1 Hz bins).
4. Window length T_win: 2 s default vs. 1 s vs. 4 s.
5. STFT window T_stft: 500 ms default vs. 250 ms vs. 1000 ms.
6. Super-window count N: 8 default vs. 4 vs. 16.
7. Regularization for near-singular S(t): none default vs.
   PSD-preserving shrinkage (see below) vs. minimum-eigenvalue floor.
   **★ Per point H,** the shrinkage rule is defined directly rather
   than adopted from Ledoit & Wolf 2004 (which concerns real
   covariance). PF-declared PSD-preserving shrinkage:
   ```
   S_shr(t; α) := (1 − α) · S(t) + α · (Tr(S(t)) / D) · I_D,   α ∈ [0, 1].
   ```
   The shrinkage parameter α is a PF preregistered choice.
8. k choice: default per §3.5 (smallest k with `3^k ≥ D`) vs. next
   power of 3 up vs. next down (constrained by `3^k ≥ D` per point G).
9. Isometric map V: default (canonical subset of basis) vs. other
   preregistered isometric choices with V† V = I.
10. Feature ordering: channel-major default vs. band-major.
11. Δt for χ_k: 2 s default vs. 1 s vs. 4 s.
12. ε_min: `10^{-12} · Tr(S̄)` default vs. `10^{-9}` vs. `10^{-15}`.

**Analysis rule (per point L):** For each axis, compute the primary
contrast statistic; report as `(default effect, alternate effect,
sign preservation, magnitude ratio)`. NO Bonferroni correction is
applied ACROSS these axes as if they were independent primary
hypotheses. The default pipeline result is the primary; the
alternate-axis results characterize robustness.

## §10. Preregistered falsification design (corrected per points K, L)

### §10.1 Primary hypothesis (single, unambiguous; qualitative in the exploratory-pilot phase)

**H1_Layer2 (exploratory-pilot form):**
> The mean of χ_k(t) over each recording, computed on the primary
> pipeline of §3 and aggregated per patient, differs between Group A
> (behaviourally-verified conscious wakefulness) and Group C ∪ Group D
> (behaviourally-verified unresponsive), with effect direction reported
> alongside a patient-level confidence interval.

The exploratory-pilot phase reports effect-size point estimates and
confidence intervals; NO fixed Cohen's-d threshold or fixed α is a
confirmatory rejection criterion in this phase. A future confirmatory
phase would sharpen H1_Layer2 into a preregistered quantitative
statement whose thresholds are derived from the χ_k-specific pilot
variance and an independently chosen smallest effect size of
interest (see §10.3 and §12 placeholders).

### §10.2 Groups (preregistered inclusion criteria; single primary contrast per point L)

- **Group A — Wakefulness (primary conscious):** Healthy adults,
  eyes-closed resting state, Karolinska Sleepiness Scale ≤ 3 at
  recording.
- **Group C — Propofol anesthesia (primary unresponsive):** BIS
  20–40, target-controlled propofol infusion at surgical plane;
  behaviorally unresponsive.
- **Group D — Unresponsive wakefulness syndrome (primary
  unresponsive):** CRS-R score ≤ 6; behaviorally unresponsive.
- **Group B — Non-REM N2/N3 sleep (SECONDARY intermediate per point
  L):** Polysomnographically confirmed stages per AASM 2007. Not part
  of the primary contrast; reported as a preregistered secondary
  intermediate condition.

**Primary contrast:** `Group A vs Group (C ∪ D)`.
Secondary contrasts: `A vs C` alone; `A vs D` alone; `B vs A` and `B vs
(C ∪ D)` as intermediate; `C vs D` as unresponsive-subclass; sleep
sub-stages within B.

### §10.3 Sample size and status (corrected 2026-09-13 post-Sitt verification)

**No power calculation is quoted from Sitt et al. 2014.** After
full-text verification of Sitt 2014 (charter §2.5, audit R13), the
reported AUC = 78 ± 4% is a MULTIVARIATE VS-vs-MCS classifier AUC on
Sitt's own feature set. It is NOT a validation of χ_k, and it MUST
NOT be converted into a Cohen's d for χ_k. Any earlier text asserting
a chain "Sitt AUC → Cohen's d → n ≈ 64/group for χ_k" is INCORRECT
and is REMOVED from this charter.

**Charter status: EXPLORATORY PILOT.**

- The Layer-2 program is EXPLICITLY LABELED AN EXPLORATORY PILOT
  with NO confirmatory rejection claim in its present form.
- A future confirmatory power analysis for χ_k must be derived from
  ONE OF:
  1. Its OWN pilot variance estimates of `χ̄_k` per group, obtained
     from a preregistered pilot dataset;
  2. AN INDEPENDENTLY CHOSEN smallest effect size of interest
     specified before data collection (justified on
     domain-substantive grounds, NOT transferred from unrelated
     classifier AUCs);
  3. Both.
- Until such a preregistered, χ_k-derived power analysis is
  produced, the charter's rejection criteria of §12 are held in
  RESERVE and results are reported only as exploratory-pilot
  findings with confidence intervals and effect-size estimates —
  no formal confirmatory hypothesis-test verdict.

**Pilot recruitment target (subject to feasibility):**
- Preregister an achievable target per site and per group; the
  target is a pilot design decision, NOT a power-calibrated
  confirmatory sample size.

**Explicit warning.** The 2026-09-13 verification confirmed that
Sitt 2014's 167 valid recordings came from 113 distinct patients;
recordings must NOT be counted as independent patients. Any pilot
design for χ_k must follow the same discipline (analysis unit is
recording, but per-patient random effects and patient-grouped
splits are required to avoid subject-level leakage).

### §10.4 Statistical model (single primary pipeline per point L; patient-grouped per 2026-09-13 correction; statistical-unit language further corrected 2026-09-13)

**Unit-of-analysis discipline (correction 2026-09-13):**
- One *recording* = one *observation*.
- One *patient* = one *independent biological / inferential unit*
  when recordings repeat.
- All resampling and cross-validation must remain PATIENT-GROUPED:
  all recordings from a single patient are held together in the same
  training/test/bootstrap fold.
- Effective sample size and power are counted at the PATIENT level,
  NOT the recording level. 167 recordings from 113 distinct
  patients (Sitt 2014) has effective N ≈ 113 for
  patient-level inference, not 167.

**Model:**
- Time-average `χ_k(t)` per recording to obtain `χ̄_k` per recording.
- With ≥ ~5 recording sites, a mixed model with
  `(1 | Patient) + (1 | Site)` random effects is defensible.
- **With only 2 sites (as in the current charter §10.5
  cross-site-replication requirement), a site random effect is NOT
  reliably estimable.** Charter's default with 2 sites is therefore:
  `χ̄_k ~ Group + Site + (1 | Patient) + covariates (age, sex, montage version)`
  where `Site` is a FIXED effect. Only when a future design includes
  enough sites to identify a site variance component (typically ≥ 5
  sites) should site be moved to a random effect.
- Any classifier or predictive-model evaluation performed as part of
  Layer 2 (if any) MUST use PATIENT-GROUPED cross-validation splits.
- Primary test: `Group A vs Group (C ∪ D)` contrast.
- Report all secondary tests (§10.2) as EXPLORATORY.
- NO Bonferroni correction across the 12 robustness axes of §9;
  robustness axes are checks on the primary pipeline, not
  independent primary hypotheses.
- Multiple-comparison correction WITHIN the secondary-contrasts
  family is preregistered separately.

### §10.5 Preregistration

- Preregister on OSF BEFORE data collection at any site.
- Locked analysis pipeline hash before any group-level analysis.
- Ethics approvals, recruitment plans, and analysis scripts archived
  at preregistration time.

## §11. Negative controls and null models (per point L distinctions)

**Negative controls (measurement-artifact tests):**

- **NC1** Recording noise floor: 5-min short-circuit recording.
- **NC2** Time-shuffled surrogates: shuffle epoch order.
- **NC3** Phase-randomized multichannel surrogates (per point I,
  distinguished from Theiler univariate original):
  - **NC3a (independent per-channel phase randomization) — SURROGATE
    NULL.** Preserves per-channel PSD (auto-spectrum); DESTROYS all
    cross-channel phase relationships including zero-lag. Primary
    null against cross-spectral cross-channel dependence.

- **INV1** (renamed from NC3b per correction BB 2026-09-13) —
  **Common-phase rotation across all channels — EXACT INVARIANCE
  TEST, NOT A SURROGATE NULL.** For any global phase φ ∈ ℝ, applying
  the SAME phase rotation to every channel:
  `X(t, f) ↦ e^{iφ} · X(t, f)` yields identically
  `(e^{iφ} X)(e^{iφ} X)† = e^{iφ} X X† e^{-iφ} = X X†` (per element)
  since e^{iφ} is a scalar; therefore `S`, `ρ_EEG`, and `χ_k` are
  UNCHANGED EXACTLY (not merely up to null-distribution
  fluctuation). This is a DETERMINISTIC INVARIANCE PROPERTY of the
  estimator — a correctness / implementation check, NOT a
  surrogate-based null. Any implementation that alters `χ_k` under
  a common phase rotation applied to all channels contains a bug.
- **NC4** Single-channel recomputation with `D_ch = 1`: sanity check.
- **NC5** Independent Gaussian channels: matched to a specified
  covariance floor.

**Null models (per-hypothesis null distributions):**

- **NM1** AR(p) per channel (★ PF choice `p = 8`; subject to §9
  robustness): fit AR(p) per channel independently, simulate
  surrogate multichannel EEG that preserves per-channel autocorrelation
  but has no cross-channel structure. χ_k on simulated data gives a
  null distribution.
- **NM2** Group-permutation null: shuffle group labels across
  subjects; recompute primary contrast statistic. ★ PF choice: 5000
  permutations. Yields empirical null distribution of the primary
  contrast statistic under the null of no group difference.

**Uncertainty estimation (NOT a null model, per point L):**

- **UN3** Bootstrap over epochs: resample epochs within each recording
  with replacement to estimate the sampling distribution of
  per-recording `χ̄_k`. This provides CONFIDENCE INTERVALS on the
  primary contrast, not a null-hypothesis distribution. It is used
  in reporting effect-size CIs and NOT for rejection testing.

## §12. Placeholder confirmatory thresholds (NOT active rejection criteria)

**★ Corrected 2026-09-13 (per user directive).** The charter is
EXPLORATORY PILOT status per §10.3 and has NO χ_k-specific power
analysis. The threshold list below is therefore a set of
**unvalidated future confirmatory placeholders** — a template that
some future preregistered confirmatory phase would need to instantiate
against its OWN pilot-derived variance and independently chosen
smallest effect size of interest. In its present form, failure to
exceed these placeholders does NOT presently reject the scientific
hypothesis; equally, passing them does NOT presently confirm it.

Placeholder confirmatory criteria (candidates for a future preregistered
confirmatory phase, after a χ_k-specific pilot and power analysis
exist):

- **P1** (placeholder). Primary contrast (`Group A vs Group (C ∪ D)`)
  mean-`χ̄_k` difference reaches an effect-size threshold and
  statistical-significance level TBD by future power analysis. The
  specific values `d > 0.5, α = 0.05` sketched in earlier drafts are
  NOT active rejection thresholds.
- **P2** (placeholder). Effect direction is stable across §9
  robustness axes (specific quorum threshold TBD by future
  preregistration).
- **P3** (placeholder). Primary effect is INCONSISTENT with the NM2
  group-permutation null (patient-grouped permutation) at a level
  TBD by future preregistration. NM1 AR(p) surrogate result reported
  alongside as a secondary characterization.
- **P4** (placeholder). Group-A χ̄_k distribution does NOT show
  majority overlap with the 95% CI of the NC1 short-circuit
  recording noise. Single-subject overlap is not a rejection
  criterion.
- **P5** (placeholder). Group-A mean χ̄_k exceeds the NC2
  time-shuffled surrogate mean at a level TBD.
- **P6** (placeholder). χ̄_k correlates (Spearman |r| above a
  threshold TBD by future preregistration) with at least one
  established consciousness measure (Sitt 2014 primary-paper
  measures; Casali 2013 PCI; behavioural CRS-R). Non-correlation
  QUALIFIES any Layer-3 interpretive claim but does NOT prove χ_k
  is intrinsically unrelated to consciousness.
- **P7** (placeholder). Pipeline is reproducibly implementable from
  a future locked specification.

**Interpretation of a failure to meet these placeholders.** Under the
current exploratory-pilot status: NEITHER success NOR failure of any
individual P_i triggers a formal confirmatory verdict. The current
program reports exploratory findings and effect-size confidence
intervals only. A confirmatory verdict is reserved for a future
preregistered phase whose thresholds are calibrated to a
χ_k-specific power analysis. Rejection language ("Layer 3
disqualified", "χ_k unrelated to consciousness") is EXPLICITLY NOT
supported by exploratory-pilot data; those framings are reserved for
outcomes of a properly powered future confirmatory phase.

**Future-confirmatory-phase language discipline (applies ONLY if the
placeholders P1–P7 above are instantiated in a preregistered
confirmatory phase, after a χ_k-specific pilot and power analysis
exist):**
- A confirmatory failure of an instantiated H1_Layer2 would mean:
  NOT SUPPORTED under this specific operationalization. It would NOT
  prove χ_k is unrelated to consciousness.
- Layer 3 (consciousness interpretation) would be DISQUALIFIED under
  such a confirmatory failure, but the underlying mathematical
  construction Layer 1 would be UNAFFECTED. Alternative Layer-2
  constructions may still be scientifically motivated.
- These are language rules for a HYPOTHETICAL future confirmatory
  phase; the current exploratory-pilot charter does NOT itself apply
  them.

**The former R8 (Q1/Q2/Q3 linear dependence) is REMOVED** as a
rejection criterion: §6.1 records what is actually established
(Q2 and Q3 satisfy the Frobenius identity; Q3 carries a cross-time
overlap not captured by Q2 alone) and what remains unknown (any
Q1 ↔ Q2/Q3 algebraic relation). It is not converted into a
"proven independence" claim.

## §13. Unresolved choices and load-bearing assumptions

The following remain OPEN and require deliberation BEFORE
implementation:

- **U1.** Choice of `k` and the specific isometric map `V` when
  natural EEG `D` does not equal `3^{k'}` for any `k' ≤ k` where a
  T5-compatible tensor construction is available. Per point G, D is
  NOT altered; V is preregistered.
- **U2.** Reference montage (per point C). Yao et al. 2019 favors
  REST/rREST; charter default CAR is under review pending pilot
  reference-choice comparison in §9.
- **U3.** Complex feature route (R2 default, R1 and R3 in §9).
- **U4.** Feature-ordering convention (§3.2).
- **U5.** Regularization for near-singular S(t) (§9 axis 7); the
  PSD-preserving shrinkage rule of §9 is a PF choice not adopted from
  a primary source.
- **U6.** Consciousness ground-truth hierarchy (CRS-R, BIS, PSG); AASM
  sleep-stage inter-rater reliability documentation required.
- **U7.** Cross-site replication requirement (≥ 2 sites); pilot
  recruitment plan per site (target is a pilot design decision, NOT
  a power-calibrated confirmatory sample size — see §10.3 correction
  2026-09-13).
- **U8.** Sitt et al. 2014 sample composition and AUC are now VERIFIED
  from primary text (see §2.5 and §14). No power-calculation transfer
  from Sitt to χ_k is permitted; the χ_k program remains exploratory
  pilot until its OWN pilot variance and independently chosen
  smallest effect size of interest supports a new power analysis.
- **U9.** Full-text verification of every remaining citation in §14
  per the audit doc.
- **U10.** Patient-grouped cross-validation in Sitt 2014 is UNKNOWN
  from the primary text (documents "stratified nested cross-validation"
  but does NOT state patient-level grouping). Subject-level leakage is
  a possible confound on Sitt's reported AUC. Independent of this
  caveat on Sitt: the χ_k pilot design (§10.4) MUST enforce
  patient-grouped splits and per-patient random effects, and MUST NOT
  treat multiple recordings from the same patient as independent
  observations.

## §14. Background references — labelled types (per point A)

**⚠ Auditor did NOT verify any citation against its full text.**
Verdicts recorded in `codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md`.

**Textbooks (BACKGROUND):**
- Bendat, J. S., & Piersol, A. G. (2010). *Random Data* (4th ed.).
  Wiley-Interscience. ISBN 978-0-470-24877-5.
- Nunez, P. L., & Srinivasan, R. (2006). *Electric Fields of the
  Brain* (2nd ed.). Oxford University Press. ISBN 978-0-19-505038-7.
- Cohen, M. X. (2014). *Analyzing Neural Time Series Data*. MIT
  Press. ISBN 978-0-262-01987-3.
- Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and
  Quantum Information* (10th anniv. ed.). ISBN 978-1-107-00217-3.
  Cited for mathematical density-operator formalism ONLY; does not
  supply EEG-to-quantum bridge (per point F).

**Reviews (BACKGROUND):**
- Michel, C. M., & Brunet, D. (2019). *Frontiers in Neurology* 10:325.
- Yao, D., et al. (2019). *Brain Topography* 32:530–549. Establishes
  reference dependence; favors REST/rREST (per point C).
- Kliesch, M., & Roth, I. (2021). *PRX Quantum* 2:010201.
  Mathematical framework; does not supply EEG-to-quantum bridge (per
  point F).

**Primary methods papers (INACCESSIBLE to auditor; full-text
verification required):**
- Welch, P. D. (1967). *IEEE Trans. Audio Electroacoust.* 15:70–73.
  (univariate PSD)
- Widmann, A., et al. (2015). *J. Neurosci. Methods* 250:34–46.
- Bigdely-Shamlo, N., et al. (2015). *Frontiers in Neuroinformatics*
  9:16.
- Rosenberg, J. R., et al. (1989). *Prog. Biophys. Mol. Biol.*
  53:1–31.
- Jung, T. P., et al. (2000). *Psychophysiology* 37:163–178.
- Chaumon, M., et al. (2015). *J. Neurosci. Methods* 250:47–63.
  Does NOT describe ICLabel (per point D correction).
- Pion-Tonachini, L., Kreutz-Delgado, K., & Makeig, S. (2019).
  *NeuroImage* 198:181–197. Correct citation for ICLabel (per point D).
- Mognon, A., Jovicich, J., Bruzzone, L., & Buiatti, M. (2011).
  *Psychophysiology* 48:229–240. Correct citation for ADJUST (per
  point D).
- Theiler, J., et al. (1992). *Physica D* 58:77–94. UNIVARIATE
  surrogate; multichannel adaptation is charter's own construction
  (per point I).
- Ledoit, O., & Wolf, M. (2004). *J. Multivariate Anal.* 88:365–411.
  REAL covariance shrinkage; complex-Hermitian extension NOT
  addressed (per point H).

**Primary experimental papers — Sitt 2014 main article VERIFIED,
others INACCESSIBLE to auditor:**
- **Sitt, J. D., et al. (2014).** *Brain* 137:2258–2270.
  doi:10.1093/brain/awu141. **Main article full text VERIFIED
  2026-09-13** via
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC4610185/?report=printable`.
  Supplementary methods / material NOT recovered or audited. Sample
  and AUC facts recorded verbatim in §2.5. **Interpretation
  caveats** (see §2.5): AUC = 78 ± 4% is multivariate VS-vs-MCS
  classification only; NOT a generic conscious-vs-unconscious
  measure; does NOT validate χ_k; MUST NOT be converted into a
  Cohen's d for χ_k. Patient-grouped CV remains UNKNOWN pending
  supplementary-methods audit.
- Casali, A. G., et al. (2013). *Sci. Transl. Med.* 5:198ra105.
  doi:10.1126/scitranslmed.3006294. INACCESSIBLE to auditor;
  cite only for PCI as measured in the primary paper.
- Sarasso, S., et al. (2015). *Curr. Biol.* 25:3099–3105.
  INACCESSIBLE to auditor; cite only for anesthesia PCI as
  measured in the primary paper.
- King, J. R., et al. (2013). *Curr. Biol.* 23:1914–1919.
  INACCESSIBLE to auditor; cite only for wSMI as measured in the
  primary paper.

**Preprint (downgraded; do not cite as primary evidence):**
- Pascual-Marqui, R. D. (2007). arXiv:0706.1776.

**Meta-science essay (SECONDARY):**
- Nosek, B. A., et al. (2018). *PNAS* 115:2600–2606.

## §15. Chapter 32 vs Layer 2 — independence and empirical relation

Q1 (ch32 clinical ch₂) and Q3 (χ_k on ρ_EEG) are DIFFERENT
operational pipelines (see §6.1). They may or may not correlate
empirically. Empirical correlation would be a convergent-finding
observation to be tested; non-correlation would indicate they read
different axes of brain-state variation. Neither by itself measures
consciousness. Layer 3 requires the preregistered protocol of §10.

## §16. Charter stopping conditions (S1 was triggered; others active)

- **S1** (TRIGGERED 2026-09-13): auditor did not verify cited sources
  against full text. Correction: this revision + audit doc.
- **S2** through **S6**: as before; particular attention:
  - **S3** negative-control dominance (per NC1, NC2).
  - **S6** any proof obligation PO1–PO6 violation.

## §17. NOT implementation-ready. Pre-implementation checklist

**This charter is a DESIGN INTENT with acknowledged unresolved
verification obligations. It IS NOT implementation-ready.**

Before Layer 2 implementation begins:
- [ ] Full-text verification of each citation-per-claim mapping in
      §14 by a qualified reader with source access. Discrepancies
      flagged and corrected in a further charter revision.
- [x] Primary-paper recovery of Sitt et al. 2014 sample and AUC
      values (COMPLETED 2026-09-13; see §2.5, §14, audit R13). No
      power calculation for χ_k is transferred from Sitt.
- [ ] χ_k-specific pilot variance data collected and power analysis
      derived from χ_k pilot with an independently chosen smallest
      effect size of interest, if a confirmatory phase is desired.
- [ ] Ethics approvals for Groups A, C, D (and secondary B) at ≥ 2
      recording sites; blinded human ICA-review protocol locked.
- [ ] OSF preregistration document drafted from §10 and locked prior
      to any data collection.
- [ ] Software implementation plan (Python + MNE-Python + NumPy)
      independently audited for reproducibility.
- [ ] Explicit further approval from Pablo.

Layer 3 (consciousness interpretation) MUST NOT begin until Layer 2
implementation is complete and the primary hypothesis of §10 has been
either supported OR rejected per §12. Even under rejection, Layer 3
disqualification does not prove independence of χ_k from
consciousness — it only disqualifies THIS specific operationalization.

---

*Charter opened 2026-09-12. Revised 2026-09-13 with source-audit
corrections A–M. Companion documents:
`codex/CHURN_CHI_K_CHARTER_2026-09-12.md` (Layer 1 charter);
`codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md` (audit doc,
committed alongside this revision); `PF/Consciousness/FrobeniusChurn.lean`
(Layer 1 Lean, HEAD `cfe64dee`). NOT implementation-ready. No code,
no data, no consciousness claim.*
