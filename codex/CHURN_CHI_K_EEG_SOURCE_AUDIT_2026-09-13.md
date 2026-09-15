# Layer 2 EEG Charter — Source Audit (2026-09-13)

*Correction-only audit of commit `1cabde90` on `r331b-provenance`.
Charter `codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md` triggered
its own §16 S1 stopping condition. This document records the
per-citation audit and required corrections; the charter is revised
in the same commit.*

## ★ Auditor-access disclosure (mandatory upfront) ★

**This auditor did NOT open the full text of any cited source when
drafting commit `1cabde90`.** The original citations were assembled
from training-time familiarity with abstracts, textbook indices, and
titles — not from live inspection of full-text bodies. That is the
exact failure mode the S1 stopping condition names ("The chosen
scientific reference for a step is found on primary-source
verification to be misquoted or unsupportive of the claimed step").

**Updated verification status (2026-09-13, cumulative through the
Layer-2 bridge revision pass):**

**Access record (2026-09-13, with per-source discipline):**
- **Sitt et al. (2014)** *Brain* 137:2258–2270 — main article via
  PMC PMC4610185. Supplementary methods / material NOT recovered
  or audited; any Sitt claim that depends on supplementary material
  remains UNVERIFIED (patient-grouped cross-validation in
  particular).
- **Prichard, D., & Theiler, J. (1994).** *Phys. Rev. Lett.*
  73:951–954. Verified via the open arXiv PDF
  `https://arxiv.org/pdf/comp-gas/9405002`. Provides the exact
  multivariate surrogate construction (Eq. 4 and Eq. 5) with the
  verbatim statement "where φ(f) is the same for all j".
- **Yao, D., et al. (2019).** *Brain Topography* 32:530–549.
  Verified via PMC PMC6592976. Explicit primary-source quotes
  recorded in the bridge audit.
- **Hu, S., Yao, D., & Valdes-Sosa, P. A. (2018).** arXiv:1802.02268
  (rREST). **PARTIAL READ**: relevant Introduction and §2.1 General
  reference model (pp. 1–5) inspected via the open arXiv PDF;
  remainder of the 21-page preprint NOT audited. Provides Eq. (1)–(4)
  of the general reference model, showing AR and REST as the
  uncorrelated-prior and volume-conductor-prior special cases of a
  unified Bayesian estimator; both are linear non-unitary
  transformations of the recorded EEG. The re-referencing matrix
  `H = I − 1·f^T` (Eq. 2) is a rank-deficient projection with
  `H · 1 = 0` (rank N−1 in general); the outer product `1·f^T`
  inside H is rank-1, but H itself is NOT rank-1 — earlier
  "rank-1" characterization was mathematically wrong and is
  corrected in this pass.

**All remaining citations in §14 / R1–R21** — UNVERIFIED by auditor
in the present access channels. In particular Nolte 2004 was
attempted at ResearchGate, DOI redirect, and Elsevier hub URLs and
returned 403 in every case; auditor could not read the primary
Nolte text this pass.

For the remaining unverified items, this audit:

1. Marks each unverified citation `INACCESSIBLE` for full-text
   verification by the auditor.
2. Applies the specific corrections directed by the user (Pablo
   Cohen) who has performed full-text verification for the corrected
   items.
3. Downgrades every unsupported specific numerical or methodological
   claim to a labelled Principia-Fractalis modelling choice per point
   B of the correction directive.
4. Triggers corresponding charter revisions in the same commit(s).

**Consequence:** the corrected charter is NOT implementation-ready.
It is a design document with acknowledged unresolved verification
obligations. Layer 2 implementation and Layer 3 initiation require
(a) full-text verification of each citation-per-claim mapping by a
qualified reader with source access, and (b) explicit further
approval by Pablo.

## §1. Verdict definitions

| Verdict | Meaning |
|---|---|
| SUPPORTED | The exact charter claim appears verbatim (or up to trivial notation change) in the cited source, at the specified page/section/equation. |
| PARTIALLY SUPPORTED | The general topic is discussed in the source, but the exact specific claim (numerical value, methodological detail) is not stated at the cited location. |
| MISMATCHED | The source does not support the charter's use of it; user-directed correction is authoritative. |
| SECONDARY ONLY | Textbook, review, or tutorial — allowed only as background per user directive A, not as primary evidence. |
| INACCESSIBLE | Auditor could not open the full text; verification pending. |

## §2. Per-citation audit table

Each row corresponds to one item in the original charter §14. Charter
sections that cited the item are enumerated; charter claim being
supported is quoted; audit verdict follows; required correction is
recorded.

### R1. Bendat, J. S., & Piersol, A. G. (2010). *Random Data* (4th ed.)

- **Source type:** Textbook (SECONDARY per point A).
- **Cited in:** §2.4 (cross-spectral estimation, Hermitian/PSD/trace≥0 properties); §3.3 (properties of `S(t)`).
- **Charter claim(s) supported:** "S(t, f) is Hermitian by construction"; "S(t, f) is positive semidefinite: for any v ∈ ℂ^D, v^H S v = (1/N) Σ_s |v^H X^(s)|² ≥ 0"; "Tr(S(t, f)) ≥ 0".
- **Cited location:** "Chapters 5–6".
- **Auditor verdict:** INACCESSIBLE (no full-text access). Also SECONDARY per point A.
- **Correction:** Downgrade from "reference" to "background textbook, pending full-text verification". Do NOT cite for the specific EEG-derived spectral-estimator construction of point E (a new PF construction, per point E correction below).

### R2. Welch, P. D. (1967). *IEEE Trans. Audio Electroacoust.* 15:70–73.

- **Source type:** Primary methods paper (univariate PSD estimation).
- **Cited in:** §2.4 (introduced as background for cross-spectral estimation).
- **Charter claim:** Method for spectral density estimation via averaged modified periodograms.
- **Auditor verdict:** INACCESSIBLE for full-text verification. Welch's original paper is UNIVARIATE PSD; the multichannel cross-spectral construction is a separate development. Charter's use as generic support for "cross-spectral estimation" is PARTIALLY SUPPORTED at best.
- **Correction:** Retain as background for the univariate PSD Welch's method; do NOT cite as origin of the multichannel cross-spectral construction. Do NOT cite as origin of the band-averaged construction of point E.

### R3. Widmann, A., Schröger, E., & Maess, B. (2015). *J. Neurosci. Methods* 250:34–46.

- **Source type:** Primary methods/tutorial (digital filter design for EEG).
- **Cited in:** §2.1, §3.1 (bandpass filter design; Hamming window; zero-phase FIR).
- **Charter claim:** "Bandpass filter: 0.5 − 45 Hz, zero-phase FIR Hamming window (Widmann et al. 2015, §5)".
- **Auditor verdict:** INACCESSIBLE. Even if the paper generally supports FIR filter design for EEG, the SPECIFIC choice of `0.5 − 45 Hz` and Hamming window are PF design choices, not values recommended by name in Widmann et al.
- **Correction:** Retain as background reference for the general practice of zero-phase FIR EEG filtering. Relabel the specific `0.5 − 45 Hz` and Hamming choices as PF-preregistered design choices per point B.

### R4. Nunez, P. L., & Srinivasan, R. (2006). *Electric Fields of the Brain* (2nd ed.).

- **Source type:** Textbook (SECONDARY per point A).
- **Cited in:** §2.1, §3.1 (recording, reference montage, volume conduction); §13 (U2).
- **Charter claim(s):** "Common average reference (CAR) computed over all channels... Rationale: canonical for cross-spectral analysis (Nunez & Srinivasan 2006, Chapter 7)".
- **Auditor verdict:** INACCESSIBLE + SECONDARY. The specific CAR-is-canonical claim is DIRECTLY CORRECTED by user (point C). Nunez & Srinivasan is a canonical textbook on EEG physics but does NOT establish CAR as the reference of choice; it in fact documents the reference-dependent nature of every scalp-EEG derived metric.
- **Correction:** Retain as background textbook. Do NOT cite as endorsing CAR. Per point C, restate the reference-montage sensitivity honestly: every choice (CAR, Laplacian, linked mastoids, REST) has known artifacts, and CAR is one of several defensible options — not the canonical one.

### R5. Michel, C. M., & Brunet, D. (2019). *Frontiers in Neurology* 10:325.

- **Source type:** Review (SECONDARY per point A).
- **Cited in:** §2.1 (preprocessing pipeline).
- **Charter claim:** Support for a preprocessing pipeline.
- **Auditor verdict:** INACCESSIBLE + SECONDARY. Per user direction (point C), this review "warns that sensor-level connectivity is reference- and volume-conduction-sensitive".
- **Correction:** Relabel as background review. Explicitly state (per point C) that channel-level covariance is a MEASUREMENT PROXY on scalp electrodes and cannot by itself be interpreted as cortical connectivity.

### R6. Cohen, M. X. (2014). *Analyzing Neural Time Series Data*. MIT Press.

- **Source type:** Textbook (SECONDARY per point A).
- **Cited in:** §2.3 (Hilbert transform, STFT, Morlet wavelets).
- **Charter claim:** General tutorial support for complex feature extraction routes R1, R2, R3.
- **Auditor verdict:** INACCESSIBLE + SECONDARY.
- **Correction:** Retain as background textbook for the three feature-extraction routes. Do NOT cite as primary origin of any specific formula.

### R7. Bigdely-Shamlo, N., Mullen, T., Kothe, C., Su, K.-M., & Robbins, K. A. (2015). *Frontiers in Neuroinformatics* 9:16.

- **Source type:** Primary methods paper (PREP pipeline software).
- **Cited in:** §2.1 (reproducible reference / rereference standard).
- **Charter claim:** Support for standardized preprocessing.
- **Auditor verdict:** INACCESSIBLE. PREP is a well-known software pipeline; auditor cannot verify the specific claims charter attributes to it.
- **Correction:** Retain as reference for the PREP pipeline concept. If PREP is chosen for the actual preprocessing, cite it against the specific pipeline version.

### R8. Yao, D., Qin, Y., Hu, S., Dong, L., Vega, M. L. B., & Sosa, P. A. V. (2019). *Brain Topography* 32:530–549.

- **Source type:** Review paper.
- **Cited in:** §2.1 (reference montage sensitivity); §13 (U2); §9 sensitivity axis 1.
- **Charter claim:** Support for the sensitivity of covariance-based metrics to reference montage choice.
- **Auditor verdict:** MISMATCHED per user direction (point C). Yao et al. establishes reference dependence and favors REST/rREST; the charter cited it in support of CAR-as-canonical, which is not what the review says.
- **Correction:** Restate honestly per point C: "Yao et al. 2019 establishes that reference-choice materially affects EEG coherence and covariance metrics, and their review favors REST/rREST over CAR as reducing volume-conduction and reference artifacts. The charter's choice of CAR is a PF design choice, and REST is a specific alternate that must be included in the §9 sensitivity analysis."

### R9. Rosenberg, J. R., Amjad, A. M., Breeze, P., Brillinger, D. R., & Halliday, D. M. (1989). *Prog. Biophys. Mol. Biol.* 53:1–31.

- **Source type:** **REVIEW** about Fourier analysis of neuronal SPIKE-TRAIN data (per correction 2026-09-13 point C). NOT a primary EEG cross-spectral methods paper. The prior classification "primary methods paper (Fourier analysis of neuronal coupling)" was wrong on both counts (paper type and application domain).
- **Cited in:** §2.4 (cross-spectral estimation).
- **Charter claim:** Support for the general practice of estimating cross-spectral matrices from windowed data.
- **Auditor verdict:** MISMATCHED (wrong paper type; wrong application domain) + INACCESSIBLE for full text.
- **Correction:** Reclassified as REVIEW about Fourier analysis of neuronal spike trains. NOT usable as a primary-source justification for the corrected charter §3.3 EEG cross-spectral construction. Remove any implication that it originates the specific band-block estimator.

### R10. Pascual-Marqui, R. D. (2007). arXiv:0706.1776.

- **Source type:** Preprint (unpublished).
- **Cited in:** §2.4 (zero-lag contribution removal from coherence).
- **Charter claim:** Support for imaginary coherence-style zero-lag removal.
- **Auditor verdict:** INACCESSIBLE. Preprints are non-peer-reviewed; retention as citation requires stronger justification than for peer-reviewed literature.
- **Correction:** Either remove or downgrade to "cf." — do not use as primary evidence.

### R11. Jung, T. P., Makeig, S., Humphries, C., Lee, T. W., McKeown, M. J., Iragui, V., & Sejnowski, T. J. (2000). *Psychophysiology* 37:163–178.

- **Source type:** Primary methods paper (ICA for EEG artifact removal).
- **Cited in:** §2.2 (ICA / blind source separation).
- **Charter claim:** Support for using ICA as an artifact-rejection tool.
- **Auditor verdict:** INACCESSIBLE. Jung et al. 2000 is canonical for ICA-based EEG cleaning; the general claim is likely SUPPORTED but auditor cannot confirm details of application.
- **Correction:** Retain as background for ICA-based artifact rejection.

### R12. Chaumon, M., Bishop, D. V., & Busch, N. A. (2015). *J. Neurosci. Methods* 250:47–63.

- **Source type:** Primary methods paper (practical guide to IC selection).
- **Cited in:** §2.2, §3.1 (automated component-based artifact selection via ADJUST/ICLabel).
- **Charter claim:** "ICA (extended Infomax) with automated selection via ADJUST or ICLabel (Chaumon et al. 2015)".
- **Auditor verdict:** MISMATCHED per user direction (point D). Chaumon et al. 2015 does NOT describe ICLabel; they explicitly caution against unsupervised automated component rejection.
- **Correction:** Per point D:
  - Remove "ICLabel" attribution to Chaumon et al.
  - Cite **Pion-Tonachini, L., Kreutz-Delgado, K., & Makeig, S. (2019).** "ICLabel: An automated electroencephalographic independent component classifier, dataset, and website." *NeuroImage* 198:181–197. (subject to same INACCESSIBLE audit caveat — retain as citation-pending-verification).
  - For ADJUST, cite the primary ADJUST paper: **Mognon, A., Jovicich, J., Bruzzone, L., & Buiatti, M. (2011).** "ADJUST: An automatic EEG artifact detector based on the joint use of spatial and temporal features." *Psychophysiology* 48:229–240. (also citation-pending-verification).
  - **Require blinded human quality review** for ICA-component selection; do NOT rely on automated classifiers alone. This is per user direction (point D).

### R13. Sitt, J. D., et al. (2014). *Brain* 137:2258–2270.

- **Source type:** Primary experimental paper.
- **Cited in:** §2.5, §10 (sample size / power calculation).
- **Charter claim (original commit 1cabde90):** "Sitt et al. (2014) which reported classifier AUC ≈ 0.78 for conscious vs unconscious discrimination with n ≈ 200 patients."
- **Verification status (2026-09-13):** **Main article read** via PMC full text at
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC4610185/?report=printable`
  (supplementary methods NOT recovered or audited)
  (accessed 2026-09-13). Auditor accessed the full primary text.
- **Verified primary-source facts (exact quotations with section
  location):**
  - *Patients section:* "We performed a total of 173 patient recordings.
    Six recordings were discarded because they presented <200 non-artefacted
    trials (see below). The remaining 167 valid recordings were acquired
    from 113 distinct patients (79 males and 34 females, sex ratio = 2.32)."
  - *Patients section:* "Patients were recorded one to six times."
  - *Results section:* "In total, 75 VS recordings, 68 MCS recordings, and
    24 brain-injured but conscious patients (CS) were recordings were
    acquired. Fourteen additional recordings were obtained from healthy
    control subjects." [sic — "were recordings" typo in source]
  - *Results section:* "We analysed a large set of 181 high-density
    256-channel EEG recordings"
  - *High-density scalp electroencephalography section:* "EEG recordings
    were sampled at 250 Hz with a 256-electrode geodesic sensor net (EGI)
    referenced to the vertex"
  - *High-density scalp section:* "Recordings were band-pass filtered
    (from 0.2 to 45 Hz)"
  - *High-density scalp section:* "Trials were then segmented from −200
    ms to +1336 ms relative to the onset of the first sound. Trials with
    voltages exceeding ±150 µV, eye-movements activity exceeding ±80 µV
    and eye-blinks exceeding ±150 µV were rejected."
  - *High-density scalp section:* "Electrodes with a rejection rate
    superior to 20% across trials were rejected and were interpolated.
    Trials with >20 corrected electrodes were rejected."
  - *High-density scalp section:* "The remaining trials were digitally
    transformed to an average reference"
  - *Auditory Stimulation section:* "Subjects were stimulated auditorily
    using the 'Local-Global' protocol"
  - *High-density scalp section:* "Connectivity measures were based on a
    spatial Laplacian transformation of the EEG—a computation also known
    as the Current Source Density estimate"
  - *Multivariate pattern section:* "we used a linear Support Vector
    Classifier (Pedregosa et al., 2011) with a probabilistic output
    calibration"
  - *Results, Combining measures section:* "To avoid over-fitting, the
    support vector machine was repeatedly fitted and evaluated on
    independent data sets using stratified nested cross-validation."
  - *Combining measures section:* "when the classifier was set to use
    the best cross-validated single measure the performance reached an
    AUC = 71 ± 4%, for the VS-MCS comparison"
  - *Combining measures section:* "By contrast, when using the whole set
    of measures, AUC was significantly higher than when using the best
    single measure: VS-MCS: AUC = 78 ± 4% (P < 0.001)"
  - *Automatic classification section:* "67% (50 of 75) of VS-diagnosed
    patients and 76% (52 of 68) of MCS-diagnosed patients were classified
    in their respective clinical categories solely from their brain
    activity"
  - *Automatic classification section:* "The great majority of these
    recordings (89%, 34 of 38) were classified as conscious (MCS rather
    than VS)"
- **Cross-validation patient-grouping — UNKNOWN:** Manuscript text
  documents *stratified nested cross-validation* but does NOT explicitly
  state whether repeated recordings from the same patient were kept in
  the SAME cross-validation fold. Given "patients were recorded one to
  six times" and 167 valid recordings from 113 distinct patients, there
  is a real risk of subject-level leakage (recordings from the same
  patient appearing in both training and test folds) if patient-grouped
  splitting was not enforced. This is FLAGGED as a possible confound in
  interpreting the reported AUC.
- **Auditor verdict:** MIXED. Sample counts, acquisition parameters,
  and classification statistics are SUPPORTED verbatim from the primary
  paper text. However:
  - The charter's earlier `n ≈ 200 patients` claim was wrong;
    correct figures are 167 valid recordings / 113 distinct patients /
    181 total recordings incl. healthy controls.
  - The AUC ≈ 0.78 figure IS in Sitt 2014, but ONLY for the multivariate
    (whole feature set) VS-vs-MCS classification, not for a generic
    conscious-vs-unconscious discrimination. It is NOT a validation of
    χ_k.
  - Whether patient-grouped CV was used is UNKNOWN from the primary
    text; flag possible subject leakage as a confound.
- **Corrections applied to charter:**
  - Sample and acquisition facts recorded with exact quotes and
    section locations (charter §2.5).
  - AUC 0.78 interpretation corrected: multivariate VS-vs-MCS only, not
    generic conscious-vs-unconscious, not a validation of χ_k.
  - Any conversion of this AUC into a Cohen's d for a χ_k power
    calculation is REMOVED. The corresponding n ≈ 64 per group claim
    (derived transitively from that AUC) is DELETED from §10.3.
  - χ_k program remains EXPLORATORY PILOT. A future power analysis
    must come from its OWN pilot variance and an independently chosen
    smallest effect size of interest, NOT from Sitt.
  - Sitt's acquisition settings (256-ch EGI, 250 Hz, vertex reference
    then average-rereferencing after cleaning, 0.2–45 Hz bandpass,
    ±150 µV threshold, Local-Global auditory task) are NOT adopted
    as universal recommendations. They are the specific settings from
    ONE experimental protocol; the χ_k pipeline (charter §3) uses its
    own PF preregistered design choices and does NOT claim to be
    Sitt-derived.
  - Patient-grouped CV UNKNOWN status flagged as UA8 in charter §13.

### R14. Casali, A. G., et al. (2013). *Sci. Transl. Med.* 5:198ra105.

- **Source type:** Primary experimental paper (PCI).
- **Cited in:** §2.5, §12 (rejection criterion R6 comparison).
- **Charter claim:** PCI is an established consciousness-index benchmark.
- **Auditor verdict:** INACCESSIBLE. Retain as reference for PCI; DO NOT quote specific measurement values or classifier performance without full-text verification.
- **Correction:** Per point J: "Keep Casali PCI ... limited to what their primary paper actually measured." Reference PCI as an established measure only within its own paper's scope.

### R15. Sarasso, S., et al. (2015). *Curr. Biol.* 25:3099–3105.

- **Source type:** Primary experimental paper (anesthesia + consciousness).
- **Cited in:** §2.5.
- **Auditor verdict:** INACCESSIBLE.
- **Correction:** Per point J: cite only for what the primary paper measured (propofol / xenon / ketamine PCI). Do NOT extrapolate to unrelated conditions.

### R16. King, J. R., et al. (2013). *Curr. Biol.* 23:1914–1919.

- **Source type:** Primary experimental paper (weighted symbolic mutual information — wSMI).
- **Cited in:** §2.5.
- **Auditor verdict:** INACCESSIBLE.
- **Correction:** Per point J: cite only for wSMI as measured in the primary paper.

### R17. Theiler, J., Eubank, S., Longtin, A., Galdrikian, B., & Farmer, J. D. (1992). *Physica D* 58:77–94.

- **Source type:** Primary methods paper (surrogate data for nonlinearity testing).
- **Cited in:** §11 (NC3, phase-randomized surrogates).
- **Charter claim:** "Phase-randomized surrogates (Theiler et al. 1992): Preserve per-channel power spectrum but destroy cross-channel phase relationships."
- **Auditor verdict:** PARTIALLY SUPPORTED per user direction (point I). Theiler's original construction is UNIVARIATE (one time series at a time). The multichannel extension used by the charter (independently randomizing phases per channel) is a well-known adaptation but is NOT identical to Theiler 1992's original construction, and its exact statistical properties depend on whether COMMON or INDEPENDENT phase rotations are applied.
- **Correction:** Per point I: distinguish Theiler's univariate surrogate from the charter's multichannel adaptation. Specify: independent phase rotations per channel PRESERVE per-channel power spectra but DESTROY all cross-channel phase relationships (including zero-lag). Common (same) phase rotation across channels PRESERVES all cross-spectral relationships but simply shifts phase globally; this is not useful for null testing. State exactly which the charter uses; if independent, note that per-channel PSD is preserved but that the resulting null is a strong one — the cross-channel PSD off-diagonals are erased.

### R18. Ledoit, O., & Wolf, M. (2004). *J. Multivariate Anal.* 88:365–411.

- **Source type:** Primary methods paper (real-covariance shrinkage estimator).
- **Cited in:** §9 (sensitivity axis 7); §13 (U5).
- **Charter claim:** "Ledoit-Wolf shrinkage" as regularization option for near-singular S(t).
- **Auditor verdict:** MISMATCHED per user direction (point H). Ledoit & Wolf 2004 concerns REAL covariance estimation; direct application to COMPLEX HERMITIAN cross-spectral matrices is a non-trivial extension that requires verification (or a separate primary source for the complex case).
- **Correction:** Per point H: either
  - (H.1) locate a primary methods paper for shrinkage estimation of complex Hermitian cross-spectral matrices; OR
  - (H.2) define a simple PSD-preserving shrinkage rule directly, e.g.
    `S_shr(t; α) := (1 − α) · S(t) + α · (Tr(S(t))/D) · I_D`
    for `α ∈ [0, 1]`, and label `α` a PF-preregistered design choice per point B.
  - Do NOT continue to cite Ledoit & Wolf 2004 for the complex-Hermitian case without such verification.

### R19. Nosek, B. A., et al. (2018). *PNAS* 115:2600–2606.

- **Source type:** Meta-science essay.
- **Cited in:** §2.5, §10 (preregistration standard).
- **Charter claim:** Support for preregistration as a standard practice.
- **Auditor verdict:** INACCESSIBLE + SECONDARY (essay-review character).
- **Correction:** Retain as general reference for preregistration practice. The specific OSF preregistration workflow is a general research-practice choice, not a scientific measurement.

### R20. Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th anniv. ed.).

- **Source type:** Textbook (SECONDARY per point A).
- **Cited in:** §14 (mathematical framework for density matrices).
- **Charter claim:** Standard reference for density operator formalism.
- **Auditor verdict:** SECONDARY + does NOT supply EEG-to-quantum bridge (per point F).
- **Correction:** Per point F: retain as textbook reference for the MATHEMATICAL density-operator formalism (Hermitian, PSD, trace-1 objects and their properties). Explicitly note it does NOT supply any physical bridge from EEG signals to quantum states. The renamed object `ρ_EEG(t)` is a mathematically well-defined density operator but is NOT interpreted as an empirically established quantum state of the brain.

### R21. Kliesch, M., & Roth, I. (2021). *PRX Quantum* 2:010201.

- **Source type:** Review paper (quantum system certification).
- **Cited in:** §14 (Frobenius / trace norm framework).
- **Charter claim:** Reference for norms in quantum verification.
- **Auditor verdict:** INACCESSIBLE + SECONDARY (review). Also per point F: does NOT supply EEG-to-quantum bridge.
- **Correction:** Retain as mathematical reference for norm-based comparison of density operators in quantum information; explicitly note the EEG-derived object is not a quantum state.

## §3. Corrections directly ordered by the user

The user's directive supplies 13 corrections labelled A–M. Each is
recorded here for cross-reference to the corrected charter revision
committed alongside this audit:

- **A.** Remove "primary" claim for §14 sources; label textbooks,
  reviews, and tutorials as background only; do not say "verified"
  where only metadata / abstract was accessible.
- **B.** Relabel every unsupported numerical/methodological choice as
  a new preregistered PF design choice pending primary-source
  justification. Specific values to relabel (per user directive):
  64 channels, ≥500 Hz sampling, CAR, 0.5–45 Hz bandpass, Hamming
  zero-phase filtering, notch Q=30, 2-s epochs, 200 µV rejection,
  STFT length/overlap, N=8, ε_min, p=8 for AR null, 5000
  permutations, 2σ, |Spearman r|>0.3 for rejection criterion R6,
  and the 5% exclusion threshold.
- **C.** CAR is not established as canonical; Yao favors REST/rREST;
  channel-level covariance is a measurement proxy, not cortical
  connectivity.
- **D.** Chaumon 2015 does not describe ICLabel; cite Pion-Tonachini
  et al. 2019 for ICLabel; cite the primary ADJUST paper (Mognon et
  al. 2011); require blinded human quality review.
- **E.** Correct the cross-spectral estimator: use
  `S_b(t) = average over segments s and frequencies f in band b of
  X_s(t,f) X_s(t,f)^H`, NOT band-average complex amplitudes then form
  a single outer product (which invites phase cancellation). If
  cross-band blocks are desired, specify a separate cross-frequency
  estimator; do not attribute to Welch / Bendat–Piersol / Rosenberg
  unless the exact construction appears there.
- **F.** Rename constructed object as "EEG-derived normalized PSD
  state matrix," `ρ_EEG(t)`. It is Hermitian, PSD, trace-1 but is NOT
  an empirically established quantum density operator. Nielsen–Chuang
  and Kliesch–Roth do not supply the EEG-to-quantum bridge.
- **G.** Do NOT discard electrodes or frequency bands to force
  `D = 3^k`. Preserve the scientifically selected feature dimension
  `D`. Treat `V : ℂ^D → ℂ^{3^k}` as a separate explicit isometric
  modelling map. `V†V = I` preserves Frobenius churn under
  `A ↦ V A V†`, but does NOT establish Timeless-Field ontology or T5
  digit-ancilla compatibility. No Lean implementation.
- **H.** Ledoit–Wolf is real-covariance; either find complex-Hermitian
  primary source or define a PSD-preserving shrinkage directly (rule
  above at R18) and label its parameter a PF choice.
- **I.** Theiler surrogate is univariate; specify common vs
  independent multichannel phase rotations; specify preserved and
  destroyed auto/cross-spectral properties.
- **J.** Sitt et al. 2014 analyzed 181 recordings; verify sample and
  AUC before quoting. Do not borrow later cross-site AUC ≈ 0.78. Keep
  Casali PCI, Sarasso anesthesia, King wSMI within primary papers'
  scope.
- **K.** Sample size 40/30/20 is NOT conservative if 64/group is
  required for d = 0.5, α = 0.05, β = 0.20. Either power the primary
  contrast adequately (target ≥ 64 per independent group per
  standard calculation) or explicitly label as EXPLORATORY PILOT with
  NO confirmatory rejection claim.
- **L.** Statistical design repair (multiple sub-items):
  - Choose ONE unambiguous primary contrast. Charter alternated
    between `A ∪ B vs C ∪ D` and `A vs C ∪ D`. Fix to
    `A vs C ∪ D`; keep B as secondary intermediate.
  - Specify ONE primary pipeline. The 12 sensitivity axes are
    sensitivity checks, not 12 Bonferroni-corrected primary
    hypotheses.
  - NM2 (group-label permutation) is a null test.
  - NM3 (bootstrap) is uncertainty estimation, NOT a null model.
  - Rewrite R3: the primary effect must be inconsistent with the
    valid null distribution(s), not merely "still positive on
    surrogates".
  - Do NOT reject the whole hypothesis because any single conscious
    participant overlaps the amplifier-noise 95% CI (statistical
    fluctuation is expected).
  - Distinguish "failure to support Layer 3" from "proof that churn
    is unrelated to consciousness" — the former is what a null result
    supports; the latter is not.
- **M.** Check `Q1, Q2, Q3` algebraic dependence NOW. Result of the
  algebraic check is stated in the revised charter §6 and summarized
  in §4 below.

## §3.5. Additional corrections applied 2026-09-13 (post-Sitt-verification pass)

Three further corrections applied to commit `05174d35` per user directive
after full-text access to Sitt 2014:

- **AA. Algebraic-independence language corrected.** Replace all
  instances of "Q1 is algebraically independent of Q2 and Q3" with
  "No definitional identity or algebraic dependence between Q1 and
  Q2 or Q3 has been established." Different computational formulas
  do NOT constitute a proof of algebraic independence; the earlier
  language was an overclaim.
- **BB. NC3b reclassified as exact-invariance test, not a surrogate
  null.** For any global phase `φ`: `(e^{iφ} X)(e^{iφ} X)† = X X†`
  identically. Therefore `S`, `ρ_EEG`, and χ_k are UNCHANGED EXACTLY
  under a common phase rotation applied uniformly to all channels.
  This is a deterministic invariance property (correctness check on
  the estimator's implementation), NOT a surrogate null distribution.
- **CC. Rosenberg 1989 reclassified as REVIEW about Fourier analysis
  of neuronal SPIKE-TRAIN data.** See R9 above. Not usable as a
  primary EEG cross-spectral methods paper.

## §4. Algebraic dependence check for Q1, Q2, Q3 (per point M — CORRECTED per AA)

**Q1 (ch32 clinical ch₂):**
```
Q1(t) = |Σ_b w_b · (1/D_ch) Σ_c exp(iπ√2 · D3(digitize(P_{c,b}(t))))|²
```
where `P_{c,b}` is the band-b power on channel c and `D3(·)` is the
base-3 digit sum. Q1 uses only real-valued channel-wise band powers,
passed through a nonlinear digitize-then-phase pipeline. It DISCARDS
cross-channel phase and cross-channel covariance information.

**Q2 (linear entropy):**
```
Q2(t) = 1 − Tr(ρ_EEG(t)²)
```
where `ρ_EEG(t) = S(t)/Tr(S(t))` is the normalized cross-spectral
matrix. Q2 depends on the full complex cross-spectral structure.

**Q3 (Frobenius churn):**
```
Q3(t) = (1/2) · ‖ρ_EEG(t + Δt) − ρ_EEG(t)‖²_F
```

**Algebraic relations found:**

**No definitional identity or algebraic dependence between Q1 and
Q2 or Q3 has been established.** The Q1 pipeline (digitized real
band powers → base-3 digit sum → phase factor → weighted sum →
squared magnitude) and the Q2/Q3 pipeline (complex cross-spectral
matrix → normalisation → single- or two-time functionals) have
disjoint computational forms. That observation, by itself, does NOT
prove algebraic independence in either direction — nor does the
observation that Q1 discards some information contained in the
complex signal. A claim of algebraic independence would require a
formal proof, and a claim of dependence in either direction would
require an explicit identity. Neither has been constructed here.
The Q1 ↔ Q2/Q3 relationship is presently UNKNOWN and empirically
testable.

**Q2 and Q3 are algebraically LINKED (but not identical).** The
Frobenius identity gives, for any Hermitian A, B:
```
‖A − B‖²_F = Tr(Aᴴ A) + Tr(Bᴴ B) − 2 Re Tr(Aᴴ B) = ‖A‖²_F + ‖B‖²_F − 2 Re Tr(A B)
```
(using Hermiticity `Aᴴ = A`, `Bᴴ = B`). Applying with
`A = ρ_EEG(t)`, `B = ρ_EEG(t+Δt)`:
```
Q3(t) = (1/2) · [Tr(ρ_EEG(t)²) + Tr(ρ_EEG(t+Δt)²)] − Re Tr(ρ_EEG(t) ρ_EEG(t+Δt))
      = (1/2) · [(1 − Q2(t)) + (1 − Q2(t+Δt))] − Re Tr(ρ_EEG(t) ρ_EEG(t+Δt))
      = 1 − (1/2) · [Q2(t) + Q2(t+Δt)] − Re Tr(ρ_EEG(t) ρ_EEG(t+Δt))
```

**Conclusion.** Q3 is DETERMINED by the triple
`(Q2(t), Q2(t+Δt), Re Tr(ρ_EEG(t) ρ_EEG(t+Δt)))`. The first two are
single-time linear-entropy readings; the third is the CROSS-TIME
Frobenius inner product, an independent quantity that neither Q2(t)
nor Q2(t+Δt) captures.

**Charter must be corrected to state (per AA correction):**
- No definitional identity or algebraic dependence between Q1 and
  Q2/Q3 has been established. Different computational formulas do
  not prove algebraic independence; only that the two constructions
  are not manifestly identical.
- Q2 and Q3 are algebraically linked through the Frobenius identity;
  Q3 is a function of the pair `(Q2(t), Q2(t+Δt))` and the cross-time
  overlap `Re Tr(ρ_EEG(t) ρ_EEG(t+Δt))`. The latter is not captured
  by Q2 alone, so Q3 is not a function of Q2 alone.
- The relationship between Q1 and Q2/Q3 is a TESTABLE EMPIRICAL
  question, not a definitional identity and not a claim of algebraic
  independence.

## §5. Load-bearing assumptions remaining unresolved after audit

Even after applying corrections A–M, the following assumptions are
load-bearing and NOT verified by primary literature:

**UA1. Every cited primary-methods paper (R2, R3, R7, R9, R10, R11,
R13, R14, R15, R16, R17) requires full-text verification** by a reader
with access. Auditor did not perform this verification.

**UA2. The corrected cross-spectral estimator (point E) is a PF
adaptation; primary-source origin (if any) not identified.** If a
standard reference exists (likely, as this construction is common in
multitaper / MEG analysis), citation and page must be located.

**UA3. The chosen preprocessing constants (bandpass edges, filter
form, notch Q, epoch length, amplitude reject threshold) are PF
choices; no primary source has been identified for each specific
value.** These are labelled PF choices in the revised charter, per
point B.

**UA4. The `D → 3^k` isometric embedding via arbitrary `V` (per
point G) has proven mathematical properties (V†V = I preserves
Frobenius) but no proven correspondence to the Layer-1
digit-compatible pure-ancilla lift.** The V used in Layer 2 is
therefore a NEW modelling map, not a T5-witnessed reduction.

**UA5. The specific power calculation for Layer 2 must NOT be
transferred from Sitt 2014.** Even after full-text verification of
Sitt 2014 (this update, 2026-09-13), the AUC = 78 ± 4% figure is a
multivariate VS-vs-MCS classification AUC on Sitt's own feature set —
NOT a validation of χ_k, NOT a generic conscious-vs-unconscious
result, and NOT convertible into a Cohen's d for a χ_k power
calculation. The χ_k program remains EXPLORATORY PILOT per point K;
a future power analysis must come from its OWN pilot variance and an
independently chosen smallest effect size of interest, NOT from
Sitt's classifier AUC.

**UA8. Patient-grouped cross-validation in Sitt 2014 is UNKNOWN
(2026-09-13 full-text verification).** The manuscript documents
"stratified nested cross-validation" but does NOT state whether
repeated recordings from the same patient (patients were recorded
1–6 times; 167 valid recordings from 113 distinct patients) were
kept in the same CV fold or could appear in both training and test
folds. If patient-grouped splitting was not enforced, subject-level
leakage may inflate reported AUC. FLAGGED as a possible confound in
any downstream use of Sitt's numbers. Note that this UNKNOWN
STATUS affects the interpretation of the Sitt paper's own AUC,
independent of any application to χ_k. Also: 167 valid recordings
must NEVER be treated as 167 independent patients.

**UA6. Ground-truth labels for the conscious/unresponsive
comparison** (CRS-R cutoffs for UWS/MCS; BIS ranges for anesthesia;
AASM sleep stages) require site-specific ethics approval and
inter-rater reliability documentation before data collection.

**UA7. The relationship between Q1 (ch32 clinical ch₂) and Q2/Q3
requires explicit modelling and is presently UNKNOWN.** The two
pipelines have disjoint computational forms (Q1: digitized powers →
digit sum → phase; Q2, Q3: complex features → cross-spectral matrix),
but that observation does NOT constitute a proof of algebraic
independence in either direction. Neither derivability nor
non-derivability of Q1 ↔ Q2/Q3 has been established. Any empirical
brain-state relationship between them is a separate empirical
question.

## §6. Auditor's summary

The commit `1cabde90` charter is NOT implementation-ready. It
represents a design intent whose specific claims were assembled
without full-text source verification. This audit records the
deficiency honestly and applies the specific corrections directed
by the user.

The revised charter (same commit as this audit) is a corrected
design intent, still not implementation-ready. Its remaining unmet
verification obligations are enumerated in §5 above.

Layer 2 implementation and Layer 3 initiation both require:
1. Full-text verification of all citation-per-claim mappings by a
   qualified reader with source access;
2. Recovery of the primary Sitt et al. 2014 sample and AUC values,
   with a valid power calculation from them;
3. Ethics approvals for Groups A–D at ≥ 2 recording sites;
4. Explicit further approval from Pablo per the standing
   collaboration discipline.

*Audit prepared 2026-09-13 in same commit as charter revision. NO
Lean modifications. NO book modifications. NO Layer 3 material. NO
implementation. `PF_Lean4_Code/PF/Analytic/RiemannXiTopEdge_r331c.lean`
untouched. Commit target: `r331b-provenance` only.*

---

## §7. 2026-09-14 primary-source verification pass for Phase-1 K4 blockers (L5)

This section is an **inaccessibility / provenance addendum**. It
records the primary-source verification pass performed on
2026-09-14 for the two Phase-1 blockers named in
`codex/CHURN_CHI_K_BENCHMARK_PHASE1_GENERATIVE_SPEC_2026-09-14.md`
§14 (K4). Neither blocker was closed against the strict
primary-source rule; both are downgraded in severity by
authoritative cross-checks that reproduce the load-bearing
equations, but neither cross-check may be promoted into primary
provenance for the K4 spec. The K4 spec is corrected only where a
mis-attribution to a paper that is NOT the primary source was
present.

### §7.1 Blocker A — Perrin et al. 1989 spherical spline: STATUS OPEN

**Primary source.** Perrin F, Pernier J, Bertrand O, Echallier JF.
*Spherical splines for scalp potential and current density mapping.*
Electroenceph Clin Neurophysiol 1989;72(2):184–187.
DOI: `10.1016/0013-4694(89)90180-6`.
PubMed: `PMID 2464490`.

**Access attempts (2026-09-14) and outcomes.**

| Channel | URL | Outcome |
|---|---|---|
| Elsevier ScienceDirect | https://www.sciencedirect.com/science/article/abs/pii/0013469489901806 | HTTP 403 to programmatic fetcher; abstract page paywalled to human reader |
| PubMed | https://pubmed.ncbi.nlm.nih.gov/2464490/ | Cookie wall; no free-full-text link visible; no PMC identifier |
| Semantic Scholar record | https://www.semanticscholar.org/paper/3633131bec6530252dc7b14af159ae1946f9a0a7 | Metadata only; no accessible PDF |
| HAL / INSERM institutional | (searched) | No hit for a self-archived preprint of the 1989 paper |
| ResearchGate | https://www.researchgate.net/publication/6774701 | Author-uploaded "Spherical Splines and Average Referencing in Scalp Electroencephalography" (Nunez-related follow-up), NOT the 1989 primary |
| GitHub allefeld/spherical-splines | https://github.com/allefeld/spherical-splines | Third-party MATLAB re-implementation; no equations reproduced; no verification statement against the primary |

**Verdict.** Perrin et al. 1989 primary full text was NOT accessed
on this branch. Blocker A remains **OPEN**.

**Cross-check obtained (non-primary; documentary only).**
Carvalhaes CG, de Barros JAdB. *The Surface Laplacian Technique
in EEG: Theory and Methods.* arXiv:1406.0458v2 (Nov 8, 2014;
preprint submitted to *International Journal of Psychophysiology*).
Openly accessible at `https://arxiv.org/pdf/1406.0458`. This is a
review paper. It reproduces Perrin 1989's spherical-spline
construction with clear attribution to Perrin et al. 1989. The
following equations are transcribed exactly from the Carvalhaes-
de Barros arXiv PDF and are attributed BY THAT PAPER to Perrin
1989. They are recorded here as a cross-check only and are NOT
promoted into primary provenance:

- **Eq. (33a)** (p. 17): `f_sph(r) = Σ_{i=1}^N c_i · g_m(r, r_i) + d`.
- **Eq. (33b)** (p. 18): `g_m(r, r_i) = (1/(4π)) · Σ_{ℓ=1}^{∞}
  ((2ℓ+1) / (ℓ^m · (ℓ+1)^m)) · P_ℓ(r̂ · r̂_i)`.
- **Eq. (36)** (p. 18): `Lap_s(f(r)) = -(1/r²) · Σ_{i=1}^N c_i ·
  g_{m-1}(r, r_i)`, valid for `m > 1`.
- Auxiliary Eq. (34)–(35): standard spherical-harmonic Laplacian
  identity `Lap_s(P_ℓ(r̂ · r̂_i)) = -(ℓ(ℓ+1)/r²) · P_ℓ(r̂ · r̂_i)`,
  derived by Carvalhaes-de Barros from Jackson 1999 (Classical
  Electrodynamics, p. 110).

**Attribution quotation** (Carvalhaes-de Barros 2014, p. 17,
verbatim): *"For the particular case of data points on spheres,
Wahba developed a pseudo-spline method that circumvent the
singularity of (26) by replacing the Euclidean distance with the
geodesic distance. This method, called spherical splines, was
used by Perrin et al. (1989) to developed one of the most popular
surface Laplacian methods in the literature."*

**Consistency with K4 §12.2.** The K4 spec's kernels `g_m` and
`h_m` are mathematically identical to Carvalhaes-de Barros
Eq. (33b) and (a rescaling of) Eq. (36):
- K4 `g_m(cos γ) = (1/(4π)) Σ_{n=1}^{N_g_trunc}
  ((2n+1)/(n^m(n+1)^m)) P_n(cos γ)` matches Eq. (33b) exactly
  (K4's `N_g_trunc` is a finite truncation; Carvalhaes-de Barros
  discuss the same truncation issue on p. 19).
- K4 `h_m(cos γ) = −(1/(4π r_scalp²)) Σ_{n=1}^{N_h_trunc}
  ((2n+1) n(n+1) / (n^m(n+1)^m)) P_n(cos γ)` equals
  `−(1/r_scalp²) · g_{m-1}(cos γ)` (algebraic reduction:
  `n(n+1)/(n^m(n+1)^m) = 1/(n^{m-1}(n+1)^{m-1})`), which matches
  Eq. (36).

**Rule preserved.** Carvalhaes-de Barros 2014 is a REVIEW paper.
It is not primary provenance for Perrin's equations. Under the
K4 §14 blocker-closure rule, Blocker A remains OPEN. Any future
attempt to close Blocker A must supply Perrin 1989 primary full
text with the equations quoted verbatim and their page numbers,
either by direct access or by an authoritative author-hosted
reproduction.

### §7.2 Blocker B — Berg-Scherg 1994 and the multishell leadfield: STATUS OPEN, RE-ATTRIBUTION APPLIED

**Named primary source (as previously in K4 §11.4).** Berg P, Scherg M.
*A fast method for forward computation of multiple-shell spherical
head models.* Electroenceph Clin Neurophysiol 1994;90(1):58–64.
DOI: `10.1016/0013-4694(94)90113-9`. PubMed: `PMID 7509274`.

**Access attempts (2026-09-14) and outcomes.**

| Channel | URL | Outcome |
|---|---|---|
| Elsevier ScienceDirect | https://www.sciencedirect.com/science/article/abs/pii/0013469494901139 | HTTP 403 to programmatic fetcher; paywalled |
| PubMed | https://pubmed.ncbi.nlm.nih.gov/7509274/ | Cookie wall; no free-full-text link visible |
| BESA (Berg's affiliation) wiki | https://wiki.besa.de/index.php?title=Source_Analysis_Head_Models | Cites Berg-Scherg 1994 but reproduces NO equations from it |
| ResearchGate / MPI-NL institutional | (searched) | No hit |

**Verdict on Berg-Scherg 1994.** Primary full text NOT accessed on
this branch. Blocker B remains **OPEN** for the strict primary-
source rule.

**Critical re-attribution finding.** Access-side reading of
authoritative secondary sources reveals that Berg-Scherg 1994 is
**NOT the primary source for an analytical Legendre-polynomial
series** for the three-shell EEG scalp potential. Berg-Scherg 1994
is a **fast-computation approximation** that fits three dipoles in
a homogeneous single-shell sphere to reproduce the potential of
a source in a multi-shell head model. My K4 §11.4 attributed a
schematic Legendre series to Berg-Scherg 1994 — that attribution
was WRONG.

**Correct primary source for the analytical multishell Legendre
series.** Zhang Z. *A fast method to compute surface potentials
generated by dipoles within multilayer anisotropic spheres.*
Phys Med Biol 1995;40(3):335–349. IOP Publishing.
URL: https://iopscience.iop.org/article/10.1088/0031-9155/40/3/001.
Access attempt: paywalled at IOPscience; no accessible PDF.
Earlier related primary: de Munck JC. *The potential distribution
in a layered anisotropic spheroidal volume conductor.* J Appl Phys
1988;64:464–470. Also paywalled.

**Cross-check obtained (non-primary; documentary only).** Mosher
JC, Leahy RM, Lewis PS. *EEG and MEG: Forward Solutions for
Inverse Methods.* IEEE Transactions on Biomedical Engineering
1999;46(3):245–259. DOI: `10.1109/10.748978`. Openly accessible
PDF at the University of Southern California Neuroimage lab:
https://neuroimage.usc.edu/paperspdf/IEEEBME99.pdf. This is a
peer-reviewed IEEE journal article that NOVELLY reformulates the
multishell EEG solution into a factored kernel form suitable for
inverse methods, and it EXPLICITLY quotes the Zhang 1995
compact series form on page 248. The following equations are
transcribed exactly from the openly accessible PDF and are
recorded as a cross-check only. Primary provenance rests with
Zhang 1995 (attributed as reference [52] in Mosher-Leahy-Lewis).

- **Eq. (15)** (p. 248, the M-shell EEG series):
  `v^M(r; r_q, q) = (q/(4π σ_M r²)) · Σ_{n=1}^{∞} ((2n+1)/n) ·
  (r_q/r)^{n-1} · f_n · (n cos α · P_n(cos γ) + cos β sin α ·
  P_n^1(cos γ))`
  where `P_n` and `P_n^1` are the Legendre and associated
  Legendre polynomials, respectively; `α` is the angle between
  the dipole moment `q` and the radial direction at the dipole
  location `r_q`; `γ` is the angle between `r_q` and the
  observation vector `r`; `β` is the angle between the plane
  `(r_q, q)` and the plane `(r_q, r)`.
- **Eq. (16)** (p. 248): `f_n = n / (n · m_22 + (1+n) · m_21)`.
- **Eq. (17)** (bottom of p. 248, product formula for the
  concentric-shell recursion, non-commuting product with the
  highest-index matrix applied first):
  ```
  [m_11 m_12]                          M-1  [ n + (n+1)σ_k/σ_{k+1}                (n+1)(σ_k/σ_{k+1} − 1)(r_q/r_k)^{2n+1} ]
  [         ] = (1/(2n+1)^{M-1}) · Π k=1   [                                                                              ]
  [m_21 m_22]                              [ n(σ_k/σ_{k+1} − 1)(r_k/r_q)^{2n+1}   (n+1) + n σ_k/σ_{k+1}                    ]
  ```
  where conductivities are arranged from innermost to outermost
  `σ_1, ..., σ_M` corresponding to radii `r_1 < r_2 < ... < r_M`.
- **Eq. (18)** (p. 248, Berg-Scherg approximation, distinct from
  Eq. (15)):
  `v^M(r; r_q, q) ≈ v^1(r; μ_1 r_q, λ_1 q) + v^1(r; μ_2 r_q,
  λ_2 q) + v^1(r; μ_3 r_q, λ_3 q)`,
  a sum of three single-shell evaluations at scaled dipole
  locations and moments (the "Berg parameters" `{μ_i, λ_i}`).

**Attribution quotation** (Mosher-Leahy-Lewis 1999, p. 248,
verbatim): *"The infinite series presentation of Zhang in [52] is
especially compact compared to earlier presentations (cf. [44])"*
(where [52] = Zhang 1995 and [44] = Rush & Driscoll 1969). And
regarding Berg-Scherg: *"Recent empirical work on closed-form
approximations by Berg and Scherg [3], and related theoretical
studies by Zhang [52], describe a valid method for approximating
the infinite series with as few as three evaluations of scaled
forms of the single shell model."*

**Consistency with K4 §11.4.** The K4 spec's schematic
`V_scalp = Σ λ_n(σ, r) (r_source/r_scalp)^n P_n(cos γ_{ij})` is
NOT the correct form of the multishell EEG series. The correct
form has:
- an angular structure with BOTH Legendre `P_n` (radial dipole)
  and associated Legendre `P_n^1` (tangential dipole);
- a `(2n+1)/n` prefactor and `(r_q/r)^{n-1}` radial-distance
  factor (NOT `(r_source/r_scalp)^n`);
- an `f_n` coefficient defined by the product-of-2×2-matrices
  recursion of Eq. (17) over conductivity and radius ratios
  across `M − 1` boundaries;
- a `(1 / (4π σ_M r²))` normalisation factor with the outermost
  conductivity `σ_M` (NOT arbitrary `σ_scalp`).

The K4 §11.4 schematic must be corrected to the Mosher-Leahy-Lewis
Eq. (15)–(17) form before any Phase-1 implementation. The
correction is applied in the K5 amendment.

**Rule preserved.** Zhang 1995 and de Munck 1988 primary full
texts were NOT accessed. Mosher-Leahy-Lewis 1999 is an accessible
peer-reviewed IEEE journal article — but it explicitly attributes
the multishell series to Zhang [52], so Mosher-Leahy-Lewis is a
secondary (though authoritative and independently re-derived)
reproduction, not the primary. Under the K4 §14 blocker-closure
rule, Blocker B remains **OPEN** as the "verify Zhang 1995
primary" obligation. The mis-attribution of the K4 schematic to
Berg-Scherg 1994 is corrected in K5.

### §7.3 Summary — Phase-1 blocker status after L5 pass

| Blocker | Primary source | Access | Status after L5 | Cross-check applied |
|---|---|---|---|---|
| A: P.LAP kernels `g_m`, `h_m` | Perrin et al. 1989 EEG Clin Neurophysiol 72(2):184–187 | INACCESSIBLE | OPEN | Carvalhaes-de Barros 2014 arXiv:1406.0458v2 (Eq. 33a, 33b, 36) |
| B: multishell leadfield analytical series | Zhang 1995 Phys Med Biol 40(3):335–349 (correct primary; Berg-Scherg 1994 was mis-attributed and is a fast approximation) | INACCESSIBLE | OPEN | Mosher-Leahy-Lewis 1999 IEEE TBME 46(3):245–259 (Eq. 15, 16, 17); K4 §11.4 mis-attribution corrected |

**Phase-1 readiness verdict unchanged.** Both blockers remain
OPEN. Neither the K4 §14 verdict nor the benchmark charter
§14.1 verdict changes at L5: Phase-1 is DOCUMENTED, NOT YET
IMPLEMENTATION-READY. No Phase-1 amendment authorised by K1–K4
has been retroactively promoted or downgraded here; K5 records
inaccessibility findings, corrects one mis-attribution, and
attaches authoritative cross-check quotations without promoting
them into primary provenance.

*L5 pass performed 2026-09-14. No Lean, no book, no
implementation, no Layer 3, no master push. Files modified in the
K5 commit: this source audit; benchmark charter; Phase-1
executable-spec document; bridge audit (K5 cross-reference
addendum only). `PF_Lean4_Code/PF/Analytic/RiemannXiTopEdge_r331c.lean`
untouched.*
