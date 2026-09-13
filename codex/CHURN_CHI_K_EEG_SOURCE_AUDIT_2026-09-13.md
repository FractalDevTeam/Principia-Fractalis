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

This auditor also has NO web-fetch, PubMed, arXiv, or publisher-PDF
access in the present environment. Therefore this audit CANNOT itself
verify the sources against their full text. It CAN and DOES:

1. Mark every citation `INACCESSIBLE` for full-text verification by
   the auditor;
2. Apply the specific corrections directed by the user (Pablo Cohen)
   who has performed full-text verification for the corrected items
   (§§C, D, E, H, I, J of the correction directive);
3. Downgrade every unsupported specific numerical or methodological
   claim to a labelled Principia-Fractalis modelling choice per point
   B of the correction directive;
4. Trigger a corresponding charter revision in the same commit.

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

- **Source type:** Primary methods paper (Fourier analysis of neuronal coupling).
- **Cited in:** §2.4 (cross-spectral estimation).
- **Charter claim:** Support for the general practice of estimating cross-spectral matrices from windowed data.
- **Auditor verdict:** INACCESSIBLE. Rosenberg et al. is well-known in the neurophysiology cross-spectral literature; auditor cannot verify whether they define the specific band-averaged construction of point E.
- **Correction:** Retain as background reference for coherence-style neurophysiology analysis. Do NOT cite as origin of point E's corrected construction unless full-text verification confirms it.

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
- **Charter claim:** "Sitt et al. (2014) which reported classifier AUC ≈ 0.78 for conscious vs unconscious discrimination with n ≈ 200 patients."
- **Auditor verdict:** MISMATCHED per user direction (point J). Per user, Sitt et al. analyzed 181 recordings (not "n ≈ 200 patients"); the AUC ≈ 0.78 value may correspond to a specific downstream cross-site analysis, not the original Sitt paper.
- **Correction:** Per point J: verify the exact sample composition and AUC as reported in Sitt et al. 2014 before quoting. Do NOT borrow the AUC ≈ 0.78 from later cross-site work. The power calculation of §10 that relied on this AUC is INVALID until the correct number is recovered from the primary paper.

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

## §4. Algebraic dependence check for Q1, Q2, Q3 (per point M)

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

**Q1 is algebraically independent of both Q2 and Q3.** Q1 uses only
digitized real-valued band powers per (channel, band), then a
non-invertible nonlinearity (digit-sum + phase factor). No identity
recovers cross-channel covariance, cross-time correlation, or the
complex phase information used by Q2 and Q3. Conversely, no identity
recovers Q1 from Q2, Q3, or their combination — the digit-sum
quantization is lossy.

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

**Charter must be corrected to state:**
- Q1 is algebraically independent of Q2 and Q3.
- Q2 and Q3 are algebraically linked through the Frobenius identity;
  Q3 is a function of the pair `(Q2(t), Q2(t+Δt))` and the cross-time
  overlap `Re Tr(ρ_EEG(t) ρ_EEG(t+Δt))`. The latter is not captured
  by Q2 alone, so Q3 is not a function of Q2 alone.
- **The empirical hypothesis is therefore not vacuous: even though
  Q3 is algebraically related to Q2, it carries information (the
  cross-time overlap) that Q2 does not. But the charter must not
  claim Q2 and Q3 are "definitionally independent" — they are not.**

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

**UA5. The specific power calculation for Layer 2 is INVALID until
the primary Sitt et al. 2014 sample and AUC values are recovered from
the primary paper.** Until then, the falsification protocol is at
"exploratory pilot" status per point K.

**UA6. Ground-truth labels for the conscious/unresponsive
comparison** (CRS-R cutoffs for UWS/MCS; BIS ranges for anesthesia;
AASM sleep stages) require site-specific ethics approval and
inter-rater reliability documentation before data collection.

**UA7. The relationship between Q1 (ch32 clinical ch₂) and Q2/Q3
requires explicit modelling.** They use disjoint input transforms
(Q1: digitized powers → digit sum → phase; Q2, Q3: complex features →
cross-spectral matrix), so Q1 is not derivable from Q2, Q3 or vice
versa. But this does not mean they carry independent BRAIN-STATE
information; that is an empirical question, distinct from the
algebraic-independence check of §4 above.

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
