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
   qualified reader with source access.
2. Recovery of the primary Sitt et al. 2014 sample and AUC (and any
   dependent power calculation) from the primary paper.
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

**Q1 and Q3 use disjoint input transforms and are algebraically
independent (§6 audit).** Q2 and Q3 are algebraically LINKED via the
Frobenius identity (§6) but Q3 carries information not in Q2 alone.
Empirical relationships beyond these algebraic facts are testable
hypotheses, not definitional identities.

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
  53:1–31. **METHODS PAPER, INACCESSIBLE.**
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
  doi:10.1093/brain/awu141. **PRIMARY EXPERIMENTAL PAPER, DIRECTLY
  CORRECTED per point J.** Per user verification, this paper analyzed
  181 recordings (not "n ≈ 200 patients"). AUC values from the
  primary paper's own analyses must be recovered for any quotation.
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

### §6.1 Algebraic dependence check (per point M — done NOW, not deferred)

**Q1 vs Q2 vs Q3:** Q1 uses digitized real-valued band powers passed
through a non-invertible nonlinear digit-sum-and-phase composition;
Q2 and Q3 use the complex cross-spectral matrix `ρ_EEG`. The two
input pipelines are DISJOINT (Q1 discards phase; Q2/Q3 use complex
values including phase). Therefore Q1 is not derivable from Q2 or Q3
by any polynomial identity, and vice versa.

**Q2 vs Q3:** By the Frobenius identity for Hermitian matrices,
```
‖A − B‖²_F = Tr(A²) + Tr(B²) − 2 Re Tr(A B).
```
Applying with `A = ρ_EEG(t)`, `B = ρ_EEG(t + Δt)`:
```
Q3(t) = (1/2)·[Tr(ρ_EEG(t)²) + Tr(ρ_EEG(t+Δt)²)] − Re Tr(ρ_EEG(t) ρ_EEG(t+Δt))
     = 1 − (1/2)·[Q2(t) + Q2(t+Δt)] − Re Tr(ρ_EEG(t) ρ_EEG(t+Δt)).
```

**Conclusion.** Q3 is DETERMINED by the triple
`(Q2(t), Q2(t+Δt), Re Tr(ρ_EEG(t) · ρ_EEG(t+Δt)))`. The first two are
single-time linear entropies; the third is the cross-time Frobenius
inner product, a quantity NOT captured by Q2 alone.

**Charter implication (replaces earlier R8 language).**
- Q1 is algebraically INDEPENDENT of Q2 and Q3.
- Q2 and Q3 are algebraically LINKED via the identity above.
- Q3 carries information about the cross-time overlap
  `Re Tr(ρ_EEG(t) ρ_EEG(t+Δt))` that Q2(t) and Q2(t+Δt) individually
  do NOT capture. This is why the charter's design is not
  reducible to reporting Q2 at two times.
- However, ANY empirical claim that Q3 tracks a phenomenon
  DIFFERENT from what the Q2 pair `(Q2(t), Q2(t+Δt))` tracks is a
  claim about the cross-time overlap, and must be tested as such.

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

### §10.1 Primary hypothesis (unified per point L)

**H1_Layer2 (primary, single, unambiguous):**
> The mean of χ_k(t) over each recording, computed on the primary
> pipeline of §3, differs between Group A (behaviourally-verified
> conscious wakefulness) and Group C ∪ Group D (behaviourally-verified
> unresponsive) with effect size Cohen's d > 0.5 at α = 0.05 on the
> primary contrast, controlling for site and recording covariates.

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

### §10.3 Sample size and status (corrected per point K)

Per point K: a Cohen's d = 0.5, α = 0.05, β = 0.20 power calculation
requires approximately `n ≥ 64` per independent group for a two-sample
comparison (standard formula `n ≈ 16 · (z_α + z_β)² / d² ≈ 16 · 7.85 /
0.25 ≈ 63`).

**Charter status (per point K):**

- The Layer-2 program is EXPLICITLY LABELED AN EXPLORATORY PILOT
  with NO confirmatory rejection claim, UNLESS Group targets are
  scaled to `n_A ≥ 64, n_(C∪D) ≥ 64` (or larger, per the site's
  achievable-recruitment plan).
- If achievable Group A + Group C + Group D recruitment is below
  the ≥ 64 per independent group threshold, the primary rejection
  criteria of §12 are suspended and results are reported as
  exploratory pilot findings only, with confidence intervals and
  effect-size estimates but no formal hypothesis-test verdict.
- If achievable recruitment meets or exceeds the threshold, primary
  rejection criteria of §12 apply.

**Recruitment target (subject to feasibility):**
- Confirmatory: `n_A ≥ 64`, `n_(C ∪ D) ≥ 64`, split across sites.
- Exploratory-pilot fallback: preregister target as ≥ 20 per group,
  results reported without confirmatory verdict.

### §10.4 Statistical model (single primary pipeline per point L)

- Time-average `χ_k(t)` per recording to obtain `χ̄_k` per subject.
- Mixed-effects linear model:
  `χ̄_k ~ Group + (1 | Site) + covariates (age, sex, montage version)`.
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
  - **NC3a (independent per-channel phase randomization):** Preserves
    per-channel PSD (auto-spectrum); DESTROYS all cross-channel phase
    relationships including zero-lag. Primary null against
    cross-spectral cross-channel dependence.
  - **NC3b (common-phase rotation across all channels):** Preserves
    all auto- AND cross-spectra; only shifts global phase; NOT a
    useful null for the primary hypothesis. Included only for
    calibration diagnostics.
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

## §12. Rejection criteria (corrected per point L)

H1_Layer2 is REJECTED if ANY of the following holds under the
confirmatory-sample condition of §10.3:

- **R1.** Primary contrast (`Group A vs Group (C ∪ D)`) mean-`χ̄_k`
  difference does not reach `d > 0.5` significance at α = 0.05 on the
  default pipeline (primary test).
- **R2.** Effect direction reverses on the majority (≥ 7 of 12) of
  §9 robustness axes.
- **R3.** Primary effect is NOT INCONSISTENT with the NM2
  group-permutation null at α = 0.05 (i.e., the observed primary
  contrast statistic lies within the 95% CI of the NM2 permutation
  null distribution). NM1 AR(p) surrogate result reported alongside
  as a secondary characterization.
- **R4.** Group-A χ̄_k distribution shows majority overlap (> 50% of
  Group A subjects) with the 95% CI of the NC1 short-circuit
  recording noise. (Per point L: single-subject overlap is not
  sufficient to reject; the criterion is majority.)
- **R5.** Group-A mean χ̄_k does not exceed the NC2 time-shuffled
  surrogate mean by any statistically detectable margin (`p > 0.05` on
  paired test).
- **R6.** χ̄_k fails to correlate `|Spearman r| > 0.3` (★ PF-selected
  threshold; the exact threshold value is a PF choice) with ANY of
  the established consciousness measures (Sitt et al. 2014 primary-
  paper measures; Casali et al. 2013 PCI; behavioural CRS-R for
  UWS/MCS). Non-correlation qualifies the interpretive claim (does
  not disprove χ_k intrinsically, but disqualifies the Layer-3
  "χ_k measures consciousness" claim).
- **R7.** Pipeline is not reproducibly implementable from this charter
  alone.

**Rejection language discipline (per point L):**
- Rejection of H1_Layer2 means: NOT SUPPORTED under this specific
  operationalization. It does NOT prove χ_k is unrelated to
  consciousness.
- Layer 3 (consciousness interpretation) is DISQUALIFIED under H1
  rejection but the underlying mathematical construction Layer 1 is
  UNAFFECTED. Alternative Layer-2 constructions may still be
  scientifically motivated.

**The former R8 (Q1/Q2/Q3 linear dependence) is REMOVED** because
the algebraic dependence check has been performed NOW in §6.1;
Q1 is algebraically independent of Q2 and Q3, and Q2 and Q3 are
algebraically linked by the Frobenius identity but Q3 carries
additional information not captured by Q2 alone.

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
- **U7.** Cross-site replication requirement (≥ 2 sites); recruitment
  plan for confirmatory `n ≥ 64` per group across sites.
- **U8.** Correct primary-paper AUC and sample composition for
  Sitt et al. 2014 (per point J), required to validate any
  power-calculation transfer.
- **U9.** Full-text verification of every citation in §14 per the
  audit doc.

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

**Primary experimental papers (INACCESSIBLE to auditor; specific
values require full-text verification):**
- Sitt, J. D., et al. (2014). *Brain* 137:2258–2270.
  doi:10.1093/brain/awu141. Per point J: 181 recordings; verify
  primary-paper AUC before quoting.
- Casali, A. G., et al. (2013). *Sci. Transl. Med.* 5:198ra105.
  doi:10.1126/scitranslmed.3006294. PCI as measured in primary paper
  only.
- Sarasso, S., et al. (2015). *Curr. Biol.* 25:3099–3105.
  Anesthesia PCI as measured in primary paper only.
- King, J. R., et al. (2013). *Curr. Biol.* 23:1914–1919. wSMI as
  measured in primary paper only.

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
- [ ] Primary-paper recovery of Sitt et al. 2014 sample and AUC
      values; valid power calculation from them.
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
