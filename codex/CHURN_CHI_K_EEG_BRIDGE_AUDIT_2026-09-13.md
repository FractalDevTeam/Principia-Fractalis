# Layer 2 EEG→ρ_EEG Measurement-Bridge Focused Audit — 2026-09-13 (Revised)

*Focused source-verification pass on the four load-bearing bridge
questions (A cross-spectral estimator; B montage representation; C
block-diagonal band combination; D phase-randomized surrogates). This
document replaces the earlier bridge audit commit `00087f33`, whose
"journal-access blocker" finding was FALSE: multiple primary/full-text
sources were openly accessible via user-supplied URLs and have now
been read in full.*

## §0. Access record (this pass)

**Access record (2026-09-13):**

- **Prichard, D., & Theiler, J. (1994).** *Phys. Rev. Lett.* 73:951–954.
  **FULL 4-page article read** via `https://arxiv.org/pdf/comp-gas/9405002`
  (arXiv comp-gas/9405002, 12 May 1994).
- **Sitt, J. D., et al. (2014).** *Brain* 137:2258–2270. **Main
  article read** (supplementary methods NOT recovered) via
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC4610185/?report=printable`.
- **Yao, D., et al. (2019).** "Which reference should we use for EEG
  and ERP practice?" *Brain Topography* 32:530–549. **REVIEW read**
  via `https://pmc.ncbi.nlm.nih.gov/articles/PMC6592976/`.
- **Hu, S., Yao, D., & Valdes-Sosa, P. A. (2018).** "Unified Bayesian
  estimator of EEG reference at infinity: rREST." arXiv:1802.02268.
  **PARTIAL READ** — Introduction and §2.1 General reference model
  (pp. 1–5 of the 21-page preprint) inspected via
  `https://arxiv.org/pdf/1802.02268`. Remainder NOT audited. Do NOT
  describe as "full-text verified" — 5-of-21 pages is not full-text
  verification.
- **Tenke, C. E., & Kayser, J. (2015).** "Surface Laplacians (SL) and
  phase properties of EEG rhythms: Simulated generators in a
  volume-conduction model." **Read** via
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC4537832/` (added
  2026-09-13 for the P.LAP evidence strengthening pass).

**GENUINELY INACCESSIBLE in this pass** (attempted, could not open
primary text):

- **Nolte, G., et al. (2004).** "Identifying true brain interaction
  from EEG data using the imaginary part of coherency." *Clin.
  Neurophysiol.* 115:2292–2307. Attempted at
  `https://www.researchgate.net/…download/…nolteG2004.pdf` (403),
  DOI redirect `https://doi.org/10.1016/j.clinph.2004.04.029` →
  `https://linkinghub.elsevier.com/retrieve/pii/S1388245704001993`
  (redirect page only, no article body), and
  `https://www.sciencedirect.com/science/article/abs/pii/S1388245704001993`
  (403). Primary Nolte text was NOT read this pass. The
  cross-spectral outer-product construction discussed below is
  treated as MATHEMATICALLY ELEMENTARY and does not require Nolte
  attribution; the volume-conduction / imaginary-coherency finding
  is treated as UNVERIFIED-from-primary.

**NOT ATTEMPTED this pass** (out of scope; general-practice
background):
- Welch 1967 (IEEE); Bendat & Piersol textbook; Rosenberg 1989
  (already reclassified as review about neuronal spike trains, not
  EEG cross-spectra); Nunez & Srinivasan 2006 (textbook); Cohen
  2014 (textbook); Widmann 2015 (filter design); Bigdely-Shamlo
  2015 (PREP); Jung 2000, Chaumon 2015, Pion-Tonachini 2019, Mognon
  2011 (artifact rejection); Theiler 1992 (univariate origin;
  multichannel adaptation is the Prichard-Theiler 1994 paper
  verified this pass).

## §1. Revised decision table

| # | Question | Candidate | Primary source (accessed/attempted) | Exact support | Limitation | Verdict |
|---|---|---|---|---|---|---|
| A | Per-frequency Hermitian PSD cross-spectral matrix `S(f,t) = ⟨X_r(f,t) X_r(f,t)†⟩_r` (average outer products over epochs/segments r at a fixed frequency f) | Mathematically elementary (Nolte 2004 uses this canonical definition in §2.1 per user directive; Nolte primary text was NOT read this pass) | **Sitt 2014 and Hu-Yao rREST read; Nolte 2004 NOT read.** Nevertheless the construction is elementary linear algebra: `S = E[X X†]`, estimator `Ŝ = (1/N) Σ_r X_r X_r†`, Hermitian by construction, PSD by construction. | Averaging across MULTIPLE frequencies within a named band is a further step not implied by the per-frequency definition alone | **PARTIALLY RESOLVED.** Per-frequency `S(f,t)` construction is mathematically well-defined and Hermitian PSD by outer-product elementary algebra; NO literature attribution is claimed for the specific averaged-outer-product form absent Nolte-primary reading. Frequency-band integration inside `S_b(t)` is a separate PF operational choice, NOT part of an established theorem. |
| B.1 | CAR / average reference (AR) as primary representation | Yao et al. 2019 (review, verified); Hu-Yao rREST 2018 (preprint, §1 and §2.1 inspected) | Yao 2019: "In general, we do not recommend using AR if the REST is available"; "AR cannot be a golden standard but an approximation"; "LM seriously biases EEG power…and coherence spectra". Hu-Yao 2018: AR corresponds to "biophysically non-informative [uncorrelated] prior"; AR reference-transform matrix `H = I − 1·f^T` (Eq. 2) is a rank-deficient re-referencing projection whose null-space contains the constant vector 1 (rank N−1 in general; the outer product `1·f^T` is itself rank-1). | AR is a linear, RANK-DEFICIENT (non-unitary) rereferencing transformation. Not endorsed by verified secondary/preprint sources for coherence/cross-spectral use. | **NOT RECOMMENDED as primary for χ_k** — verified sources argue against AR/CAR-sensor-level as canonical. Neither is unitary; Layer-1 unitary-invariance theorem does NOT apply to AR. |
| B.2 | REST / rREST (Reference Electrode Standardization Technique) | Hu-Yao rREST 2018 (preprint, §1 and §2.1 inspected); Yao 2019 (review, verified) | Hu-Yao 2018: REST corresponds to "correlations between electrodes are assumed to be caused by sources filtered through a volume conductor model"; rREST is "the regularized version of REST"; Bayesian estimator formula in Eq. (4). Yao 2019: "REST (rREST) is the best to approach the ideal unipolar infinity reference with golden standard data as the ground true". | REST is MODEL-DEPENDENT (requires a head model with equivalent sources); linear transformation, non-unitary; H reference-projection is rank-deficient in the same sense as AR. Marzetti 2007 and Qin 2010 cited within Hu-Yao reportedly show REST outperforms AR for spectra and coherence; not directly read. | **REVIEW-LEVEL AND PREPRINT-METHODS SOURCES SUPPORT REST/rREST OVER AR** for spectra/coherence-adjacent applications, but the transformation is MODEL-DEPENDENT and NON-UNITARY. Layer-1 unitary-invariance does NOT apply. |
| B.3 | Surface Laplacian / Current Source Density (CSD) | Sitt 2014 (VERIFIED for connectivity use) | Sitt 2014 High-density scalp section (verbatim): "Connectivity measures were based on a spatial Laplacian transformation of the EEG—a computation also known as the Current Source Density estimate." | Sitt endorses Laplacian/CSD FOR CONNECTIVITY specifically, not as a universal primary representation; primary Laplacian-method papers (Perrin 1989 spline surface Laplacian; Kayser-Tenke 2015) NOT read this pass. Laplacian is a spatial derivative that SUPPRESSES broad volume-conducted components at the cost of discarding/altering spatial-scale information. Non-unitary. | **SUPPORTED as a defensible representation for connectivity-adjacent quantities** by one verified primary source (Sitt 2014). Not unitary. Layer-1 unitary-invariance does NOT apply. |
| B.4 | Source-space reconstruction (LORETA, MNE, LCMV beamformer, DICS) before cross-spectra | NONE of the primary source-imaging methods papers were accessed this pass | — | Auditor did not access Pascual-Marqui/Michel/Lehmann 1994, Hämäläinen/Ilmoniemi 1994, Van Veen 1997, or Gross 2001 | **UNVERIFIED** — reserved as a design alternative pending primary-source access |
| C | Block-diagonal direct-sum of independently estimated per-band Hermitian PSD blocks (charter §3.3 default) | PF-declared; no primary-source origin claimed | — | Charter itself declares this as a PF operational choice. No verified primary source establishes this as standard OR as forbidden. | **PF-SPECIFIC CONSTRUCTION.** Retains within-band channel cross-spectra and (in the block traces) relative power; DELIBERATELY sets cross-frequency blocks to zero, so cannot test cross-frequency coupling. Global trace normalization additionally removes total signal power; χ_k measures changes in the normalized spatial-spectral structure, not changes in total EEG power. **The earlier claim that "no standard EEG estimator" uses this form is RETRACTED** — no verified source establishes that universal negative. |
| D.1 | Prichard-Theiler multivariate surrogate (COMMON frequency-dependent phase applied to all channels) | Prichard & Theiler 1994 (VERIFIED via arXiv comp-gas/9405002) | Eq. (5): `x̃_j(t) = F^{−1}{X_j(f) e^{iφ(f)}}`, "where φ(f) is the same for all j". Preceding text (Eq. 4 discussion): "To preserve all the linear auto- and cross-correlations, we need to fix `X*_j(f) X_k(f)` for all pairs j, k. Since Eq. (4) only involves differences of phases, this is readily achieved by adding the same random sequence φ(f) to φ_j(f) for all j." | Preserves per-channel spectra AND all pairwise cross-spectra/cross-correlations by construction. It tests only nonlinear structure BEYOND the preserved multivariate linear structure. | **SUPPORTED** as the Prichard-Theiler multivariate surrogate with the exact common-phase construction verified. |
| D.2 | PF independent-channel phase surrogate (INDEPENDENT random phase per channel per positive-freq bin) | NOT the Prichard-Theiler algorithm; a distinct PF construction | — | Each channel's Fourier magnitude and hence AUTO-spectrum preserved exactly; cross-spectrum phase is randomized. Off-diagonal cross-spectrum is zero only IN EXPECTATION over the phase distribution, not identically for any one finite surrogate. Requires explicit statement of independent-uniform-phase assumptions. | **PF NULL CONSTRUCTION** — a defensible null against zero-lag cross-channel structure but NOT the Prichard-Theiler algorithm and NOT proven to leave the finite-sample off-diagonal cross-spectrum exactly zero. |
| D.3 | Constant global phase invariance test — `e^{iφ}` scalar applied everywhere | Elementary algebra | `(e^{iφ} X)(e^{iφ} X)^H = X X^H` per element (scalar `e^{iφ}` commutes and cancels with its conjugate `e^{−iφ}`) | Deterministic invariance identity; NOT a surrogate null | **SUPPORTED as an implementation-check invariance test** (charter §11 INV1). |

## §2. Corrected findings on the four questions

### §2.A — Cross-spectral estimator (PARTIALLY RESOLVED)

The per-frequency Hermitian PSD cross-spectral matrix
```
S(f, t) = ⟨ X_r(f, t) · X_r(f, t)† ⟩_r
```
(with `X_r(f, t)` the complex-valued spectral coefficient of channel
vector X for epoch/segment r at time t and frequency f) is a
canonical construction, elementary from linear algebra: outer
products are Hermitian by construction; the average preserves
Hermiticity; PSD follows from `v† (X X†) v = |v† X|² ≥ 0`.

Hermiticity and positive semidefiniteness follow mathematically
from the outer-product construction and do NOT require primary
attribution. Averaging outer products over epochs is standard
practice and requires no theorem.

**Nolte 2004 was not read this pass**, so no Nolte-specific quote
is claimed. The earlier bridge-audit statement that "Welch is
required to justify the multichannel outer-product construction"
is RETRACTED — the outer-product construction is
mathematically elementary. Welch's own paper concerns univariate
PSD; the multichannel extension is a separate object that does not
need Welch as a source.

**Frequency-band integration** inside a band-averaged
`S_b(t) := ⟨S(f, t)⟩_{f ∈ F_b}` is a further PF operational choice.
It is NOT part of Nolte's per-frequency definition. Charter §3.3
adopts this band integration as a PF choice; the charter has already
labelled it as such.

### §2.B — Reference / volume-conduction representation

Verified primary-source findings:

**Yao 2019 (verbatim, Discussion sections):**
- "In general, we do not recommend using AR if the REST is available."
- "AR cannot be a golden standard but an approximation."
- "Nonzero reference has distinct effects on waveform and related
  parameters, such as … coherence, correlation, network … and
  statistic test."
- "LM seriously biases EEG power … and coherence spectra
  confounding the interpretation of results."
- "REST (rREST) is the best to approach the ideal unipolar infinity
  reference with golden standard data as the ground true."

**Hu-Yao rREST 2018 (verbatim, §1 Introduction and §2.1 General
reference model):**
- "the average reference (AR) and the reference electrode
  standardization technique (REST) are two primary, apparently
  irreconcilable contenders."
- "AR and REST share the same model and just differ in the prior
  distribution for the covariance of EEG potentials at infinity."
- "assuming uncorrelated activities over electrodes leads to the AR
  estimator. On the other hand, if the correlations between
  electrodes are assumed to be caused by sources filtered through a
  volume conductor model, the resulting estimator is REST."
- Eq. (2): `v_r = Hφ + e, e = Hε`, with `H = I − 1·f^T`. All
  unipolar references (including AR) satisfy `f^T·1 = 1`, so
  `H · 1 = 0` and H is a **rank-deficient re-referencing projection**
  (rank N−1 in general). The outer-product term `1·f^T` inside H is
  itself rank-1, but H itself is NOT rank-1. (Correction 2026-09-13:
  the earlier claim "H is rank-1" was mathematically wrong;
  correcting per user directive.)
- Eq. (4) gives the Bayesian estimator for the potentials at
  infinity from any reference-recorded EEG.

**Sitt 2014 (verbatim, High-density scalp EEG section):**
- "Connectivity measures were based on a spatial Laplacian
  transformation of the EEG — a computation also known as the
  Current Source Density estimate."

**Consequences that do follow from the verified sources:**

1. **AR/CAR sensor-level cross-spectral matrix is NOT recommended
   as the primary connectivity-adjacent representation** for χ_k.
   Yao 2019 explicitly recommends against AR when REST is available;
   coherence and correlation are among the quantities Yao 2019 lists
   as affected by reference choice.
2. **REST/rREST is a MODEL-DEPENDENT re-referencing transformation.**
   Hu-Yao 2018 explicitly shows it as a linear transformation
   corresponding to a specific prior on infinity-potential
   covariance. It is NOT unitary.
3. **Surface Laplacian is a spatial transformation that suppresses
   broad volume-conducted components** but discards/alters spatial
   information (a spatial derivative). It is NOT unitary. Verified
   as Sitt's connectivity choice.
4. **Source reconstruction is inverse-model-dependent.** Not
   audited this pass.
5. **None of AR, REST/rREST, Laplacian/CSD, or source
   reconstruction is generally unitary.** Therefore Layer 1's
   unitary-invariance theorem (charter §5, Layer-1 T4) does NOT
   make χ_k invariant under these preprocessing choices. χ_k WILL
   depend on the montage/representation choice.

**What does NOT follow from the verified sources:**
Nolte 2004 was not read; therefore the specific claim "ordinary
sensor-level coherency is affected by common reference and volume
conduction; imaginary coherency detects lagged interaction under a
quasi-static instantaneous-mixing assumption" (user directive B)
remains attributed to the user's own reading of Nolte 2004, not to
this auditor's reading. The verified Yao 2019 and Hu-Yao 2018
sources support the general reference-choice-affects-coherence
finding but do NOT themselves distinguish real vs imaginary
coherency.

**Scientific disposition (unchanged):**
There is no literature-derived canonical representation. The
representation must be fixed as an explicit empirical
operationalization, and χ_k's dependence on it MUST be measured
(charter §9 robustness axis 1 stands, with primary/secondary
representations specified in §3 below).

### §2.C — Block-diagonal per-band matrix

The earlier bridge-audit statement "most standard EEG cross-frequency
work uses per-frequency CSD matrices with explicit cross-frequency
coupling functions" is a general observation NOT anchored to a
verified primary source. **The universal negative claim "no
standard EEG estimator" uses a block-diagonal band construction is
RETRACTED** — no verified source establishes that universal
negative.

Corrected statement:

- The block-diagonal direct sum
  `S(t) = block_diag(S_{b_1}(t), …, S_{b_{D_bd}}(t))` in charter §3.3
  is a PF operational construction.
- It retains WITHIN-BAND channel cross-spectra and the relative
  power carried by the block traces (each `Tr(S_b(t))` is the
  within-band total power).
- It DELIBERATELY sets cross-frequency blocks to zero.
- It therefore CANNOT test cross-frequency coupling.
- Global trace normalization `ρ_EEG(t) = S(t) / Tr(S(t))`
  additionally removes TOTAL signal power. Consequently χ_k measures
  changes in the NORMALIZED SPATIAL-SPECTRAL STRUCTURE, not changes
  in total EEG power.

### §2.D — Surrogates (three distinct constructions)

**D1. Prichard-Theiler multivariate surrogate (VERIFIED).**
- Common frequency-dependent random phase φ(f) added to every
  channel's Fourier phase.
- Preserves per-channel spectra AND all pairwise
  cross-spectra/cross-correlations by construction (Eq. 4–5 of
  Prichard-Theiler 1994).
- Tests nonlinear structure BEYOND the preserved multivariate
  linear structure.

**D2. PF independent-channel phase surrogate (DISTINCT PF NULL, NOT
Prichard-Theiler).**
- Independent random phase φ_j(f) drawn separately per channel j
  for each positive-frequency bin.
- Each channel's Fourier magnitude and auto-spectrum preserved
  exactly.
- Off-diagonal cross-spectrum's phase is randomized; off-diagonal
  cross-spectrum is zero only IN EXPECTATION under stated
  independent-uniform-phase assumptions, NOT identically for one
  finite surrogate realisation.
- This is a PF null construction against zero-lag cross-channel
  structure; it is NOT the Prichard-Theiler algorithm.

**D3. Constant global phase invariance test (SUPPORTED as
implementation check).**
- One scalar `e^{iφ}` applied everywhere. `(e^{iφ} X)(e^{iφ} X)^H
  = X X^H` per element (scalar `e^{iφ}` commutes with its conjugate
  and cancels).
- Leaves every outer product unchanged identically.
- Implementation check only, NOT a surrogate null.
- Corresponds to charter §11 INV1.

Charter §11 and §12 must be updated to explicitly distinguish D1,
D2, D3 by these names.

## §3. Adversarial three-pipeline comparison (representation decision)

Comparison of exactly three candidate primary pipelines:

**Pipeline P.LAP — reference-free estimate of the scalp surface
Laplacian → per-frequency spectral cross-spectral-density (spectral
CSD) matrices.**

Naming discipline: "surface Laplacian" and "spatial CSD" are used
here as synonyms for a spatial derivative of scalp potential (Tenke
& Kayser 2015 use "SL" and "spatial CSD" interchangeably; the
spherical-spline construction of Perrin et al. 1989 is one
established estimator). This is a **reference-free estimate of the
scalp surface Laplacian, interpretable under stated volume-conductor
assumptions as radial current-flow structure — NOT a direct
cortical current-source density.** "Spectral CSD" below refers to
the cross-spectral density matrix (§2.A), a distinct object.

| Attribute | Value |
|---|---|
| Physical assumption (from Tenke & Kayser 2015, §4.5) | The surface Laplacian, under isotropic-tissue simplification, is a **minimal description** of the neural current generators underlying a scalp EEG topography — NOT a direct cortical CSD. Tenke & Kayser 2015: "CSD provides a minimal description of the neural current generators underlying a scalp-recorded EEG topography." |
| Reference dependence (Tenke & Kayser 2015, §1) | "A surface Laplacian offers a clear advantage for both of these shortcomings: it is a reference-independent method that eliminates or substantially reduces volume conduction." |
| Volume-conduction sensitivity (Tenke & Kayser 2015, §4.4, citing Nunez & Srinivasan 2006) | "CSD 'algorithms essentially filter out the very large scale (low spatial frequency) scalp potentials.'" |
| Sensitivity to superficial vs deep generators (Tenke & Kayser 2015, §4.3) | Nontrivial and computation-parameter-dependent: "The first caveat pertains to the relative selectivity of CSD for superficial, rather than deep sources"; but "the relative peak attenuation with depth is of the same order of magnitude as that observed for EEG data using an AR … and can easily be countered by altering computation parameters." Discovered dependence on spline flexibility: "Variations in spline flexibility strongly influenced the spatial tuning of the CSD for Model 3." |
| Dependence on interpolation, smoothing, montage geometry (Tenke & Kayser 2015 §2.3.3, §3, §4.3) | Depends on spline-order m and smoothing λ. Their "standard parameters" for group averaging: `λ = 10⁻⁵`, 50 iterations, `m = 4`. "A more flexible spline (m = 3) leads to a more precise localization of generators, but at the expense of further attenuation with depth." |
| Edge-electrode behaviour | Not explicitly addressed in the passages read this pass; treated as UNKNOWN pending further primary-source access. |
| Information lost or spatially filtered (Tenke & Kayser 2015, §4.4) | "Globally recorded, reference-dependent empirical EEG may retain important temporal (phase) information that is removed by the CSD when employing high-resolution CSD estimates." Removes "the two integration constants eliminated by the Laplacian" (broad spatial-DC and linear-spatial components). |
| Preprocessing map unitary? | **No** (spatial-derivative operator, further composed with a spherical-spline interpolation, is not unitary) |
| Consequence for Frobenius churn | χ_k values on Laplacian-transformed signals will DIFFER from χ_k on sensor-level signals; not invariant |
| Data / electrode-density requirements | Tenke & Kayser 2015 simulated with a 67-channel scalp montage on a 4-shell spherical head model. NO threshold like ">32 electrodes required" appears in the passages read this pass. The evidence-supported dependence is on spatial sampling adequate to support the chosen spline order and smoothing without aliasing; specific minimums not established this pass. |
| Suitability for Sitt/UWS/MCS population | Sitt 2014 (primary-experimental precedent, verified) uses spatial Laplacian / CSD for its own connectivity measures on this exact population. |

**Pipeline P.REST — rREST (regularised Reference Electrode
Standardization Technique) → per-frequency cross-spectral
matrices.**

| Attribute | Value |
|---|---|
| Physical assumption | Sources filtered through a volume-conductor head model; potentials referenced to infinity |
| Reference dependence | Explicit: rREST estimates potentials at infinity from any reference-recorded EEG |
| Volume-conduction sensitivity | Attempted correction via the head-model prior (Hu-Yao 2018, Eq. 4) |
| Information discarded | Depends on regularisation parameter; rREST retains more information than AR (verified in Hu-Yao 2018 simulations) |
| Model dependence | Strong: requires an equivalent-source distribution and head-conduction model |
| Preprocessing map unitary? | **No** (rank-deficient re-referencing projection H = I − 1·f^T with H·1 = 0, rank N−1; further composed with rREST's Bayesian inverse estimator, still non-unitary) |
| Consequence for Frobenius churn | χ_k values on rREST-referenced signals will DIFFER from sensor-level; not invariant |
| Data/head-model requirements | Requires (a) high-density electrode coverage for good rank of forward map, and (b) a head model (spherical acceptable; realistic MRI-based preferred) |
| Suitability for Sitt/UWS/MCS population | rREST is not used by Sitt 2014 (Sitt used AR for spectra); patient population sometimes lacks MRI, complicating realistic head model |

**Pipeline P.SRC — source-space reconstruction (e.g., LCMV
beamformer or MNE inverse) → per-frequency cross-spectral
matrices.**

| Attribute | Value |
|---|---|
| Physical assumption | Distributed or focal cortical current sources whose activity is estimated via an inverse problem |
| Reference dependence | Reference choice is absorbed into the inverse problem; downstream cross-spectra are effectively reference-independent |
| Volume-conduction sensitivity | Attempted correction by explicit forward-model inversion |
| Information discarded | Regularisation/inversion prior discards small-eigenvalue subspaces |
| Model dependence | Strongest: requires head model AND source model (e.g., leadfield, distributed dipole grid); solutions vary across inverse methods |
| Preprocessing map unitary? | **No** (inverse-problem operator is not unitary) |
| Consequence for Frobenius churn | χ_k values on source-space signals will DIFFER; not invariant |
| Data/head-model requirements | HIGH: co-registered MRI, boundary/volume element head model, high-density EEG (usually 64–256 channels) |
| Suitability for Sitt/UWS/MCS population | Frequently NOT feasible in UWS/MCS patients due to MRI unavailability, sedation, MRI-incompatible implants, or clinical constraints |

## §4. Recommendation

**Exploratory-pilot primary pipeline candidate: P.LAP** (reference-free
scalp surface Laplacian → per-frequency spectral cross-spectral-density
matrices).

**Sources of evidence (with each source's status made explicit):**

- **Primary experimental precedent (fully read):** Sitt 2014 uses
  spatial Laplacian / spatial CSD for connectivity measures on the
  same UWS/MCS population that motivates the χ_k program.
- **Primary simulation/methods (read this pass):** Tenke & Kayser
  2015 supplies evidence-supported statements about reference
  freedom, broad-scale suppression, and parameter dependence of
  surface Laplacian.
- **Primary/preprint methods model (partial read):** Hu-Yao rREST
  2018 (pp. 1–5 inspected) supports REST/rREST as one specific
  Bayesian-inverse re-referencing alternative.
- **Review-level synthesis (fully read):** Yao 2019 argues against
  AR/CAR-as-canonical and in favour of REST/rREST for
  coherence-adjacent applications.
- **Mathematical deductions made by PF:** outer-product Hermiticity
  and PSD (§2.A); the AR reference-projection H = I − 1·f^T is
  rank-deficient (not rank-1); χ_k is not invariant under non-unitary
  preprocessing.

Do NOT collapse these categories into "verified primary sources".

**Preregistered sensitivity representations:**

- **P.REST** (rREST → per-frequency spectral CSD) — supported by
  the Yao 2019 review and the partial Hu-Yao 2018 read as a
  reference-independent alternative. Included as a sensitivity axis
  to test whether the χ_k signal survives an infinity-reference
  choice.
- **P.SRC** (source-space) — included as a preregistered
  sensitivity axis when an MRI-based head model is available, to
  test whether χ_k signal survives an inverse-model transformation.

**Sample-size disposition:** Even with P.LAP as primary, the χ_k
program remains EXPLORATORY PILOT per charter §10.3 (Sitt's AUC is
NOT transferable). χ_k-specific pilot variance data are required
before any confirmatory phase.

**Nature of this recommendation.** This is a **PF experimental-design
decision** informed by a mix of evidence types (primary experimental
precedent, primary simulation, primary/preprint methods model,
review, and PF mathematical deductions). It is NOT a theorem or
literature mandate. Nolte 2004 was NOT read; any Nolte-specific
imaginary-coherency choice is NOT a component of this
recommendation. Kayser & Tenke's separate tutorial (attempted at
their Columbia URL, connection refused) was not read either; if a
future read contradicts the Tenke & Kayser 2015 findings above,
this recommendation is subject to revision.

**Scientific status of the P.LAP recommendation.** P.LAP is a
technically coherent exploratory operationalization with direct
primary-experimental precedent for the spatial-Laplacian step in the
target population (Sitt 2014). Its validity as a **churn
measurement** is UNESTABLISHED pending nuisance/sensitivity
validation. A synthetic measurement-validity benchmark is required
before a P.LAP-primary pilot can be preregistered; the benchmark
charter is committed alongside this revision.

## §5. Remaining genuinely inaccessible sources

- **Nolte, G., et al. (2004).** *Clin. Neurophysiol.* 115:2292–2307.
  Attempted at three URLs (ResearchGate download; DOI redirect;
  sciencedirect abstract); all returned 403 or cookie-gates without
  content.

Other unaudited primary sources (Perrin 1989 spline surface
Laplacian; Kayser & Tenke 2015 CSD toolbox; Van Veen 1997 LCMV;
Gross 2001 DICS; Pascual-Marqui / Michel / Lehmann 1994 LORETA;
Hämäläinen & Ilmoniemi 1994 MNE; Marzetti 2007; Qin 2010) were NOT
attempted this pass and are out of scope for this focused bridge
audit.

## §6. Charter items requiring follow-up beyond this bridge audit

Not touched by this commit (bridge-audit focus only). Follow-up
work if further approval is granted:

- Charter §11 to relabel the D1/D2/D3 surrogate constructions
  under the verified Prichard-Theiler naming.
- Charter §3.1 item 2 reference-montage default: consider
  switching from CAR-with-REST-in-§9 to P.LAP primary.
- Charter §3.3 band-block estimator: retain, but strengthen
  language (per §2.C above).
- Charter §13 U11–U15 adjust to reflect the verified sources.

## §7. Corrected verdict on the EEG→ρ_EEG map

**Not blocked as claimed in commit 00087f33.** Also NOT "defensible"
in the strong sense implied by commit 2d4e5a6a. The correct narrower
verdict is:

**The proposed P.LAP → spectral-CSD → trace-normalized-state pipeline
is a technically coherent exploratory operationalization with direct
primary-experimental precedent for the spatial-Laplacian step in the
target population. Its validity as a churn measurement remains
unestablished pending nuisance/sensitivity validation.**

**A. Algebraically valid (proven or elementary):**
- The outer-product spectral matrix `S(f, t) = ⟨X_r(f, t) X_r(f, t)†⟩_r`
  is Hermitian and positive semidefinite by construction.
- Trace normalization `ρ_EEG(t) = S(t) / Tr(S(t))` yields a
  trace-one PSD matrix whenever `Tr(S(t))` is positive.

**B. Statistical-estimation assumptions still unresolved:**
- Local stationarity of the underlying process.
- Segment length choice.
- Taper / window choice.
- Overlap choice.
- Frequency-smoothing choice.
- Band-integration choice (§2.C).
- Effective degrees of freedom of the empirical estimator.
- Regularization for near-singular `S(t)`.
- Bias and variance under all of the above.

None of these has been resolved from primary sources in this pass.

**C. Physical interpretation not established:**
- A normalized scalp spatial-spectral change is NOT automatically an
  intrinsic brain-state change. It is a change in a projected /
  filtered / normalized quantity whose relation to underlying neural
  dynamics is model-dependent.
- Trace normalization deliberately removes total-power change; χ_k
  does NOT respond to changes in overall EEG power (charter §2.C).
- Non-unitary preprocessing (Laplacian, rREST, source inversion)
  makes χ_k representation-dependent; Layer-1 T4 unitary-invariance
  does NOT rescue χ_k here.

**Consequence.** Even under the P.LAP candidate, the χ_k pipeline
requires an ADDITIONAL VALIDATION STEP — a synthetic
measurement-validity benchmark that establishes the pipeline's
false-churn rate under nuisance-only changes, its sensitivity under
genuine latent-structure changes, its representation-to-representation
agreement, and its stability under estimator parameters. That
benchmark is designed in a separate charter committed alongside this
revision.

**Charter §17 pre-implementation checklist stands.** No estimator
implementation, no simulated results, no human-data claims.
χ_k pilot data collection, power analysis, ethics approvals, and
Pablo's explicit further approval are still required before any
Layer-2 estimator implementation or Layer-3 initiation.

---

*Bridge audit revised 2026-09-13 replacing the earlier commit
`00087f33` whose "journal-access blocker" finding was false.
Companion documents: `codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md`
(charter, HEAD after this commit will be updated by follow-up);
`codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md` (main audit,
HEAD `b229a6d9`). No Lean, no book, no estimator, no Layer 3, no
master push.*

---

**2026-09-14 cross-reference addendum (K4).** The quarterback
stack K1–K4 on `r331b-provenance` has landed a staged Phase-1
readiness surface for the χ_k measurement benchmark restricted to
`(M19, P.LAP, Benchmark B)`. The Phase-1 executable specification
lives in
`codex/CHURN_CHI_K_BENCHMARK_PHASE1_GENERATIVE_SPEC_2026-09-14.md`
and covers G2/G3/G4 (K3) and G5/G6-P.LAP (K4). Two Phase-1-
blocking primary-source obligations are named in that document
that touch this bridge audit's remit:

1. **Berg-Scherg 1994** (or equivalent) analytical leadfield-
   series `λ_n(...)` coefficients for the three-shell concentric
   sphere. NOT in this bridge audit's verified-source set as of
   this addendum. Blocks Phase-1 forward-model implementation.
2. **Perrin et al. 1989** exact spline kernel `g_m` and Laplacian
   kernel `h_m` closed forms. NOT in this bridge audit's
   verified-source set. Bridge audit §3 records only secondary
   Tenke & Kayser 2015 quotations supporting the spherical-spline
   family and its reference-independence property; the primary
   Perrin-1989 equation forms are unverified. Blocks Phase-1
   P.LAP algorithm implementation.

Both blockers can only be closed by primary-source full-text
verification recorded in the source audit, not by any
documentation-only amendment on this branch. Phase-1
implementation remains authorised only after such a source-audit
update lands.

No content of this addendum revises this bridge audit's earlier
findings; it only closes the K1–K4 cross-references so future
readers of the bridge audit are pointed at the Phase-1 spec
document. The A/B/C decomposition of §7 is unchanged: Phase-1
addresses A (algebraic well-formedness) and the estimator side of
B (statistical assumptions), and explicitly does NOT resolve C
(physical interpretation as intrinsic brain-state change).
