# Layer 2 EEG→ρ_EEG Measurement-Bridge Focused Audit — 2026-09-13 (Revised)

*Focused source-verification pass on the four load-bearing bridge
questions (A cross-spectral estimator; B montage representation; C
block-diagonal band combination; D phase-randomized surrogates). This
document replaces the earlier bridge audit commit `00087f33`, whose
"journal-access blocker" finding was FALSE: multiple primary/full-text
sources were openly accessible via user-supplied URLs and have now
been read in full.*

## §0. Access record (this pass)

**FULL-TEXT VERIFIED (accessed via open URLs supplied by the user):**

- **Prichard, D., & Theiler, J. (1994).** *Phys. Rev. Lett.* 73:951–954.
  Read in full via `https://arxiv.org/pdf/comp-gas/9405002` (arXiv
  comp-gas/9405002, 12 May 1994).
- **Sitt, J. D., et al. (2014).** *Brain* 137:2258–2270. Read in full
  (main article; supplementary methods not recovered) via
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC4610185/?report=printable`.
- **Yao, D., et al. (2019).** "Which reference should we use for EEG
  and ERP practice?" *Brain Topography* 32:530–549. Read in full via
  `https://pmc.ncbi.nlm.nih.gov/articles/PMC6592976/`.
- **Hu, S., Yao, D., & Valdes-Sosa, P. A. (2018).** "Unified Bayesian
  estimator of EEG reference at infinity: rREST." arXiv:1802.02268.
  Read in full via `https://arxiv.org/pdf/1802.02268` (first 5
  pages, sufficient to extract the reference-model equations).

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
| B.1 | CAR / average reference (AR) as primary representation | Yao et al. 2019 (VERIFIED); Hu-Yao rREST 2018 (VERIFIED) | Yao 2019: "In general, we do not recommend using AR if the REST is available"; "AR cannot be a golden standard but an approximation"; "LM seriously biases EEG power…and coherence spectra". Hu-Yao 2018: AR corresponds to "biophysically non-informative [uncorrelated] prior"; AR reference-transform matrix `H = I − 1·f^T` is rank-1 (Eq. 2). | AR is a linear, RANK-1 (non-unitary) transformation. Not endorsed by verified primary sources for coherence/cross-spectral use. | **NOT RECOMMENDED as primary for χ_k** — verified primary sources argue against AR/CAR-sensor-level as canonical. Neither is unitary; Layer-1 unitary-invariance theorem does NOT apply to AR. |
| B.2 | REST / rREST (Reference Electrode Standardization Technique) | Hu-Yao rREST 2018 (VERIFIED); Yao 2019 (VERIFIED) | Hu-Yao 2018: REST corresponds to "correlations between electrodes are assumed to be caused by sources filtered through a volume conductor model"; rREST is "the regularized version of REST"; Bayesian estimator formula in Eq. (4). Yao 2019: "REST (rREST) is the best to approach the ideal unipolar infinity reference with golden standard data as the ground true". | REST is MODEL-DEPENDENT (requires a head model with equivalent sources); linear transformation, non-unitary (rank-1 same as AR). Marzetti 2007 and Qin 2010 (secondary, cited within Hu-Yao) reportedly show REST outperforms AR for spectra and coherence; not directly read. | **PRIMARY SOURCES SUPPORT REST/rREST OVER AR** for spectra/coherence-adjacent applications, but the transformation is MODEL-DEPENDENT and NON-UNITARY. Layer-1 unitary-invariance does NOT apply. |
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
- Eq. (2): `v_r = Hφ + e, e = Hε`, where **H = I − 1·f^T is a rank-1
  matrix**. All unipolar references (including AR) satisfy `f^T·1 = 1`
  and are of this form.
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

**Pipeline P.LAP — surface-Laplacian EEG → per-frequency
cross-spectral matrices.**

| Attribute | Value |
|---|---|
| Physical assumption | Local radial current-source density under a homogeneous local cortex model |
| Reference dependence | Weak; Laplacian is a spatial derivative and is largely reference-invariant for interior electrodes |
| Volume-conduction sensitivity | Suppresses broad (long-spatial-scale) volume conduction; retains local components |
| Information discarded | Distant/low-spatial-frequency components; edge artifacts on the electrode array |
| Model dependence | Weak (spatial interpolation model, e.g., spherical spline for Perrin 1989) |
| Preprocessing map unitary? | **No** (spatial-derivative operator is not unitary) |
| Consequence for Frobenius churn | χ_k values on Laplacian-transformed signals will DIFFER from χ_k on sensor-level signals; not invariant |
| Data/head-model requirements | Requires >32 electrodes for a stable Laplacian; simple sphere or realistic head geometry |
| Suitability for Sitt/UWS/MCS population | Aligned: Sitt 2014 (verified) uses Laplacian/CSD for its own connectivity measures on this exact population |

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
| Preprocessing map unitary? | **No** (rank-1 reference matrix H = I − 1·f^T; further composed with rREST's Bayesian estimator, still non-unitary) |
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

**Exploratory-pilot primary pipeline: P.LAP (surface Laplacian /
CSD → per-frequency cross-spectral matrices).**

**Rationale (from verified primary sources only):**

1. Sitt 2014 (VERIFIED primary source on the same UWS/MCS patient
   population) explicitly uses surface Laplacian / CSD for
   connectivity-adjacent quantities. This is the ONLY
   representation choice in the audit that has a directly verified
   primary-source precedent on the target population.
2. Laplacian is minimally model-dependent (spatial-derivative
   operator; spherical-spline model for Perrin 1989 style, not
   audited).
3. It is feasible in UWS/MCS patients without an MRI-based head
   model.
4. It suppresses broad volume-conducted components (verified
   textbook property; not re-attributed to any specific primary
   source in this pass).

**Preregistered sensitivity axes (RETAINED for χ_k robustness):**

- **P.REST** (rREST → per-frequency CSD) — supported by Yao 2019
  and Hu-Yao 2018 as reference-independent for coherence-adjacent
  applications. Included as a sensitivity axis to test whether the
  χ_k signal survives an infinity-reference choice.
- **P.SRC** (source-space) — included as a preregistered
  sensitivity axis when a MRI-based head model is available for a
  subset of subjects, to test whether χ_k signal survives an
  inverse-model transformation.

**Sample-size disposition:** Even with P.LAP as primary, the χ_k
program remains EXPLORATORY PILOT per charter §10.3 (Sitt's AUC is
NOT transferable). χ_k-specific pilot variance data required
before any confirmatory phase.

**Nature of this recommendation.** This recommendation is a
**PF experimental-design decision** informed by the verified
primary sources, NOT a theorem or literature mandate. Verified
sources argue against AR/CAR as primary (Yao 2019), support REST/rREST
as an infinity-reference alternative (Yao 2019, Hu-Yao 2018), and
verify Sitt's own use of Laplacian/CSD on the target population
(Sitt 2014). Nolte 2004 was NOT read; any Nolte-specific
imaginary-coherency choice is NOT a component of this
recommendation. If a future full-text read of Nolte 2004 supplies
additional constraints, this recommendation is subject to revision.

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

## §7. Overall verdict on the EEG→ρ_EEG map

**Not blocked as claimed in commit 00087f33** — that finding was
wrong. Corrected verdict:

- The per-frequency cross-spectral matrix (Q.A) is mathematically
  elementary; NO primary-source blocker.
- The reference/representation choice (Q.B) HAS a defensible
  primary-source-informed answer (P.LAP as primary; P.REST and
  P.SRC as sensitivity), even though none of the transformations is
  unitary and χ_k will depend on the choice.
- The band-block matrix (Q.C) is a PF operational choice, correctly
  labelled as such.
- The surrogates (Q.D) split into three distinct constructions with
  verified properties (D1 Prichard-Theiler common-phase; D2 PF
  independent-channel null; D3 global-phase invariance test).

**The EEG→ρ_EEG bridge is scientifically DEFENSIBLE as a Layer-2
exploratory-pilot operationalization** with P.LAP as primary,
P.REST and P.SRC as sensitivity axes, `S(f, t)` per-frequency CSD
as elementary estimator, block-diagonal band grouping as an
explicit PF operational choice, and surrogates D1/D2/D3 as three
distinct constructions.

**This is a defensibility disposition, NOT an implementation-ready
green light.** Charter §17 pre-implementation checklist stands.
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
