# Layer 2 EEG→ρ_EEG Measurement-Bridge Focused Audit — 2026-09-13

*Focused source-verification pass on the load-bearing measurement
bridge from raw multichannel EEG to the normalised state matrix
ρ_EEG(t) that feeds Layer 1's χ_k. Restricted to the four questions
the user identified as load-bearing (A, B, C, D). No general
citation-cleanup work; no exhaustive audit of §14 background.*

## ★ Auditor-access disclosure ★

Auditor attempted direct full-text fetch of primary methods sources
via publisher, DOI, PMC, and open-access channels. **The following
were INACCESSIBLE in the current environment** (paywalls, cookie
walls, publisher 403, or content requiring a browser session):

- Welch, P. D. (1967). *IEEE Trans. Audio Electroacoust.* 15:70–73.
- Bendat, J. S., & Piersol, A. G. (2010). *Random Data* (4th ed.).
- Rosenberg, J. R., et al. (1989). *Prog. Biophys. Mol. Biol.* 53:1–31.
- Nolte, G., et al. (2004). "Identifying true brain interaction from
  EEG data using the imaginary part of coherency." *Clin.
  Neurophysiol.* 115:2292–2307 (attempted at sciencedirect and
  PubMed; both returned 403 / cookie-gate).
- Yao, D. (2001). "A method to standardize a reference of scalp EEG
  recordings to a point at infinity." *Physiol. Meas.* 22:693–711
  (not attempted successfully at open URL).
- Nunez, P. L., & Srinivasan, R. (2006). *Electric Fields of the
  Brain* (2nd ed.).
- Cohen, M. X. (2014). *Analyzing Neural Time Series Data*.
- Prichard, D., & Theiler, J. (1994). *Phys. Rev. Lett.* 73:951–954
  (not accessible open).
- Theiler, J., et al. (1992). *Physica D* 58:77–94 (paywall).
- Michel & Brunet (2019) *Frontiers in Neurology* 10:325 (not
  attempted this pass; audit already flagged as review).
- Pascual-Marqui, R. D. (2007). arXiv:0706.1776 (not attempted this
  pass).

**Accessed successfully:**
- Sitt et al. 2014 main article via PMC
  (`https://pmc.ncbi.nlm.nih.gov/articles/PMC4610185/?report=printable`),
  already recorded in prior commit `fadd08aa` and refined in
  `815f07e4`.
- Wikipedia "Welch's method" — secondary; provided no formulae.
- Wikipedia "Surrogate data testing" — secondary; provided the
  Prichard & Theiler 1994 reference but no full mathematical
  content.
- MNE-Python `csd_array_multitaper` API page — documentation;
  provided no formulae or primary references.

**Consequence:** this bridge audit is HONEST-SCOPE ONLY. For each of
the four load-bearing questions below, if no primary source could be
opened this pass, the entry is marked UNKNOWN. Under the standing
discipline, an UNKNOWN entry BLOCKS implementation of the
corresponding step of the pipeline. This audit's decisive output is
therefore whether the EEG→ρ_EEG bridge is scientifically defensible
from primary sources accessible to this auditor in this pass — and
the answer is that it is NOT so defensible; the bridge is BLOCKED
pending primary-source access by a reader with journal privileges.

## §1. Decision table

| # | Question | Candidate method | Primary source | Exact support | Limitation | Verdict |
|---|---|---|---|---|---|---|
| A | Cross-spectral matrix via averaging channel-vector outer products over segments AND frequency samples | Welch-style averaged modified periodograms extended to multichannel outer products | Welch 1967 (IEEE); Bendat–Piersol 2010 (Ch. 5–6); Rosenberg 1989 (spike-train review); Nolte 2004 (imag-coh CSD); Percival–Walden 1993 (multitaper) | **None verified in this pass** (all INACCESSIBLE) | Auditor could not open the full text of Welch 1967, Bendat–Piersol, or Nolte 2004 to verify the specific averaged-outer-product estimator | **UNKNOWN — BLOCKED** |
| A′ | Alternative: multitaper CSD as computed by MNE-Python `csd_array_multitaper` | MNE documentation cites internal references | MNE API page (accessed) provides no primary reference or formula | Documentation-only; not a primary source | **INACCESSIBLE (documentation-only)** |
| B.1 | CAR (common average reference) as primary representation for sensor-level cross-spectral matrix | Nunez–Srinivasan 2006 Ch. 7; Yao et al. 2019 Brain Topography review | **None verified in this pass** | Yao et al. 2019 has been described elsewhere (charter §2.5, per user directive) as favoring REST/rREST over CAR; full-text access needed | **UNKNOWN — likely NOT best-practice** (per user directive; unverified this pass) |
| B.2 | REST / rREST (Reference Electrode Standardization Technique) | Yao 2001 *Physiol. Meas.* 22:693–711; Yao et al. 2019 review | **None verified in this pass** | Auditor could not open Yao 2001 or the Yao 2019 review this pass | **UNKNOWN — flagged as user-favored alternative** |
| B.3 | Surface Laplacian / Current Source Density (CSD) | Nunez 1981 & 1988; Nunez–Srinivasan 2006 Ch. 7; Perrin et al. 1989 (spline surface Laplacian); Kayser–Tenke 2015 | Sitt et al. 2014 (verified this pass: "Connectivity measures were based on a spatial Laplacian transformation of the EEG—a computation also known as the Current Source Density estimate", High-density scalp section) | Sitt used Laplacian/CSD FOR CONNECTIVITY specifically, average-rereferencing for spectral analyses; primary Laplacian-method papers not accessed this pass | **SUPPORTED by Sitt only as a connectivity-oriented choice (not endorsed by Sitt for arbitrary cross-spectral applications); PRIMARY LAPLACIAN METHOD PAPERS UNKNOWN this pass** |
| B.4 | Source-space reconstruction (LORETA / MNE / beamformer) before cross-spectra | Pascual-Marqui, Michel, & Lehmann 1994 (LORETA); Hämäläinen & Ilmoniemi 1994 (MNE); Van Veen et al. 1997 (LCMV beamformer); Gross et al. 2001 (DICS) | **None verified in this pass** | Auditor could not open any of these primary source-imaging methods papers | **UNKNOWN** |
| C | Block-diagonal combination of independently estimated frequency-band matrices (as in charter §3.3 default) | Charter §3.3 (PF-declared) | No primary source in the pipeline that would establish this specific block-diagonal choice | Charter itself declares (§3.3 caveat) this as PF-specific and identifies what it removes (cross-frequency coupling) | **PF-SPECIFIC; not a supported standard estimator. INFORMATION IT REMOVES: all cross-band phase-and-magnitude coupling. INFORMATION IT KEEPS: within-band cross-channel Hermitian PSD structure per band.** |
| D.1 | Independent per-channel Fourier-phase randomization (each channel gets its own uniform random phase per positive-freq bin) — proven algebraic properties | Prichard & Theiler 1994 *Phys. Rev. Lett.* 73:951 (multivariate surrogate methods); Theiler et al. 1992 *Physica D* 58:77 (univariate origin) | **None verified in this pass** (Prichard–Theiler paywalled; Theiler paywalled) | Wikipedia surrogate-data article mentions Prichard–Theiler for constrained-realization multivariate approaches but does not reproduce the mathematical statements | **UNKNOWN — algebraic properties (which auto/cross-spectra preserved vs destroyed) NOT verified from primary source** |
| D.2 | Common (identical) Fourier-phase rotation applied to all channels — as invariance test | Elementary algebra: `(e^{iφ}X)(e^{iφ}X)^H = X X^H` per element | **Directly derivable; no source needed** | Deterministic invariance identity; not a surrogate null | **SUPPORTED as a deterministic invariance test (already reclassified in charter §11 INV1)** |
| D.3 | Amplitude-adjusted Fourier transform (AAFT) surrogate for non-Gaussian data | Theiler et al. 1992; Schreiber & Schmitz 1996 (iterative AAFT) | **None verified in this pass** | Full-text UNKNOWN | **UNKNOWN** |

## §2. Load-bearing findings

**F1 — Question A (cross-spectral estimator) is BLOCKED.**
The charter's §3.3 corrected estimator (average outer products over
segments and frequencies within a band) is a common finding in
multichannel EEG/MEG analysis (multitaper CSD; Welch-CSD; DPSS
tapers) but the auditor could NOT verify the exact form against any
primary source in this pass. The four candidate primary sources
(Welch 1967, Bendat–Piersol 2010, Nolte 2004, Percival–Walden 1993)
are all INACCESSIBLE at the URLs attempted. Implementation of the
Layer-2 estimator therefore requires primary-source verification by
a reader with journal access, OR a switchover to a
software-verified reference implementation (e.g., MNE-Python's
`csd_array_multitaper`) accompanied by inspection of that
implementation's own primary references.

**F2 — Question B (montage/representation choice) is BLOCKED except
for a partial constraint.** The only PRIMARY-SOURCE-VERIFIED input
this pass is Sitt et al. 2014's use of Laplacian/CSD specifically
for connectivity measures. That verified fact ARGUES AGAINST using
CAR sensor-level cross-spectral matrices as the primary
connectivity-adjacent representation without a separate primary
justification (as recorded in charter §2.5 revised 2026-09-13).
The full comparative literature (Nunez 2006, Yao 2001 REST, Yao
2019 review, Michel & Brunet 2019, Nolte 2004 imaginary coherence)
is INACCESSIBLE this pass. Charter §3.1 item 2 already flagged
reference-montage as PENDING DECISION; that flag stands.

**F3 — Question C (block-diagonal band combination) is
NON-STANDARD.** The charter's §3.3 default forms a block-diagonal
matrix from independently estimated per-band Hermitian PSD blocks,
with zero off-block-diagonal (cross-band) content. This is a
PF-specific construction (not a supported standard). It DELIBERATELY
DISCARDS cross-frequency coupling. Charter §3.3 already labels this
as a PF choice with an explicit caveat; the audit corroborates this
labelling and adds that no standard EEG estimator constructs a
block-diagonal cross-band matrix in this way — most cross-band work
in EEG uses per-frequency CSD matrices with explicit cross-frequency
coupling functions (e.g., n:m PAC, cross-frequency coherence).

**F4 — Question D (multichannel phase-randomized surrogates) is
BLOCKED on the primary-source side, but D.2 is DIRECTLY DERIVABLE.**
- D.1 (independent per-channel phase randomization) is described
  in the general literature as producing surrogates that preserve
  per-channel PSD while altering cross-channel phase relations; the
  exact algebraic characterization requires primary-source access
  (Prichard–Theiler 1994) that this pass could not obtain.
- D.2 (common-phase rotation) is a deterministic invariance test:
  `(e^{iφ}X)(e^{iφ}X)^H = X X^H` per element. This is derivable
  without a source. Charter §11 INV1 already correctly labels it
  as such.

## §3. Recommended primary representation — HELD

Given the BLOCKED status of A, B, and D.1 above, this audit CANNOT
recommend a primary representation for the Layer-2 EEG→ρ_EEG bridge.
Any recommendation now would be an inference from
secondary/documentation sources — which is exactly the failure mode
the S1 stopping condition names.

The charter's §3.1 item 2 flag "reference montage: PENDING DECISION"
stands and is REINFORCED by this audit. The charter's §3.3
`block-diagonal per-band` estimator remains a PF-declared choice
awaiting primary-source justification and expected to be REPLACED
with a per-frequency CSD-matrix construction in any implementation
that follows established EEG methodology.

## §4. Overall verdict on the EEG→ρ_EEG map

**Blocked.** The Layer-2 measurement bridge is NOT presently
scientifically defensible from primary sources accessible to this
auditor in this pass. Sitt 2014 (verified) supplies neither the
estimator's primary-source origin (question A) nor a validated
montage recommendation for χ_k (question B). Question C is a PF
construction the auditor confirms is non-standard. Question D.1
remains algebraically UNKNOWN. Question D.2 is derivable without
a source and correctly labelled in the charter.

**Recommended disposition:**
1. Do NOT implement the Layer-2 estimator on the current charter
   specification.
2. Escalate the four load-bearing questions to a domain expert with
   journal access for primary-source verification of Welch 1967,
   Bendat–Piersol 2010 (or an equivalent multichannel-CSD standard
   text), Nolte 2004 imaginary coherence, Yao 2001 REST, Prichard &
   Theiler 1994 multivariate surrogates.
3. In parallel: if a software-only path is preferred, inspect the
   MNE-Python source code for `csd_array_fourier`,
   `csd_array_multitaper`, and `mne.time_frequency.psd_multitaper`,
   record the exact estimator formulas as implemented, and cite the
   primary references those implementations themselves cite in their
   docstrings and MRO.
4. Do NOT proceed to any Layer-3 (consciousness interpretation)
   step from a blocked Layer-2 bridge.

## §5. Unresolved load-bearing assumptions (updated 2026-09-13 post-pass)

Adding to charter §13 U1–U10:

- **U11 (this audit).** Primary-source origin and exact formulation
  of the multichannel cross-spectral estimator (Question A). BLOCKED
  pending journal access.
- **U12 (this audit).** Comparative literature for reference-montage
  choice under volume conduction (Question B): CAR vs REST/rREST vs
  surface Laplacian/CSD vs source-space. BLOCKED pending journal
  access to Nunez 2006 Ch. 7, Yao 2001, Yao 2019, Nolte 2004.
- **U13 (this audit).** Sitt 2014's use of Laplacian/CSD for
  connectivity is a POSITIVE PARTIAL SIGNAL against CAR-primary but
  is NOT a full endorsement of Laplacian/CSD for χ_k; the
  connectivity-versus-spectral distinction Sitt makes must be
  respected in any Layer-2 implementation.
- **U14 (this audit).** Block-diagonal per-band matrix
  (Question C): PF-specific non-standard construction. Consider
  replacement with a per-frequency CSD matrix (D×D at each
  frequency f) as the standard representation, followed by an
  explicit cross-frequency coupling model if PF requires it.
- **U15 (this audit).** Independent per-channel phase-randomized
  surrogates (Question D.1): algebraic properties not verified this
  pass. BLOCKED pending Prichard & Theiler 1994 access. Note the
  general expectation (per-channel PSD preserved; cross-channel
  imaginary coherence destroyed) is folklore; the exact statement
  requires primary-source verification.

## §6. What was NOT audited this pass (out of scope by directive)

- Background textbook/review citations for general practice (charter
  §14 background list). The directive specifically asked NOT to audit
  every background citation; only load-bearing bridge questions
  A–D.
- Individual consciousness-study primary papers other than Sitt
  (Casali 2013 PCI, Sarasso 2015, King 2013 wSMI) — audit already
  flagged these INACCESSIBLE.
- Statistical / null-model background (Nosek 2018 preregistration,
  Ledoit & Wolf 2004 shrinkage). Already addressed in main audit.

---

*Companion documents: `codex/CHURN_CHI_K_EEG_LAYER_CHARTER_2026-09-12.md`
(charter, HEAD 815f07e4); `codex/CHURN_CHI_K_EEG_SOURCE_AUDIT_2026-09-13.md`
(broader audit). This bridge audit is a FOCUSED source-verification
pass on the four load-bearing questions and does NOT constitute a
green-light for Layer 2 implementation.*
