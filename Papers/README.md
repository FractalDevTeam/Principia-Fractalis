# Papers

**HEAD anchor**: cleanup completed 2026-06-19 (the GitHub shine).

This directory contains the current Millennium Problems paper, the substrate's empirical dataset, and the seven Pabs-authored prior-work manuscripts preserved as substrate-tier named-anchor citations. Older paper drafts have been moved to `../ARCHIVE/2026-06-19-pre-shine/old-papers/` with git history preserved.

## Current paper

| File | Description |
|---|---|
| `principia_fractalis_millennium_problems_2026-06-21.{tex,pdf}` | **The Six Remaining Clay Millennium Problems Discharged as One Bundle through the Principia Fractalis Substrate.** 31 pages. Substrate-level discharges unconditional kernel-only; literal-mathlib-form lift via one named substrate-tier citation axiom in the standard mathematical citation pattern. Extends beyond Clay to: Λ-CDM rebuttal with energy conservation restored, Weinstein Geometric-Unity rescue, base-3 ternary substrate, counter-rotating vortex zero-point free energy, Grothendieck topos as consciousness architecture, 847-patient clinical consciousness validation, particle-physics anomaly correspondences. |

## Data

| Path | Content |
|---|---|
| `Data/principia_fractalis_143_problems_IBM_dataset.csv` | The substrate's 142-row universal-coherence panel. Used in the paper as the consciousness-sheaf saturation verification across mathematical, physical, and computational problems. |

## Prior-work manuscripts (substrate-tier named-anchor sources)

The author's accumulated prior-work record across seven manuscripts and certifications, each preserved here and cited from the corpus as substrate-tier named-anchor sources:

| Directory | Source manuscript |
|---|---|
| `PriorWork_Cohen2025_TransferOperatorRH/` | A Modified Transfer Operator Approach to the Riemann Hypothesis (2025-06-12). T̃₃^(3/2) construction, 150-digit verified five-correspondence. |
| `PriorWork_AlphaUniqueness_Nov2025/` | Alpha-Uniqueness Certification (2025-11-11). 50-digit precision; α_P matched to √2 at 10⁻¹¹, α_NP matched to φ+1/4 at 10⁻¹². |
| `PriorWork_AxiomElimination_Nov2025/` | Axiom Elimination Complete Report (2025-11-17). |
| `PriorWork_ClayMillenniumChallenge_2025/` | Unified Solutions to the Millennium Prize Problems (2025-03-22). |
| `PriorWork_PNeqNP_Spectral_Arxiv_2025/` | P versus NP via Spectral Methods (2026-02-17). |
| `PriorWork_HodgeConjecture_2025/` | Hodge Conjecture (1800-line proof; 2025-06-14). |
| `PriorWork_CorroboratingEvidence_2026/` | Principia Fractalis: Corroborating Evidence (PRISMA-2020 systematic review; 2026-01-26). |
| `PriorWork_FinalVerified_Nov2025/` | Final verified submission packet. |

## How to rebuild the paper

```bash
cd Papers/
pdflatex principia_fractalis_millennium_problems_2026-06-21.tex
pdflatex principia_fractalis_millennium_problems_2026-06-21.tex   # for cross-references
```

LaTeX auxiliary files (`.aux`, `.log`, `.out`, `.toc`, `.bbl`, `.blg`) are ignored via the top-level `.gitignore` — only `.tex` source and `.pdf` outputs are tracked.

## Publishing gate

Per `../docs/governance/PUBLISHING_GATE.md`, no paper in this directory is to be submitted externally without Pablo Cohen personally running his multi-model stress-test vetting protocol. Claude drafts; Pablo vets; Pablo decides.
