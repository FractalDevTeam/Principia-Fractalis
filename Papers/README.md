# Papers

**HEAD anchor**: cleanup completed 2026-06-08.

This directory contains the **three current papers**. Older drafts (paper_A, paper_B, paper_C, prior arxiv preprint versions, per-axis single-Clay papers, per-attack non-Clay papers, deprecated TOE-canonical and seven-millennium-definitive drafts) have been moved to `ARCHIVE/2026-06-08-cleanup/papers/` with git history preserved.

## Current papers

| File | Description |
|---|---|
| `principia_fractalis_substrate_model.{tex,pdf}` | **Canonical publishable paper.** Written using the transcendental conventions of `PF/CrossMillenniumSharedInvariants.lean`. Honest scope on encoding bridges. Cited from the top-level `README.md`. |
| `principia_fractalis_six_as_one.{tex,pdf}` | **The Six Clay Millennium Problems Are One.** Per-axis Clay-axis presentation with four unconditional discharges and two named residuals. v4 with empirical-validation framing. 11 pages. |
| `principia_fractalis_total_reach_ten_pillars.{tex,pdf}` | **A Substrate-Level Theory of Everything With Ten Machine-Verified Pillars.** Framework-first presentation: Clay axes are pillar T1 among ten. Includes full rigidity-derivation chain, IBM Galois-pair derivation, inter-pillar reinforcement, and falsifiability layer. 9 pages. |

## How to rebuild any paper

```bash
cd Papers/
pdflatex <paper>.tex
pdflatex <paper>.tex   # for cross-references
# Optional: bibtex <paper> if bibliography needed
```

LaTeX auxiliary files (`.aux`, `.log`, `.out`, `.toc`, `.bbl`, `.blg`) are ignored via the top-level `.gitignore` — only `.tex` source and `.pdf` outputs are tracked.

## Publishing gate

Per `../PUBLISHING_GATE.md`, no paper in this directory is to be submitted externally without Pablo Cohen personally running his multi-model stress-test vetting protocol. Claude drafts; Pablo vets; Pablo decides.
