# Principia Fractalis — Master LaTeX Folder

**Version**: 2.5.0
**Date**: 2026-06-08
**Pages**: 840
**Status**: Canonical book source.

This is the source-of-truth for the Principia Fractalis textbook. It contains the complete LaTeX source for the book authored by Pablo Cohen, plus the compiled `main.pdf` output.

## Layout

```
main.tex                  — Master document (compile this)
preamble.tex              — Shared preamble for all chapters
bibliography.bib          — BibTeX database

frontmatter/              — Title page, copyright, prologue, preface,
                            how-to-use, notation, acknowledgments,
                            version history
chapters/                 — All chapters (Ch 1 through Ch 35)
appendices/               — Appendices A through J
backmatter/               — Glossary, About the Author, Epilogue,
                            Appendix Lexicon
figures/                  — Figure source files (TikZ / images)

main.pdf                  — Built output (864 pages, 9.25 MB)
NOTICE.md                 — Copyright notice
```

## Building the book

```bash
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex   # for cross-references
```

Auxiliary files (`.aux`, `.log`, `.toc`, `.lof`, `.lot`, `.out`, `.idx`, `.bbl`, `.blg`) are not tracked — they regenerate during the build.

## Structure

The book is organized into seven parts plus extensive appendices:

- **Part I** — Foundations (numbers, complex analysis, fractal resonance, Timeless Field, Peixoto theory, consciousness, universal constants)
- **Part II** — Field Equations (8 chapters covering field equations, spectral unity, hydrodynamics, geometric unity, QFT-consciousness, dynamics, symmetries, computational methods)
- **Part III** — Spectral Theory (4 chapters: foundations, operator theory, spectral measures, physical applications)
- **Part IV** — Millennium Problems (6 chapters, one per Clay axis: RH, P vs NP, NS, YM, BSD, Hodge)
- **Part V** — Cosmology (4 chapters: cosmological constant, dark energy, early universe, observational tests)
- **Part VI** — Consciousness (3 chapters: clinical, neuroscience/IIT, quantification)
- **Part VII** — Computation (Chapters 33, 34, 34A, 35) including **Chapter 34A: The Principia Fractalis Substrate Theorem** — the master citable form of the framework's reach
- **Appendices A through J** including **Appendix I (Lean Theorem Cross-Reference)** and **Appendix J (Refinement Pass 2026-06-07)**

## Companion artifacts

- `../PF_Lean4_Code/` — Lean 4 formalization (8360 jobs clean, zero project axioms)
- `../PF_Coq_Code/` — Coq structural-parity mirror (184/184 files clean; backbone Admitted-free; Clay statements as `Prop := True` placeholders on the Coq side, content parity in Lean)
- `../PF_Lean4Lean/` — External Lean kernel re-verifier
- `../Papers/` — Three current papers (canonical substrate model, six-as-one, ten-pillars)
- `../docs/CLAY_PER_AXIS_CITATION_CARDS.md` — Per-Clay-axis presentation with exact Lean theorem names and reproducible verify commands
- `../docs/REFEREE_QUICKSTART.md` — 10-minute independent verification guide

## Copyright

See `NOTICE.md`. All rights reserved to Pablo Cohen under the project's Non-Commercial Research License (`../LICENSE`).
