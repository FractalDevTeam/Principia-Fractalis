# Bibliography Audit — Principia Fractalis V1.2.1 (Revision Two)

**Date:** 2026-06-03
**Manuscript version:** 1.2.1 (Revision Two: Annotations + Bibliography Polish)
**Bibliography file:** `bibliography.bib`
**Scope:** all `.tex` sources under `frontmatter/`, `chapters/`, `appendices/`, `backmatter/`

## Summary

| Metric | Count |
|---|---|
| Total bibliography entries (`@…{…,`)        | **367** |
| Distinct `\cite{}` keys used                | **276** |
| Missing references (cited but undefined)    | **0**  |
| Orphan entries (defined but never cited)    | **90** |
| Entries missing `year`                      | 0  |
| Entries missing `title`                     | 0  |
| Entries missing `author`/`editor` (non-misc)| 0  |
| Malformed `url=` values                     | 0  |
| Malformed `doi=` values                     | 0  |

**Bottom line:** zero missing references, zero malformed URL/DOI/author/title/year fields. The bibliography is structurally clean. The only finding is a long tail of 90 orphan entries — historical references that were once cited (or held in reserve) but no longer appear in the current text.

## Entry-type breakdown

| Type             | Count |
|------------------|-------|
| `@article`       | 246   |
| `@book`          |  74   |
| `@misc`          |  34   |
| `@incollection`  |   8   |
| `@inproceedings` |   5   |

## Method

```bash
# Extract cited keys
grep -hoE '\cite\{[^}]+\}' frontmatter/*.tex chapters/*.tex \
                            appendices/*.tex backmatter/*.tex \
  | sed 's/\\cite{//;s/}//' | tr ',' '\n' \
  | sed 's/^ *//;s/ *$//' | sort -u > cites_used.txt

# Extract defined keys
grep -oE "^@[a-zA-Z]+\{[^,]+," bibliography.bib \
  | sed -E 's/^@[a-zA-Z]+\{//;s/,$//' | sort -u > cites_defined.txt

comm -23 cites_used.txt cites_defined.txt   # missing
comm -13 cites_used.txt cites_defined.txt   # orphan
```

URL/DOI/required-field linting performed with a Python pass over the
parsed entries (regex split on `^@` boundaries). All checks passed.

## Missing references

**None.** Every `\cite{}` key used in the manuscript resolves to a
`bibliography.bib` entry. No `?` markers will appear in the rendered PDF
from undefined citations.

## Orphan entries (defined but never cited)

These 90 keys exist in `bibliography.bib` but are not cited from any
`.tex` file. They are NOT removed in this revision — they may be
intended for future chapters, or may have been dropped from a prior
revision without removing the entry. Curating this list is deferred to
a future minor revision; for V1.2.1 they are retained but listed here
for visibility.

```
aaronson2008                  aaronson2020quantum             anita2018
arkani2013                    bailey2001                      baker1975
beale1984                     birch1965                       bombieri2000
boyd2001                      brans1961                       caffarelli1982
cardano1545                   chorin1994                      clifton2012
cohen2025cnt                  cohen2025consciousness          cohen2025cosmology
cohen2025grothendieck         cohen2025hodgedata              cohen2025omega
cohen2025peixoto              cohen2025riemann                cohen2025riemanndata
cohen2025technicalappendix    cohen2025xenon                  connes1976
conrey2003                    constantin1993                  cook1971
damgaard1987stochastic        deligne1971                     euler1748
gauss1799                     gehry2001                       gosseries2023microstate
griffiths1969                 grothendieck1969                grothendieck1985
gu_rqg_rescue                 hameroff2014consciousness       hendren2024iitwiki
hodge1950                     johnstone2002                   karp1972
kastrup2014why                kastrup2016more                 kastrup2017universe
kato1984                      kiefer2009                      kodaira1954
kogut1975hamiltonian          kolmogorov1941                  lawvere_rosebrugh
lefschetz1924                 leibniz1703                     leray1934
lewin1981polylogarithms       lurie2009                       maclanemoerdijk
mashour2022criticality        minlos1963generalized           muong2021
navier1822                    ns_fro_resolution               osterwalder1973axioms
osterwalder1975axioms         parisi1981perturbation          penrose1996orchestrated
poulin2023ede                 priest2002                      pvsnp_fro_resolution
raissi2019                    razborov1997                    reynolds1883
rh_fro_resolution             riess2019                       riess2021shoes
rovelli2004                   schwartz1971radon               stokes1845
tarkovsky1989                 telescope2025quipu              topoi_architectural
vazirani2018quantum           voisin2018                      weil1977
weinstein2021                 witten1995                      zhirnov2024ternary
```

### Likely-reason categories (informal)

- **Historical primary sources** retained for completeness but
  cited only indirectly (`euler1748`, `gauss1799`, `cardano1545`,
  `leibniz1703`, `navier1822`, `stokes1845`, `riemann1859`-style):
  the manuscript prefers to cite the modern textbook treatment.
- **Author's own preprints / data files** (`cohen2025*`): self-referential
  drafts that the published edition may not need to cite literally.
- **Duplicate keys with slight variants** (`aaronson2008` vs
  `aaronson2008algebrization`; `razborov1997` vs `razborov1997natural`;
  `cook1971` vs `cook1971complexity`): the longer-keyed variant is the
  one cited in text; the shorter is the orphan.
- **Reserved for future chapters** (`hodge1950`, `kodaira1954`,
  `lefschetz1924`, `griffiths1969`, `voisin2018`, `lurie2009` —
  algebraic-geometry classics; `osterwalder1973axioms`,
  `osterwalder1975axioms`, `kogut1975hamiltonian`,
  `damgaard1987stochastic`, `parisi1981perturbation` — QFT/YM
  axiomatics; `kastrup2014why`, `kastrup2016more`,
  `kastrup2017universe`, `penrose1996orchestrated`,
  `hameroff2014consciousness` — consciousness literature).
- **Recent data anchors** referenced in Lean but not yet wired into
  the manuscript prose (`gosseries2023microstate`,
  `hendren2024iitwiki`, `mashour2022criticality`,
  `telescope2025quipu`, `riess2021shoes`,
  `poulin2023ede`, `zhirnov2024ternary`).
- **FRO-resolution placeholders** (`*_fro_resolution`): reserved keys
  for forthcoming companion papers; not cited in the textbook.

### Recommendation

No removal in V1.2.1. A future curation pass should:
1. Merge duplicate-key variants (keep the cited variant, delete the
   orphan).
2. Either cite the historical primary sources from the prologue /
   preface, or move them to a dedicated `archive/historical.bib`.
3. Decide per-key whether each `cohen2025*` self-reference is needed.

## URL / DOI sanity

A scripted scan of all `url=` and `doi=` fields turned up:

- **0 malformed URLs** (every URL begins with `http`, `https`, or `ftp`).
- **0 malformed DOIs** (every DOI begins with `10.` or contains
  `doi.org`).

No further action needed.

## Required-field consistency

| Required field | Entries missing it |
|----------------|--------------------|
| `year`         | 0 |
| `title`        | 0 |
| `author` (non-`@misc`) | 0 |

All entries carry the BibTeX-required core fields for `plain` style.

## V1.2.0 → V1.2.1 transition issues

None surfaced. The bibliography is stable across the transition; only
the manuscript prose received targeted `\manuscriptcorrection`
footnotes (Ch~7 \texttt{thm:fine-structure}, Ch~11
\texttt{thm:anomaly\_cancel}, Ch~11 \texttt{prop:rqg\_mean},
Appendix~A Resonance Coefficients table at line~153).

## Sign-off

| Check                                              | Status |
|----------------------------------------------------|--------|
| Every `\cite` resolves                             | PASS   |
| Required fields populated                          | PASS   |
| URL / DOI syntactically well-formed                | PASS   |
| Orphan inventory captured                          | PASS (deferred curation) |
| Manuscript-correction footnotes referenced         | PASS (4/4 inconsistencies annotated) |

**Bibliography is publication-grade as of V1.2.1.**
