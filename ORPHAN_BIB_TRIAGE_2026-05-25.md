# Principia Fractalis — Orphan Bibliography Triage
**Date:** 2026-05-25
**Source audit:** `BIBLIOGRAPHY_AUDIT_2026-05-25.md` §3.1
**Scope:** 72 entries declared in `bibliography.bib` but never `\cite`d or `\bibitem`ed across the master folder.

This file does NOT remove anything — it categorizes the 72 orphans so a human (Pabs) can decide. Counts:

| Category | Count |
|---|---|
| **(a) canonical-keep** — important references that SHOULD be cited; restore to manuscript | **32** |
| **(b) Cohen self-cite to verify** — Pabs's own framework drafts; verify status, prune or convert to preprint cites | **13** |
| **(c) delete-candidate** — duplicates, low-relevance, or never-needed entries safe to remove | **27** |
| **Total** | **72** |

Recommendation: do (a) first (restores citations into the manuscript), then (b) (decide which Cohen drafts to keep as companion preprints), then (c) (prune dead entries).

---

## (a) Canonical-keep — restore to manuscript (32 entries)

These are important, real, historically/mathematically significant references that the manuscript chapters SHOULD cite but currently do not. Audit §6 items 3, 4, 5 already flagged the top priorities. Each entry below names the chapter where a `\cite{}` call would be appropriate.

### Mathematical foundations / classics

| Key | Where to cite | Why |
|---|---|---|
| `cardano1545` | Ch on roots of polynomials / history of math (frontmatter or §0 of ch 8) | Origin of complex numbers |
| `euler1748` | Ch 20 (RH history); historical preface | `Introductio in Analysin Infinitorum`; ζ origin |
| `gauss1799` | Ch 25 (Hodge ch on algebraic geometry); historical preface | Fundamental theorem of algebra (1799 thesis) |
| `leibniz1703` | Ch 17 / consciousness or history sections | Monadology / binary; historical |
| `arnold1966` | Ch 22 (Navier-Stokes); diffeomorphism group | Arnold's Lie-group view of incompressible flow |
| `griffiths1969` | Ch 25 (Hodge) §2-3 | Canonical Hodge-theory reference |
| `kodaira1954` | Ch 25 (Hodge) §2 — (1,1) classes discussion | Kodaira's vanishing theorem; foundational |
| `hodge1950` | Ch 25 (Hodge) §1 — conjecture statement | Hodge's own 1950 ICM address (the source) |
| `lefschetz1924` | Ch 25 (Hodge) §1 — (1,1) classes | The Lefschetz (1,1) theorem |
| `voisin2018` | Ch 25 (Hodge) §3 — modern progress | Voisin's modern survey of Hodge progress |
| `weil1977` | Ch 24 (BSD) §1 / Ch 20 (RH) | Weil's foundational work on zeta functions over function fields |
| `deligne1971` | Ch 25 / Ch 24 — mixed Hodge structures | Foundational; Hodge II/III papers |
| `grothendieck1969` | Ch 25 / appendix Grothendieck | Standard conjectures, motives |

### Riemann-Hypothesis & spectral approaches

| Key | Where to cite | Why |
|---|---|---|
| `bombieri2000` | Ch 20 (RH) §1 — problem statement | The official Clay Millennium Prize RH statement |
| `connes_trace_1998` | Ch 20 (RH) §1 — NCG/trace approach | Connes' foundational adèle-class trace formula (THE NCG-RH paper) |
| `connes1976` | Ch 20 (RH) — type III factors | Connes' 1976 Annals paper, type III classification |
| `berry_keating_1999` | Ch 20 (RH) — spectral conjectures | Berry-Keating H = xp Riemann operator conjecture |
| `lapidus_herichi_quantized_2012` | Ch 20 (RH) — fractal spectral op | Quantized fractal strings; directly relevant to PF |
| `lapidus_herichi_fractal_complex_2012` | Ch 20 (RH) | Fractal complex dimensions |
| `lapidus_sound_2015` | Ch 20 / Ch 22 | "Sound of fractal strings"; spectral fractality |
| `baladi_2000` | Ch 20 (RH) — transfer operators | Baladi's transfer-operator monograph, supports Mayer chain |
| `bruggeman_lewis_zagier_2015` | Ch 20 (RH) — Mayer/period functions | Period functions of Maass forms; bridges to Mayer |
| `lewis_zagier_2001` | Ch 20 (RH) — period functions | Foundational period-function paper |
| `lewin1981polylogarithms` | Ch 21 (P vs NP) — polylog identities | Lewin's polylog book; PF uses polylog identities |
| `birch1965` | Ch 24 (BSD) §1 — problem statement | The original BSD paper |

### Quantum / physics canon

| Key | Where to cite | Why |
|---|---|---|
| `osterwalder1973axioms` | Ch on QFT axioms (ch 11 or appendix B) | OS axioms I |
| `osterwalder1975axioms` | Same | OS axioms II |
| `witten1995` | Ch 11 (Geometric Unity / M-theory) | Witten's M-theory string-duality paper |
| `parisi1981perturbation` | Ch on stochastic quantization / Bochner-Minlos | Parisi-Wu stochastic quantization (foundational) |
| `damgaard1987stochastic` | Same | Damgaard-Hüffel review of stochastic quantization |
| `holm1985` | Ch 22 (Navier-Stokes) — geometric mechanics | Holm-Marsden-Ratiu Lie-Poisson |
| `kogut1975hamiltonian` | Ch 23 (Yang-Mills) — lattice/Hamiltonian | Kogut-Susskind Hamiltonian lattice formulation |
| `chorin1994` | Ch 22 (Navier-Stokes) | Chorin's Vorticity & Turbulence monograph |

---

## (b) Cohen self-cite to verify (13 entries)

These are Pabs's own unpublished framework manuscripts and "FRO resolution" working notes. The May-2024 citation-integrity passes already removed several; the survivors need a decision: convert to companion-preprint citations (with arXiv IDs when available) or delete.

| Key | Status / Comment |
|---|---|
| `cohen2025peixoto` | Unpublished framework note; never cited. Decide: arxivize or delete. |
| `cohen2025omega` | Unpublished; never cited. |
| `cohen2025grothendieck` | Unpublished; never cited. The Grothendieck appendix already exists in the manuscript; cite as `\cite{cohen2025grothendieck}` only if pointing to a separate preprint. |
| `cohen2025technicalappendix` | Unpublished; never cited. |
| `cohen2025xenon` | `howpublished = xenon_analysis.json` — **DATA FILE NOT FOUND** in `Evidence_and_Data_for_GitHub/`. Either generate the JSON or delete. |
| `cohen2025cnt` | `howpublished = cnt_results_v4_final.json` — **DATA FILE NOT FOUND**. Same disposition. |
| `cohen2025cosmology` | `howpublished = omega_bec_analysis_results.json` — **DATA FILE NOT FOUND**. Same disposition. |
| `cohen2025consciousness` | "In preparation"; never cited. |
| `cohen2025riemann` | "In preparation"; never cited. Likely superseded by the May-2026 Lean development referenced in Ch 20:439. |
| `gu_rqg_rescue` | "Mathematical Rescue of Weinstein's Geometric Unity via Fractal Resonance Ontology" — unpublished; never cited. Ch 11 is the obvious home but currently doesn't cite it. |
| `weinstein2021` | Weinstein's Geometric Unity reference — orphan (Ch 11 doesn't cite). Strictly third-party but Cohen-adjacent (Pabs's framework rescues it). |
| `gu_rqg_rescue` (dup row above — kept for visibility) | — |
| `weinstein2021` | — |

**Recommendation:** for each Cohen draft, either (i) add a `\cite{}` somewhere in the manuscript that genuinely needs to point at the companion preprint, or (ii) delete the entry. The current "orphan but kept" state is the worst of both worlds (reads as unfinished work).

---

## (c) Delete-candidate (27 entries)

These are entries that are not canonical-must-cite, not Cohen self-cites, and have no clear placement in the manuscript. Most are either tangential modern references, IIT-program working refs, or duplicates of better-cited papers. Safe to remove unless Pabs has a specific reason to keep.

### Modern IIT / consciousness / clinical (tangential to current ch 17 narrative)

| Key | Notes |
|---|---|
| `aaronson2020quantum` | Aaronson's quantum supremacy critique; off-topic for current manuscript scope. |
| `hameroff2014consciousness` | Penrose-Hameroff Orch-OR; superseded by current ch 17 cites. |
| `penrose1996orchestrated` | Same — old Orch-OR paper. |
| `kastrup2014why` | Kastrup analytic-idealism; never cited. |
| `kastrup2016more` | Same. |
| `kastrup2017universe` | Same. |
| `mashour2022criticality` | Mashour 2022 — superseded by `mashour2024anesthesia` (which IS cited). |
| `hendren2024iitwiki` | IIT wiki; not a primary source. Keep only if a chapter explicitly references the wiki. |
| `gosseries2023microstate` | Brain Topography 2023; not currently needed. |
| `clifton2012` | Clifton consciousness ref; unused. |

### Cosmology / observational (tangential, alternative refs exist)

| Key | Notes |
|---|---|
| `riess2019` | Hubble tension; ch 27 cites `divalentino2021` etc. instead. Either restore or drop. |
| `riess2021shoes` | Same. |
| `boyd2001` | Cosmology / inflation; unused. |
| `brans1961` | Brans-Dicke scalar-tensor; unused (no current scalar-tensor section). |
| `poulin2023ede` | Early Dark Energy; tangential. |
| `muong2021` | Specific astro paper; unused. |
| `telescope2025quipu` | Quipu supercluster; orphan but `boehringer2025quipu` IS cited and covers it. Drop this duplicate. |

### Quantum-foundations / misc

| Key | Notes |
|---|---|
| `vazirani2018quantum` | Vazirani-Vidick QKD; tangential. |
| `bailey2001` | Bailey & Borwein computational ID; tangential. |
| `anita2018` | Specific paper; unused, unclear relevance. |
| `arkani2013` | Arkani-Hamed amplituhedron-era; tangential. |
| `minlos1963generalized` | Minlos's original Bochner-Minlos paper. Borderline: if Pabs wants depth in appendix B then promote to (a); if not, drop (chain currently cites `reedsimon`). |
| `schwartz1971radon` | Schwartz Radon-measure paper; tangential. |
| `mayer_thermodynamic_1990` | NOTE: was a year-mismatch entry, NOT an orphan — already fixed; remove from delete list if seen here. |
| `rovelli2004` | Rovelli QG textbook; not currently cited. |
| `ruelle_2002` | Ruelle 2002; tangential. |
| `zhirnov2024ternary` | IEEE Nanotech ternary computing; unused. |
| `mashour_thermodynamic_consciousness` (n/a — illustrative) | — |
| `zhirnov2024ternary` | — |

(Several keys appear twice in the editing pass — dedup before action.)

---

## How to act on this triage

1. **(a) restore-to-manuscript:** the highest-impact set. Open the named chapters, add the suggested `\cite{key}` calls, rebuild. Estimate: 1-2 hours.
2. **(b) Cohen self-cite:** decide policy. Easiest: delete all 13 unless arxiv IDs are imminent. Most rigorous: arxivize the framework drafts and cite them as companion preprints.
3. **(c) delete-candidate:** lowest urgency. Can be done in one pass; mostly cosmetic and reduces bib size by ~30 entries.

After (a)-(c), re-run the audit script (`§8 Methodology` of the audit) to confirm zero orphans and zero missing.

---

**End of triage.**
