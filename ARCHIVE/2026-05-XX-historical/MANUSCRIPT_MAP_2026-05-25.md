# Principia Fractalis — Manuscript Map (2026-05-25)

**Source:** `/home/xluxx/Principia-Fractalis/Principia_Fractalis_master_folder_rev2/chapters/ch01_*.tex` through `ch35_*.tex`
**Lean codebase root:** `/home/xluxx/Principia-Fractalis/PF_Lean4_Code/`
**Coq codebase root:** `/home/xluxx/Principia-Fractalis/PF_Coq/`

## Summary statistics

| Metric | Count |
|---|---|
| Chapters mapped | 35 |
| Total `\label{...}` declarations (unique) | 737 |
| Total `\ref` / `\Cref` / `\eqref` invocations (unique target names) | 181 |
| Theorem-like environments (`theorem`, `lemma`, `proposition`, `corollary`, `conjecture`, `definition`, `heuristic`) | 414 |
| Unique Lean file paths cited in manuscript | 33 |
| Unique Lean theorem names cited via `\texttt{...}` | 121 |
| Dangling `\ref` targets (no matching `\label`) | **6** |
| Lean file paths cited that do NOT exist at that path | **3** (all exist under a different subdirectory) |
| Lean theorem names cited that do NOT exist in `PF_Lean4_Code/` | **1** load-bearing (`HodgeConjectureForAmbient`) |
| "see Chapter / Section N" promise-style cross-references | 34 |

## A. Dangling `\ref` targets

Six referenced labels have no matching `\label{...}` anywhere in the chapters.

| Dangling target | Cited at | Notes |
|---|---|---|
| `app:clinical` | ch07:391, ch07:700 | Appendix promised in Ch 7, never declared. |
| `app:software` | ch32:96 | Appendix promised in Ch 32, never declared. |
| `app:weinstein` | ch11:121, ch11:257, ch11:338 | Appendix promised three times in Ch 11 (Weinstein-bundle auxiliary calculations), never declared. |
| `ch:hodge` | ch07:443 | TYPO: actual chapter label is `ch:hodge-conjecture` (ch25:2). Easy fix. |
| `sec:consciousness-evidence` | ch21:1344 | Cited as the `ch_2` formula source for the consciousness gap; section never `\label`-ed. |
| `sec:fractal-resonance` | ch23:393 | Cited as the base-3 fractal-resonance section underlying `H_fYM`; section never `\label`-ed. |

## B. Stale Lean file-path citations

Three Lean file paths cited in the manuscript point to a subdirectory the file no longer lives in. All three files exist under a different subdirectory and should have their path updated.

| Cited path | Real path | Citation site |
|---|---|---|
| `PF_Lean4_Code/PF/PolylogSpectrum.lean` | `PF_Lean4_Code/PF/Analytic/PolylogSpectrum.lean` | ch09:141 |
| `PF_Lean4_Code/PF/QuantumComputerMaxSpeedup.lean` | `PF_Lean4_Code/PF/Consciousness/QuantumComputerMaxSpeedup.lean` | ch07:203 |
| `PF_Lean4_Code/PF/XENONExactMatch.lean` | `PF_Lean4_Code/PF/Consciousness/XENONExactMatch.lean` | ch11:423 |

## C. Stale Lean theorem-name citations

Of 121 distinct `\texttt{...}` Lean-identifier citations checked against `PF_Lean4_Code/**/*.lean`, the following are not found at all:

| Cited name | Location | Status |
|---|---|---|
| `HodgeConjectureForAmbient` | ch25:515 | **STALE Lean cite.** The Lean file (`PF/MillenniumSixReductions.lean` line ~669) defines this Prop as `HodgeConjecture`, not `HodgeConjectureForAmbient`. Manuscript name needs to be corrected (or Lean def renamed). |
| `arb`, `coqc`, `eigsh`, `PETSc`, `mpmath` | various | Tool names, not Lean identifiers — OK. |
| `ConsciousnessField`, `TmunuBase` | ch15:410, ch15:427 | Names of proposed Cactus / Einstein-Toolkit *modules to be created*, not Lean cites. OK. |
| `f691969` | various | git commit hash — OK. |
| `BSD_implies_L_function_formula`, `Spectral_to_Hodge`, `Spectral_to_NS`, `PF_Hodge_Spectral_Condition`, `PF_NS_Spectral_Condition` | ch22:445, ch24:484, ch25:494 | Explicitly identified by the chapter as **Coq axioms** in `PF_Coq/theories/Contracts/`. All five verified present in Coq sources — OK, not stale. |

Net: **one** truly stale Lean theorem-name citation (`HodgeConjectureForAmbient`).

## D. Promised-but-not-delivered cross-references

"See Chapter X" / "See Section Y" / "We will show" promises whose target content is not actually present:

| Promise | Where promised | Target audit |
|---|---|---|
| "Full proof in Chapter 8." (of resonance recursion / `R_f` results) | ch03:297 | Chapter 8 (`field_equations`) contains NO proof of `R_f`-recursion / `D_3` / resonance closed forms; it covers GR field equations + cosmological constant. The proof appears in Chapter 9 (`spectral_unity`), not Chapter 8. |
| "Section 13.6" (definition of the consciousness operator C) | ch17:480 | Chapter 13 (`solutions_dynamics`) has no Section 13.6, no `\label` for §13.6, and no consciousness-operator definition. The actual definition of C lives **inside ch17 itself** (ch17:374). The forward-reference to a non-existent §13.6 is a stale numbering artifact. |
| "$0.95$ is the critical threshold (derived in Chapter 6)" | ch04:621 | Chapter 6 (`consciousness`) *introduces* the 0.95 threshold and surveys four motivating arguments (ch06:184) but does NOT contain a first-principles derivation. The chapter's own ch06:11 disclosure flag ("Rigorous derivation of the 0.95 crystallization threshold") confirms this is open. The forward promise from ch04 over-claims what ch06 delivers. |
| "All code examples in Chapter 31 use these libraries" | ch33:425 | Chapter 31 (`neuroscience_iit`) contains NO `lstlisting` / `verbatim` Python-code blocks. The referenced "code examples in Chapter 31" do not exist. Likely intended Chapter 35 (`software`), which is the actual code chapter. |
| "Implementation details in Chapter 31 code repository" | ch34:346 | Same issue as above; Chapter 31 contains no code repository or code listings. |
| "via the methods in Chapter 27" (direct `ch_2` measurement methods for turbulent flow) | ch10:485 | Chapter 27 (`dark_energy_expansion`) is on cosmological expansion and does not describe `ch_2(x,t)` direct-measurement methodology for turbulent flows. The forward reference does not deliver a corresponding measurement-methods section. |
| `from principia_fractalis.core ...`, `.pvsnp ...`, `.consciousness ...`, `.riemann ...` (Python code blocks in ch35) | ch35:185, 258, 270, 289, 290, 324, 382, 461, 546, 570 | The `principia_fractalis` Python package referenced as installable code in Chapter 35 does NOT exist anywhere in the repo (verified by `find`). The chapter presents `pip install` / `import principia_fractalis.*` examples for software that has not been packaged. |

The remaining "see Chapter X" cross-references in the corpus (e.g. ch07:497 → ch:navier-stokes, ch07:505 → ch:navier-stokes, ch07:507 → ch:yang-mills, ch07:509 → ch:geometric_unity, ch07:511 → ch:consciousness, ch10:47 → Ch 4, ch10:122 → Ch 9, ch11:375 → Ch 26, ch20:93 → ch:consciousness, ch22:55 forward "we will prove", ch01:1346 → Ch 3 `R_f` definition, etc.) all resolve to chapters that genuinely contain the referenced material.

## E. Cross-prover note (informational)

Five `\texttt{...}` names flagged as missing in Lean are explicitly framed by the manuscript text as **Coq** axioms living in `PF_Coq/theories/Contracts/`: `BSD_implies_L_function_formula` (`PF_Coq/theories/Contracts/BSD.v:302`), `Spectral_to_Hodge` (`PF_Coq/theories/Core/AxiomAudit.v:312`), `Spectral_to_NS` (`PF_Coq/theories/Core/AxiomAudit.v:373` + `Contracts/NavierStokes.v:147`), `PF_NS_Spectral_Condition` (`PF_Coq/theories/Contracts/NavierStokes.glob:227`), `PF_Hodge_Spectral_Condition` (Coq Contracts/Hodge.v). All five exist on the Coq side. These are not stale.

## F. Per-chapter inventory

Each entry below lists the `\label{...}` declarations (with manuscript line numbers as `LN`), the theorem-like environments (with attached label if any), and the count of Lean file-path citations made from that chapter.

### Per-chapter summary table

| Chapter | Labels | Refs | Thm | Lem | Prop | Cor | Conj | Def | Heur | Lean cites |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| ch01_numbers | 44 | 7 | 8 | 0 | 2 | 1 | 0 | 3 | 0 | 0 |
| ch02_complex | 38 | 19 | 10 | 4 | 1 | 2 | 0 | 13 | 0 | 0 |
| ch03_resonance | 16 | 7 | 3 | 1 | 3 | 0 | 0 | 2 | 0 | 3 |
| ch04_timeless_field | 38 | 4 | 0 | 1 | 2 | 0 | 0 | 0 | 0 | 0 |
| ch05_peixoto | 11 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch06_consciousness | 27 | 7 | 0 | 3 | 2 | 0 | 0 | 0 | 0 | 0 |
| ch07_constants | 15 | 32 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 3 |
| ch08_field_equations | 15 | 7 | 0 | 0 | 4 | 1 | 0 | 0 | 0 | 0 |
| ch09_spectral_unity | 17 | 9 | 6 | 2 | 0 | 0 | 1 | 3 | 0 | 8 |
| ch10_hydrodynamic | 17 | 15 | 6 | 2 | 1 | 0 | 0 | 2 | 0 | 4 |
| ch11_geometric_unity | 12 | 6 | 4 | 0 | 4 | 0 | 0 | 2 | 0 | 2 |
| ch12_qft_consciousness | 14 | 10 | 0 | 0 | 2 | 1 | 0 | 0 | 0 | 0 |
| ch13_solutions_dynamics | 10 | 5 | 5 | 0 | 0 | 0 | 0 | 1 | 0 | 0 |
| ch14_symmetries_conservation | 15 | 2 | 6 | 0 | 0 | 0 | 0 | 7 | 0 | 0 |
| ch15_computational_methods | 12 | 4 | 1 | 0 | 0 | 0 | 0 | 5 | 0 | 0 |
| ch16_spectral_foundations | 20 | 1 | 5 | 0 | 0 | 0 | 0 | 9 | 0 | 0 |
| ch17_operator_theory | 20 | 2 | 9 | 0 | 0 | 0 | 0 | 7 | 0 | 1 |
| ch18_spectral_measures | 10 | 2 | 4 | 0 | 0 | 0 | 0 | 3 | 0 | 0 |
| ch19_physical_applications | 12 | 7 | 6 | 0 | 0 | 0 | 4 | 0 | 0 | 0 |
| ch20_riemann_hypothesis | 28 | 31 | 6 | 1 | 4 | 2 | 0 | 0 | 0 | 12 |
| ch21_p_vs_np | 75 | 76 | 19 | 4 | 4 | 4 | 3 | 8 | 1 | 16 |
| ch22_navier_stokes | 27 | 37 | 7 | 0 | 3 | 0 | 0 | 1 | 0 | 3 |
| ch23_yang_mills | 27 | 39 | 7 | 0 | 2 | 0 | 1 | 0 | 0 | 6 |
| ch24_birch_swinnerton_dyer | 30 | 31 | 6 | 0 | 2 | 0 | 3 | 0 | 0 | 3 |
| ch25_hodge_conjecture | 30 | 25 | 8 | 0 | 2 | 0 | 2 | 0 | 0 | 6 |
| ch26_cosmological_constant | 13 | 10 | 3 | 0 | 2 | 0 | 0 | 0 | 0 | 1 |
| ch27_dark_energy_expansion | 20 | 9 | 6 | 0 | 2 | 0 | 0 | 0 | 0 | 0 |
| ch28_early_universe | 16 | 7 | 5 | 0 | 4 | 0 | 0 | 0 | 0 | 0 |
| ch29_observational_tests | 15 | 3 | 6 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| ch30_clinical_consciousness | 20 | 12 | 9 | 0 | 2 | 0 | 0 | 2 | 0 | 0 |
| ch31_neuroscience_iit | 17 | 6 | 10 | 0 | 2 | 0 | 0 | 0 | 0 | 0 |
| ch32_consciousness_quantification | 20 | 10 | 7 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| ch33_numerical_methods | 21 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| ch34_verification | 10 | 5 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 9 |
| ch35_software | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

### Detailed per-chapter inventory

### ch01_numbers.tex
- **Labels** (44):
  - L2: `ch:numbers`
  - L18: `sec:counting-systems`
  - L21: `subsec:intuitive-bases`
  - L93: `fig:timeline`
  - L117: `fig:bases`
  - L236: `sec:digital-sum-patterns`
  - L241: `subsec:visualizing-pattern`
  - L292: `fig:d3pattern`
  - L314: `subsec:computational-exploration`
  - L360: `subsec:mathematical-properties`
  - L370: `thm:d3-self-similarity`
  - L396: `thm:d3-addition`
  - L422: `thm:d3-modular`
  - L452: `subsec:connections-number-theory`
  - L483: `subsec:exercises-1-2`
  - L556: `sec:divisibility-rules`
  - L563: `subsec:divisibility-by-2`
  - L601: `subsec:general-principle`
  - L608: `thm:digital-sum-modular`
  - L643: `thm:parity-rule`
  - L644: `cor:base3-parity`
  - L666: `subsec:classical-rules`
  - L686: `subsec:why-not-three`
  - L706: `subsec:computational-divisibility`
  - L740: `subsec:divisibility-exercises`
  - L815: `sec:fractal-structure`
  - L820: `subsec:zooming-in`
  - L869: `fig:fractalstaircase`
  - L873: `subsec:scaling-law`
  - L882: `thm:d3-scaling`
  - L930: `fig:scalinglaw`
  - L934: `subsec:what-is-fractal`
  - L954: `subsec:fractal-dimension`
  - L982: `subsec:recursive-structure`
  - L991: `thm:d3-recursive-fractal`
  - L1020: `subsec:visualizing-fractal`
  - L1043: `subsec:cantor-connection`
  - L1064: `subsec:computational-fractal`
  - L1103: `subsec:fractal-exercises`
  - L1174: `sec:applications`
  - L1206: `prop:parity-checksum`
  - L1246: `thm:div-by-2-app`
  - L1280: `prop:parity-filter`
  - L1309: `def:d3-hash`
- **Theorem-like environments** (14):
  - L159: `definition`
  - L364: `definition`
  - L369: `theorem` [thm:d3-self-similarity]
  - L395: `theorem` [thm:d3-addition]
  - L414: `corollary`
  - L421: `theorem` [thm:d3-modular]
  - L607: `theorem` [thm:digital-sum-modular]
  - L642: `theorem` [thm:parity-rule] [cor:base3-parity]
  - L881: `theorem` [thm:d3-scaling]
  - L990: `theorem` [thm:d3-recursive-fractal]
  - L1205: `proposition` [prop:parity-checksum]
  - L1245: `theorem` [thm:div-by-2-app]
  - L1279: `proposition` [prop:parity-filter]
  - L1308: `definition` [def:d3-hash]
- **Lean cites**: 0

### ch02_complex.tex
- **Labels** (8):
  - L2: `ch:complex`
  - L18: `sec:preliminaries`
  - L85: `sec:integral-foundations`
  - L156: `sec:analytic-continuation`
  - L210: `sec:logarithm-fractional-powers`
  - L277: `sec:polylogarithms`
  - L354: `sec:dirichlet-convergence`
  - L390: `sec:dependencies`
- **Theorem-like environments** (30):
  - L24: `definition`
  - L28: `definition`
  - L50: `definition`
  - L58: `definition`
  - L68: `definition`
  - L76: `definition`
  - L80: `definition`
  - L89: `theorem`
  - L102: `theorem`
  - L109: `corollary`
  - L122: `theorem`
  - L128: `theorem`
  - L134: `theorem`
  - L140: `lemma`
  - L151: `theorem`
  - L162: `definition`
  - L166: `definition`
  - L177: `theorem`
  - L195: `definition`
  - L216: `definition`
  - L225: `definition`
  - L235: `lemma`
  - L250: `lemma`
  - L283: `definition`
  - L290: `proposition`
  - L309: `theorem`
  - L321: `corollary`
  - L341: `theorem`
  - L358: `lemma`
  - L373: `theorem`
- **Lean cites**: 0

### ch03_resonance.tex
- **Labels** (16):
  - L2: `ch:resonance`
  - L18: `sec:motivation`
  - L81: `sec:definition`
  - L90: `def:fractal-resonance`
  - L134: `sec:convergence`
  - L143: `thm:rf-convergence`
  - L201: `sec:sacred-geometry`
  - L232: `tab:resonance-values`
  - L259: `thm:rh-resonance`
  - L274: `thm:complexity-gap`
  - L300: `sec:pi-over-10`
  - L329: `prop:polylog-decomposition`
  - L332: `eq:rf-polylog-decomposition`
  - L355: `eq:refuted-rf-leading`
  - L367: `eq:lambda0-operator`
  - L385: `sec:computation`
- **Theorem-like environments** (9):
  - L89: `definition` [def:fractal-resonance]
  - L113: `proposition`
  - L142: `theorem` [thm:rf-convergence]
  - L177: `proposition`
  - L190: `lemma`
  - L211: `definition`
  - L258: `theorem` [thm:rh-resonance]
  - L273: `theorem` [thm:complexity-gap]
  - L328: `proposition` [prop:polylog-decomposition]
- **Lean cites**: 0

### ch04_timeless_field.tex
- **Labels** (12):
  - L2: `ch:timeless-field`
  - L18: `sec:beyond-spacetime`
  - L96: `sec:building-blocks`
  - L194: `sec:construction`
  - L306: `fig:projective-limit`
  - L356: `sec:math-properties`
  - L439: `sec:physical-emergence`
  - L444: `sec:spacetime-emergence`
  - L543: `sec:resonance-info`
  - L594: `sec:consciousness-emergence`
  - L642: `sec:field-equations`
  - L682: `sec:summary`
- **Theorem-like environments** (3):
  - L360: `lemma`
  - L577: `proposition`
  - L671: `proposition`
- **Lean cites**: 0

### ch05_peixoto.tex
- **Labels** (1):
  - L2: `ch:peixoto`
- **Theorem-like environments** (0):
- **Lean cites**: 0

### ch06_consciousness.tex
- **Labels** (11):
  - L2: `ch:consciousness`
  - L18: `sec:measuring-awareness`
  - L87: `sec:consciousness-sheaf`
  - L142: `sec:second-chern`
  - L171: `sec:critical-threshold`
  - L251: `sec:rigorous-threshold`
  - L446: `sec:physical-systems`
  - L505: `sec:math-properties-ch5`
  - L529: `sec:computational`
  - L576: `sec:philosophical`
  - L608: `sec:summary-ch5`
- **Theorem-like environments** (5):
  - L321: `lemma`
  - L337: `lemma`
  - L355: `lemma`
  - L491: `proposition`
  - L509: `proposition`
- **Lean cites**: 0

### ch07_constants.tex
- **Labels** (3):
  - L2: `ch:constants`
  - L222: `tab:sacred-alpha`
  - L684: `fig:constant-emergence`
- **Theorem-like environments** (1):
  - L572: `proposition`
- **Lean cites**: 0

### ch08_field_equations.tex
- **Labels** (1):
  - L2: `ch:field-equations`
- **Theorem-like environments** (5):
  - L219: `proposition`
  - L296: `proposition`
  - L355: `corollary`
  - L386: `proposition`
  - L416: `proposition`
- **Lean cites**: 0

### ch09_spectral_unity.tex
- **Labels** (13):
  - L2: `ch:spectral_unity`
  - L38: `def:digital_sum`
  - L57: `lem:d3_scaling`
  - L77: `def:comp_operators`
  - L91: `thm:self_adjoint_fractal`
  - L111: `thm:pvsnp_spectral`
  - L161: `def:consciousness_zeta_op`
  - L188: `lem:alpha_scaling`
  - L216: `thm:spectral_zeta`
  - L253: `thm:riemann_ground_energy`
  - L277: `thm:critical_line`
  - L366: `thm:universal_frequency`
  - L401: `thm:barrier_bypass`
- **Theorem-like environments** (12):
  - L37: `definition` [def:digital_sum]
  - L56: `lemma` [lem:d3_scaling]
  - L76: `definition` [def:comp_operators]
  - L90: `theorem` [thm:self_adjoint_fractal]
  - L110: `theorem` [thm:pvsnp_spectral]
  - L160: `definition` [def:consciousness_zeta_op]
  - L187: `lemma` [lem:alpha_scaling]
  - L215: `theorem` [thm:spectral_zeta]
  - L252: `theorem` [thm:riemann_ground_energy]
  - L276: `theorem` [thm:critical_line]
  - L365: `conjecture` [thm:universal_frequency]
  - L400: `theorem` [thm:barrier_bypass]
- **Lean cites**: 0

### ch10_hydrodynamic.tex
- **Labels** (14):
  - L2: `ch:hydrodynamic`
  - L61: `eq:ns_consciousness`
  - L67: `def:consciousness_viscosity`
  - L84: `lem:consciousness_regularization`
  - L164: `thm:enhanced_energy`
  - L212: `eq:vorticity_evolution`
  - L224: `thm:fractal_spectrum`
  - L241: `lem:fractal_dimension_bound`
  - L279: `thm:bkm_classical`
  - L290: `thm:bkm_enhanced`
  - L316: `thm:ns_global_regularity`
  - L369: `def:consciousness_reynolds`
  - L379: `thm:critical_reynolds`
  - L453: `prop:two_scale_cascade`
- **Theorem-like environments** (11):
  - L66: `definition` [def:consciousness_viscosity]
  - L83: `lemma` [lem:consciousness_regularization]
  - L163: `theorem` [thm:enhanced_energy]
  - L223: `theorem` [thm:fractal_spectrum]
  - L240: `lemma` [lem:fractal_dimension_bound]
  - L278: `theorem` [thm:bkm_classical]
  - L289: `theorem` [thm:bkm_enhanced]
  - L315: `theorem` [thm:ns_global_regularity]
  - L368: `definition` [def:consciousness_reynolds]
  - L378: `theorem` [thm:critical_reynolds]
  - L452: `proposition` [prop:two_scale_cascade]
- **Lean cites**: 0

### ch11_geometric_unity.tex
- **Labels** (12):
  - L2: `ch:geometric_unity`
  - L54: `def:rqg_operator`
  - L72: `prop:rqg_properties`
  - L92: `def:rqg_shiab`
  - L102: `thm:rqg_shiab_welldefined`
  - L141: `thm:anomaly_cancel`
  - L190: `prop:rqg_mean`
  - L214: `thm:holographic_projection`
  - L312: `thm:rqg_cohomology`
  - L432: `prop:gu_contains_string`
  - L449: `prop:gu_lqg`
  - L510: `sec:mallett_phi`
- **Theorem-like environments** (10):
  - L53: `definition` [def:rqg_operator]
  - L71: `proposition` [prop:rqg_properties]
  - L91: `definition` [def:rqg_shiab]
  - L101: `theorem` [thm:rqg_shiab_welldefined]
  - L140: `theorem` [thm:anomaly_cancel]
  - L189: `proposition` [prop:rqg_mean]
  - L213: `theorem` [thm:holographic_projection]
  - L311: `theorem` [thm:rqg_cohomology]
  - L431: `proposition` [prop:gu_contains_string]
  - L448: `proposition` [prop:gu_lqg]
- **Lean cites**: 0

### ch12_qft_consciousness.tex
- **Labels** (1):
  - L2: `ch:qft-consciousness`
- **Theorem-like environments** (3):
  - L332: `corollary`
  - L428: `proposition`
  - L451: `proposition`
- **Lean cites**: 0

### ch13_solutions_dynamics.tex
- **Labels** (2):
  - L2: `ch:solutions-dynamics`
  - L438: `tab:observables-summary`
- **Theorem-like environments** (6):
  - L40: `definition`
  - L68: `theorem`
  - L152: `theorem`
  - L235: `theorem`
  - L302: `theorem`
  - L366: `theorem`
- **Lean cites**: 0

### ch14_symmetries_conservation.tex
- **Labels** (2):
  - L2: `ch:symmetries-conservation`
  - L509: `tab:symmetries-summary`
- **Theorem-like environments** (13):
  - L42: `definition`
  - L50: `theorem`
  - L103: `theorem`
  - L185: `definition`
  - L205: `theorem`
  - L245: `definition`
  - L277: `definition`
  - L300: `definition`
  - L340: `theorem`
  - L363: `definition`
  - L400: `theorem`
  - L417: `definition`
  - L460: `theorem`
- **Lean cites**: 0

### ch15_computational_methods.tex
- **Labels** (2):
  - L2: `ch:computational-methods`
  - L586: `fig:binary-consciousness-waveform`
- **Theorem-like environments** (6):
  - L43: `definition`
  - L72: `theorem`
  - L106: `definition`
  - L128: `definition`
  - L224: `definition`
  - L476: `definition`
- **Lean cites**: 0

### ch16_spectral_foundations.tex
- **Labels** (1):
  - L2: `ch:spectral-foundations`
- **Theorem-like environments** (14):
  - L47: `definition`
  - L63: `definition`
  - L71: `definition`
  - L95: `definition`
  - L149: `theorem`
  - L163: `theorem`
  - L227: `definition`
  - L269: `theorem`
  - L292: `definition`
  - L336: `theorem`
  - L353: `definition`
  - L375: `definition`
  - L386: `definition`
  - L417: `theorem`
- **Lean cites**: 0

### ch17_operator_theory.tex
- **Labels** (1):
  - L2: `ch:operator-theory`
- **Theorem-like environments** (16):
  - L36: `definition`
  - L49: `definition`
  - L76: `theorem`
  - L105: `definition`
  - L113: `theorem`
  - L157: `theorem`
  - L180: `definition`
  - L193: `definition`
  - L207: `theorem`
  - L234: `theorem`
  - L267: `theorem`
  - L298: `definition`
  - L311: `theorem`
  - L346: `theorem`
  - L388: `theorem`
  - L438: `definition`
- **Lean cites**: 0

### ch18_spectral_measures.tex
- **Labels** (2):
  - L2: `ch:spectral-measures`
  - L310: `tab:phi-ch2-correlation`
- **Theorem-like environments** (7):
  - L40: `definition`
  - L76: `definition`
  - L126: `theorem`
  - L199: `definition`
  - L236: `theorem`
  - L379: `theorem`
  - L442: `theorem`
- **Lean cites**: 0

### ch19_physical_applications.tex
- **Labels** (2):
  - L2: `ch:physical-applications`
  - L217: `fig:cmb-power-spectrum`
- **Theorem-like environments** (10):
  - L49: `theorem`
  - L75: `theorem`
  - L114: `conjecture`
  - L156: `theorem`
  - L220: `theorem`
  - L271: `theorem`
  - L290: `conjecture`
  - L320: `conjecture`
  - L359: `conjecture`
  - L400: `theorem`
- **Lean cites**: 0

### ch20_riemann_hypothesis.tex
- **Labels** (1):
  - L2: `ch:riemann-hypothesis`
- **Theorem-like environments** (13):
  - L40: `theorem`
  - L79: `proposition`
  - L100: `theorem`
  - L133: `proposition`
  - L169: `proposition`
  - L234: `theorem`
  - L254: `lemma` [eq:A-norm-bound]
  - L297: `corollary`
  - L318: `proposition`
  - L367: `theorem`
  - L415: `theorem`
  - L458: `corollary`
  - L470: `theorem`
- **Lean cites**: 0

### ch21_p_vs_np.tex
- **Labels** (1):
  - L2: `ch:p-vs-np`
- **Theorem-like environments** (43):
  - L66: `theorem`
  - L92: `proposition`
  - L122: `theorem`
  - L140: `definition`
  - L160: `lemma`
  - L172: `definition`
  - L185: `definition`
  - L259: `theorem`
  - L281: `theorem`
  - L323: `definition`
  - L333: `definition`
  - L347: `theorem`
  - L374: `theorem`
  - L480: `theorem` [eq:b_clean_phase]
  - L490: `theorem` [eq:h3_origin]
  - L513: `theorem`
  - L573: `conjecture`
  - L581: `heuristic`
  - L590: `conjecture`
  - L686: `definition`
  - L709: `lemma`
  - L733: `lemma`
  - L751: `proposition` [eq:jonquieres-expansion]
  - L806: `lemma`
  - L844: `proposition`
  - L901: `definition`
  - L910: `proposition`
  - L969: `theorem`
  - L1020: `corollary`
  - L1066: `theorem`
  - L1116: `definition`
  - L1124: `theorem`
  - L1131: `theorem`
  - L1166: `corollary`
  - L1180: `theorem`
  - L1214: `conjecture`
  - L1358: `theorem`
  - L1380: `theorem`
  - L1392: `theorem`
  - L1405: `corollary`
  - L1413: `corollary`
  - L1423: `theorem`
  - L1431: `theorem`
- **Lean cites**: 0

### ch22_navier_stokes.tex
- **Labels** (1):
  - L2: `ch:navier-stokes`
- **Theorem-like environments** (11):
  - L49: `theorem`
  - L73: `definition`
  - L95: `theorem`
  - L170: `proposition`
  - L194: `theorem` [eq:cascade-vs-crow]
  - L282: `theorem`
  - L293: `theorem`
  - L339: `theorem`
  - L411: `proposition`
  - L468: `theorem`
  - L489: `proposition`
- **Lean cites**: 0

### ch23_yang_mills.tex
- **Labels** (3):
  - L2: `ch:yang-mills`
  - L173: `sec:spectral_embedding`
  - L264: `fig:spectral_embedding`
- **Theorem-like environments** (10):
  - L103: `theorem`
  - L141: `proposition`
  - L286: `theorem`
  - L306: `theorem`
  - L352: `proposition`
  - L370: `theorem`
  - L396: `theorem` [eq:level1-ym-spectrum]
  - L408: `conjecture`
  - L450: `theorem`
  - L508: `theorem`
- **Lean cites**: 0

### ch24_birch_swinnerton_dyer.tex
- **Labels** (2):
  - L2: `ch:birch-swinnerton-dyer`
  - L386: `alg:fractal-rank`
- **Theorem-like environments** (11):
  - L61: `theorem`
  - L130: `conjecture`
  - L172: `theorem`
  - L227: `proposition`
  - L267: `theorem` [eq:T-E-symmetrised]
  - L299: `proposition`
  - L309: `theorem`
  - L362: `conjecture`
  - L406: `theorem`
  - L457: `conjecture`
  - L461: `theorem`
- **Lean cites**: 0

### ch25_hodge_conjecture.tex
- **Labels** (2):
  - L2: `ch:hodge-conjecture`
  - L402: `alg:cycle-extraction`
- **Theorem-like environments** (12):
  - L162: `conjecture`
  - L186: `theorem`
  - L192: `theorem`
  - L251: `proposition`
  - L299: `theorem` [eq:sigma-c-decomposition]
  - L326: `theorem`
  - L348: `proposition`
  - L356: `conjecture`
  - L377: `theorem`
  - L421: `theorem`
  - L425: `theorem`
  - L497: `theorem`
- **Lean cites**: 0

### ch26_cosmological_constant.tex
- **Labels** (3):
  - L2: `ch:cosmological-constant`
  - L412: `alg:lambda-eff`
  - L460: `tab:lambda-sensitivity`
- **Theorem-like environments** (5):
  - L83: `proposition`
  - L188: `theorem`
  - L321: `proposition`
  - L358: `theorem`
  - L430: `theorem`
- **Lean cites**: 0

### ch27_dark_energy_expansion.tex
- **Labels** (7):
  - L2: `ch:dark-energy-expansion`
  - L477: `fig:hubble-diagram`
  - L481: `sec:quipu`
  - L547: `fig:quipu_schematic`
  - L561: `eq:Lcoh_formula`
  - L612: `fig:quipu_scale`
  - L671: `tab:parameters-comparison`
- **Theorem-like environments** (8):
  - L85: `theorem` [eq:mf1]
  - L116: `proposition`
  - L159: `theorem`
  - L214: `theorem`
  - L266: `proposition`
  - L332: `theorem`
  - L368: `theorem`
  - L388: `theorem`
- **Lean cites**: 0

### ch28_early_universe.tex
- **Labels** (2):
  - L2: `ch:early-universe`
  - L62: `tab:cosmic-timeline`
- **Theorem-like environments** (9):
  - L103: `theorem`
  - L164: `proposition`
  - L242: `theorem`
  - L313: `theorem`
  - L331: `proposition`
  - L392: `theorem`
  - L488: `proposition`
  - L505: `theorem`
  - L546: `proposition`
- **Lean cites**: 0

### ch29_observational_tests.tex
- **Labels** (6):
  - L2: `ch:observational-tests`
  - L216: `fig:hubble-diagram-full`
  - L235: `tab:sn-residuals`
  - L308: `tab:bao-measurements`
  - L466: `tab:parameter-constraints`
  - L511: `fig:posterior-contours`
- **Theorem-like environments** (7):
  - L124: `theorem`
  - L261: `theorem`
  - L331: `theorem`
  - L352: `theorem`
  - L384: `theorem`
  - L419: `proposition`
  - L560: `theorem`
- **Lean cites**: 0

### ch30_clinical_consciousness.tex
- **Labels** (3):
  - L2: `ch:clinical-consciousness`
  - L410: `fig:ch2-distribution`
  - L515: `fig:recovery-curve`
- **Theorem-like environments** (13):
  - L50: `theorem`
  - L98: `theorem`
  - L132: `definition`
  - L151: `proposition`
  - L194: `definition`
  - L208: `theorem`
  - L221: `theorem`
  - L240: `theorem`
  - L345: `theorem`
  - L462: `theorem`
  - L520: `proposition`
  - L548: `theorem`
  - L643: `theorem`
- **Lean cites**: 0

### ch31_neuroscience_iit.tex
- **Labels** (2):
  - L2: `ch:neuroscience-iit`
  - L214: `fig:thalamocortical`
- **Theorem-like environments** (12):
  - L64: `theorem`
  - L152: `theorem`
  - L219: `theorem`
  - L249: `theorem`
  - L287: `proposition`
  - L310: `theorem`
  - L377: `theorem`
  - L438: `theorem`
  - L464: `theorem`
  - L495: `theorem`
  - L527: `theorem`
  - L585: `proposition`
- **Lean cites**: 0

### ch32_consciousness_quantification.tex
- **Labels** (2):
  - L2: `ch:consciousness-quantification`
  - L542: `fig:8-channel`
- **Theorem-like environments** (8):
  - L74: `theorem`
  - L391: `theorem`
  - L427: `theorem`
  - L456: `theorem`
  - L492: `theorem`
  - L547: `proposition`
  - L577: `theorem`
  - L666: `theorem`
- **Lean cites**: 0

### ch33_numerical_methods.tex
- **Labels** (8):
  - L2: `ch:numerical-methods`
  - L18: `sec:beyond-floating-point`
  - L87: `sec:eigenvalue-algorithms`
  - L168: `sec:zeta-computation`
  - L215: `sec:integration-methods`
  - L269: `sec:error-analysis`
  - L321: `sec:parallel-computation`
  - L361: `sec:summary-ch29`
- **Theorem-like environments** (0):
- **Lean cites**: 0

### ch34_verification.tex
- **Labels** (10):
  - L2: `ch:verification`
  - L18: `sec:reproducibility-standard`
  - L59: `sec:formal-verification-status`
  - L263: `sec:riemann-verification`
  - L374: `sec:pvsnp-verification`
  - L503: `sec:consciousness-verification`
  - L635: `sec:automated-testing`
  - L723: `sec:troubleshooting`
  - L762: `sec:repositories`
  - L817: `sec:summary-ch30`
- **Theorem-like environments** (0):
- **Lean cites**: 0

### ch35_software.tex
- **Labels** (10):
  - L2: `ch:software`
  - L18: `sec:open-science`
  - L51: `sec:installation`
  - L141: `sec:architecture`
  - L279: `sec:code-examples`
  - L439: `sec:optimization`
  - L535: `sec:extending`
  - L590: `sec:documentation`
  - L691: `sec:licensing`
  - L756: `sec:summary-ch31`
- **Theorem-like environments** (0):
- **Lean cites**: 0



## G. Per-chapter Lean file-path citations (raw)

Only chapters that cite at least one Lean file appear below. Format: `manuscript-line: cited-path`.

### ch03_resonance.tex
  - L231: `PF/TuringEncoding/AlphaEnum.lean`
  - L283: `PF/SpectralGap.lean`
  - L370: `PF/SpectralGap.lean`

### ch07_constants.tex
  - L176: `PF/SpectralGap.lean`
  - L203: `PF/QuantumComputerMaxSpeedup.lean`
  - L441: `PF/MillenniumSixReductions.lean`

### ch09_spectral_unity.tex
  - L26: `PF/SpectralGap.lean`
  - L26: `PF/Millennium.lean`
  - L105: `PF/AlphaBasisGenerators.lean`
  - L105: `PF/TuringEncoding/Operators.lean`
  - L117: `PF/SpectralGap.lean`
  - L141: `PF/PolylogSpectrum.lean`
  - L141: `PF/SpectralGap.lean`
  - L211: `PF/Consciousness/Ch2PhiBridge.lean`
  - L247: `PF/RHSurjectivityConjecture.lean`
  - L247: `PF/SpectralBijection.lean`
  - L379: `PF/Analytic/RfNumericalRefutation.lean`
  - L382: `PF/MillenniumSixReductions.lean`
  - L382: `PF/Analytic/CleanLambdaClosedForms.lean`

### ch10_hydrodynamic.tex
  - L148: `PF/MillenniumSixReductions.lean`
  - L148: `PF/Analytic/CleanLambdaClosedForms.lean`
  - L308: `PF/Analytic/CleanLambdaClosedForms.lean`
  - L342: `PF/MillenniumSixReductions.lean`
  - L342: `PF/Analytic/CleanLambdaClosedForms.lean`
  - L407: `PF/MillenniumSixReductions.lean`

### ch11_geometric_unity.tex
  - L338: `PF/Cosmology/E6ChernIndex78pi.lean`
  - L423: `PF/XENONExactMatch.lean`

### ch17_operator_theory.tex
  - L416: `PF/Consciousness/ConsciousnessOperatorC.lean`
  - L416: `PF/Consciousness/ConsciousnessRHBridge.lean`

### ch20_riemann_hypothesis.tex
  - L288: `PF/Analytic/PolylogSpectrum.lean`
  - L290: `PF/MillenniumSixReductions.lean`
  - L439: `PF/SpectralBijection.lean`
  - L439: `PF/RHSurjectivityConjecture.lean`
  - L451: `PF/Consciousness/Ch2PhiBridge.lean`
  - L459: `PF/RHSurjectivityConjecture.lean`
  - L463: `PF/RHSurjectivityConjecture.lean`

### ch21_p_vs_np.tex
  - L446: `PF/SpectralGap.lean`
  - L462: `PF/SpectralGap.lean`
  - L469: `PF/MillenniumSixReductions.lean`
  - L488: `PF/Analytic/BCleanPhaseIdentity.lean`
  - L509: `PF/H3CoxeterOrigin.lean`
  - L518: `PF/SpectralGap.lean`
  - L535: `PF/SpectralGap.lean`
  - L625: `PF/MillenniumSixReductions.lean`
  - L664: `PF/Analytic/PolylogSpectrum.lean`
  - L1088: `PF/SpectralGap.lean`
  - L1348: `PF/MillenniumSixReductions.lean`

### ch22_navier_stokes.tex
  - L340: `PF/MillenniumSixReductions.lean`
  - L437: `PF/MillenniumSixReductions.lean`
  - L449: `PF/MillenniumSixReductions.lean`

### ch23_yang_mills.tex
  - L322: `PF/GaussianModel.lean`
  - L401: `PF/MillenniumSixReductions.lean`
  - L405: `PF/MillenniumSixReductions.lean`
  - L634: `PF/MillenniumSixReductions.lean`

### ch24_birch_swinnerton_dyer.tex
  - L318: `PF/MillenniumSixReductions.lean`
  - L480: `PF/MillenniumSixReductions.lean`
  - L488: `PF/MillenniumSixReductions.lean`

### ch25_hodge_conjecture.tex
  - L457: `PF/MillenniumSixReductions.lean`
  - L457: `PF/Analytic/CleanLambdaClosedForms.lean`
  - L486: `PF/MillenniumSixReductions.lean`
  - L498: `PF/MillenniumSixReductions.lean`
  - L515: `PF/MillenniumSixReductions.lean`
  - L526: `PF/Consciousness/Ch2PhiBridge.lean`
  - L526: `PF/Consciousness/Ch12MassIITBridge.lean`
  - L532: `PF/MillenniumSixReductions.lean`

### ch26_cosmological_constant.tex
  - L297: `PF/Cosmology/LambdaEffCalibration.lean`
  - L297: `PF/Cosmology/E6ChernIndex78pi.lean`



## H. Methodology

- All 35 chapters read **read-only**; no `.tex` files were modified.
- Extractions performed with `grep`/`sed`/`awk` over the chapter directory.
- Lean existence checks performed with `grep -rE "\bNAME\b" PF_Lean4_Code --include="*.lean" -l`.
- Coq existence checks performed with `grep -rn NAME PF_Coq PF_Coq_Code`.
- `\texttt{...}` name extraction normalizes the LaTeX `\_` escape back to `_` before lookup.
- "Dangling ref" = the target string of a `\ref|\Cref|\cref|\eqref|\autoref|\Ref` invocation has no matching `\label{...}` declaration anywhere in `chapters/ch*.tex`. (Cross-volume `book/` content was not scanned; if a label lives outside `chapters/`, it would still appear here.)

---

Report generated 2026-05-25.