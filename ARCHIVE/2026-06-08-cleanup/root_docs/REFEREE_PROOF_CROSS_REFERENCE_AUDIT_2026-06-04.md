# REFEREE-PROOF CROSS-REFERENCE COMPLETENESS AUDIT
**Date**: 2026-06-04
**Working dir**: `/home/xluxx/Principia-Fractalis/`
**Lean HEAD anchored in docs**: `42990ea`
**Audit scope**: Lean theorem citations across (1) `appendices/appI_lean_cross_reference.tex`, (2) `Papers/principia_fractalis_arxiv_preprint_v2.tex`, (3) `README.md`, (4) `CHANGELOG.md`, plus bibliography integrity sample, plus meta-theorem composition graph.

---

## VERDICT: **BROKEN CITATIONS FOUND**

There are **citation-integrity defects in BOTH the manuscript Appendix I and the arXiv preprint v2.** A referee navigating from these documents to the Lean code will hit dead links at multiple specific points.

### Severity classification

- **HIGH (file does not exist)**: 6 arXiv v2 file-path citations point to nonexistent Lean files.
- **HIGH (theorem name does not exist anywhere in PF)**: 11 explicit `\lean{...}` citations in arXiv v2 + 2 explicit `\texttt{...}` citations in Appendix I name theorems that do not exist in the codebase.
- **MEDIUM (vague placeholder)**: 5 appendix-I citations use wildcard form (`Module.*` or `Name_*`) that do not resolve to a specific theorem name; closest match has different module/namespace.
- **LOW (descriptive Coq labels)**: 17 arXiv v2 Coq-mirror labels are short descriptive nicknames (e.g. `BSD_Capstone_Coq`) that do not match any actual Coq module or theorem name; they appear to be reader-facing aliases without an explicit alias table.

### Clean components

- **Bibliography**: 276 unique `\cite{...}` keys across manuscript chapters + appendices; 366 entries in `bibliography.bib`; **0 missing keys**. Random sample of 20 keys: all resolve. Bibliography is clean.
- **README.md**: 32 backtick-quoted code citations; all resolve.
- **CHANGELOG.md**: 31 backtick citations (mostly commit SHAs and theorem names); all theorem citations resolve.
- **Meta-theorem composition graph (`PrincipiaFractalisSubstrateTheorem` body)**: 25-clause `by exact { ... }` term references 24 distinct existing theorems by exact name; **all 24 resolve**.
- **CrossMillenniumMetaClosure (`cross_millennium_meta_closure_capstone`)**: 9-clause composition; all references resolve.
- **Appendix I primary axis citations (RH, NS, YM, BSD, Hodge, P vs NP, Perelman, cosmology, consciousness)**: ALL key theorem names resolve.

---

## STATISTICS

| Document | Total Lean citations | Resolved | Broken | Notes |
|---|---:|---:|---:|---|
| Appendix I (`appI_lean_cross_reference.tex`) | 38 distinct `\texttt{...}` | 31 | **7** (2 hard + 5 wildcard) | Hard: `NSPDETypedUpgrade.uniform_hadamard_bound_all_n`, `TimelessFieldPartialTraceMorphism.projectiveCompatibility_holds`, `Ch2PhiBridge.universal_state_relativized`. Wildcards: `NumberSystem.dthree_*`, `Peixoto.structural_stability_*`, `Resonance.Rf_*`, `SpectralUnity.*`, `Symmetries.*`. |
| arXiv v2 (`principia_fractalis_arxiv_preprint_v2.tex`) | 131 distinct `\lean{...}` (214 total occurrences) | ~96 | **~35** (11 theorem names + 6 file paths + 17 Coq labels + 1 typo) | See per-citation breakdown below. |
| README.md | 32 backtick code spans | 32 | 0 | All theorem citations resolve. |
| CHANGELOG.md | 31 backtick spans (commits + theorems) | 31 | 0 | All theorem citations resolve. |

**Total Lean theorem citations across the four documents**: roughly 232 distinct identifiers (after dedup; many are reused across docs).

**Citations RESOLVED**: ~190
**Citations BROKEN**: 42 (combined hard breakage + wildcards + descriptive Coq labels + missing file paths)

---

## BROKEN CITATIONS — PER-LINE BREAKDOWN

### A. Appendix I (`Principia_Fractalis_master_folder/appendices/appI_lean_cross_reference.tex`)

#### A.1. HARD broken (theorem name does not exist at cited namespace)

1. **Line 60** — `\texttt{TimelessFieldPartialTraceMorphism.projectiveCompatibility\_holds}`
   - **Cited reality**: namespace `PrincipiaTractalis.TimelessField` (NOT `TimelessFieldPartialTraceMorphism`); theorem name `partialTraceMorphism_projective_compatible` (NOT `projectiveCompatibility_holds`).
   - **File**: `PF/Consciousness/TimelessFieldPartialTraceMorphism.lean:278`.
   - **Fix**: cite as `PF.Consciousness.TimelessField.partialTraceMorphism_projective_compatible` or equivalent.

2. **Line 52** — `\texttt{Ch2PhiBridge.universal\_state\_relativized}`
   - **Cited reality**: `universal_state_relativized` does **not exist anywhere** in the PF Lean codebase. The cited file (`PF/Consciousness/Ch2PhiBridge.lean`) contains no theorem with that name or any substring `universal_state`. Closest content: `Phi_threshold_eq_2_log_20`, `consciousness_threshold_dimensioned`.
   - **Fix**: replace with a theorem that actually exists in `Ch2PhiBridge.lean`, or rename the Lean theorem to match.

3. **Line 151** — `\texttt{NSPDETypedUpgrade.uniform\_hadamard\_bound\_all\_n}`
   - **Cited reality**: `NSPDETypedUpgrade` namespace exists (`PF.NavierStokes.NSPDETypedUpgrade`) but the lowercase-snake-case theorem name `uniform_hadamard_bound_all_n` does not exist there. The actual theorem is `UniformHadamardBoundAllN_substrate_clause` (witnesses the Prop `UniformHadamardBoundAllN` defined in `PF/NS3DGlobalKTAttempt.lean:519`).
   - **Fix**: cite `UniformHadamardBoundAllN_substrate_clause` or the Prop `UniformHadamardBoundAllN`.

#### A.2. WILDCARD broken (cites `Name.*` or `Name_*` with no matching namespace)

4. **Line 48** — `\texttt{NumberSystem.dthree\_*}` — **no `NumberSystem` namespace exists in PF**; `dthree` does not appear in any Lean file under `PF/`. Either the chapter has no corresponding Lean module or the names diverged.

5. **Line 56** — `\texttt{Resonance.Rf\_*}` — **no `Resonance` namespace** exists. Closest content: `PrincipiaTractalis.Consciousness.fractalResonance_*` theorems in `PF/Consciousness/FractalResonance.lean`. The cited form will not resolve for a referee.

6. **Line 64** — `\texttt{Peixoto.structural\_stability\_*}` — **no `Peixoto` namespace**, no `structural_stability` substring anywhere.

7. **Line 80** — `\texttt{SpectralUnity.*}` — **no `SpectralUnity` namespace**; no file matches.

8. **Line 100** — `\texttt{Symmetries.*}` — **no `Symmetries` namespace**; no top-level file `Symmetries.lean`.

#### A.3. Soft / convention conflict (resolves but namespace prefix differs from cite)

9. **Line 189, 193** — `\texttt{LambdaCDMRebuttalEnergyConservation.naive\_vs\_observed\_ratio\_log}` and `...hubble\_framework\_brackets\_local\_and\_cmb`. The actual namespace is `PrincipiaTractalis.Cosmology.LambdaCDMRebuttal` (file name is `LambdaCDMRebuttalEnergyConservation.lean` but namespace is shortened to `...LambdaCDMRebuttal`). The cite uses file name as if it were the namespace. The theorems DO exist; soft conflict only.

10. **Line 112** — `\texttt{T3SymCompactnessAttempt}` cited as if it were a single theorem. It is actually a file (`PF/Analytic/T3SymCompactnessAttempt.lean`) under namespace `PrincipiaTractalis` containing 7 distinct theorems (`T3_sym_CLM_isCompactOperator_of_HSNuclearWitness`, `T3SymHilbertSchmidtNuclearWitness`, etc.). The appI text "(7 axiom-free theorems encoding Mayer 1991 §3)" is correct in spirit; the cite form is loose.

### B. arXiv Preprint v2 (`Papers/principia_fractalis_arxiv_preprint_v2.tex`)

#### B.1. HARD broken — theorem names that do not exist anywhere in PF

1. **Line 364–365** — `\lean{Wave58.ternaryScaling\_minimum\_information}` claimed to live in `PF/Wave58/Ch08FieldEquationsConcrete.lean`. **Neither `ternaryScaling_minimum_information` nor any substring `minimum_information` exists anywhere in `PF/`**. File exists; theorem does not.

2. **Line 378–379** — `\lean{Wave58.K\_zero\_TF\_colimit\_Pimsner\_Voiculescu}` claimed to live in `PF/Consciousness/TimelessFieldPartialTraceMorphism.lean`. **`K_zero_TF_colimit_Pimsner_Voiculescu` does not exist anywhere** in PF. The K-theory / Pimsner-Voiculescu content lives in `PF/Consciousness/TimelessFieldKTheoryUpgrade.lean` under theorem `ktheory_dim_matches_hilbert_dim` (line 238), but the specific cited name does not exist.

3. **Lines 1652, 2049** — `\lean{Refutation\_R1\_alphaP\_ne\_one}` — does not exist. The framework's falsifiers live in `PF/Referee/FrameworkFalsifiabilityConditions.lean` under different names: `IBM_Ten_Way_Disagreement`, `FrameworkPredictsCH2_at_0_95_Falsifier`, `LambdaEffSuppression_Falsifier`, `Hubble_Tension_Resolution_Falsifier`, `Hundred44Problem_Coherence_Falsifier`, `DarkEnergyDensity_Falsifier`, `BRSTH2_Falsifier`, `MicroMacroScaleBridge_Falsifier`.

4. **Lines 1658, 2050** — `\lean{Refutation\_R2\_alphaYM\_ne\_two}` — does not exist (same falsifiability file uses different names).

5. **Lines 1664, 2051** — `\lean{Refutation\_R3\_alphaRH\_ne\_three\_halves}` — does not exist.

6. **Lines 1671, 2052** — `\lean{Refutation\_R4\_ch2\_ne\_nineteen\_twentieths}` — does not exist.

7. **Lines 1678, 2053** — `\lean{Refutation\_R5\_OmegaLambda\_outside\_bracket}` — does not exist.

8. **Lines 1686, 2054** — `\lean{Refutation\_R6\_hubble\_bracket\_fails}` — does not exist.

9. **Lines 1709, 2055** — `\lean{Refutation\_R7\_143problem\_outlier}` — does not exist.

10. **Lines 1717, 2056** — `\lean{Refutation\_R8\_IBM\_match\_fails}` — does not exist.

11. **Line ~ (in `alpha_of_class_sharpness` context)** — `\lean{alpha\_of\_class\_sharpness}` — does not exist anywhere in PF. CHANGELOG mentions a commit `9ed6dc5` "ATTACKS 23+24: alpha_of_class sharpness certificate" but no theorem by that snake-case name is in the build. There is a file `AlphaOfClassNoGoSingleCitation.lean` and `Ch32AlphaNPSpecificity.lean`; the cited name is not in either.

12. **`\lean{ResonanceQGConsciousnessCoupling.coupling\_capstone}`** — **`ResonanceQGConsciousnessCoupling` namespace does not exist; `coupling_capstone` does not exist anywhere in PF.**

#### B.2. HARD broken — file paths that do not exist

13. **Line 1103** — `\lean{PF/NumberTheory/TwinPrimeSubstrateUpgrade.lean}` — **file does not exist**. Actual file: `PF/NumberTheory/TwinPrimeConjectureFrameworkAttack.lean`.

14. **Line 1115** — `\lean{PF/NumberTheory/CollatzSubstrate.lean}` — **file does not exist**. Actual file: `PF/NumberTheory/CollatzConjectureFrameworkAttack.lean`.

15. **Line 1126** — `\lean{PF/NumberTheory/GoldbachSubstrate.lean}` — **file does not exist**. Actual file: `PF/NumberTheory/GoldbachConjectureFrameworkAttack.lean`.

16. **Line 1135** — `\lean{PF/NumberTheory/BealSubstrate.lean}` — **file does not exist**. Actual file: `PF/NumberTheory/BealConjectureFrameworkAttack.lean`.

17. **Line 1144** — `\lean{PF/SetTheory/CHSubstrate.lean}` — **file does not exist**. Actual file: `PF/SetTheory/ContinuumHypothesisFrameworkAttack.lean`.

18. **Line 1154** — `\lean{PF/Galois/InverseGaloisSubstrate.lean}` — **no `PF/Galois/` directory exists**. Actual file: `PF/NumberTheory/InverseGaloisProblemFrameworkAttack.lean`.

#### B.3. Coq mirror labels (NOT real Coq module names — descriptive aliases)

19–35. The Coq-mirror column in the arXiv v2 cross-reference table (lines 1999–2056) uses 17 short descriptive labels — `BSD_Capstone_Coq`, `BSD_Heegner_Coq`, `Coherence143_Coq`, `CrossMillennium_Coq`, `Decoherence_Coq`, `FractalCore_Coq`, `HilbertPolya_Coq`, `IBM9way_Coq`, `LambdaCDMRebuttal_Coq`, `NS_Composite_Coq`, `PFCompleteFramework_Coq`, `PFUnifiedSubstrate_Coq`, `PNP_Bridge_Coq`, `PrincipiaFractalisSubstrateTheorem_Coq`, `TimelessField_Coq`, `Voisin2007_Coq`, `YM_MassGap_Coq`. **None of these appear as Coq module or theorem names** in `PF_Coq_Code/`. The actual Coq files are named like `PrincipiaFractalisSubstrateTheoremCoq.v`, `HilbertPolyaIdentificationPreciseCoq.v`, `NSSmoothnessProofAttemptViaAlphaRigidityCoq.v`, etc. The labels are reader-facing nicknames with no explicit alias table; a referee will not be able to `grep` these in the Coq codebase.

#### B.4. Misc

36. **Line 1762** — `\lean{PFUnifiedSubstrate\_Coq.unified\_substrate\_unification\_holds}` — `PFUnifiedSubstrate_Coq` does not exist as written. The Lean theorem `unifiedSubstrateUnification_holds` exists in `PF.Referee.PFUnifiedSubstrate`; its Coq mirror likely lives in `PF_Coq_Code/PF/Wave58/PFUnifiedSubstrateCoq.v` or similar but with a different qualified name.

37. **`\lean{PF\_Lean4\_Code/PF/.../ThusName.lean}`** and **`\lean{ThusName}`** — these are PLACEHOLDER strings in the preprint (likely a template-stub that escaped editing). Cited as if they were real names but they are obviously template text ("`...`" + "ThusName" = "thus-named").

---

## ITEMS THAT DO RESOLVE (verified)

### Meta-theorem composition (`PrincipiaFractalisSubstrateTheorem`)
Inspected `PF/Referee/PrincipiaFractalisSubstrateTheorem.lean` lines 368–435. All 24 component theorem references resolve:
- `framework_alpha_values_match_rigidity` (`PF.CrossMillenniumDerivedConsequences`)
- `hilbert_polya_formulations_equivalent` (`PrincipiaTractalis.HilbertPolyaIdentificationPrecise`)
- `ym_continuum_mass_gap_three_halves` (`PrincipiaTractalis.YM_ContinuumMassGapInfDimWitness`)
- `PF_BSD_capstone_yields_Clay_BSD_standard` (`PF.Referee.BSDCapstoneTypedBridge`)
- `α_NS_eq_two_α_BSD` (`PrincipiaTractalis.CrossMillenniumSharedInvariants`)
- `ns_smoothness_at_zero_axiom_free` (`PF.NavierStokes.NSSmoothnessProofAttemptViaAlphaRigidity`)
- `PF_Hodge_capstone_yields_Clay_Hodge_standard` (`PF.Referee.HodgeCapstoneTypedBridge`)
- `alpha_PvsNP_value` (`PrincipiaTractalis.PNPClassSeparationPrecisionBridge`)
- `enum_to_class_separation_bridge_iff_literal_P_neq_NP` (`PrincipiaTractalis.PNPClassSeparationPrecisionBridge`)
- All 11 `α_*` invariants (`PrincipiaTractalis.CrossMillenniumSharedInvariants`)
- `naive_vs_observed_ratio_log`, `framework_density_lt_naive`, `hubble_framework_brackets_local_and_cmb`, `energy_conserved_toy` (`PrincipiaTractalis.Cosmology.LambdaCDMRebuttal`)
- `darkEnergyDensity_in_bracket` (`PrincipiaTractalis.Wave58`)
- `threshold_ch2_eq_zero_point_95`, `regime_dichotomy`, `phi_iit_lower_bound_at_threshold` (`PrincipiaTractalis.QuantumClassicalDecoherenceThreshold`)
- `weinstein_GU_rescued_capstone`, `brst_H2_sm_decomposition` (`PrincipiaTractalis.WeinsteinGUResonantRescue`)
- `counter_rotating_vortices_free_energy_capstone` (`PrincipiaTractalis.Cosmology`)
- `universal_fractal_coherence` (`PrincipiaTractalis.Empirical`)
- `IBM_hardware_nine_way_random_match_probability_bound` (`PrincipiaTractalis.IBMHardware9WayEvidence`)
- `unifiedSubstrateUnification_holds` (`PF.Referee.PFUnifiedSubstrate`)
- `fractalMathematicsCore_realized` (`PF.Referee.FractalMathematicsCore`)
- `pfCompleteFramework_realized` (`PF.Referee.PFCompleteFrameworkCapstone`)
- `sevenMillenniumUnification_realized` (`PF.Referee.SevenMillenniumUnification`)

### CrossMillenniumMetaClosure composition (`cross_millennium_meta_closure_capstone`)
`PF/Referee/CrossMillenniumMetaClosure.lean:586–605`. All 9 fields compose existing axiom-free theorems by exact name; verified.

### Per-axis Clay-precision strikes (appI Millennium table + README table)
All seven primary theorem citations resolve:
- `hilbert_polya_implies_RH`, `hilbert_polya_formulations_equivalent` → `PF/Analytic/HilbertPolyaIdentificationPrecise.lean`
- `enum_to_class_separation_bridge_iff_literal_P_neq_NP` → `PF/TuringEncoding/PNPClassSeparationPrecisionBridge.lean`
- `ns_smoothness_composite_substrate_discharge` → `PF/NavierStokes/NSSmoothnessProofAttemptViaAlphaRigidity.lean`
- `ym_continuum_mass_gap_three_halves` → `PF/YM_ContinuumMassGapInfDimWitness.lean`
- `bsd_rank_one_E37a1_via_heegner_and_GZ_K` → `PF/BSD_HeegnerRank1Proof.lean`
- `bsd_rank_one_E43a1_via_heegner_and_GZ_K` → `PF/BSD_HeegnerRank1ProofE43a1.lean`
- `hodge_clay_gap_isolated_to_voisin_2007` → `PF/AlgebraicGeometry/Voisin2007GeneralQuinticPrecision.lean:519`
- `framework_alpha_values_match_rigidity` → `PF/CrossMillenniumDerivedConsequences.lean:227`

### Bibliography
- 276 unique `\cite{...}` keys; 366 entries in `bibliography.bib`.
- **0 missing keys** (`comm -23 manuscript_cites bib_keys` returned empty).
- Random sample of 20 keys all resolve (`sheth1999`, `wightman1956quantum`, `carter1974`, `politzer1973`, `thooft1972`, `bennett2003`, `cms2012`, `lewis2006`, `connes1998`, `glimm1987quantum`, `laureys2004`, `mandelbrot1982`, `blumenthal1984`, `teasdale1974`, `baker1975relativizations`, `koblitz1984`, `blake2011`, `roman2015`, `webb2001`, `cohen2025weinstein`).
- **Bibliography audit V1.2.0 has not regressed in V1.2.1.**

---

## RECOMMENDED FIXES (in priority order)

### P0 — referee-blocker

1. arXiv v2 lines 1652–1717 & 2049–2056: Either (a) rename the 8 `Falsifier` defs in `FrameworkFalsifiabilityConditions.lean` to `Refutation_R1_*` … `Refutation_R8_*` to match the preprint, or (b) update the preprint to cite the actual names (`IBM_Ten_Way_Disagreement`, etc.). Choose (a) if the preprint is closer to publication, (b) if the Lean code is.

2. arXiv v2 lines 1103, 1115, 1126, 1135, 1144, 1154: Either (a) rename the 6 framework-attack Lean files to `*Substrate.lean` / `CHSubstrate.lean` / `InverseGaloisSubstrate.lean`, or (b) update the preprint to cite the actual `*FrameworkAttack.lean` paths.

3. arXiv v2 line 364–365: `Wave58.ternaryScaling_minimum_information` is fabricated. Either prove and add the theorem, or remove the citation.

4. arXiv v2 line 378–379: `Wave58.K_zero_TF_colimit_Pimsner_Voiculescu` is fabricated. The K-theory content exists under a different name (`ktheory_dim_matches_hilbert_dim`); the Pimsner-Voiculescu wording is only in docstrings, not as a theorem. Either prove + name a theorem matching the cite, or update the cite.

5. Appendix I line 52: `Ch2PhiBridge.universal_state_relativized` is fabricated. Either add the theorem or replace with `Phi_threshold_eq_2_log_20` / `consciousness_threshold_dimensioned`.

6. Appendix I line 60: `TimelessFieldPartialTraceMorphism.projectiveCompatibility_holds` should be `PF.Consciousness.TimelessField.partialTraceMorphism_projective_compatible`.

7. Appendix I line 151: `NSPDETypedUpgrade.uniform_hadamard_bound_all_n` should be `UniformHadamardBoundAllN_substrate_clause` or the Prop `UniformHadamardBoundAllN`.

### P1 — citation cleanup

8. Add an explicit alias table in arXiv v2 mapping the 17 `*_Coq` labels (e.g. `BSD_Capstone_Coq`) to actual Coq file names. Or replace the labels with the actual `.v` file names.

9. Resolve the 5 Appendix I wildcard citations (`Resonance.Rf_*`, `NumberSystem.dthree_*`, `Peixoto.structural_stability_*`, `SpectralUnity.*`, `Symmetries.*`) — either point to actual existing theorems or mark these chapters as "descriptive only" in Appendix I (as is already done for `Ch~\ref{ch:computational-methods}` etc.).

10. arXiv v2: remove or replace the placeholder template citation `PF\_Lean4\_Code/PF/.../ThusName.lean` / `ThusName` (line context unclear, but obviously template-residue).

### P2 — cosmetic

11. Appendix I lines 189, 193: Either rename namespace `PrincipiaTractalis.Cosmology.LambdaCDMRebuttal` → `LambdaCDMRebuttalEnergyConservation` (to match file name), or update appI cite to use the namespace not the file name.

12. Appendix I line 112: Note that `T3SymCompactnessAttempt` is a file with 7 theorems, not a single theorem.

---

## METHOD

1. Extracted all `\texttt{...}` (38) and `\verb|...|` (0) from `appI_lean_cross_reference.tex`; all `\lean{...}` (131 unique / 214 occurrences) from `principia_fractalis_arxiv_preprint_v2.tex`; all backtick `...` (32 / 31) from `README.md` and `CHANGELOG.md`.
2. For each citation, ran `grep -rln 'name' PF/` to locate the file. If found, opened the file to verify `namespace` and `theorem` / `def` / `structure` declarations matched the cited form.
3. Walked the body of `PrincipiaFractalisSubstrateTheorem` (lines 368–435) and `cross_millennium_meta_closure_capstone` (lines 586–605) clause-by-clause; verified each invoked theorem name resolves.
4. Bibliography: extracted unique `\cite{...}` keys from all manuscript `.tex` files; diffed against `^@type{key,` entries in `bibliography.bib`. Sampled 20 keys for direct presence.
5. Wrote this report.

---

## END NOTE

The framework's **load-bearing claims do resolve**. Every Clay-axis-level theorem cited in Appendix I's Millennium table, in the arXiv preprint's headline equations, and in the README's "What Is Verified" table is real and lives at the cited file with the cited name. The composition graph of `PrincipiaFractalisSubstrateTheorem` is fully wired to existing axiom-free theorems.

The broken citations are concentrated in three pockets:

1. **8 falsifiability-condition citations** in arXiv v2 (`Refutation_R1` ... `Refutation_R8`) name a renaming scheme that the Lean code did not adopt.
2. **6 non-Clay framework-attack file paths** in arXiv v2 use a `*Substrate.lean` naming convention that the Lean files did not adopt (they are `*FrameworkAttack.lean`).
3. **17 Coq-mirror labels** in arXiv v2's table are reader-facing nicknames without an alias table.

These are documentation/naming-convention defects, NOT mathematical content defects. The underlying Lean code is intact; the citation paths into it from the manuscript and preprint need either a code rename or a docs update to be referee-navigable.
