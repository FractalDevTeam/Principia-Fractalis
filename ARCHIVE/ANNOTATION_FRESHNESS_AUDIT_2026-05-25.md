# Annotation Freshness Audit — 2026-05-25

Auditor pass scope: every `.tex` chapter under
`Principia_Fractalis_master_folder_rev2/chapters/` (35 chapters). Citations
classified against the current Lean state under
`PF_Lean4_Code/PF/` and Coq state under `PF_Coq/theories/`, plus the
`git log` history. Audit is READ-ONLY (no manuscript edits).

## Summary

- Total citations found across the six grep patterns: **~190**
  - commit-SHA citations (`commit \texttt{...}`): 23 hits, 8 unique SHAs
  - build-job-count citations (`6354 jobs` / `5750 jobs`): 6 hits
  - date-stamped status claims (`as of 2026-...`): 7 hits
  - Lean file-path citations (`\texttt{PF...\.lean}`): 76 hits, 28 unique paths
  - Lean theorem-name citations: ~110 unique theorem names
  - `#print axioms` invocations cited in prose: 6 hits (all in ch34, ch20, ch17)
- **FRESH: ~175**
- **STALE: 5** (build-job-count drift; documented as "current as of <date>" so
  factually accurate at time-of-stamp)
- **BROKEN: 4** (3 file-path BROKEN, 1 theorem-name BROKEN; all in ch07, ch09,
  ch11)
- **AMBIGUOUS: ~5** (mostly vague "axiom-free in Lean" cites without specific
  theorem name; deliberately not enumerated unless load-bearing)

All 8 cited commit SHAs (`4e0f6d2`, `6303c02`, `6834c1c`, `72c0137`, `9cc2a3d`,
`b41429f`, `f313ceb`, `f597ecc`) exist in `git log` and match the headline
they're cited for.

## Per-chapter findings

### Ch 03 — Resonance
- [FRESH] L231: cites `PF/TuringEncoding/AlphaEnum.lean` — file exists.
- [FRESH] L359: cites `cascade_attack_headline_refutation` in
  `PF/Analytic/PhiCorrectionPerAlpha.lean` — verified at line 279.

### Ch 07 — Constants
- [BROKEN] L203: cites
  `PF_Lean4_Code/PF/QuantumComputerMaxSpeedup.lean` — file does **not**
  exist at that path. Actual location is
  `PF_Lean4_Code/PF/Consciousness/QuantumComputerMaxSpeedup.lean`.

### Ch 09 — Spectral Unity
- [BROKEN] L26: cites theorem `spectral_gap_pos` in
  `PF_Lean4_Code/PF/SpectralGap.lean` — theorem is actually named
  `spectral_gap_positive`. (Compare ch21:21 and ch21:1231 which cite
  the correct name.)
- [BROKEN] L141: cites `PolylogEigenvalueConjecture` in
  `PF_Lean4_Code/PF/PolylogSpectrum.lean` — file at that path does
  **not** exist. The Prop is defined in
  `PF_Lean4_Code/PF/TuringEncoding/Operators.lean` line 250 (correctly
  cited at ch21:1261). There is a related file
  `PF/Analytic/PolylogSpectrum.lean`, but it does **not** house
  `PolylogEigenvalueConjecture`.
- [FRESH] L126: commit `72c0137`, def-not-axiom — verified.
- [FRESH] L211, L382, L379: theorem names `Ch3_Line328_LiteralClaim_at_sqrt_two_refuted`,
  `lambda_0_canonical_times_alpha_eq_pi_10`, file paths
  `PF/Consciousness/Ch2PhiBridge.lean`, `PF/Analytic/CleanLambdaClosedForms.lean`,
  `PF/Analytic/RfNumericalRefutation.lean` — all verified present.

### Ch 10 — Hydrodynamic
- [FRESH] L148, L308, L342: theorem `lambda_0_canonical_times_alpha_eq_pi_10`,
  files `MillenniumSixReductions.lean`, `Analytic/CleanLambdaClosedForms.lean`,
  theorem `navier_stokes_via_fractal_emergence` — all verified.

### Ch 11 — Geometric Unity
- [BROKEN] L423: cites
  `PF_Lean4_Code/PF/XENONExactMatch.lean` — file does **not** exist at
  that path. Actual location is
  `PF_Lean4_Code/PF/Consciousness/XENONExactMatch.lean`.
- [FRESH] L338: cites `PF/Cosmology/E6ChernIndex78pi.lean` — verified.

### Ch 16 — Spectral Foundations
- [FRESH] L441: discusses deletion of `nuclearity_essential` axiom — accurate;
  see `PF/BochnerMinlos.lean:195` historical note.

### Ch 17 — Operator Theory
- [FRESH] L416: 2026-05-25 status block citing
  `IsSelfAdjoint_C`, `IsPositive_C`, `IsUnbounded_C`,
  `IsTraceClassOnFiniteRegions_C`, `CommutatorVanishesAtRiemannZeros`
  in `PF/Consciousness/ConsciousnessOperatorC.lean`, commit `6303c02`,
  plus `CommutatorVanishesAtRHZeros`,
  `ConsciousnessStationaryStateCompleteness`,
  `riemann_hypothesis_via_consciousness_bridge` in
  `PF/Consciousness/ConsciousnessRHBridge.lean` — every name verified;
  every file present; commit exists.

### Ch 20 — Riemann Hypothesis
- [FRESH] L241, L266: `T3NormSquaredBound_proved` in
  `PF/Analytic/T3NormSquaredBoundDischarge.lean`, commit `6834c1c` —
  verified (single theorem at the cited file).
- [FRESH] L270: `T3_self_adjoint_conj` in `PF/TransferOperator.lean`,
  commit `1b0deb7`, `b41429f` — verified; both commits exist.
- [STALE-marked-historical] L266: "Build state: **6354 jobs clean**" —
  the citation is qualified as "current as of 2026-05-22"; current jobs
  count not re-measured here. Acceptable per the audit rules
  (LOW-priority numeric drift).
- [BROKEN] L288: cites theorem `manuscript_target_unreachable_via_M0_sheet`
  in `PF_Lean4_Code/PF/Analytic/PolylogSpectrum.lean` — theorem exists
  (file is `PF/Analytic/PolylogSpectrum.lean`); however the same
  theorem name is cited at ch21:664 with the same correct subdirectory.
  Treat ch20:288 as **FRESH** (path is `PF/Analytic/PolylogSpectrum.lean`,
  which does exist — distinct from the BROKEN `PF/PolylogSpectrum.lean`
  cite in ch09:141).
- [FRESH] L451: `PF/Consciousness/Ch2PhiBridge.lean` — verified.

### Ch 21 — P vs NP
- [FRESH] L17, L21, L1217, L1224, L1236, L1242, L1251, L1258, L1261, L1263, L1265:
  All commit citations `72c0137`, `f313ceb` verified. All theorem names
  (`P_NEQ_NP`, `lambda_0_P_precise`, `lambda_0_NP_precise`,
  `alpha_class_separation_lt`, `spectral_gap_positive`, `PolylogEigenvalueConjecture`,
  `MonodromyGluingLemma_proven`, `principia_fractalis_millennium_capstone`,
  `alpha_at_ClassP_eq_sqrt2`, `alpha_at_ClassNP_eq_phi_plus_quarter`,
  `alpha_class_distinct`, `alpha_of_class_pos_at_ClassP`,
  `p_eq_np_spectrum_collapse`, `P_neq_NP_from_spectral_gap`,
  `jonquieresIdentityPointGermAtHalf_zero_proved`,
  `manuscript_target_unreachable_via_M0_sheet`,
  `manuscript_sine_ratio_bracket`,
  `manuscript_sqrt5_minus_one_div_three_bracket`,
  `manuscript_sine_identity_both_sides_wrong`,
  `manuscript_spectral_gap_analysis_triple_error`,
  `manuscript_gap_golden_bracket`, `manuscript_lambda_NP_golden_bracket`,
  `lambda_NP_alt_closed`) — verified present.
- [FRESH] L488: file `PF/Analytic/BCleanPhaseIdentity.lean` — verified
  (commit `7bba1c7`, May 24).
- [STALE-marked-historical] L17, L1251: "Build state: **6354 jobs clean**"
  and "up from 5750 jobs on May 20" — historical numbers, framed as
  "current as of 2026-05-22"; not re-measured this pass.

### Ch 22 — Navier–Stokes
- [FRESH] L437: `MillenniumSixReductions.lean`,
  `navier_stokes_via_fractal_emergence`, commit `72c0137` — verified.
- [FRESH] L445: Coq references `PF_NS_Spectral_Condition`,
  `Spectral_to_NS` — verified as Coq axioms in
  `PF_Coq/theories/Contracts/NavierStokes.glob` and registered in
  `PF_Coq/theories/Core/AxiomAudit.v`.

### Ch 23 — Yang–Mills
- [FRESH] L328: `gauge_field_space_nuclear` — disclosed as deleted in
  `BochnerMinlos.lean:199` historical note. Matches manuscript wording.
- [FRESH] L330: `minlos_sigma_additivity` — disclosed as deleted in
  `BochnerMinlos.lean:33` historical note. Matches manuscript wording.
- [FRESH] L333: `bochner_minlos_existence`/`bochner_minlos_uniqueness`
  retired 2026-05-14, commit `4e0f6d2` — commit exists, headline matches.
- [FRESH] L336: commit `72c0137`, theorem `yang_mills_via_fractal_resonance` —
  verified.
- [FRESH] L401: `fractalYMLevel1SpectrumGap_holds`,
  `fractalYMLevel1_gap_pos` in `MillenniumSixReductions.lean`,
  commit `9cc2a3d` — verified.
- [FRESH] L405: `yang_mills_via_level1_resonance_gap`,
  `fractalYMLevel1LiftsToContinuum`, commit `9cc2a3d` — verified.

### Ch 24 — Birch–Swinnerton-Dyer
- [FRESH] L480: `bsd_via_fractal_resonance` in
  `PF/MillenniumSixReductions.lean`, commit `72c0137`,
  `bsd_distinguished_eigenvalue_bracket` — all verified.
- [FRESH] L484, L490: Coq axioms `rank_equals_multiplicity`,
  `BSD_implies_L_function_formula`, `BSD_equality_holds` (defined
  `:= True`) — verified in `PF_Coq/theories/Contracts/BSD.v`.

### Ch 25 — Hodge
- [FRESH] L457: `hodge_via_fractal_resonance`,
  `PF/Analytic/CleanLambdaClosedForms.lean` — verified.
- [FRESH] L486: `hodge_via_fractal_resonance`, `ch_2_Hodge_bracket`,
  commit `72c0137` — verified.
- [FRESH] L494: Coq axioms `PF_Hodge_Spectral_Condition`,
  `Spectral_to_Hodge` — verified in `PF_Coq` axiom audit.
- [FRESH] L498: `hodge_phi_unconditional_anchors` in
  `PF/MillenniumSixReductions.lean`, commit `f597ecc`, "around line ~894"
  — theorem verified (line offsets in such files may drift but the
  symbol is found).
- [FRESH] L526: `PF/Consciousness/Ch2PhiBridge.lean`,
  `PF/Consciousness/Ch12MassIITBridge.lean` — both verified present.

### Ch 26 — Cosmological Constant
- [FRESH] L297-L305: `PF/Cosmology/LambdaEffCalibration.lean`,
  `PF/Cosmology/E6ChernIndex78pi.lean`, theorems
  `cosmological_constant_calibration_discharged`, `N_78pi_bracket`,
  `Lambda_eff_parameter_free_via_78pi`,
  `Lambda_eff_required_exponent_pos`,
  `dim_E6_via_trinification_arithmetic`, `seventyEight_decomp`,
  `twentySeven_eq_3pow3` — all verified. Manuscript correctly downgraded
  per commit `6a0ce86` per memory note `principia_ch26_overclaim_verification_2026-05-25`.

### Ch 34 — Verification
- [FRESH] L80: "Last axiom retired & 2026-05-20 (commit `72c0137`)" — verified.
- [FRESH] L81: historic closures `6834c1c`, `f313ceb` — verified.
- [STALE-marked-current] L78: "Build jobs **6354 (clean)**" — printed in
  a status table without an "as of" stamp on the row itself, but the
  surrounding section is dated. LOW priority.
- [FRESH] L95-L106, L179-L207: file-path bullets for
  `MonodromyTheorem.lean`, `BernoulliGrowthBound.lean`,
  `PolyLogLocalPatches.lean`, `HankelFubini.lean`,
  `T3NormSquaredBoundDischarge.lean`,
  `BernoulliFnHasSumOnSomeBallDischarge.lean` — every file verified.
- [FRESH] L132-L149: `#print axioms` verbatim block for `P_NEQ_NP`,
  `principia_fractalis_millennium_capstone`,
  `riemann_hypothesis_via_T3_sym_framework`,
  `MonodromyGluingLemma_proven` — all four symbols verified present.
  The literal `[propext, Classical.choice, Quot.sound]` claim is
  consistent with memory's authoritative `principia_zero_axioms_2026-05-20`
  note; AMBIGUOUS without re-running `lake env lean -e ...` in this
  audit, but no contradictory evidence found.

### Ch 01, 02, 04-06, 08, 12-15, 18, 19, 27-33, 35
- No commit-SHA, no build-job-count, no specific theorem-name, and no
  specific Lean file-path citations found in this audit pass. These
  chapters use either generic "axiom-free in Lean" phrasing or no
  Lean cross-references at all. Marked **out-of-scope** for this
  freshness audit (would require a broader prose audit).

## Recommended fix queue

Ordered by impact: BROKEN file-path / theorem-name cites first
(reader cannot follow them), then numeric drift.

1. **Ch 09 L141** — change
   `PF_Lean4_Code/PF/PolylogSpectrum.lean` → 
   `PF_Lean4_Code/PF/TuringEncoding/Operators.lean`
   for the `PolylogEigenvalueConjecture` citation. ch21:1261 already
   has the correct path; copy that. **HIGH** (ch09 is a load-bearing
   cross-chapter spectral-unity claim).

2. **Ch 09 L26** — change theorem name `spectral_gap_pos` → 
   `spectral_gap_positive` (file path `PF/SpectralGap.lean` is correct).
   ch21:21 and ch21:1231 already use the correct name. **HIGH** (same
   load-bearing claim).

3. **Ch 07 L203** — change `PF_Lean4_Code/PF/QuantumComputerMaxSpeedup.lean`
   → `PF_Lean4_Code/PF/Consciousness/QuantumComputerMaxSpeedup.lean`.
   **MEDIUM** (chapter-internal numerical correction note; reader
   needs to find the file to verify).

4. **Ch 11 L423** — change `PF_Lean4_Code/PF/XENONExactMatch.lean` →
   `PF_Lean4_Code/PF/Consciousness/XENONExactMatch.lean`. **LOW**
   (numerical-coincidence disclaimer; chapter explicitly disclaims
   derivation).

5. **Ch 34 L78** (and the various "6354 jobs clean" cites in ch20:266,
   ch21:17, ch21:1251) — consider either (a) re-measuring the build
   and updating, or (b) rephrasing as "as of 2026-05-22, **6354** jobs"
   and adding a freshness note for the latest 2026-05-25 work
   (ConsciousnessOperatorC, ConsciousnessRHBridge,
   H3UnifiedMillenniumStructure landed since). **LOW** — these
   citations are honestly date-stamped.

## Notes on what was NOT audited

- Generic "axiom-free in Lean" sentences without specific theorem
  names (e.g., ch09:105 "...is machine-checked axiom-free in
  `PF_Lean4_Code/PF/AlphaBasisGenerators.lean` and
  `PF_Lean4_Code/PF/TuringEncoding/Operators.lean`...") are
  AMBIGUOUS by design and not enumerated here.
- Chapters 01-06, 08, 12-15, 18, 19, 27-33, 35 may contain
  cross-references in plain prose (not matching the six grep
  patterns) that this pass did not catch.
- Build-job counts (5750, 6354) were not re-measured in this pass
  (audit is read-only and re-running `lake build` is out-of-scope).
- `#print axioms` outputs (ch34:132-149) were not re-executed in this
  pass; classified AMBIGUOUS-leaning-FRESH given memory's authoritative
  zero-axioms note.

## Provenance

Audit performed against:
- Repository HEAD: `96fa9cb` ("Manuscript close-the-loop sweep
  (2026-05-25): Ch 17, 20, 22, 24, 25")
- 259 `.lean` files under `PF_Lean4_Code/PF/`
- 6 `.v` axiom-contract files under `PF_Coq/theories/Contracts/`
- 35 `.tex` chapters under
  `Principia_Fractalis_master_folder_rev2/chapters/`
