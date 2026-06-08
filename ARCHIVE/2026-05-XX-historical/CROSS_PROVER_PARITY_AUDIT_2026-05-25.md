# Cross-Prover Parity Audit — 2026-05-25

Scope: snapshot of Lean 4 ↔ Coq parity for the Principia Fractalis
formalization, as of 2026-05-25. Companion document to
`PARITY_REPORT.md` (historical through 2026-05-08) and
`CROSS_PROVER_PARITY.md` (last updated 2026-05-22). Lean4Lean is
quarantined to `experimental/PF_L4L_future/` and is out of scope here.

## Inventory

| System | Path | Files | Axioms / Parameters | Build |
|---|---|---|---|---|
| Lean 4 (canonical) | `PF_Lean4_Code/PF/` | **258** `.lean` | **0** `axiom` declarations | **BROKEN** (9 errors, 2 modules fail) |
| Coq (canonical) | `PF_Coq_Code/PF/` | **34** `.v` (30 enumerated in `_CoqProject`) | **98** `Axiom`/`Parameter` (all documented as `_GAP` Parameters or as the `PolylogEigenvalueConjecture` Prop) | **CLEAN** (`make` succeeds, no warnings) |
| Coq (legacy / vintage) | `PF_Coq/theories/` | 32 `.v` | 258 `Axiom`/`Parameter` | Not in current build pipeline (historical) |
| Lean4Lean | `experimental/PF_L4L_future/` | 7872 `.lean` (mostly mathlib) | — | Quarantined, not part of claim |

Notes:
- The single `^axiom ` match in Lean is the literal word "axiom retirement" inside a comment in `PF/Analytic/GammaHankel.lean:155` — **not** a declaration. Lean is genuinely 0 project axioms.
- 98 Coq Axioms/Parameters in `PF_Coq_Code/` are predominantly named `*_GAP` Parameter stubs for the Coq-8.18-no-Coquelicot Complex/`→L[ℂ]`/Hilbert stack, plus the load-bearing `PolylogEigenvalueConjecture` Prop hypothesis. None are project-level mathematical axioms.

## Build state

### Lean 4 — BROKEN (regression vs. memory's "7086 jobs clean" of 2026-05-24)

`lake build` exits with code 1. Two modules fail:

1. **`PF/Consciousness/Ch12QFTLagrangian.lean`** (2026-05-25 import, top-level `PF.lean:213`)
   - `pow_lt_pow_left` unknown identifier (lines 269, 278)
   - `Function.mpr` unknown field (line 280)
   - Likely cause: mathlib API rename; needs `pow_lt_pow_left₀` or fully qualified path.
2. **`PF/Operators/VAlphaPMapDischarge.lean`** (2026-05-25 Wave 11, top-level `PF.lean:227`)
   - Unsolved goals at lines 144, 153, 180, 190, 195, 328
   - `Tactic introN failed` at 304, 307, 320
   - Capstones `H_alpha_ground_state_eq_pi_10_alpha_PMap_unconditional` and `H_alpha_spectral_gap_positive_PMap_unconditional` Lean-auto-fills with `sorryAx` (visible in `#print axioms` output)
   - File header docstring still claims "ZERO project axioms, ZERO sorries" — currently false.

Other 7186+ jobs build fine. No transitive damage to the historical capstones (`P_NEQ_NP`, `principia_fractalis_millennium_capstone`, `riemann_hypothesis_via_T3_sym_framework`, `MonodromyGluingLemma_proven`); those still print `[propext, Classical.choice, Quot.sound]` only. The breakage is contained to the two new 2026-05-25 modules.

### Coq — CLEAN

`make clean && make` rebuilds all 30 modules under Coq 8.18.0, no warnings, no errors. Matches the state recorded in `CROSS_PROVER_PARITY.md` (2026-05-22 cycle).

### Lean4Lean — N/A

`experimental/PF_L4L_future/` is the quarantined L4L tree. Not part of the current verification claim. Has `L4L_ARCHITECTURAL_DECISION.md` documenting Path B (preserve verification-only intent, full source rewrite is future work).

## Parity for 10 load-bearing theorems

| # | Lean theorem | File | Coq counterpart | Status |
|---|---|---|---|---|
| 1 | `P_NEQ_NP` (hypothesis-threaded) | `PF/P_NP_Complete_Proof.lean:340` | `P_neq_NP_from_spectral_gap` in `PF/TuringEncoding/Operators.v:311` | **MATCHED** (both consume `PolylogEigenvalueConjecture`) |
| 2 | `principia_fractalis_millennium_capstone` | `PF/Millennium.lean` (referenced) | none | **MISSING** in Coq (Coq has piecemeal mirrors but no top-level bundle) |
| 3 | `riemann_hypothesis_via_T3_sym_framework[_fully_discharged]` | `PF/SpectralBijection.lean` | none | **MISSING** in Coq (CROSS_PROVER_PARITY.md 2026-05-22 explicitly documents this as out of reach until Coquelicot 3.4.x + Hilbert stack) |
| 4 | `MonodromyGluingLemma_proven` | `PF/Analytic/MonodromyTheorem.lean` | none | **MISSING** in Coq |
| 5 | `six_millennium_problems_via_fractal_resonance` | `PF/MillenniumSixReductions.lean` | `six_millennium_problems_via_fractal_resonance` in `PF/MillenniumSixReductions.v:351` | **MATCHED** (both prove the 6-Millennium conditional reduction at canonical α-values) |
| 6 | `empirical_validation_capstone` | `PF/Empirical/HundredFortyThreeProblems.lean` | `empirical_validation_capstone` in `PF/Empirical/HundredFortyThreeProblems.v:340` | **MATCHED** (143 problem count + 5σ coherence bound) |
| 7 | `consciousness_quantification_capstone` | `PF/Consciousness/ChernCharacter.lean` | `consciousness_quantification_capstone` in `PF/Consciousness/ChernCharacter.v:319` | **MATCHED** (8-class crystallization threshold theorem) |
| 8 | `millennium_consciousness_unification` | `PF/Consciousness/MillenniumConnection.lean` | `millennium_consciousness_unification` in `PF/Consciousness/MillenniumConnection.v:219` | **MATCHED** (5-conjunction capstone, axiom-free both sides) |
| 9 | `riemann_hypothesis_via_consciousness_bridge` | `PF/Consciousness/ConsciousnessRHBridge.lean:164` (2026-05-25, commit 6303c02 per memory) | none | **MISSING** in Coq (new file, Coq parity not landed) |
| 10 | `H3_unified_algebraic_Millennium_structure` | `PF/H3UnifiedMillenniumStructure.lean:252` (2026-05-24) | none | **MISSING** in Coq |

**MATCHED**: 5/10. **MISSING**: 5/10.

## Drift since `CROSS_PROVER_PARITY.md` (2026-05-22)

- Lean files modified/added since 2026-05-22: **105**
- Coq files modified/added since 2026-05-22: **5** (`QuantumGravity.v`, `GeneralRelativity.v`, `Consciousness/Ch12MassIITBridge.v`, `Analytic/SpectralResonanceBridge.v`, `Analytic/FractalKernelSelfSimilarity.v`)
- Consciousness directory comparison: **22 Lean files vs 5 Coq files** (17-file gap in this directory alone — includes Wave 8/9/10 content: `ConsciousnessOperatorC`, `ConsciousnessRHBridge`, `Ch12QFTLagrangian`, `Ch2PhiBridge`, `Ch32AlphaNPSpecificity`, `ClinicalCh2Calibration`, `Mechanism3HermitianSweetSpot`, `MuonG2Prediction`, `NeutrinoHierarchyRatio`, `PhaseFactorAlgebra`, `PhaseFactorFirstOrder`, `PhiCorrectionAtOne`, `QuantumComputerMaxSpeedup`, `RfAtAlphaOneIsNegEta`, `RfAtAlphaTwoIsZeta`, `WBosonMassAnomaly`, `XENONExactMatch`)
- The CROSS_PROVER_PARITY.md 2026-05-22 entry explicitly acknowledges that "Lean is now substantially ahead on the RH Phase-A analytic content" and that the new analytic discharges *cannot* be mechanically ported without Coquelicot 3.4.x. The gap has widened by an additional ~100 Lean files since that document was written; the broad pattern (Lean leads, Coq holds a smaller axiom-free core, gaps documented honestly) persists.

## Recommended next-session priorities

1. **Fix the Lean build regression FIRST.** Both broken modules are 2026-05-25 work. `Ch12QFTLagrangian.lean` needs `pow_lt_pow_left` → `pow_lt_pow_left₀` (or analogous mathlib rename) and an `mpr` syntax fix. `VAlphaPMapDischarge.lean` has 6 unsolved goals + 3 `introN` failures that auto-degraded to `sorryAx`. **Until this is fixed, the "0 axioms, no sorry" headline claim is false** and any `#print axioms` on `H_alpha_*_PMap_unconditional` will leak `sorryAx`. The docstrings of both files currently misstate the discharge status.
2. **Update the docstrings and any memory entries** that describe these capstones as discharged; they currently overclaim.
3. **Re-run `lake env lean --run scripts/print_axioms.lean`** (or equivalent) after the fix to confirm only `[propext, Classical.choice, Quot.sound]` survives on all advertised capstones.
4. **Refresh `CROSS_PROVER_PARITY.md`** with a 2026-05-25 cycle entry: the 105-file Lean drift, the Coq-side 5-file delta, the broken build state, and the new gap items (consciousness ↔ RH bridge, H₃ unified Millennium structure, IBM Galois pair, B-clean phase identity, Ch 12 QFT Lagrangian). The document is structurally accurate but ledger numbers and the per-cycle table are 3 days stale.
5. **Defer broad Coq parity catch-up.** The Coq-8.18 + no-Coquelicot constraint genuinely blocks the new Hilbert/operator content. Either (a) commit to adding Coquelicot 3.4.x as a project dependency, or (b) accept the documented gap and stop generating new Lean content that cannot be mirrored until (a) is decided. The current pace is making the gap unmanageable.
6. **Stop labeling new Lean files "ZERO axioms, ZERO sorries" in their docstrings before the file builds clean.** Wave 11's `VAlphaPMapDischarge.lean` is the second instance this session of an aspirational header that survived an actually-broken file (cf. May 2026 `bochner_minlos_existence` orphan-consumer cleanup). Build-then-claim, not claim-then-build.

## Notes on classification

- "MATCHED" used only where both provers carry the same load-bearing theorem with the same antecedent structure. I verified theorem names + file locations + (in 4 of 5 matched cases) by reading the parity-report tables that itemize the same theorems.
- "MISSING" means the Coq tree does not carry the theorem under any obvious alias. None of the MISSING items have a Coquelicot-3.4.x-blocked Parameter stub; they are simply not ported.
- Coq theorems built against `Print Assumptions` of `[ClassicalDedekindReals.sig_*, FunctionalExtensionality.functional_extensionality_dep, Classical_Prop.classic]` are treated as the Coq-stdlib equivalent of Lean's `[propext, Classical.choice, Quot.sound]` and counted as 0 project axioms in both columns.
