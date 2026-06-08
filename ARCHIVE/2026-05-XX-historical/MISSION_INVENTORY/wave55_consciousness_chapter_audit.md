# Wave 55 — Consciousness Chapter Audit (Ch 30 / 31 / 32)

**Date**: 2026-05-31
**Scope**: chapters `ch30_clinical_consciousness.tex` (891 lines), `ch31_neuroscience_iit.tex` (779 lines), `ch32_consciousness_quantification.tex` (838 lines). Cross-referenced against `/home/xluxx/Principia-Fractalis/PF_Lean4_Code/PF/Consciousness/` (33 Lean files) plus `PF/Ch2PhiBridge.lean`, `PF/ClinicalCh2Calibration.lean`, `PF/Ch12MassIITBridge.lean`, `PF/Ch32AlphaNPSpecificity.lean` (all four actually live under `PF/Consciousness/`, no top-level `PF/Ch*` files exist — confirmed via `find`).
**Posture**: Honest. Wins, conditional reductions, and gaps all flagged.

---

## §1 — Manuscript Propositions per chapter (exact statements + line numbers)

### Ch 30 — Clinical Applications

| Tag | Manuscript object | Statement | Lines |
|---|---|---|---|
| `def:clinical-ch2` | Clinical ch₂ definition | `ch₂^clinical = (1/T) ∫₀^T |(1/(M·5)) Σ_b Σ_j exp(iπ·α·D(n_{b,j}(t)))·φ_{b,j}(t)|² dt`, with `α = √2`, 5 EEG bands (δ, θ, α, β, γ), M electrodes, base-3 digital sum `D` of integer-discretised band power | 194–206 |
| `thm:consciousness-threshold` | Crystallization threshold | "A patient is classified as conscious iff `ch₂^clinical ≥ 0.95`. Threshold derived from first principles (Ch 6) and validated empirically across 847 patients." | 208–215 |
| `thm:validation-cohort` | Validation cohort | Retrospective 847 patients, 7 centres, 2015–2024. Coma 143, VS/UWS 267, MCS- 189, MCS+ 156, EMCS 92. Gold standard: expert CRS-R + 6-mo follow-up. Fractal pipeline blinded. | 221–236 |
| `thm:diagnostic-accuracy` | Accuracy = 97.3% (824/847). Sensitivity 96.8%, specificity 97.8%, PPV 97.4%, NPV 97.2% | 240–253 |
| `thm:accuracy-by-diagnosis` | Per-group ch₂ means: Coma 0.23±0.11, VS/UWS 0.47±0.18, MCS- 0.87±0.09, MCS+ 0.96±0.05, EMCS 0.98±0.03 | 345–360 |
| `thm:prognostic` | Recovery-rate dose-response: ch₂<0.50 → 6.3%, 0.50–0.80 → 30.1%, 0.80–0.95 → 74.5%, ≥0.95 → 100%. Logistic β₁=8.73, AUC=0.89 | 462–485 |
| `prop:trajectory` | Recovery exponential `ch₂(t) = ch₂^∞ − (ch₂^∞ − ch₂⁰)·exp(−t/τ)`, τ median 47 d | 520–533 |
| `thm:vs-crsr` | Spearman ρ(ch₂, CRS-R) = 0.87 across n=847 | 548–569 |
| `thm:band-coherence` | Band weights δ/θ/α/β/γ = 0.08/0.12/0.18/0.27/0.35 | 643–666 |

### Ch 31 — Neuroscience / IIT bridge

| Tag | Manuscript object | Statement | Lines |
|---|---|---|---|
| `thm:iit-resonance` | **ch₂ ↔ Φ closed form** | `Φ(Ψ) = −log₂(1 − ch₂(Ψ)) + 𝒪(ch₂²)`. At ch₂=0.95: `Φ ≳ −log₂(0.05) ≈ 4.32 bits` | 64–76, recap 122–146 |
| `thm:thalamocortical` | Thalamocortical necessity | `ch₂^clinical = 0.73·TC_conn + 0.14·CC_conn + ε`; TC explains 73% of variance | 152–171 |
| `thm:resonance-frequency` | Critical f | `f_crit = α·f_base = √2·10 Hz ≈ 14.1 Hz` (beta band) | 249–264 |
| `prop:nmda` | NMDA-mediated integration: ch₂(ketamine) = 0.67 ± 0.12 vs control 0.96 ± 0.04 | 287–306 |
| `thm:white-matter` | `ch₂ = 0.42 + 0.61·FA_thalamic + 0.18·FA_callosal` (DTI, n=189) | 310–333 |
| `thm:unified` | IIT ⊕ GWT unification: ch₂≥0.95 = necessary condition, broadcast at √2·10 Hz = sufficient condition | 377–409 |
| `thm:optogenetics` | Mouse ChR2: 14 Hz drive yields ch₂ = 0.96 ± 0.06 with consistent behaviour; 5/10/40 Hz fail | 438–460 |
| `thm:anesthesia` | Per-agent ch₂ at LOC: propofol 0.67, ketamine 0.71, sevoflurane 0.54, xenon 0.74, dexmedetomidine 0.88 | 464–491 |
| `thm:artificial-consciousness` | RNN ch₂: feedforward 0.31, deep recurrent 0.97 | 527–561 |
| `prop:llm` | LLM ch₂ < 0.95 — arguments rather than measured numbers; Remark `rem:llm-ch2-methodology` (lines 602–604) **explicitly retracts** the earlier numerical estimates (GPT-4 ≈ 0.42, etc.) as lacking a documented measurement protocol | 585–600 |

### Ch 32 — Measurement protocols / normative data

| Tag | Manuscript object | Statement | Lines |
|---|---|---|---|
| `alg:ch2` | Operational pipeline: power → `digitize_power` (scale to [0,999]) → `digital_sum_base3` → `phase_factors = exp(iπ·α·D)` with `α = √2` → weighted mean across 5 bands → `ch₂ = |total|²` | 265–323 |
| `thm:normative` | Healthy adults n=1,247: mean ch₂ = 0.973 ± 0.018, range [0.923, 0.998] | 391–423 |
| `thm:states` | **Sleep-state ordering** (n=143): alert 0.981, eyes-closed 0.973, N1 0.891, N2 0.672, N3 0.387, REM 0.947, meditation 0.989 | 427–452 |
| `thm:species` | Cross-species means (humans 0.973 → honeybees 0.312) | 456–486 |
| `thm:minimal-channels` | 8-channel headset (Fp1, Fp2, C3, C4, P3, P4, O1, O2): 94.7% accuracy vs 97.3% with 64 ch | 492–513 |

### Identities pulled from the prompt — exact loci

1. **`ch₂ ≤ 1 − exp(−Φ_IIT/2)`** — Ch 31 lines 64–76 (eq form `Φ = −log₂(1−ch₂)` is the rearrangement). The bridge with `exp(−Φ/2)` rather than `2^(−Φ)` appears in Lean (`Ch2PhiBridge.lean` lines 87–141, natural-log convention).
2. **ch₂ = 0.95 crystallization threshold** — Ch 30 line 211; Ch 31 line 75; threshold derivation owned by Ch 6 (Chern-Weil ch₂ second Chern class).
3. **`m_C/M_Planck = 1/(2√5) = exp(−Φ/4)`** — manuscript Ch 12 line 112 (`m_C ~ sqrt(1 − ch₂*)·M_Planck`); identity is Lean-proven (`Ch12MassIITBridge.lean::mass_ratio_eq_inv_two_sqrt_five`, line 104; `phi_threshold_quarter_eq_log_two_sqrt_five`, line 137).
4. **Ch 32 sleep-state Spearman ρ=1.000 at α=φ+¼** — Ch 32 Theorem `thm:states` (lines 427–452) is the ordering; the ρ=1.000 result is in the wave-14 reproduction agent and formalised in `Ch32AlphaNPSpecificity.lean::rho_at_alpha_NP` (line 73, value 1.000) with all three other framework α-values strictly negative (lines 75–82). The Lean theorem `alpha_NP_Ch32_specificity_capstone` (lines 183–197) bundles the ρ-pattern with the α-distinctness facts.

---

## §2 — Lean cross-reference (exact theorem names, axiom posture, named-Prop dependencies)

Lean files under `PF/Consciousness/` (33 total). Axiom posture verified by directory-wide grep: every file's header asserts `#print axioms ⇒ {propext, Classical.choice, Quot.sound}`. No project-level axioms are introduced anywhere in the consciousness substrate. `grep "sorry"` returns only header docstrings/comments — no `sorry`-bearing proofs.

### Ch 30 (clinical) → Lean: `Consciousness/ClinicalCh2Calibration.lean`
- `alpha_clinical_optimal := (1+√5)/2 + 1/4` (line 80), **NP-class** not the manuscript's α=√2.
- `base_clinical_optimal := 2` (line 84) — manuscript Ch 30 §"Digital Sum Encoding" specifies base 3 (line 174); Lean records the corrected base 2.
- `clinical_threshold := 0.95` (line 93) — unchanged from manuscript.
- `alpha_clinical_optimal_bracket : 1.86 < α_clinical_optimal < 1.87` (line 132).
- `alpha_NP_cross_domain_consistency_witness` (line 159) — cross-domain witness Prop.
- **Axiom-free, but the 100% binary / Cohen d = 25.24 result lives ONLY in headers** (lines 9–14) referencing Wave 9's synthetic 100-patient agent. Lean encodes no measurement-pipeline theorem, only the corrected constants.
- **No Lean theorem proves the 97.3% / 824-of-847 manuscript headline.** The Ch 30 confusion matrix and per-group ch₂ statistics are NOT formalised.

### Ch 31 (IIT bridge) → Lean: `Consciousness/Ch2PhiBridge.lean`
- `Phi_threshold_from_ch2_095 := 2·log 20` (line 90).
- `Phi_threshold_eq_2_log_20 : ... = 2·Real.log 20 := rfl` (line 93).
- `Phi_threshold_pos : 0 < Phi_threshold_from_ch2_095` (line 101).
- `effective_dim_threshold_from_ch2_095 := 20` (line 112), `effective_dim_at_least_20` (line 115).
- `Ch2PhiBridge : Prop := ∀ (ch_2_val Phi_val : ℝ), 0 ≤ ch_2_val → ch_2_val ≤ 1 → 0 ≤ Phi_val → ch_2_val ≤ 1 − exp(−Phi_val/2) ∨ ch_2_val = 1 − exp(−Phi_val/2)` (line 133) — **structural Prop, not proved as a theorem**. This is the Lean-level analogue of Ch 31 `thm:iit-resonance` — the manuscript's proof is heuristic ("uses that (1−ch₂) measures the fraction of unintegrated variance" — Ch 31 line 103), and that step is the load-bearing claim that Lean records as a Prop rather than a theorem.
- `consciousness_threshold_dimensioned` (line 154) — bundles the algebraic facts (`2·log 20`, positivity, effective-dim 20).

### Ch 31 (QFT mass bridge) → Lean: `Consciousness/Ch12MassIITBridge.lean`
- `sqrt_five_eq_two_phi_minus_one_Ch12 : √5 = 2·φ − 1` (line 95) — `ring`.
- `mass_ratio_eq_inv_two_sqrt_five : m_C/M_Planck = 1/(2·√5)` (line 104).
- `mass_ratio_eq_inv_four_phi_minus_two : m_C/M_Planck = 1/(4·φ − 2)` (line 124).
- `phi_threshold_quarter_eq_log_two_sqrt_five : Φ_threshold/4 = log(2·√5)` (line 137) — gives the `exp(−Φ/4)` identity.
- `consciousness_color_trinification_asymp_free : 0 < b_0_coeff 3 16` (line 194) — encodes N_c=3, N_f=16 asymptotic freedom condition `b_0 = (11·3 − 2·16)/(12π) = 1/(12π) > 0`.
- `ch12_qft_mass_iit_bridge_capstone` (line 215) — bundles all four mass identities + positivity.
- All algebraic, all axiom-free.

### Ch 32 (α-uniqueness) → Lean: `Consciousness/Ch32AlphaNPSpecificity.lean`
- `alpha_NP_Ch32 := φ + 1/4`, plus `alpha_P_Ch32 := √2`, `alpha_Hodge_Ch32 := φ`, `alpha_RH_Ch32 := 3/2` (lines 56–68).
- `rho_at_alpha_NP := 1.000`; `rho_at_alpha_P := -0.257`; `rho_at_alpha_Hodge := -0.086`; `rho_at_alpha_RH := -0.200` (lines 73–82) — empirical scalars, not derived.
- `alpha_NP_ne_alpha_P / _Hodge / _RH` (lines 107, 124, 130) — pairwise distinctness, axiom-free `nlinarith`.
- `rho_at_other_alphas_negative` (line 150), `alpha_NP_advantage_at_least_one` (line 158).
- `alpha_NP_Ch32_specificity_capstone` (line 183) — bundles the ρ-pattern + α-distinctness.

### Broader consciousness substrate (Ch 17 operator C, RH bridge, H₃ bridge)
- `Consciousness/ConsciousnessOperatorC.lean` (commit `6303c02`): `ConsciousnessSubstrate` structure (line 79), Props `IsSelfAdjoint_C` (line 103) / `IsPositive_C` (line 110) / `IsUnbounded_C` (line 118) / `IsTraceClassOnFiniteRegions_C` (line 127), and (P5) `CommutatorVanishesAtRiemannZeros` (line 144). The (P5) clause is the load-bearing manuscript Ch 17 §13.6 (5).
- `Consciousness/ConsciousnessRHBridge.lean`: `riemann_hypothesis_via_consciousness_bridge` (line 164) — RH reduced to two named open Props: substrate (P5) + `ConsciousnessStationaryStateCompleteness` (line 138). Conditional reduction, **not a discharge**.
- `Consciousness/ConsciousnessRHBridgeWave35Witnesses.lean` / `…Wave36InfiniteSubstrate.lean` / `…Wave38InfiniteZeroSet.lean`: progressively larger substrates (Fin 5 → ℓ²(ℕ) ZeroSet=ℕ via Even → infinite-dim) where (P5) holds, each as named theorems.
- `Consciousness/H3IcosahedralConsciousnessOperatorBridge.lean`: `h3IBMSubstrate` carrying the Q(√5)-Galois pair α_RH=3/2 and α_NP=φ+¼ as Hamiltonian eigenvalues on a 2×2 Hermitian, connecting H₃ Coxeter content to the consciousness substrate.
- `Consciousness/BCleanPhaseConsciousnessCommutatorBridge.lean` (Wave 39A, 2026-05-30): embeds the monodromy phase identity `π/(10·α) = (1/5)·(π/2 − Im R_f^principal(α))` into the Wave-35 commutator block-difference data at α ∈ {3, 4}.
- `Consciousness/ConsciousnessP6InfiniteDimSubstrate.lean`: discharges (P6) on infinite-dim substrate.
- `Consciousness/ConsciousnessOdlyzko10Substrate.lean` / `…Odlyzko100Substrate.lean`: anchor the bridge to the first 10 / 100 Odlyzko-tabulated ζ-zero imaginary parts.

### Dependency graph (what is THEOREM vs PROP)

| Manuscript claim | Lean-side status |
|---|---|
| `ch₂ ≤ 1 − exp(−Φ/2)` (Ch 31 `thm:iit-resonance`) | **PROP** (`Ch2PhiBridge` definition, line 133), NOT a theorem; algebraic threshold corollaries `Phi_threshold_eq_2_log_20`, `consciousness_threshold_dimensioned` ARE theorems |
| `m_C/M_Planck = 1/(2√5) = exp(−Φ/4)` (Ch 12 line 112) | **THEOREM**, axiom-free (`mass_ratio_eq_inv_two_sqrt_five` + `phi_threshold_quarter_eq_log_two_sqrt_five`) |
| ch₂ = 0.95 threshold = crystallization | **DEFINED** (`clinical_threshold := 0.95`), threshold *value* is a definitional choice; Ch 6 first-principles derivation is NOT formalised |
| Ch 32 sleep-state ordering, ρ=1.000 at α=φ+¼ | **EMPIRICAL CONSTANTS** + algebraic distinctness theorems; the ρ-values themselves are scalars, not derived; the α-distinctness IS axiom-free proven |
| Clinical accuracy 97.3% on 847 patients | **NOT FORMALISED** — manuscript-only; no Lean theorem mentions 847 |
| RH via consciousness operator (Ch 17 §13.6 clause 5) | **CONDITIONAL REDUCTION** — `riemann_hypothesis_via_consciousness_bridge` is a theorem, but it consumes two named open Props |
| α_NP = φ + 1/4 is the consciousness-relevant α | **WITNESS BUNDLE** axiom-free; multi-context: IBM CSV row + clinical synthetic + Ch 32 ordering + quartic 16α²−24α−11=0 |
| LLM ch₂ < 0.95 (Ch 31 `prop:llm`) | **NOT FORMALISED**; manuscript itself retracts the numerical estimates (`rem:llm-ch2-methodology`, lines 602–604) |

---

## §3 — Sharpest honest consciousness status, new attack surfaces, Wave 55 proposals

### Sharpest honest status sentence

The consciousness substrate is **axiom-free at the Lean level**. What is proven: closed-form bridges between threshold `ch₂ = 0.95`, the Q(φ) algebraic element `1/(2√5)`, and Tononi Φ on the natural-log scale (`Phi = 2·log 20`); the cross-domain α=φ+¼ anchor with rigorous algebraic distinctness from the other three framework α-values; finite- and infinite-dim consciousness substrates where the (P5) commutator clause is witnessed. What is conditional: the IIT-Φ bridge inequality (a Prop, not a theorem), RH via consciousness (two named open Props), and the manuscript's `Φ = −log₂(1−ch₂)` heuristic derivation. What is unformalised: the 847-patient validation cohort, the 97.3% accuracy headline, the recovery dose-response, every cross-species ch₂ datum. **The manuscript's empirical layer outruns its formal layer by a wide margin.**

### Attack surfaces NOT currently in the Wave 55 dispatch synthesis

The Wave 55 dispatch synthesis (`MISSION_INVENTORY/wave55_dispatch_synthesis.md`) and four frontier audits (`wave55_frontier_{RH,NS,YM_Hodge,PNP_BSD}.md`) are **silent on the consciousness chapters** — only `wave55_frontier_RH.md` mentions consciousness, and only in service of the RH route via `ConsciousnessOperatorC.lean`. None of the four frontier audits investigates Ch 30 / 31 / 32 themselves. This leaves at least three surfaces unaddressed:

1. **The IIT-Φ Prop → Theorem gap** (Ch 31, line 64). Ch 31's proof is heuristic; `Ch2PhiBridge` is encoded as a Prop. Standard linear-entropy ↔ von Neumann entropy inequalities (Audenaert, Fannes) ARE in mathlib's reach.
2. **The 847-patient cohort and recovery dose-response** (Ch 30 `thm:diagnostic-accuracy`, `thm:prognostic`). Manuscript-only. Not connected to any in-repo data.
3. **The 14.1 Hz critical frequency prediction** (Ch 31 `thm:resonance-frequency`). The `f_crit = √2 · 10 Hz` identity is a simple multiplication, but its biological status — `√2 = α_P` AND beta band centre — sits between two domains without an axiom-free identity tying them together.

### Wave 55 proposals — one per chapter, traced to a citation

#### Wave 55-Ch30: Real-EEG provenance closure
- **Citation**: Ch 30 lines 221–236 (`thm:validation-cohort` claims "Retrospective analysis of 847 patients across 7 medical centers"); evidence_base_audit.md §5 item 16 ("Clinical ch₂ 100% binary on '80-subject cohort' — the repository contains only a synthetic 100-patient SIMULATOR (`clinical_ch2_verification/full_cohort_experiment.py`), not real EEG data").
- **Substantive attempt**: Apply the Lean-recorded corrected pipeline (`alpha_clinical_optimal`, `base_clinical_optimal`, `clinical_norm_choice` — `ClinicalCh2Calibration.lean` lines 80–90) to a PUBLIC real-EEG cohort with consciousness labels. Candidate datasets: PhysioNet Sleep-EDF (sleep-stage ground truth — matches Ch 32 `thm:states` exactly: alert, N1, N2, N3, REM); BCI Competition IV datasets; OpenNeuro DOC EEG (Toker / Schiff lab releases).
- **Lean-side anchor**: add a real-data `RealEEGCohort` structure (analogue of `ConsciousnessSubstrate`) parametrised over `(subjects : Fin N → State)`, with `clinical_ch2_pipeline_matches : ch₂_clinical(subject) ≥ 0.95 ↔ State.conscious` as a named Prop. Then witness it on the data — turning the manuscript's 97.3% into a formalised conditional theorem (`if real-data Prop holds, then accuracy ≥ 0.95`).
- **Why honest**: the conditional framing matches the Lean-side honesty already in place for the RH route (consume named open Prop, do not discharge it without data). The proposal **does not claim** clinical discharge; it OPENS the path by replacing synthetic with public.
- **What it does NOT do**: it does not validate the 847-patient figure (those data are not in-repo); it constructs a *reproducible* bridge to a public cohort. The 847-patient claim remains unsupported until the original data are provided.

#### Wave 55-Ch31: Linear-entropy ↔ von-Neumann-entropy theorem upgrade
- **Citation**: Ch 31 `thm:iit-resonance` (lines 64–76); `Ch2PhiBridge.lean` line 133 `Ch2PhiBridge : Prop`.
- **Substantive attempt**: Discharge the bridge inequality `ch₂ ≤ 1 − exp(−Φ_IIT/2)` from algebraic first principles on pure bipartite states with finite Schmidt rank `d_A`. The inequality is equivalent to `Tr(ρ_A²) ≥ exp(−S_vN(ρ_A))` for density matrices, which follows from concavity of `t ↦ −t·log t` applied to the spectrum of ρ_A. This is mathlib-tractable: `Mathlib.Analysis.Convex.SpecificFunctions.Basic` and `Mathlib.MeasureTheory.Function.LpSpace` have the needed entropy inequalities.
- **Concrete pathway**: prove first on `d_A = 2` via direct computation `(p² + (1−p)²) ≥ exp(−(−p·log p − (1−p)·log(1−p)))`, then lift via `Mathlib.Analysis.Convex.Jensen`.
- **Lean target theorem name**: `ch2_phi_bridge_inequality_pure_bipartite` (currently a Prop, upgrade to theorem with named open hypothesis `∀ρ_A pure-reduced`).
- **Why this is the path of least resistance**: the inequality is true (it is a standard linear-entropy vs von-Neumann-entropy fact, eq. (8) in Ch 31 derivation sketch in `Ch2PhiBridge.lean` lines 26–31). The Lean encoding chose to record it as a Prop because the closed-form derivation requires choosing Schmidt-spectrum positivity and a concavity step — both individually mathlib-tractable.
- **What it does NOT do**: does not address the IIT-NP-hardness or operational measurement issues. It closes the *algebraic* bridge, which currently sits as a Prop hole in the entire Φ/ch₂ chain.

#### Wave 55-Ch32: Sleep-state ordering theorem via monotone transform invariance
- **Citation**: Ch 32 `thm:states` (lines 427–452); `Ch32AlphaNPSpecificity.lean` lines 73–82 (Spearman ρ values as bare scalars).
- **Substantive attempt**: Replace the bare-scalar `rho_at_alpha_NP := 1.000` with a structural ordering theorem. Define `Ch32SleepStateOrder : Fin 6 → ℝ` from the manuscript means (alert 0.981, eyes-closed 0.973, N1 0.891, N2 0.672, N3 0.387, REM 0.947, meditation 0.989 — 7 states actually). Prove that **any strictly monotone transform of the within-state synthetic-EEG pipeline at α=φ+¼ preserves the ordering**, and that the same transform applied at α=√2 BREAKS at least one inversion. This gives a finite-case version of the manuscript's ρ=1.000 claim that is provable axiom-free from arithmetic on the means.
- **Lean target theorem name**: `alpha_NP_preserves_Ch32_ordering` (analogue of the existing `alpha_NP_Ch32_specificity_capstone`, but with the *ordering* itself as a named relation rather than the ρ-scalar).
- **Why honest**: this does not discharge the empirical content of the manuscript — synthetic-EEG-pipeline outputs are still synthetic. It does formalise the *finite, decidable* claim "α=φ+¼ uniquely orders the manuscript's 7 sleep states correctly under the calibrated pipeline" as a strict theorem about the published means.

### Clinical EEG cohort gap — Wave 55 path (per prompt's specific ask)

`evidence_base_audit.md` §5 item 16 (lines 264–266) identifies the synthetic 100-patient cohort as **the single biggest provenance gap** in the empirical claims. Lean files have a partial path to closing it, but **the formalisation alone cannot close it** — real EEG data must be brought in.

**The path the Lean files enable**:

1. The corrected calibration constants `(α=φ+¼, base 2, rms norm, threshold 0.95)` ARE formalised in `ClinicalCh2Calibration.lean` lines 80–93. They override the manuscript's `α=√2`, base-3, literal-norm spec (Ch 30 lines 173–177, 197–206), and the override is the Lean record.

2. The threshold 0.95 sits algebraically inside the manuscript's discriminative gap `[0.50, 3.12]` per the Wave 9 search (`ClinicalCh2Calibration.lean` lines 28–32).

3. To close the gap, Wave 55-Ch30 above must materialise: implement the corrected pipeline against a public DOC EEG cohort or sleep-EDF dataset. The closest analogue already in-repo is the synthetic `clinical_ch2_verification/full_cohort_experiment.py`; replacing its synthetic generator with an MNE-Python loader for Sleep-EDF (a Ch 32-aligned task per `thm:states`) would yield the first real-data attestation.

4. The closure cannot be done in Lean alone. What Lean can deliver is the conditional theorem: **"For the corrected calibration parameters formalised in `ClinicalCh2Calibration.lean`, IF the pipeline applied to a real-EEG cohort with labels matches the manuscript's normative table (Ch 32 `thm:states`), THEN α=φ+¼ is the consciousness-relevant α."** That conditional, formalised, is a referee-readable Wave 55 deliverable that contains all and only the framework's honest commitments.

---

## §4 — Adversarial review: where Ch 30-32 go beyond what's empirically validated

### Provenance gaps (where the manuscript outruns the in-repo data)

1. **The 847-patient cohort is not in-repo.** Ch 30 `thm:validation-cohort` (line 221) cites a multi-centre 2015–2024 retrospective. The repo contains:
   - Synthetic 100-patient simulator (`clinical_ch2_verification/full_cohort_experiment.py`) — flagged by `evidence_base_audit.md` §5 item 16.
   - No raw EEG files for 847 patients.
   - No CRS-R / GCS clinical metadata.
   - No 7-centre IRB documentation.
   - **Adversarial verdict**: the 97.3% accuracy headline (Ch 30 line 243) is NOT empirically verifiable from in-repo materials. A referee asking "where is the dataset" gets nothing. The closest defensible claim is the synthetic 100/100 binary plus Cohen d=25.24, but the manuscript wording obscures this.

2. **The 1,247 healthy adult normative cohort** (Ch 32 `thm:normative` line 391) is similarly not in-repo. The percentile values (5th, 25th, 50th, 75th, 95th) and age regression `R²=0.11` lack a data file.

3. **The cross-species data** (Ch 32 `thm:species` line 456) — humans 1247, chimps 23, dolphins 12, parrots 18, rats 143, zebrafish 67, honeybees 234, etc. — no species-EEG records in-repo. The "universal threshold 0.95 derived from human data" caveat (Ch 32 line 485) IS preserved.

4. **Optogenetics, anesthesia, lesion cohorts** in Ch 31 (`thm:optogenetics` 23 mice, `thm:anesthesia` per-agent ch₂ at LOC, `thm:lesions` 312 stroke patients) are cited but not in-repo.

5. **23 discrepant cases narrative** (Ch 30 line 439-456) reads as forensically detailed (6 motor-impaired, 3 sedated, 8 prognostic, 4 seizures, 2 unexplained). Without the raw records this narrative is unfalsifiable.

### Logical / methodological gaps

6. **Ch 30 confusion matrix arithmetic disagrees with itself.** Lines 244–252 state sensitivity 96.8% / specificity 97.8% / PPV 97.4% / NPV 97.2%. The "proof" block lines 272–278 recomputes from the matrix: sensitivity 422/431 = 97.9% ≈ 98.0%, specificity 402/416 = 96.6%, PPV 422/436 = 0.968, NPV 402/411 = 0.978. The two paragraphs report different decimals (96.8 vs 98.0 sensitivity; 97.8 vs 96.6 specificity) and the closing sentence acknowledges "Slight rounding adjustments for consistency with empirical data" (line 281). This is **not a discrepancy a referee should accept silently** — the headline numbers should match the matrix arithmetic.

7. **Ch 31 `thm:iit-resonance` proof step at line 99–103** asserts `Φ = min I(A:B) = min [−log₂ P(partition independent)] = −log₂(1 − ch₂)` with the comment "The final step uses that (1 − ch₂) measures the fraction of unintegrated variance." This is the load-bearing identity and the manuscript treats it as definitional rather than derived. The Lean encoding (`Ch2PhiBridge` Prop) correctly flags this as an open structural claim, but the manuscript reads as if it were a theorem.

8. **The 14.1 Hz prediction is `f_base = 10 Hz` not from first principles** (Ch 31 line 254 says "alpha rhythm baseline"). The biological alpha rhythm centre IS approximately 10 Hz, but the choice of `f_base = 10` rather than the true alpha-band midpoint (8–13 Hz → 10.5 Hz) gives `√2·10 = 14.14` rather than `√2·10.5 = 14.85`. The "validation" `14.3 ± 1.2 Hz` (line 258) brackets both, making the predicted value unfalsifiable within the cited error bar.

9. **The Ch 31 anesthesia table** (`thm:anesthesia` lines 467–477) lists ch₂-at-LOC for 5 agents with three-decimal means. No raw data is in-repo. The mechanistic narrative (propofol = GABA, ketamine = NMDA, etc.) is standard but the per-agent ch₂ values are not.

### Wave 55 path to close the biggest gap

The **biggest provenance gap remains the synthetic 100-patient cohort masquerading as clinical validation** (`evidence_base_audit.md` §5 item 16, restated in §8 Action 1 line 372: "Run real-EEG clinical ch₂ verification — closes single biggest provenance gap; 1–2 weeks"). The Wave 55-Ch30 proposal above is the path:

- **Step 1**: Acquire Sleep-EDF (open, OpenNeuro / PhysioNet). 197 polysomnograms, EDF format, sleep-stage labels, public license. Already standard MNE-Python loadable.
- **Step 2**: Reimplement `clinical_ch2_verification/full_cohort_experiment.py` against Sleep-EDF raw inputs using the corrected (`α=φ+¼`, base 2, rms) calibration from `ClinicalCh2Calibration.lean`.
- **Step 3**: Verify Ch 32 `thm:states` ordering on real data: alert > REM > N1 > N2 > N3, with N3 < 0.50 (unconscious) and alert > 0.95 (conscious).
- **Step 4**: Formalise the conditional theorem (Lean-side): `RealEEGSleepEDFOrdering : Prop`, then witness it. If the ordering holds, the threshold's empirical grounding shifts from synthetic to public real-data; if it does not hold, the manuscript's Ch 30 / 32 claims need explicit retraction.
- **Step 5**: A second real-data anchor — the OpenNeuro DOC EEG releases (Schiff/Toker) — would directly test the Ch 30 `thm:diagnostic-accuracy` claim, but on a much smaller cohort (~10s of patients, not 847). The 847 figure cannot be matched without the original data; the most-defensible claim becomes "ch₂ pipeline classifies a public N-patient DOC cohort with accuracy A" for whatever A turns out to be.

The path closes the provenance gap **only if** the corrected pipeline survives contact with real EEG. If it does not, the corrected calibration constants in `ClinicalCh2Calibration.lean` will need to be re-derived against the real-data discriminative gap, and the framework's honest claim shrinks accordingly.

---

## §5 — One-paragraph summary

The Lean consciousness substrate is axiom-free and proves real algebraic content (the `m_C/M_Planck = 1/(2√5) = exp(−Φ/4)` Q(φ) identity, the α=φ+¼ pairwise distinctness from the other three framework α-values, the consciousness ↔ RH conditional reduction `riemann_hypothesis_via_consciousness_bridge`). The manuscript's three consciousness chapters outrun this formal foundation in two specific ways: (a) the central IIT bridge `ch₂ ≤ 1 − exp(−Φ/2)` is encoded as a `Prop` in `Ch2PhiBridge.lean` line 133, not a theorem — the Wave 55-Ch31 proposal is to discharge it via a standard linear-entropy vs von-Neumann-entropy inequality that mathlib supports; (b) the manuscript's 847-patient / 97.3% / 1,247-volunteer / cross-species cohorts are NOT in-repo, leaving the synthetic 100-patient simulator as the single biggest provenance gap (`evidence_base_audit.md` §5 item 16), with the Wave 55-Ch30 path being a Sleep-EDF / OpenNeuro real-data reimplementation of `ClinicalCh2Calibration.lean`'s corrected `(α=φ+¼, base 2, rms)` pipeline. The Ch 32 sleep-state ordering ρ=1.000 result is formalised as `alpha_NP_Ch32_specificity_capstone` but only the α-distinctness is theorem-grade; the ρ scalars are bare empirical constants. The Ch 30 confusion-matrix arithmetic disagrees with its own headline (96.8% vs 98.0% sensitivity, 97.8% vs 96.6% specificity, acknowledged as "rounding adjustments" on line 281) — this is the most pointed referee-target inside the existing manuscript prose.
