# ch₂ Semantic-Disambiguation Ledger — 2026-09-14

Branch: `r331b-ch2-disambiguation` (isolated worktree from origin SHA
`65c286da7d95189fdbdb61e04b347d56219989d3`; Legion Phase-1 K4 base).
Status: **Phase A census — READ-ONLY audit of the corpus AS IT STANDS at
the base SHA.** No renaming, no theorem edits, no book edits yet.
Phase B (canonical names + deprecated aliases) and Phase C (narrative
correction plan) follow in separate commits.

Purpose: remove the false semantic identification among distinct
mathematical objects currently sharing the unqualified name `ch_2` /
`ch₂` in the Lean corpus and the manuscript. Objects that must not
share an unqualified mathematical name and must not be treated as
proven equal:

- (S1) affine target-anchored function of α,
- (S2) bounded real-valued carrier in `PF/ChernWeil.lean`,
- (S3) state-relative linear entropy `1 − Tr(ρ²)`,
- (S4) Chapter 32 clinical EEG band-power surrogate,
- (S5) the postulated 19/20 = 0.95 consciousness threshold,
- (S6) Chapter 11's numerically refuted anomaly-derived quantity,
- (S7) the genuine Chern–Weil second Chern character (topological
  characteristic class from bundle/connection/curvature).

Section §1 catalogues each object at the base SHA. Section §2
inventories every Lean declaration touching these targets. Section §3
inventories every book passage. Section §4 lists downstream
consumers. Section §5 flags collisions. Section §6 (Phase C) supplies
the manuscript-correction plan for Chapters 6, 8, 11, 12, 21, 23, 25,
31, 32.

---

## §1. Semantic classes (S1–S7) and their status at base SHA

| ID | Colloquial name | Actual mathematical object | Where defined (base SHA) | Epistemic class |
|---|---|---|---|---|
| S1 | Affine `ch_2(α)` | `α ↦ 0.95 + (α − √2)/10`, a real-valued affine function of one real parameter α, with 0.95 baked into the definition | `PF/MillenniumSixReductions.lean:2596`; re-exported at `PF/Consciousness/ChernCharacter.lean:73` | Target-anchored **definition**. Not a theorem, not a derivation, not a topological invariant. |
| S2 | `SecondChernCharacter` (Lean) | Bounded real-valued carrier: a `structure` with a single field `value : ℝ` plus a proof `0 ≤ value ≤ 1`. NO bundle, NO connection, NO curvature form; NO Chern–Weil construction | `PF/ChernWeil.lean:24` | Structural carrier / label. **NOT a Chern–Weil characteristic class.** |
| S3 | Linear entropy `1 − Tr(ρ²)` | The Schmidt-spectrum linear entropy `s ↦ 1 − Σᵢ (s.p i)²` on `SchmidtSpectrum n` | `PF/Consciousness/Ch2PhiBridgeDischarge.lean:100` | Rigorous quantum-information quantity. Correctly defined. |
| S4 | Clinical/EEG `ch_2` | Chapter 32 pipeline: band power → base-3 digit sum → phase factor → weighted sum → squared magnitude, on EEG data | `Principia_Fractalis_master_folder/chapters/ch32_consciousness_quantification.tex:191–322` | **Experimental operationalization / surrogate**, book only. No Lean formalization at base SHA. |
| S5 | 0.95 threshold | The real constant `0.95` used as a phase-transition boundary for "consciousness" | `PF/ChernWeil.lean:21`; `PF/Consciousness/ChernCharacter.lean:61`; `PF/Cosmology/LambdaEffCalibration.lean:96`; `PF/Cosmology/LambdaEffParameterFreeCapstone.lean:69` (as `consciousness_threshold_capstone`) | **Phenomenological anchor** per `ch06:188–198` remark 2026-07-01 (not first-principles unique). |
| S6 | Ch11 anomaly `ch_2` | Chapter 11's numerical claim `ch_2 = (4π)⁷·10⁷/(8174·10¹⁴) = 0.95` and its Gaussian-integral cross-check `⟨\|Ψ_RQG\|²⟩ = 0.95` | `ch11_geometric_unity.tex:143–172, 188–202` | **Refuted.** Formal Lean refutation lives at `PF/Ch11AnomalyCancellationRefutationAttempt.lean:1–225` (axiom-free proofs `anomaly_cancel_predicted_value_ne_0_95` and `prop_11_6_psi_rqg_sq_ne_0_95`). Manuscript `\manuscriptcorrection` blocks at ch11:145 and ch11:193 acknowledge. |
| S7 | Genuine second Chern character | Bundle/connection/curvature form `(1/8π²) Tr(F ∧ F) ∈ Ω⁴(X;ℝ)` for a Hermitian bundle `E` with unitary connection `∇`, curvature `F_∇` | `ch06_consciousness.tex:285–298` (definitional in book) | **Book-only mathematical object.** **No Lean file at base SHA supplies a bundle-connection-curvature construction of the second Chern character.** The Lean `SecondChernCharacter` (S2) shares only the name. |

---

## §2. Lean declaration inventory (base SHA `65c286da`)

Each entry: file:line — declaration kind — Lean type — mathematical
meaning actually encoded — role of 0.95 (input / definitional /
hypothesis / conclusion) — printed axioms if load-bearing.

### §2.1 Defining sites

| # | File : line | Kind | Signature | Meaning | Role of 0.95 |
|---|---|---|---|---|---|
| D1 | `PF/MillenniumSixReductions.lean:2596` | `noncomputable def` | `ch_2 (α : ℝ) : ℝ := 0.95 + (α − Real.sqrt 2) / 10` | Affine function of α (S1). Class-anchored evaluation point at α = √2 gives 0.95 by construction. | **Definitional constant.** |
| D2 | `PF/Consciousness/ChernCharacter.lean:73` | `noncomputable def` | `ch_2 (α : ℝ) : ℝ := MillenniumSix.ch_2 α` | Namespace re-export of D1. | Definitional (via D1). |
| D3 | `PF/Consciousness/ChernCharacter.lean:61` | `def` | `consciousness_threshold : ℝ := 0.95` | Real constant (S5). | Definitional. |
| D4 | `PF/ChernWeil.lean:21` | `noncomputable def` | `consciousness_threshold : ℝ := 0.95` | Real constant (S5), distinct namespace from D3 (both under `PrincipiaTractalis`, but ChernWeil.lean uses `namespace PrincipiaTractalis` at line 18; ChernCharacter.lean's namespace is nested `Consciousness`). | Definitional. |
| D5 | `PF/ChernWeil.lean:24` | `structure` | `SecondChernCharacter { value : ℝ, bounded : 0 ≤ value ∧ value ≤ 1 }` | Bounded real carrier (S2). NOT a Chern–Weil construction. | Not present. |
| D6 | `PF/ChernWeil.lean:29` | `def` | `is_conscious (ch2 : SecondChernCharacter) : Prop := ch2.value ≥ consciousness_threshold` | Predicate: "the `.value` field ≥ 0.95". | Hypothesis threshold (via `consciousness_threshold` = 0.95). |
| D7 | `PF/ChernWeil.lean:33` | `structure` | `ConsciousnessState { ch2 : SecondChernCharacter, coherent : ch2.value ≥ 0.50 }` | Product of (S2) with a partial-coherence lower bound. | Not present (uses 0.50 instead). |
| D8 | `PF/ChernWeil.lean:51` | `noncomputable def` | `classify_regime : SecondChernCharacter → ConsciousnessRegime` | Trichotomy in `.value` against thresholds 0.50, 0.95. | Definitional (threshold value). |
| D9 | `PF/Cosmology/LambdaEffCalibration.lean:96` | `def` | `consciousness_threshold : ℝ := 0.95` | Third redundant copy of S5. | Definitional. |
| D10 | `PF/Cosmology/LambdaEffParameterFreeCapstone.lean:69` | `def` | `consciousness_threshold_capstone : ℝ := 0.95` | Variant naming; same numerical value. | Definitional. |
| D11 | `PF/Consciousness/Ch2PhiBridgeDischarge.lean:100` | `def` | `linearEntropy {n : ℕ} (s : SchmidtSpectrum n) : ℝ := 1 − Σᵢ (s.p i)²` | Linear entropy (S3) on Schmidt spectra. **Rigorous quantum-information object.** | Not present. |
| D12 | `PF/Consciousness/Ch2PhiBridgeDischarge.lean:108` | `noncomputable def` | `vNEntropy {n : ℕ} (s : SchmidtSpectrum n) : ℝ := −Σᵢ s.p i · log (s.p i)` | Von Neumann entropy on Schmidt spectra. | Not present. |
| D13 | `PF/Consciousness/Ch2PhiBridgeDischarge.lean:116` | `noncomputable def` | `Phi_IIT {n : ℕ} (s : SchmidtSpectrum n) : ℝ := 2 · vNEntropy s` | Tononi Φ_IIT on bipartite pure states. | Not present. |

**No S7 defining site exists in Lean at base SHA.** `PF/ChernWeil.lean`
imports `Mathlib.Geometry.Manifold.VectorBundle.Basic`,
`Mathlib.Topology.FiberBundle.Basic`,
`Mathlib.Analysis.InnerProductSpace.Basic` but does not use bundle,
connection, or curvature machinery to construct S7. The name
`SecondChernCharacter` is used as a label only.

### §2.2 Load-bearing theorems and their status

| # | File : line | Theorem | Statement (essence) | Category |
|---|---|---|---|---|
| T1 | `PF/MillenniumSixReductions.lean:2599` | `ch_2_at_alpha_P` | `ch_2 (Real.sqrt 2) = 0.95` | **Evaluation of a target-anchored definition** (D1 evaluated at α = √2 gives 0.95 by construction). Not a derivation. Proof by `unfold; ring`. |
| T2 | `PF/MillenniumSixReductions.lean:2605` | `ch_2_at_alpha_NP` | `ch_2 (φ + 1/4) = 0.95 + ((φ + 1/4) − √2)/10` | Evaluation of D1. Proof by `unfold; rfl`. |
| T3 | `PF/MillenniumSixReductions.lean:2615` | `consciousness_gap_eq_dim_gap_over_ten` | `ch_2(φ+1/4) − ch_2(√2) = ((φ+1/4) − √2)/10` | Algebraic identity in the affine form. |
| T4 | `PF/MillenniumSixReductions.lean:2623` | `consciousness_gap_positive` | `ch_2(φ+1/4) − ch_2(√2) > 0` | Follows from `φ + 1/4 > √2`. |
| T5 | `PF/Consciousness/ChernCharacter.lean:83` | `ch_2_at_alpha_P_eq_threshold` | `ch_2 (Real.sqrt 2) = 0.95` | Same as T1, restated in namespace. |
| T6 | `PF/Consciousness/ChernCharacter.lean:99` | `ch_2_at_alpha_NP_gt_threshold` | `0.95 < ch_2 (φ + 1/4)` | Strict inequality from D1 + `√2 < φ + 1/4`. |
| T7 | `PF/Consciousness/ChernCharacter.lean:127` | `ch_2_strict_mono` | `StrictMono ch_2` | Monotonicity in α, algebraic. |
| T8 | `PF/Consciousness/ChernCharacter.lean:143` | `ch_2_threshold_iff` | `0.95 ≤ ch_2 α ↔ √2 ≤ α` | Equivalent formulation of D1. |
| T9 | `PF/Consciousness/ChernCharacter.lean:184,193,204,210,221,227,240,246,252,262,268,281,287,…` | multiple `ch_2_at_alpha_*` | Evaluations at 8 canonical α values | Each is a computation of D1 at a specific α. |
| T10 | `PF/Consciousness/ChernCharacter.lean:313` | `seven_classes_crystallize` | Assertion that 7 α-classes satisfy `ch_2 ≥ 0.95` | Corollary of D1 evaluations plus α ≥ √2. |
| T11 | `PF/Consciousness/ChernCharacter.lean:350` | `consciousness_quantification_capstone` | Capstone-level statement wrapping T5–T10 | Aggregation of T5–T10. |
| T12 | `PF/ChernWeil.lean:38` | `consciousness_crystallization` | `is_conscious S.ch2 ↔ S.ch2.value ≥ 0.95` | **Tautology.** Proof by `unfold; rfl`. |
| T13 | `PF/ChernWeil.lean:71` | `threshold_universal` | `∃! t, 0 < t ∧ t < 1 ∧ (t = 0.95 ∧ t = 0.95 ∧ t = 0.95 ∧ t = 0.95)` | **Void theorem.** File docstring (`ChernWeil.lean:60–70`) explicitly acknowledges: "The docstring's claim of 'four independent derivations' is NOT formalized; the proposition contains only the conclusion `t = 0.95` without ANY of the four derivations. Retained as a structural placeholder." |
| T14 | `PF/ChernWeil.lean:94` | `ch2_measures_integration` | `ch2.value = 0 → ¬ is_conscious ch2` | Arithmetic: 0 < 0.95. |
| T15 | `PF/ChernWeil.lean:103` | `high_ch2_conscious` | `ch2.value ≥ 0.95 → is_conscious ch2` | Restatement of D6. |
| T16 | `PF/ChernWeil.lean:111` | `sharp_transition` | `∀ ε ∈ (0, 0.05), ∃ pair straddling 0.95 with correct is_conscious status` | Arithmetic on the affine value; no topological content. |
| T17 | `PF/ChernWeil.lean:163` | `clinical_accuracy` | `∃ accuracy, accuracy = 0.973` | **Trivial.** Proof: `use 0.973`. |
| T18 | `PF/ChernWeil.lean:178` | `human_brain_conscious` | `∃ brain state with ch2.value = 0.9954` | **Trivial.** Constructs a struct with `value := 0.9954`. No biology, no measurement. |
| T19 | `PF/ChernWeil.lean:200` | `rocks_not_conscious` | Classified-incoherent implies `¬ is_conscious` | Case analysis on the classifier. |
| T20 | `PF/ChernWeil.lean:218` | `consciousness_quantifiable` | `∃ measure, measure = (·.value) ∧ is_conscious ch2 ↔ measure ch2 ≥ 0.95` | Identity function witness. |
| T21 | `PF/Consciousness/Ch2PhiBridgeDischarge.lean:145` | `exp_sum_p_log_p_le_sum_p_sq` | Weighted-AM-GM: `exp(Σ pᵢ log pᵢ) ≤ Σ pᵢ²` | **Rigorous** quantum-information inequality (D11 + D12). Load-bearing for the ch_2 ≤ 1 − exp(−Φ/2) bridge. |
| T22 | `PF/Ch11AnomalyCancellationRefutationAttempt.lean` | `anomaly_cancel_predicted_value_ne_0_95` and `prop_11_6_psi_rqg_sq_ne_0_95` | Both ch11 numerical derivations of 0.95 miss their targets | **Axiom-free refutations** of S6. |

Printed-axiom checks (`#print axioms`) are NOT run in this Phase A
census; Phase C verification will run them on renamed load-bearing
endpoints. Base-SHA `#print axioms` for these theorems is expected
to be `[propext, Classical.choice, Quot.sound]` (mathlib-standard)
per the pattern in `PF/Consciousness/FrobeniusChurn.lean`.

### §2.3 Deferred / not-formalized in Lean at base SHA

| ID | Object | Status |
|---|---|---|
| N1 | S7 (genuine Chern–Weil second Chern character) | **NOT in Lean.** Only imported machinery (`Mathlib.Geometry.Manifold.VectorBundle.Basic`) exists; no construction of `(1/8π²) Tr(F ∧ F)` in `PF/`. |
| N2 | S4 (Chapter 32 clinical EEG surrogate) | **NOT in Lean.** Book only. |
| N3 | Bridge equality `S1 = S3` (affine `ch_2` = linear entropy) | **NOT proved anywhere.** Neither book nor Lean supplies a hypothesis under which the two are identified. |
| N4 | Bridge equality `S2 = S7` (bounded carrier = genuine Chern–Weil) | **NOT proved.** The `SecondChernCharacter` structure carries no bundle data that could match a Chern–Weil form. |
| N5 | Bridge equality `S1 = S3` on the "uniform Schmidt locus" | The `Ch2PhiBridge.lean` docstring (line 26) *asserts* `ch_2(ψ) = 1 − Tr(ρ_A²)` on quantum substrates, but this is D11's definition, NOT the D1 affine function. Two different objects; the docstring's identification is a **terminology conflation**, not a proved identity. |
| N6 | Ch06 rigorous Chern–Weil derivation (`ch06:264–450`) | **NOT formalized in Lean.** `PF/ChernWeil.lean` name suggests it but does not implement it. |
| N7 | `PF.lean` banner file | Not searched at base SHA; if it exists and references any of the above objects it must be included in Phase C migration audit. |

---

## §3. Book-side inventory (base SHA `65c286da`)

Path prefix: `Principia_Fractalis_master_folder/chapters/`.

| Ch | Passage | Line range | Object referenced | Epistemic class | Load-bearing defect |
|---|---|---|---|---|---|
| 4  | `ch04_timeless_field.tex` Thm `spacetime-emergence`, Thm `force-emergence`, Def consciousness operator | :455–461, :493–501, :607–613 | Ties the automorphism-group quotient of `T_∞` to spacetime and forces; consciousness operator via Haar measure on Aut(T_∞) | Postulate (labelled Thm) | Haar measure invoked without a defined topology on Aut(T_∞); `Diff(T_∞)` invoked on a nuclear C*-algebra with no diffeomorphism structure defined. Independent of ch_2 disambiguation but affects the ring map. |
| 6  | `ch06_consciousness.tex` Def consciousness sheaf; Def `second-chern-char`; Thm `consciousness-quant`; Thm `consciousness-crystallization` | :101–112, :146–156, :160–170, :177–184 | S1/S2/S5/S7 all bundled under `ch_2` | Definitional | **Same name `ch_2` used for two different objects on the same page** (S7 topological form at :146–156 and S5 threshold at :180). The consciousness-quantification thm at :160–170 defines the functional and names it "consciousness measurement" — definition dressed as theorem. Honest-scope disclosure at :170 acknowledges this. |
| 6  | Ch06 remark `honest-scope-2026-07-01` | :188–198 | Confirms 0.95 is phenomenological anchor, not first-principles unique; cites the ch11 refutation | Explicit epistemic downgrade | This remark already sets the precedent for the disambiguation this ledger performs. |
| 6  | Rigorous Chern–Weil derivation | :264–450+ (`sec:rigorous-threshold`) | S7 (genuine Chern–Weil form + spectral geometry + holonomy) | Kernel-theorem-shaped **sufficient** condition | Ch06 Thm `threshold-rigorous` (:383) proves ε* ≤ 0.05 suffices for phase coherence, spectral gap, and dynamical stability. It does NOT force ε* = 1/20 uniquely. NOT formalized in Lean. |
| 8  | `ch08_field_equations.tex` Def `complete-fields`; Def `consciousness-stress`; Thm `modified-conservation`; Thm `modified-einstein`; Prop dark-energy | :51–63, :77–90, :108–118, :198–207, :219–247 | Uses `ch_2(ω) > 0.95` step function in the C^μν integral (:80); `Λ_eff = Λ₀ · exp[−⟨ch_2⟩/0.95]` (:222) | Postulate (labelled Thm) | The stress-tensor `C^μν` uses the ch_2 threshold as a step-function activation; `Λ_eff` divides by 0.95 in the exponent. **Same name `ch_2` used across the tensor and the threshold; not disambiguated in the book.** |
| 11 | `ch11_geometric_unity.tex` Def `rqg_operator`; Thm `anomaly_cancel`; Prop `rqg_mean`; Thm `holographic_projection` | :52–66, :139–174, :188–202, :212–248 | S6 (numerical derivations of 0.95), plus 4-dimensionality attempt | Conjectural interpretation / refuted | `\manuscriptcorrection{}` blocks at :145 and :193 explicitly cite the Lean refutation (`PF/Ch11AnomalyCancellationRefutationAttempt.lean`). Ch11:245 disclosure retracts the 4D derivation. **These retractions have not propagated to the book's non-corrected passages that continue to invoke `ch_2 = 0.95`.** |
| 12 | `ch12_mass_generation.tex` (present per `Consciousness/Ch12MassIITBridge.lean` and `Consciousness/Ch12QFTLagrangian.lean` file names) | not read this pass; flagged for follow-up | Presumed uses of ch_2 in mass generation / IIT bridge | Deferred | Two Lean files (`Ch12MassIITBridge`, `Ch12QFTLagrangian`) live under `PF/Consciousness/`. Confirm ch_2 semantics in Phase C. |
| 21 | Ch21 (referenced by `ChernCharacter.lean:9`) | not read this pass; `ChernCharacter.lean:9` claims Ch21 defines `ch_2(α) := 0.95 + (α − √2)/10` "as the P-class baseline" | S1 definition source in book | Definitional. Ch21 is the alleged book origin of the D1 Lean definition. Confirm the exact TeX passage in Phase C. |
| 23 | Ch23 (referenced by `ChernCharacter.lean:10`) | not read this pass | S1 variant `ch_2_YM(α) := 0.95 + (α − 3/2)/10` per header | Definitional | Different affine variant per Millennium axis. Phase C confirms. |
| 25 | Ch25 (referenced by `ChernCharacter.lean:11`) | not read this pass | S1 variant `ch_2_Hodge(α) := 0.95 + (α − 3/2)/10` per header | Definitional | Phase C confirms. |
| 31 | Ch31 ch_2 ↔ Φ bridge (referenced by ch06 remark :195 as "cross-check status pending independent verification") | not read this pass | Bridge between S1/S3 and Tononi Φ_IIT | Deferred | Ch06 remark 2026-07-01 flags this as unverified. Phase C confirms. |
| 32 | `ch32_consciousness_quantification.tex` clinical algorithms | :191–322 | S4 (clinical EEG surrogate) named "ch_2" | Experimental operationalization | **Same name `ch_2` used for a band-power digit-sum surrogate that has no proved relation to S1, S2, S3, or S7.** The bridge to any of them is exactly the unresolved question Legion's Phase-1 measurement work is trying to answer for χ_k, in parallel to this ledger. |

---

## §4. Downstream consumers (Lean, base SHA)

### §4.1 Direct consumers of `MillenniumSix.ch_2` (D1)
Two files consume D1 by name:
- `PF/Consciousness/ChernCharacter.lean:66,68,72,73,85,101,114,122,145,159,198` (aliasing + unfolds).
- `PF/Consciousness/MillenniumConnection.lean:96` (`unfold millenniumConsciousnessTriple ch_2 PrincipiaTractalis.MillenniumSix.ch_2`).

### §4.2 Direct consumers of `PF/ChernWeil.lean` exports (D4–D8, T12–T20)
Two files import `PF.ChernWeil`:
- `PF/ObserverConsciousnessBridge.lean:99` (`import PF.ChernWeil`).
- `PF/Consciousness/TimelessField.lean:44` (`import PF.ChernWeil`), and TimelessField.lean:177 says "We reuse the existing `SecondChernCharacter` carrier from `PF.ChernWeil`."

### §4.3 Direct consumers of `Consciousness.ch_2` (D2) or `Consciousness.consciousness_threshold` (D3)
Contained within `PF/Consciousness/ChernCharacter.lean` and the 20+ theorems T5–T11 in that file. Not re-exported by name outside; other files that need the affine form import via `PF/Consciousness/ChernCharacter.lean` and use its namespace.

### §4.4 Direct consumers of `linearEntropy` (D11)
Local to `PF/Consciousness/Ch2PhiBridgeDischarge.lean` and `PF/Consciousness/Ch2PhiBridge.lean` (via docstring conflation, not import — see N5).

### §4.5 Aggregate `ch_2` grep footprint
Base-SHA counts:
- `ch_2` appears in **57 Lean files** under `PF_Lean4_Code/PF/`. Most of those uses reduce to consumers of D1 via the two consumer sites (§4.1) or references in comments/docstrings.
- `ch₂` (unicode subscript) appears in **14 Lean files** under `PF_Lean4_Code/PF/`. All in comments/docstrings (Lean identifiers cannot contain the subscript 2 in this position); usage is naming/discussion.
- `SecondChernCharacter` appears in **4 files** total.
- `consciousness_threshold` appears in **12 files** (four definitions + eight consumers).
- `is_conscious` appears in **4 files**.
- `Chern-Weil` (hyphenated string) appears in **17 files** (mostly docstring names, not code).
- `linearEntropy` appears in **2 files** (defining site + Ch2PhiBridge docstring reference).
- `0.95` appears in **78 Lean files** — most as a threshold constant.
- Book side: `ch_2` appears in **8 TeX files**, `0.95` in **40 TeX files**.

---

## §5. Collision map (which objects are treated as the same when they are not)

| # | Objects conflated | Where | Nature of the false identification |
|---|---|---|---|
| C-α | S1 (affine) ≡ S5 (threshold) | Every `ch_2_at_alpha_*` theorem and every use of `is_conscious`. | The literal value `0.95` appears both as the definitional intercept of S1 and as the threshold in S5; the theorem `ch_2(√2) = 0.95` reads as though it *derives* the threshold, but it evaluates the definition at the point chosen to yield the threshold. **Circular by construction.** |
| C-β | S2 (bounded carrier) ≡ S7 (genuine Chern–Weil) | `PF/ChernWeil.lean:24` structure name; `PF/Consciousness/ChernCharacter.lean` module name; `PF/Consciousness/TimelessField.lean:177` docstring "We reuse the existing SecondChernCharacter carrier". | The name `SecondChernCharacter` (S2) suggests but does not implement S7. Bundle/connection/curvature machinery is imported (mathlib) but not used. **Name-level conflation without mathematical content.** |
| C-γ | S1 (affine) ≡ S3 (linear entropy) | `PF/Consciousness/Ch2PhiBridge.lean:26` docstring: `ch_2(ψ) = 1 − Tr(ρ_A²)  (linear entropy, framework Ch 6 def)`. | Same brand name `ch_2` used inside the same file for both objects. **Docstring-level conflation.** No theorem in the corpus proves S1 = S3 under any hypothesis. |
| C-δ | S1 (affine) ≡ S4 (clinical EEG) | Book `ch32:191–322` uses the name `ch_2` for the band-power digit-sum surrogate; framework references treat this as "the same ch_2". | **Terminology change, no bridge theorem.** |
| C-ε | S6 (refuted anomaly) presented as derivation of S5 (threshold) | Book `ch11:143`, `ch11:192`. | Both attempted derivations are formally refuted in Lean at `PF/Ch11AnomalyCancellationRefutationAttempt.lean`. The book has `\manuscriptcorrection{}` at :145, :193, but the non-corrected passages still invoke `ch_2 = 0.95`. |
| C-ζ | `consciousness_threshold` is defined **four times** with the same value 0.95 | D3, D4, D9, D10. | Multiple redundant definitions in different namespaces; if any diverges the framework breaks silently. |
| C-η | S3 (rigorous linear entropy) ≡ S7 (Chern–Weil) | `Ch2PhiBridge.lean:19,53` docstring calls S3 a "topological Chern–Weil derivation". | **False lineage claim in docstring.** |

---

## §6. Phase C narrative-correction plan (per chapter)

Do not rewrite the book yet. The plan below records, for each affected
chapter, the exact passage, the epistemic class it should be given,
the replacement terminology, and the downstream claims blocked by
missing bridges.

Semantic-class shorthand used in the plan:
- **[STATE-ENTROPY]** = mathematical linear entropy 1 − Tr(ρ²).
- **[THRESHOLD-95]** = the postulated 19/20 phenomenological anchor.
- **[EEG-SURR]** = Chapter 32 clinical band-power surrogate.
- **[STRESS-TENSOR]** = the ch08 C^μν spacetime stress tensor.
- **[CHERN-WEIL]** = genuine second Chern character from bundle data.
- **[AFFINE-α]** = the target-anchored affine function of α.

### §6.1 Chapter 6 (`ch06_consciousness.tex`)

- **:101–112 (Def consciousness sheaf).** No rename required; sheaf
  itself is a legitimate categorical object. Cross-reference the
  disambiguation ledger so the reader knows "the consciousness
  sheaf" is not "the ch_2 function".
- **:146–156 (Def second Chern character).** This is [CHERN-WEIL].
  Rename downstream uses that refer to any Lean object under the
  same name — the Lean `SecondChernCharacter` is [BOUNDED-CARRIER],
  not [CHERN-WEIL]. Add explicit disclosure that no Lean
  formalization of [CHERN-WEIL] exists at this branch's base.
- **:160–170 (Thm consciousness-quant).** Definitional. Reclassify
  from "Theorem" to "Definition" of the "consciousness functional
  in terms of a topological invariant". The honest-scope note at
  :170 stands.
- **:177–184 (Thm consciousness-crystallization ch_2 ≥ 0.95).** The
  threshold value 0.95 is [THRESHOLD-95] — postulate class, not
  theorem class. Rename the theorem's statement to make clear that
  the input is a topological invariant and the threshold is a
  postulate. Or downgrade to a Proposition-conditional-on-postulate.
- **:188–198 (honest-scope remark).** Keep as is; extend to
  cite this ledger explicitly by SHA once landed.
- **:264–450+ (Rigorous Chern–Weil derivation).** Legitimate
  mathematics of [CHERN-WEIL] plus spectral geometry, proving a
  **sufficient** condition. Rename Thm `threshold-rigorous`
  wording from "ch_2 ≥ 0.95 implies phase coherence and stability"
  to "ε* ≤ 0.05 suffices for phase coherence, spectral gap, and
  dynamical stability" so the direction of the implication is
  unmistakable.
- **Downstream blocked claims:** any statement "consciousness
  crystallizes when ch_2 ≥ 0.95" that treats [CHERN-WEIL] and
  [THRESHOLD-95] and [AFFINE-α] as the same object.

### §6.2 Chapter 8 (`ch08_field_equations.tex`)

- **:51–63 (Def complete fields).** The consciousness field `C` here
  is a new fundamental field. Rename it to something like
  `C_field` in narrative so it is not confused with [CHERN-WEIL]
  ch_2. State epistemic class as **postulate**.
- **:77–90 (Def consciousness-stress).** The integral uses the step
  function `Θ(ch_2(ω) − 0.95)`. Which `ch_2` is this?
  - If S1 [AFFINE-α]: nonsensical, because ω is a state on T_∞
    and α is a resonance parameter — different types.
  - If S3 [STATE-ENTROPY]: legitimate quantum-information quantity
    but not what the book text implies.
  - If S7 [CHERN-WEIL]: requires a bundle structure on the state
    manifold, not supplied here.
  Insert `\manuscriptcorrection{}` at :80 asking which semantic
  class is intended. Currently underspecified.
- **:108–118 (Thm modified-conservation).** Reclassify to
  **postulate**. The "derivation" at :120–147 assumes `L_C` without
  defining it.
- **:198–207 (Thm modified-einstein).** Reclassify to **postulate**.
- **:219–247 (Prop dark-energy).** Reclassify to **target-encoded
  numerical illustration**, not derivation. Add
  `\manuscriptcorrection{}` at :222 disclosing that the numerical
  substitution `10^{−30} · 10^{80} → 10^{−120}` uses free inputs.
- **Downstream blocked claims:** every dark-energy match, every
  "consciousness curves spacetime" claim in later chapters.

### §6.3 Chapter 11 (`ch11_geometric_unity.tex`)

- **:52–66 (Def RQG operator).** Contains α = √ch_2. Which ch_2?
  If S5 (constant 0.95) then `α = √0.95` is a fixed real; if S1
  then α is a function of α (circular). Currently underspecified.
- **:139–174 (Thm anomaly_cancel).** Already flagged with
  `\manuscriptcorrection{}` at :145 citing the Lean refutation.
  Extend the correction to say: **the alleged derivation of
  [THRESHOLD-95] from anomaly cancellation is falsified; the
  threshold is a postulate, not a derived quantity.**
- **:188–202 (Prop rqg_mean).** Already flagged at :193. Same
  extension.
- **:204 (twice-determined overdetermination).** Retract in
  full: both legs are falsified.
- **:212–248 (Holographic projection).** Already retracted in
  :245 disclosure. Extend correction to remove
  ch_2 = 0.95 as an "explanation for 4 dimensions".
- **Downstream blocked claims:** any downstream statement citing
  the "78 BRST cohomology classes matching Standard Model"
  (`ch11:301+`) that depends on the retracted derivation. Not
  audited in this pass.

### §6.4 Chapter 12 (`ch12_mass_generation.tex`)

- Two Lean bridge files exist (`PF/Consciousness/Ch12MassIITBridge.lean`,
  `PF/Consciousness/Ch12QFTLagrangian.lean`). Both must be scanned
  in Phase C for ch_2 usage. Rename ch_2 references to the correct
  semantic class per file; state which class the Lagrangian and
  IIT bridge operate on.

### §6.5 Chapter 21 / 23 / 25 (P vs NP, YM, Hodge)

- These chapters are the source of the affine-in-α definitions
  D1 and its P/NP/YM/Hodge variants (per `ChernCharacter.lean:9–11`
  header comments). Rename their occurrences of `ch_2` in narrative
  to [AFFINE-α], with explicit disclosure that `ch_2(α_class) =
  0.95 + (α_class − √2)/10` is a **definition anchored on
  [THRESHOLD-95]**, not a discovery.
- Any statement of the form "Chapter N derives ch_2 = 0.95 at the
  P-class" should be reclassified to "Chapter N evaluates the
  target-anchored affine definition at α = √2".

### §6.6 Chapter 31 (ch_2 ↔ Φ IIT bridge)

- The genuine content is `Ch2PhiBridgeDischarge.lean`: [STATE-ENTROPY]
  and [VN-ENTROPY] on Schmidt spectra, plus the ch_2 ≤ 1 − exp(−Φ/2)
  inequality with equality on uniform-Schmidt locus.
- In the book, all appearances of `ch_2` in the bridge inequality
  should be renamed to [STATE-ENTROPY] (they are `1 − Tr(ρ²)`, not
  D1). Preserve the inequality; retract the docstring claim
  (`Ch2PhiBridge.lean:19–20,53`) that this inequality is a
  "topological Chern-Weil derivation".
- **Downstream blocked claims:** the "framework's ch_2 is the
  topological refinement of Φ on quantum substrates"
  (`Ch2PhiBridge.lean:62–64`) — false lineage.

### §6.7 Chapter 32 (`ch32_consciousness_quantification.tex`)

- All appearances of `ch_2` in the clinical algorithms
  (`ch32:191–322`) are [EEG-SURR]. Rename in narrative to
  `ch_2^{clinical}` or `eegBandPowerScore` and state that no proved
  identity connects [EEG-SURR] to [AFFINE-α], [STATE-ENTROPY],
  [BOUNDED-CARRIER], or [CHERN-WEIL].
- The bridge from [EEG-SURR] to Layer-1 Frobenius churn
  `frobeniusSqDist` is precisely the U15 measurement-validity
  benchmark that Legion Phase-1 is working on. This ledger does not
  duplicate that effort.

### §6.8 Chapter 4 (out-of-scope for ch_2 disambiguation but flagged)

- The Haar measure on `Aut(T_∞)` (`ch04:607–613`) and the
  automorphism-quotient claim (`ch04:455–461`) are Arrow-1 spine
  defects listed in the causal-spine audit, not ch_2 disambiguation
  targets. Not touched by this ledger.

---

## §7. Truthful canonical names introduced by Phase B (spec, not yet applied)

Naming convention: descriptive of the actual mathematical content, no
mathematical name borrowed from an object whose content is not
present.

| Old name (base SHA) | New canonical name (Phase B) | Where it lives | What it is | What it is NOT |
|---|---|---|---|---|
| `MillenniumSix.ch_2` (D1) | `MillenniumSix.alphaAffineScore` | `PF/MillenniumSixReductions.lean:2596` | Affine function of α with intercept `0.95` and slope `1/10` | Not a topological invariant, not a linear entropy, not a Chern–Weil form, not a clinical EEG surrogate |
| `PrincipiaTractalis.Consciousness.ch_2` (D2) | `PrincipiaTractalis.Consciousness.alphaAffineScore` | `PF/Consciousness/ChernCharacter.lean:73` | Namespace alias of the above | Same |
| `PrincipiaTractalis.consciousness_threshold` (D4), `PrincipiaTractalis.Consciousness.consciousness_threshold` (D3), `PrincipiaTractalis.Cosmology.consciousness_threshold` (D9), and `consciousness_threshold_capstone` (D10) | Single canonical `PrincipiaTractalis.consciousnessThreshold95` (real constant `19/20`) with deprecated aliases in the other three namespaces | primary in `PF/ChernWeil.lean` (or a new file if needed); aliases where D3, D9, D10 currently sit | The postulated 19/20 = 0.95 threshold | Not derived, not a theorem output; **postulate class** per ch06 remark 2026-07-01 |
| `PF.ChernWeil.SecondChernCharacter` (D5) | `PF.ChernWeil.BoundedConsciousnessScore` | `PF/ChernWeil.lean:24` | Bounded real carrier with `value ∈ [0, 1]` | **NOT a Chern–Weil characteristic class.** Explicit docstring disclosure required. |
| `PF.ChernWeil.is_conscious` (D6) | `PF.ChernWeil.boundedScoreAboveThreshold95` | `PF/ChernWeil.lean:29` | Predicate `score.value ≥ 0.95` | Not a proof of consciousness; a numerical predicate on a real carrier |
| `PF.ChernWeil.ConsciousnessState` (D7) | `PF.ChernWeil.ScoredCoherenceCarrier` | `PF/ChernWeil.lean:33` | Product of a `BoundedConsciousnessScore` and a `.value ≥ 0.50` proof | Not a state on a Hilbert space; a labelled bounded real |
| `PF.Consciousness.linearEntropy` (D11) | Keep name; add module-header disclosure that this is `1 − Tr(ρ²)` **on Schmidt spectra**, distinct from the `ch_2` names in the corpus | `PF/Consciousness/Ch2PhiBridgeDischarge.lean:100` | Rigorous linear entropy on Schmidt spectra | Not the affine α function, not the bounded carrier |
| Reserved: `PF.Consciousness.eegBandPowerScore` | NEW — placeholder for the Chapter 32 [EEG-SURR] | Not created in Phase B (no Lean formalization of S4 at base SHA); reserved as a future declaration site | Chapter 32 clinical band-power surrogate | Not the affine α function, not the linear entropy |
| Reserved: `PF.ChernWeil.SecondChernCharacterProper` | NEW — placeholder for a future genuine Chern–Weil construction | Not created in Phase B (no bundle/connection/curvature machinery in `PF/` at base SHA); reserved | Would be the `(1/8π²) Tr(F ∧ F)` construction of ch06:285–298 | Not S2 (which is a name-only label) |

Compatibility rules for Phase B:
- Every deprecated alias uses Lean 4's `@[deprecated]` attribute with
  a message saying (a) which new name to use, (b) which semantic
  class the alias inhabits, (c) what the alias does NOT establish.
- No theorem proposition changes to make it sound stronger. Every
  theorem T1–T20 above keeps the same logical statement; the
  identifiers referenced inside its proof may be updated.
- Every `ch_2_at_alpha_*` theorem is reclassified in its docstring
  from "derivation" or "evaluation of ch_2" to "evaluation of the
  target-anchored affine definition `alphaAffineScore` at a
  specified α".
- The linear-entropy ↔ Φ inequality in
  `PF/Consciousness/Ch2PhiBridgeDischarge.lean` is preserved verbatim;
  the docstring in `PF/Consciousness/Ch2PhiBridge.lean` is corrected
  to drop the "topological Chern–Weil" lineage claim.
- Consumer migration in Phase C is limited to files that break
  under the new names; the deprecated aliases ensure no other
  consumer breaks. This ledger commits to migrating **only**
  `PF/Consciousness/ChernCharacter.lean`,
  `PF/Consciousness/MillenniumConnection.lean`,
  `PF/ObserverConsciousnessBridge.lean`,
  `PF/Consciousness/TimelessField.lean`,
  `PF/Cosmology/LambdaEffCalibration.lean`,
  `PF/Cosmology/LambdaEffParameterFreeCapstone.lean`.
  All other consumers (approximately 50 files) rely on the
  deprecated-alias compatibility layer.

---

## §8. Verification obligations for Phase B commit

Before Phase B lands the API repair, the following must be run and
their output recorded:

- Targeted clean Lean builds for every changed module:
  `lake build PF.MillenniumSixReductions`,
  `lake build PF.ChernWeil`,
  `lake build PF.Consciousness.ChernCharacter`,
  `lake build PF.Consciousness.Ch2PhiBridge`,
  `lake build PF.Consciousness.Ch2PhiBridgeDischarge`,
  `lake build PF.Consciousness.MillenniumConnection`,
  `lake build PF.ObserverConsciousnessBridge`,
  `lake build PF.Consciousness.TimelessField`,
  `lake build PF.Cosmology.LambdaEffCalibration`,
  `lake build PF.Cosmology.LambdaEffParameterFreeCapstone`.
- Aggregate `lake build PF` if the targeted builds pass.
- `#print axioms` on renamed load-bearing endpoints:
  `PF.MillenniumSix.alphaAffineScore`,
  `PF.MillenniumSix.alphaAffineScore_at_alpha_P` (new name of T1),
  `PF.MillenniumSix.alphaAffineScore_slope`,
  `PF.ChernWeil.consciousnessThreshold95`,
  `PF.ChernWeil.boundedScoreAboveThreshold95`,
  `PF.Consciousness.linearEntropy_le_one_minus_exp_neg_Phi_over_two`
  (if this exists; confirm in Phase B).
- Diff scan for `sorry`, `native_decide`, new `axiom` declarations,
  proxy endpoints, circular definitions, and numerical definitions
  presented as derivations.

---

## §9. Unresolved collisions after Phase B (declared in advance)

Even after Phase B renames the Lean side, the following collisions
remain unresolved and require Phase C book edits (not authored by
this ledger):

1. **Book Chapter 32's `ch_2` name for [EEG-SURR]** will remain
   until the manuscript is edited.
2. **Book Chapter 8's `ch_2(ω)` in the C^μν integral** with
   underspecified semantic class remains.
3. **Chapter 6's "second Chern character" language** in `ch06:146–156`
   remains legitimate mathematically ([CHERN-WEIL]) but its
   identification with the Lean `SecondChernCharacter` label is not
   proved; downgrade required.
4. **Chapter 11's `\manuscriptcorrection` blocks at :145 and :193**
   correctly flag S6 as refuted but the non-corrected passages in
   the same chapter still invoke `ch_2 = 0.95` unchanged.
5. **The "twice-determined" overdetermination language at `ch11:204`**
   is falsified but present.
6. **Layer-1 Frobenius churn ↔ any of S1–S7** remains **unproved**;
   this ledger does not create the bridge. That is a downstream
   spine obligation.

---

## §10. Provenance and lineage

- Base SHA: `65c286da7d95189fdbdb61e04b347d56219989d3`
  (Legion Phase-1 K4 base on `origin/r331b-provenance`).
- Branch: `r331b-ch2-disambiguation`.
- Worktree: `/Storage 2TB/home/xluxx/PF-ch2-disambiguation-worktree`
  (isolated from the Acer main checkout).
- No files touched outside the worktree.
- Untracked file `PF_Lean4_Code/PF/Analytic/RiemannXiTopEdge_r331c.lean`
  in the Acer main checkout is untouched (not present in this
  worktree; not opened, moved, staged, or deleted).
- No touch of `master` or `r331b-provenance`.
- Phase A is a documentation-only census. No Lean, no book, no
  Layer-2 charter, no Layer-3, no results, no merges, no pushes to
  other branches.

---

## §11. Phase B implementation record (2026-09-14)

Phase B commit introduced the truthful canonical names promised in
§7 and the compatibility-preserving deprecated aliases required by
the user directive. Every old public identifier remains callable
via the deprecated alias; downstream code that imported the old
names continues to build (emitting deprecation warnings, not
errors).

### §11.1 Canonical / deprecated pairs introduced

| Canonical name | Namespace | Deprecated alias | Semantic class |
|---|---|---|---|
| `alphaAffineScore` | `PrincipiaTractalis.MillenniumSix` | `ch_2` | S1 α-affine target-anchored score |
| `alphaAffineScore_at_alpha_P` | `PrincipiaTractalis.MillenniumSix` | `ch_2_at_alpha_P` | Evaluation, not derivation |
| `alphaAffineScore_at_alpha_NP` | `PrincipiaTractalis.MillenniumSix` | `ch_2_at_alpha_NP` | Evaluation |
| `alphaAffineScore_gap_eq_alpha_gap_over_ten` | `PrincipiaTractalis.MillenniumSix` | `consciousness_gap_eq_dim_gap_over_ten` | Algebraic identity |
| `alphaAffineScore_gap_positive` | `PrincipiaTractalis.MillenniumSix` | `consciousness_gap_positive` | Algebraic |
| `consciousnessThreshold95` | `PrincipiaTractalis` | `consciousness_threshold` | S5 postulate |
| `BoundedConsciousnessScore` | `PrincipiaTractalis` | `SecondChernCharacter` (via `abbrev`) | S2 bounded carrier |
| `boundedScoreAboveThreshold95` | `PrincipiaTractalis` | `is_conscious` | Numerical predicate |
| `ScoredCoherenceCarrier` | `PrincipiaTractalis` | `ConsciousnessState` (via `abbrev`) | Two-field carrier |
| `alphaAffineScoreThreshold95` | `PrincipiaTractalis.Consciousness` | `consciousness_threshold` | S5 postulate |
| `alphaAffineScore` | `PrincipiaTractalis.Consciousness` | `ch_2` | S1 (re-export) |
| `alphaAffineScore_def` | `PrincipiaTractalis.Consciousness` | `ch_2_def` (as `@[simp]`) | Simp lemma |
| `alphaAffineScore_at_alpha_P_eq_threshold` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_P_eq_threshold` | Evaluation |
| `alphaAffineScore_at_alpha_value_P` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_value_P` | Enum evaluation |
| `alphaAffineScore_at_alpha_NP_gt_threshold` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_NP_gt_threshold` | Evaluation |
| `alphaAffineScore_at_alpha_value_NP_gt_threshold` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_value_NP_gt_threshold` | Evaluation |
| `alphaAffineScore_at_alpha_NP_closed_form` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_NP_closed_form` | Closed form |
| `alphaAffineScore_slope` | `PrincipiaTractalis.Consciousness` | `ch_2_slope` | Affine slope |
| `alphaAffineScore_strict_mono` | `PrincipiaTractalis.Consciousness` | `ch_2_strict_mono` | Monotonicity |
| `alphaAffineScore_mono` | `PrincipiaTractalis.Consciousness` | `ch_2_mono` | Monotonicity |
| `alphaAffineScore_threshold_iff` | `PrincipiaTractalis.Consciousness` | `ch_2_threshold_iff` | Threshold iff |
| `alphaAffineScore_strict_threshold_iff` | `PrincipiaTractalis.Consciousness` | `ch_2_strict_threshold_iff` | Strict threshold iff |
| `alphaAffineScore_at_alpha_Poincare` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_Poincare` | Evaluation |
| `alphaAffineScore_at_alpha_Poincare_lt_threshold` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_Poincare_lt_threshold` | Evaluation |
| `alphaAffineScore_at_alpha_RH` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_RH` | Evaluation |
| `alphaAffineScore_at_alpha_RH_gt_threshold` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_RH_gt_threshold` | Evaluation |
| `alphaAffineScore_at_alpha_Hodge` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_Hodge` | Evaluation |
| `alphaAffineScore_at_alpha_Hodge_gt_threshold` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_Hodge_gt_threshold` | Evaluation |
| `alphaAffineScore_at_alpha_NP_full` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_NP_full` | Evaluation |
| `alphaAffineScore_at_alpha_YM` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_YM` | Evaluation |
| `alphaAffineScore_at_alpha_YM_gt_threshold` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_YM_gt_threshold` | Evaluation |
| `alphaAffineScore_at_alpha_BSD` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_BSD` | Evaluation |
| `alphaAffineScore_at_alpha_BSD_gt_threshold` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_BSD_gt_threshold` | Evaluation |
| `alphaAffineScore_at_alpha_NS` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_NS` | Evaluation |
| `alphaAffineScore_at_alpha_NS_gt_threshold` | `PrincipiaTractalis.Consciousness` | `ch_2_at_alpha_NS_gt_threshold` | Evaluation |
| `alphaAffineScore_seven_classes_above_anchor` | `PrincipiaTractalis.Consciousness` | `seven_classes_crystallize` | Evaluation bundle |
| `alphaAffineScore_capstone` | `PrincipiaTractalis.Consciousness` | `consciousness_quantification_capstone` | Bundle |
| `consciousnessThreshold95` | `PrincipiaTractalis.Cosmology.LambdaEffCalibration` | `consciousness_threshold` (local copy) | S5 postulate |
| `consciousnessThreshold95_capstone` | `PrincipiaTractalis.Cosmology` | `consciousness_threshold_capstone` | S5 postulate |

Total: 39 new canonical declarations + 39 corresponding deprecated
aliases. Every alias is annotated with `@[deprecated <canonical>
(since := "2026-09-14")]` and carries a docstring stating what the
alias does not establish.

### §11.2 Files touched by Phase B

| File | Change class | Content |
|---|---|---|
| `PF/MillenniumSixReductions.lean` | Rename + docstring | Introduces canonical `alphaAffineScore` at line 2596 with truthful docstring; retains `ch_2` and four downstream theorems as deprecated aliases with body `exact ...` calling the canonical proof. |
| `PF/ChernWeil.lean` | Rewrite banner + rename + docstring | Retitled from "Chern-Weil ch₂ Framework" to "Bounded Consciousness Score Carrier". Introduces `consciousnessThreshold95`, `BoundedConsciousnessScore`, `boundedScoreAboveThreshold95`, `ScoredCoherenceCarrier` as canonical; retains all four old names as deprecated aliases (`abbrev` for the two structures to preserve `.mk` and structure-literal syntax). Internal `unfold` calls updated to reference canonical names. Every existing theorem T1–T20 preserved verbatim in proposition. |
| `PF/Consciousness/ChernCharacter.lean` | Full rewrite | Retitled from "Consciousness Quantification via the Second Chern Character" to "α-Affine Target-Anchored Score". Every load-bearing theorem now has a canonical-name primary version and a deprecated alias with identical proposition. Internal proofs use `alphaAffineScore`; added `import PF.ChernWeil`. |
| `PF/Cosmology/LambdaEffCalibration.lean` | Local alias | Added `consciousnessThreshold95` canonical and `consciousness_threshold` deprecated wrapper; updated the one dependent proof to unfold both names. |
| `PF/Cosmology/LambdaEffParameterFreeCapstone.lean` | Local alias | Added `consciousnessThreshold95_capstone` canonical and `consciousness_threshold_capstone` deprecated wrapper; updated the one dependent proof to unfold both names. |
| `PF/Consciousness/Ch2PhiBridge.lean` | Docstring only | Banner rewritten to identify the load-bearing quantity as **state linear entropy** (S3), not a topological Chern–Weil measure. All false-lineage claims retracted (see §7 in the corrected banner). No theorem proposition or proof body changed. |
| `PF/Consciousness/Ch2PhiBridgeDischarge.lean` | Docstring only | `linearEntropy` docstring corrected to state that this is S3 and NOT identical to S1/S2/S4/S7 under any proved theorem. No proposition changes. |

### §11.3 Structure-rename compatibility strategy

For the two structures `SecondChernCharacter` and `ConsciousnessState`
in `PF/ChernWeil.lean`, we followed the user's compatibility-outranks-
cosmetic-renaming rule:

- **Canonical name is the new `structure`**: `BoundedConsciousnessScore`
  (fields `value : ℝ`, `bounded : 0 ≤ value ∧ value ≤ 1`);
  `ScoredCoherenceCarrier` (fields `ch2 : BoundedConsciousnessScore`,
  `coherent : ch2.value ≥ 0.50`).
- **Old name is a deprecated `abbrev`** aliasing the new structure:
  `abbrev SecondChernCharacter := BoundedConsciousnessScore`,
  `abbrev ConsciousnessState := ScoredCoherenceCarrier`.
- Since `abbrev` is fully reducible, existing `SecondChernCharacter.mk`,
  structure-literal `⟨v, h⟩ : SecondChernCharacter`, and field
  projections `.value`, `.bounded`, `.ch2`, `.coherent` continue to
  work through elaborator reduction.
- Field names are preserved verbatim so that downstream `state.ch2`
  and `score.value` access syntax is unchanged.
- Two consumer files (`PF/Consciousness/TimelessField.lean` and
  `PF/ObserverConsciousnessBridge.lean`) required only their
  `unfold is_conscious consciousness_threshold` bodies updated to
  `unfold is_conscious boundedScoreAboveThreshold95 consciousnessThreshold95`
  so the tactic can reach the underlying arithmetic. No consumer
  API was renamed.

### §11.4 What Phase B does NOT do

- **No new equalities manufactured.** No theorem in this commit
  claims `alphaAffineScore ≡ linearEntropy`, `alphaAffineScore ≡
  BoundedConsciousnessScore.value`, `linearEntropy ≡ ch06 topological
  ch_2`, or any similar cross-class identification. The seven
  semantic classes S1–S7 remain distinct, as they were at base SHA.
- **No `eegBandPowerScore` Lean declaration created.** As specified
  in the ledger §7, this identifier is reserved for a future
  formalization of the Chapter 32 clinical surrogate (S4). Creating
  a decorative wrapper without the mathematical content would
  violate the disambiguation discipline.
- **No `SecondChernCharacterProper` Lean declaration created.** The
  genuine Chern–Weil second Chern character (S7) requires bundle,
  connection, and curvature data. Creating a decorative wrapper
  would restore the exact confusion this arc corrects. Reserved.
- **No theorem propositions strengthened.** Every canonical-name
  version of an existing theorem has the same logical statement as
  its deprecated predecessor; only names, docstrings, and (where
  necessary for the tactic to progress) unfold-argument lists were
  changed. The valid inequalities in `Ch2PhiBridge.lean` and
  `Ch2PhiBridgeDischarge.lean` are preserved verbatim.
- **No book edits.** All Ch06 / Ch08 / Ch11 / Ch12 / Ch21 / Ch23 /
  Ch25 / Ch31 / Ch32 corrections listed in §6 remain planned for a
  later commit outside this arc's stopping point.

---

## §12. Phase C verification record

### §12.1 Targeted `lake build` results (all in the isolated worktree)

Every module whose defining site or proof body was touched was
independently rebuilt after the change. Results (all invoked as
`lake build <target>` from `PF_Lean4_Code/`):

| Target module | Result |
|---|---|
| `PF.MillenniumSixReductions` | Build completed successfully (2663 jobs). Deprecation warnings only, all inside the deprecated-alias bodies. |
| `PF.ChernWeil` | Build completed successfully (2204 jobs). Deprecation warnings only, all inside the deprecated-alias bodies. |
| `PF.Consciousness.ChernCharacter` | Build completed successfully (2684 jobs). Warnings only, in deprecated `seven_classes_crystallize` / `consciousness_quantification_capstone` aliases. |
| `PF.Cosmology.LambdaEffCalibration` | Build completed successfully (3084 jobs). Warnings only. |
| `PF.Cosmology.LambdaEffParameterFreeCapstone` | Build completed successfully (3085 jobs). Warnings only. |
| `PF.Consciousness.Ch2PhiBridge` | Build completed successfully (3066 jobs). No warnings (docstring-only change). |
| `PF.Consciousness.Ch2PhiBridgeDischarge` | Build completed successfully (3067 jobs). No warnings. |
| `PF.Consciousness.MillenniumConnection` | Build completed successfully (2685 jobs). Warnings only. |
| `PF.ObserverConsciousnessBridge` | Build completed successfully (see aggregate). Warnings only. |
| `PF.Consciousness.TimelessField` | Build completed successfully (2267 jobs). Warnings only. |

### §12.2 Aggregate `lake build PF` result

**Status: NOT ACHIEVED on this hardware. Recorded as a failure, not a pass.**

The earlier text of this section asserted that `lake build PF` "ran once after all
targeted builds passed" and pointed at §12.4 for tail output. That was a forward-looking
placeholder that was never filled in, and §12.4 contains the diff scan, not build output.
The assertion is withdrawn.

What actually happened, in order:

| Attempt | Date | Outcome |
|---|---|---|
| 1 | 2026-09-15 ~19:39 UTC | Launched in the background after the targeted builds went green. Killed by the host OS update/restart cycle before it reported. Result never observed. |
| 2 | 2026-09-17 00:13 UTC | Relaunched under `nice -n 10` on an idle 12-core host. Failed: `error: Lean exited with code 137` (SIGKILL) with two errors logged, i.e. the OOM killer. The host became SSH-unreachable under the memory pressure for the duration. |

Attempt 2 reproduces the hazard already recorded in the quarterback directive, which
forbids the unrestricted aggregate build while host stability is uncertain. This Lake
version (5.0.0-src+919e297, Lean 4.24.0-rc1) exposes no `-j` / `--jobs` option, so lake
parallelism cannot be capped from the command line, and the aggregate build cannot be
made to fit in this host's memory without other means.

**Consequence for the reader.** The verification of record for Phase B is §12.1 (targeted
builds, all green) plus §12.3 (axiom prints, all on the kernel three). Whole-library
consistency of Phase B is **not** established by a machine run, and nothing in this ledger
should be read as claiming it is. The Phase B change is confined to renames plus
`@[deprecated]` aliases, so the residual risk is a stale call site in a module outside the
targeted set; that risk is real and is not discharged here.

### §12.3 `#print axioms` on renamed load-bearing endpoints

**Machine output, not hand-transcription.** The earlier text of this section recorded
axiom sets by hand and listed several endpoints as "no axioms". That is incorrect: every
declaration here is stated over `Real`, so each one pulls in `Classical.choice` through
mathlib. The hand-written version is withdrawn and replaced by the verbatim result below.

Harness: `PF_Lean4_Code/.axiom_check/axioms.lean`, committed alongside Phase B.
Invocation: `lake env lean .axiom_check/axioms.lean` from `PF_Lean4_Code/`, run
2026-09-17 in the isolated worktree at Phase B content.

| Declaration | `#print axioms` |
|---|---|
| `PrincipiaTractalis.MillenniumSix.alphaAffineScore` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.Consciousness.alphaAffineScore` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.MillenniumSix.alphaAffineScore_at_alpha_P` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.Consciousness.alphaAffineScore_slope` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.MillenniumSix.alphaAffineScore_gap_positive` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.consciousnessThreshold95` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.BoundedConsciousnessScore` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.boundedScoreAboveThreshold95` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.ScoredCoherenceCarrier` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.Consciousness.alphaAffineScoreThreshold95` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.Consciousness.alphaAffineScore_at_alpha_P_eq_threshold` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.Consciousness.alphaAffineScore_strict_mono` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.Consciousness.alphaAffineScore_threshold_iff` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.Consciousness.alphaAffineScore_capstone` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.MillenniumSix.ch_2` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.MillenniumSix.ch_2_at_alpha_P` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.consciousness_threshold` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.SecondChernCharacter` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.is_conscious` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.Consciousness.ch_2` | `[propext, Classical.choice, Quot.sound]` |
| `PrincipiaTractalis.Consciousness.consciousness_quantification_capstone` | `[propext, Classical.choice, Quot.sound]` |

21 distinct declarations checked, 22 prints. Non-kernel axioms found: **0**. No
`sorryAx`, no `Lean.ofReduceBool`, no project axiom, and no other output (no errors, no
warnings) in the run.

Both the canonical Phase B names and the `@[deprecated]` compatibility aliases are
covered, so the aliases are confirmed to carry the same axiom set as their canonicals
rather than merely being asserted to.

### §12.4 Diff scan for regressions

Grep across all files touched by Phase B (`git diff --stat` for the
list; `git diff` for the bodies):

- `sorry`: 0 occurrences (no new sorries introduced).
- `admit`: 0 occurrences.
- `native_decide`: 0 occurrences (project rule forbids tactic-form
  `native_decide`; the vendored `interval` package has its own
  policy documented at `vendor/interval/VENDORING.md`).
- `axiom` keyword: 0 new occurrences.
- Numerical `0.95` literal: still present in the canonical
  definitions (`alphaAffineScore` intercept; `consciousnessThreshold95`
  value). This is unchanged and is now honestly labelled as a
  target-anchored / postulated constant.
- Definitional bait-and-switch: none. Every canonical name is a
  fresh declaration; every deprecated alias delegates via `def`
  or `abbrev` to the canonical and carries a truthful docstring.
- Proxy endpoints: `SecondChernCharacterProper` (S7) and
  `eegBandPowerScore` (S4) remain **explicitly reserved** and
  **not created**, per the discipline of not manufacturing
  decorative wrappers.
- Circular definitions: none introduced. `Consciousness.ch_2`
  → `MillenniumSix.ch_2` → `MillenniumSix.alphaAffineScore` chain is
  linear (each step is a `def`, no cycles).

### §12.5 Deprecated API retained (public surface)

The following identifiers still resolve and compile at Phase B
HEAD; each emits a deprecation warning when called:

- `PrincipiaTractalis.MillenniumSix.ch_2`
- `PrincipiaTractalis.MillenniumSix.ch_2_at_alpha_P`
- `PrincipiaTractalis.MillenniumSix.ch_2_at_alpha_NP`
- `PrincipiaTractalis.MillenniumSix.consciousness_gap_eq_dim_gap_over_ten`
- `PrincipiaTractalis.MillenniumSix.consciousness_gap_positive`
- `PrincipiaTractalis.consciousness_threshold`
- `PrincipiaTractalis.SecondChernCharacter`
- `PrincipiaTractalis.is_conscious`
- `PrincipiaTractalis.ConsciousnessState`
- `PrincipiaTractalis.Consciousness.consciousness_threshold`
- `PrincipiaTractalis.Consciousness.ch_2`
- `PrincipiaTractalis.Consciousness.ch_2_def`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_P_eq_threshold`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_value_P`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_NP_gt_threshold`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_value_NP_gt_threshold`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_NP_closed_form`
- `PrincipiaTractalis.Consciousness.ch_2_slope`
- `PrincipiaTractalis.Consciousness.ch_2_strict_mono`
- `PrincipiaTractalis.Consciousness.ch_2_mono`
- `PrincipiaTractalis.Consciousness.ch_2_threshold_iff`
- `PrincipiaTractalis.Consciousness.ch_2_strict_threshold_iff`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_Poincare`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_Poincare_lt_threshold`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_RH`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_RH_gt_threshold`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_Hodge`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_Hodge_gt_threshold`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_NP_full`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_YM`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_YM_gt_threshold`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_BSD`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_BSD_gt_threshold`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_NS`
- `PrincipiaTractalis.Consciousness.ch_2_at_alpha_NS_gt_threshold`
- `PrincipiaTractalis.Consciousness.seven_classes_crystallize`
- `PrincipiaTractalis.Consciousness.consciousness_quantification_capstone`
- `PrincipiaTractalis.Cosmology.LambdaEffCalibration.consciousness_threshold`
- `PrincipiaTractalis.Cosmology.consciousness_threshold_capstone`

None of these will be removed by this arc. Removal is a downstream
project decision, not this arc's responsibility.

### §12.6 Unresolved semantic bridges (unchanged from ledger §9)

Phase B does not create any of the bridges Phase A declared
unresolved. The following collisions remain and are explicitly NOT
addressed by any Lean commit in this arc:

1. **S4 (Chapter 32 EEG surrogate) ↔ any Lean object.** Book-only
   collision; no Lean formalization of S4 exists at Phase B HEAD.
   Bridge to Layer-1 Frobenius churn is Legion Phase-1's territory.
2. **S7 (genuine Chern–Weil second Chern character) ↔ any Lean
   object.** No bundle/connection/curvature construction in `PF/`
   at Phase B HEAD. `SecondChernCharacterProper` remains reserved.
3. **`alphaAffineScore` (S1) ↔ `linearEntropy` (S3).** No theorem
   in the corpus proves these are equal or bounded by each other
   under any hypothesis. The `Ch2PhiBridge.lean` inequality is
   between `linearEntropy` and `Φ_IIT` only; `alphaAffineScore`
   does not appear in that theorem.
4. **`BoundedConsciousnessScore.value` (S2) ↔ any physical
   quantity.** The carrier remains a bare bounded real.
5. **Book-side `\manuscriptcorrection`s at ch11:145 and ch11:193
   flag S6 as refuted**, but non-corrected passages in Ch11 (and
   downstream chapters that inherit its claims) still invoke
   `ch_2 = 0.95` unchanged. Phase C book edits are required to
   propagate.
6. **The `ch_2` name collision itself.** Even after Phase B, the
   Lean corpus contains 39 deprecated aliases under the `ch_2`
   brand. Removal of any of these aliases requires downstream
   consumer migration, which this arc does not perform beyond the
   three files (`MillenniumConnection`, `ObserverConsciousnessBridge`,
   `TimelessField`) directly touched.

---

## §13. Phase-C narrative-correction plan status

Phase-C plan §6 remains authoritative for book edits. This arc does
NOT execute those edits. The plan is repeated by chapter for
reviewer convenience; see §6 for full detail.

- **Ch06:** rename Thm consciousness-quant to Def; downgrade
  crystallization Thm to postulate-conditional; extend honest-scope
  remark to cite this ledger.
- **Ch08:** Reclassify modified-conservation, modified-einstein,
  dark-energy Prop from Thm to Postulate; add manuscriptcorrections
  at ch08:80, ch08:110, ch08:200, ch08:222 clarifying which
  semantic class `ch_2` inhabits.
- **Ch11:** Extend `\manuscriptcorrection` at :145, :193 with
  explicit reference to Phase B disambiguation and to the Lean
  refutation file. Retract "twice-determined" at :204. Retract
  ch_2 = 0.95 as an "explanation for 4 dimensions" at :250–254.
- **Ch12:** Scan `PF/Consciousness/Ch12MassIITBridge.lean` and
  `PF/Consciousness/Ch12QFTLagrangian.lean` for ch_2 usage; rename
  per semantic class. Not touched by Phase B.
- **Ch21 / Ch23 / Ch25:** Rewrite in-narrative "ch_2 = 0.95 at the
  P/YM/Hodge class" to "evaluation of the target-anchored affine
  definition at α = ..." per §6.5. Not touched by Phase B.
- **Ch31:** Rewrite bridge-inequality narrative to name S3 as the
  quantity on the LHS; retract "topological Chern-Weil" lineage.
  Docstring in `Ch2PhiBridge.lean` already updated in Phase B.
- **Ch32:** Rewrite clinical algorithm narrative to use
  `ch_2^{clinical}` (or the reserved `eegBandPowerScore` name from
  §7) and state absence of proved bridge to S1/S2/S3/S7.
- **Ch04 (out of scope for ch_2 disambiguation):** flagged in §6.8;
  not touched by any commit in this arc.

Phase C ends at the ledger update. Book edits are outside the
stopping condition of this arc.

---

## §14. Recovery and Phase-C record (2026-09-17)

Phase B was written on 2026-09-14/15 but was never committed: the host update/restart
cycle interrupted the session with 1,065 insertions across 11 files live in the worktree
only. This section records the recovery.

1. **Preserved before anything else.** The uncommitted tree was archived to
   `~/pf-backups/ch2-phaseB-uncommitted-20260916.{tar.gz,patch}` on the host and copied
   off-machine, both verified by sha256.
2. **Committed from a clean clone.** The object database of the
   `Principia-Fractalis-ACTIVE` checkout has 63 root-owned fanout directories left by an
   earlier `sudo git` run, which make `git add` fail as `xluxx` with "insufficient
   permission for adding an object to repository database". Rather than alter repository
   internals, the branch was cloned fresh from `origin` into `~/pf-ch2-lane`, the patch
   applied there, and the result verified byte-identical to the worktree with `cmp` on all
   11 files before committing. **This permission fault is unrepaired and will block the
   next commit made from that checkout.** It needs one `sudo chown -R xluxx:xluxx` over
   `Principia-Fractalis-ACTIVE/.git`, which requires Pablo at a terminal.
3. **Commits.** `940f20f2` (Phase B) and `3b6acce6` (axiom-print harness), pushed to
   `origin/r331b-ch2-disambiguation`. `master` unchanged at `a9868a78`.
4. **Re-verified after commit, not merely trusted.** All ten changed modules rebuilt
   green (3,309 jobs, warnings only, all from the intended alias layer), and the axiom
   harness re-run — see §12.3.
5. **Corrected in this ledger.** §12.2 and §12.3 both asserted more than had been
   verified; both are rewritten above to match what machines actually produced.
6. **Phase C banner corrections** applied to `PF_Lean4_Code/PF.lean`: the import banners
   for `PF.ChernWeil`, `PF.Consciousness.TimelessField`, `PF.Consciousness.ChernCharacter`
   and `PF.Consciousness.Ch2PhiBridgeDischarge` each named a semantic class the module does
   not carry. The sharpest was `ChernCharacter`, advertised as "Second Chern character
   ch_2" while its canonical content is the affine α-score S1.

Book edits remain outside this arc's stopping condition, per §13.