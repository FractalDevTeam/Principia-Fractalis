# PF_L4L – Contracts and Axiom Usage

This document summarizes the **Lean4Lean** verification layer (referred to historically as `PF_L4L`) and how it uses the canonical Principia Fractalis axioms.

**Path note (post-rev-3, 2026-04-28).** The repository structure has evolved; path references below should be read with these substitutions:

| Older path label                               | Current canonical path                                                          |
|------------------------------------------------|---------------------------------------------------------------------------------|
| `PF_canonical/2_LEAN_SOURCE_CODE/`             | `PF_Lean4_Code/PF/` (canonical Lean 4 library; **1 axiom**, 0 sorries, 5626 jobs clean as of 2026-05-16)          |
| `PF_L4L/PF_L4L/`                               | `experimental/PF_L4L_future/PF_L4L/` (quarantined under experimental)            |

L4L is currently quarantined under `experimental/PF_L4L_future/` per the architectural decision recorded at `experimental/PF_L4L_future/L4L_ARCHITECTURAL_DECISION.md` (2026-04-28, Path B selected: preserve verification-only design intent + canonical axiom count). The `lake build` command at the repository root refers EXCLUSIVELY to the canonical `PF_Lean4_Code/PF/`; an explicit `cd experimental/PF_L4L_future && lake build` is required to build L4L. CI does not currently run L4L's build. *Note: this document and L4L's tag system were authored when the canonical library had 8 axioms; the canonical library now has 1, with 7 axioms retired across the rev-2-finale and May 2026 elimination arcs. The axiom-tag taxonomy below remains pedagogically useful for the historical record.*

The substantive content of this document — the L4L axiom-tag classification of canonical Principia Fractalis axioms — remains valid for the L4L layer when restored.

- Canonical Lean axioms: `PF_Lean4_Code/PF/**`
- PF_L4L contracts and audit: `experimental/PF_L4L_future/PF_L4L/**`
- **PF_L4L introduces no new `axiom`s**. It only references and classifies existing canonical axioms.

---

## 1. Axiom tags (`PFAxiomTag`)

**File:** `PF_L4L/PF_L4L/Core/AxiomAudit.lean`

PF_L4L defines the following tags to group canonical axioms:

- `P_vs_NP_prime_encoding`
- `P_vs_NP_resonance_spectrum`
- `P_vs_NP_numeric_certificates`
- `UniversalFramework_consciousness`
- `RH_operator_axioms`
- `YM_pillar_axioms`
- `BSD_pillar_axioms`

The predicate

```lean
uses_axiom (tag : PFAxiomTag) : Prop
```

is defined by matching on each tag and asserting trivial equalities
(e.g. `nthPrime = nthPrime`) involving the **canonical** PF constants. This makes the dependency **explicit** in a way that Lean can inspect, while adding no new content.

---

## 2. Tag meanings

### 2.1 P_vs_NP_prime_encoding

Complexity/encoding side of the P vs NP pillar.

- Canonical axioms referenced:
  - `nthPrime`, `nthPrime_is_prime`, `nthPrime_increasing`, `nthPrime_zero`, `nthPrime_one`
  - `encodeConfig_injective`, `nat_log`
  - `encodeConfig_polynomial_time`, `encodeConfig_growth_bound`

### 2.2 P_vs_NP_resonance_spectrum

Resonance/spectral interface axioms for P vs NP.

- Canonical axioms referenced:
  - `resonance_determines_spectrum`
  - `np_not_p_requires_certificate`
  - `p_eq_np_iff_zero_gap`

### 2.3 P_vs_NP_numeric_certificates

Numeric and interval certificates used by the P vs NP spectral-gap analysis.

- Canonical axioms referenced (in `IntervalArithmetic.lean`):
  - `sqrt2_in_interval_ultra`, `phi_in_interval_ultra`
  - `sqrt2_lower`, `sqrt2_upper`, `phi_lower`, `phi_upper`
  - `phi_plus_quarter_gt_sqrt2`, `sqrt2_lt_1415`, `phi_gt_16`
  - `lambda_P_lower_certified`, `lambda_P_upper_certified`
  - `lambda_NP_lower_certified`, `lambda_NP_upper_certified`
  - `lambda_0_P_precise`, `lambda_0_NP_precise`
  - `lambda_P_pi10_relation`, `lambda_NP_pi10_relation`

### 2.4 UniversalFramework_consciousness

Global consciousness/framework assumptions.

- Canonical axioms referenced (in `PF/ConsciousnessCore.lean`):
  - `ch2_universal_threshold`
  - `ch2_P_vs_NP`
  - `ch2_RH`
  - `ch2_YM`
  - `ch2_BSD`

These summarize the ch₂ pattern across all four PF pillars.

### 2.5 RH_operator_axioms

Operator-theoretic assumptions for the RH pillar.

- Canonical axioms referenced (in `PF/RH_Equivalence.lean`):
  - `LogHilbertSpace`
  - `T3_self_adjoint`
  - `T3_compact`
  - `eigenvalue_convergence_rate`
  - `T3_eigenvalues_real`
  - `eigenvalue_zero_bijection`
  - `spectral_bijection_iff_RH`

### 2.6 YM_pillar_axioms

QFT/measure-theoretic assumptions for the Yang–Mills pillar.

- Canonical axioms referenced (in `YM_Equivalence.lean` and related files):
  - `GaugeGroup`, `FieldStrength`, `standard_YM_action`, `mass_gap_property`
  - `R_f_at_alpha_2`, `resonance_coefficient`
  - `omega_critical_is_zero`, `omega_critical_is_first_zero`,
    `omega_critical_numerical_precision`, `mass_gap_numerical_value`
  - `fractal_YM_action`, `fractal_action_properties`
  - `NuclearSpace`, `minlos_theorem`, `YM_measure_exists`
  - `WilsonLoop`, `wilson_loop_expectation`, `string_tension_value`
  - `area_law_confinement`, `mass_gap_iff_YM`
  - `YM_perfect_consciousness`, `confinement_via_measurement`

### 2.7 BSD_pillar_axioms

Spectral and algorithmic assumptions for the BSD pillar.

- Canonical axioms referenced (in `PF/BSD_Equivalence.lean`):
  - `RationalPoints`, `algebraic_rank`, `trace_of_frobenius`, `conductor`
  - `L_function`, `L_function_order_at_1`
  - `BSD_strong_conjecture`, `BSD_proven_rank_0_1`
  - `fractal_L_function`, `T_E`, `T_E_self_adjoint`
  - `spectral_concentration`, `rank_equals_multiplicity`
  - `fractal_rank_algorithm_complexity`
  - `L_function_formula_iff_BSD`, `BSD_highest_consciousness`

---

## 3. Pillar-wise usage predicates

PF_L4L also defines convenience predicates describing which tags are used for each pillar:

```lean
uses_P_vs_NP_axioms (tag : PFAxiomTag) : Prop
uses_RH_axioms      (tag : PFAxiomTag) : Prop
uses_YM_axioms      (tag : PFAxiomTag) : Prop
uses_BSD_axioms     (tag : PFAxiomTag) : Prop
```

They are defined as simple disjunctions:

- `uses_P_vs_NP_axioms tag` iff
  - `tag = P_vs_NP_prime_encoding ∨`
  - `tag = P_vs_NP_resonance_spectrum ∨`
  - `tag = P_vs_NP_numeric_certificates ∨`
  - `tag = UniversalFramework_consciousness`.

- `uses_RH_axioms tag` iff
  - `tag = RH_operator_axioms ∨`
  - `tag = UniversalFramework_consciousness`.

- `uses_YM_axioms tag` iff
  - `tag = YM_pillar_axioms ∨`
  - `tag = UniversalFramework_consciousness`.

- `uses_BSD_axioms tag` iff
  - `tag = BSD_pillar_axioms ∨`
  - `tag = UniversalFramework_consciousness`.

These make the sharing of the global consciousness framework across all four pillars completely explicit.

---

## 4. Example: ch₂ pillars band lemma

At the end of `Core/AxiomAudit.lean`, PF_L4L provides a convenience lemma:

```lean
lemma ch2_pillars_in_band_PF_L4L (c : ℝ)
  (h : c = ch2_P_vs_NP ∨ c = ch2_RH ∨ c = ch2_YM ∨ c = ch2_BSD) :
  0.90 ≤ c ∧ c ≤ 1.25 :=
  PrincipiaTractalis.ch2_pillars_in_band c h
```

This simply re-exports the canonical `ch2_pillars_in_band` lemma to the PF_L4L namespace.

---

## 5. How to read PF_L4L as a referee

1. **PF_L4L does not add axioms.** All assumptions come from canonical files under `PF_canonical/2_LEAN_SOURCE_CODE`.
2. **Contracts** (e.g. `PF_L4L/Ch21/PNP.lean`, `Ch20/RH.lean`, `Ch23/YM.lean`, `Ch24/BSD.lean`) use the tags defined here to declare which groups of axioms they rely on.
3. **Axiom usage** for each pillar can be read via:
   - The contracts for that chapter.
   - The `uses_*_axioms` predicates.
   - The tag definitions in `uses_axiom` above.

Together with `README.md`, `AXIOM_AUDIT.md`, and `CHAPTER_MAP.md`, this gives a complete, machine-aligned picture of:

- Which axioms exist (canonical layer).
- How they are grouped (PFAxiomTag).
- Which pillar contracts depend on which groups (PF_L4L layer).
