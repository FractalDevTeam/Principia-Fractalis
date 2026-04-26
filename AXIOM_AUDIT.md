# Lean 4 Axiom Audit — PF_Lean4_Code/PF/

*As of 2026-04-26, commit `76c7699` and post-rev-2 verification updates. **8 axioms** remain, 0 sorries.*

The NUM category is now empty — `log_3_bounds` was eliminated via direct n=60 Taylor at x=2/3, with `simp [Finset.sum_range_succ, ...]` + `norm_num` handling the 60-term sum.

Each axiom is one of:
- **CLASSIC** — Classical theorem from analysis/probability literature.
- **LOAD-BEARING PLACEHOLDER** — Trivializing would break other proofs.
- **BOOK-CORE** — Stated as a book theorem; represents substantive math claim.
- **NEEDS REDESIGN** — Independent verification has shown the axiom statement is false under the surrounding definitions; retained as a formal placeholder until the redesigned object lands.

## ⚠ Post-rev-2 verification finding (2026-04-26)

Independent symbolic verification (sympy + 40-digit mpmath), kernel-transversality analysis, and external literature cross-check (Baladi, Ruelle, Connes, Lapidus, Mayer) have together established that **`T3_self_adjoint_conj` (entry 5) is FALSE under the manuscript's own definitions of T̃₃ and ⟨·,·⟩**, not merely unproven. In particular:

- ⟪T₃ x, x⟫ ≈ −0.110 + 0.162i — a self-adjoint operator must yield a real diagonal.
- ⟪T₃ f, g⟫ − ⟪f, T₃ g⟫ ≈ 0.096 + 0.188i for f = x, g = x² (40-digit precision; not roundoff).
- The chosen weight √(bx/(x+k)) is the Frobenius-Perron symmetrizer for Lebesgue dx, not for the log-weighted measure dx/x.
- The naive correction (replace weight with √((x+k)/(bx))) ALSO fails: branches y_k(x) = (x+k)/b are non-involutive, so the kernel support is geometrically asymmetric.
- The asserted phase identity "ω̄_k = ω_{2−k}" (book ch20:204) is false for ω = {1, −i, −1}.
- No published transfer-operator-on-L²(dx/x) construction matches Pabs's setup; the (1, −i, −1) phase pattern has no precedent in the literature.

The axiom is **retained** (not deleted) so downstream proofs in `SpectralBijection.lean` continue to typecheck. They are now to be read as conditional on a future redesigned T₃ for which an analogous self-adjointness statement holds. Recovery requires a structural redesign (symmetrize via (T+T*)/2, augment with expanding-direction branches, change measure, or downgrade Theorem 20.2 to a conjecture). Tracked in `RESEARCH_ROADMAP.md`.

The **other 7 axioms are unaffected** by this finding.

## The 8

### 1. `bochner_minlos_existence` (CLASSIC)
- **File**: `PF/BochnerMinlos.lean:81`
- **Statement**: ∀ CharacteristicFunctional C, ∃ probability measure μ on S'(R^d) with Fourier = C
- **Why hard**: Classical Minlos theorem. Needs full Kolmogorov extension on nuclear spaces.
- **Book reference**: Chapter 23, Minlos Theorem

### 2. `bochner_minlos_uniqueness` (CLASSIC)
- **File**: `PF/BochnerMinlos.lean:93`
- **Statement**: Two measures with same Fourier transform are equal
- **Why hard**: Fourier-transform injectivity on measures

### 3. `finite_dim_bochner` (CLASSIC)
- **File**: `PF/CylindricalMeasures.lean:155`
- **Statement**: ∀ PD+normalized+continuous C on ℝⁿ, ∃! probability measure with Fourier = C
- **Why hard**: Not in mathlib. Would be substantial mathlib contribution.

### 4. `LogWeightedL2.inner` (LOAD-BEARING PLACEHOLDER)
- **File**: `PF/TransferOperator.lean:70`
- **Statement**: signature `LogWeightedL2 → LogWeightedL2 → ℂ`
- **Why cannot trivialize**: defining as `fun _ _ => 0` would make all downstream self-adjointness proofs vacuously true
- **Real elimination**: construct log-weighted Lebesgue integral ∫₀¹ f̄·g dx/x

### 5. `T3_self_adjoint_conj` (NEEDS REDESIGN — was BOOK-CORE)
- **File**: `PF/TransferOperator.lean:221`
- **Statement**: ∀ f g, ⟪T₃.apply f, g⟫ = ⟪f, T₃.apply g⟫
- **Book reference**: Chapter 20, Theorem 20.2 (under revision)
- **Depends on**: `LogWeightedL2.inner`
- **Status**: ⚠ Post-rev-2 verification (2026-04-26) established this is FALSE under the current operator and inner-product definitions. See "Post-rev-2 verification finding" section above. Retained as formal placeholder; downstream `SpectralBijection` proofs are conditional on a future redesigned T₃.

### 6. `turingTimeComplexity` (LOAD-BEARING PLACEHOLDER)
- **File**: `PF/TuringEncoding/Complexity.lean:57`
- **Statement**: signature `(Γ Λ σ : Type) → TM2.Machine Γ Λ σ → BinString → ℕ`
- **Why cannot trivialize**: constant 0 would prove P = NP against the spectral-gap theorem
- **Real elimination**: parameterize or construct from TM2 stepping semantics

### 7. `p_eq_np_spectrum_collapse` (BOOK-CORE)
- **File**: `PF/TuringEncoding/Operators.lean:191`
- **Statement**: `ClassP = ClassNP → λ₀_P = λ₀_NP`
- **Book reference**: Chapter 21 (core P vs NP bridge)

### 8. `operator_collapse_hypothesis` (BOOK-CORE)
- **File**: `PF/P_NP_Complete_Proof.lean:175`
- **Statement**: (∀ L vtime, IsInNP vtime → ∃ t, IsInP t) → α_NP = α_P
- **Book reference**: Chapter 21, Theorem 21.3

## Summary by category

| Category | Count | Axioms |
|---|---|---|
| NUM | 0 | (all eliminated 2026-04-24) |
| CLASSIC | 3 | bochner_minlos_existence/uniqueness, finite_dim_bochner |
| LOAD-BEARING PLACEHOLDER | 2 | LogWeightedL2.inner, turingTimeComplexity |
| BOOK-CORE | 2 | p_eq_np_spectrum_collapse, operator_collapse_hypothesis |
| NEEDS REDESIGN | 1 | T3_self_adjoint_conj (post-rev-2 verification finding) |

## Counterfactual: where we started

Beginning of rev2 cycle (2026-04-22 early session): 41 Lean axioms in PF/.

Tonight's 32 eliminations (late session commits, ordered by method):

**Proven as genuine theorems (14):**
- sqrt2_in_interval_ultra, phi_in_interval_ultra
- sqrt2_in_interval_10digit, sqrt5_in_interval_10digit, phi_in_interval_10digit (new supporting theorems)
- Q_4_ge_Q_larger, Q_decreasing_from_4
- pos_def_hermitian (via strengthened IsPositiveDefinite definition)
- pos_def_normalized_bounded
- radix_economy_max_at_exp1
- lambda_P_lower_certified, lambda_P_upper_certified
- lambda_NP_lower_certified, lambda_NP_upper_certified
- lambda_0_P_precise, lambda_0_NP_precise

**Deleted as latently unsound (4):**
- empty_tape_bound (claimed log(2^s·3^h) ≤ 0, false)
- characteristic_cylindrical_round_trip (contradicted CharacteristicFunctional.normalized field)
- cylindrical_measure_fourier_is_characteristic (same pattern)
- nuclearity_essential (contradicted trivial NuclearSpace witness)

**Deleted as unused dead code (3):**
- prime_bound, log_conversion (unused entirely)
- axiom_head_and_tape_eq (forward-declaration pattern; consumers also unused)

**Promoted to structure fields (4):**
- TestGaugeField.instAddCommGroup, TestGaugeField.instModule (via Pi-type refactor)
- embedding_strictly_monotone (→ TimelessFieldTorus.embedding_mono)
- shell_has_natural_frequency (→ CurvatureShell.alpha_natural)

**Proven with explicit placeholder caveats (8) — Yang-Mills cluster:**
- yang_mills_4d_gaussian_valid, yang_mills_positive_definite, yang_mills_continuous
- yang_mills_construction_complete
- gauge_field_space_nuclear
- FreeYangMillsGaussian.generatingFunctional (converted axiom → def)
- minlos_sigma_additivity
- gaussian_is_characteristic (via 3 new GaussianCharacteristic fields)

## Major scientific findings

1. **Four latent unsoundness bugs** in the pre-session formalization (the "Deleted as latently unsound" group above). A referee would catch all four.
2. **`IsPositiveDefinite` definition was weaker than standard** — only required `.re ≥ 0`, not full real-and-nonneg. Strengthened during this session.
3. **Yang-Mills `CovarianceOperator.quadraticForm` is a placeholder `:= 0`**. All YM-cluster theorems are honest about this in their docstrings and in `rev2` Chapter 23 LaTeX.
4. **One parallel unsoundness in Coq** (characteristic_cylindrical_round_trip) caught and corrected.

## Supporting artifacts

- `PARITY_REPORT.md` — Lean ↔ Coq ↔ Lean4Lean axiom audit
- `Principia_Fractalis_master_folder_rev2/frontmatter/rev2_formalization_status.tex` — frontmatter referee summary
- Per-chapter "Formal verification (rev 2)" notes in ch07, ch21, ch23
- Full commit history on GitHub `FractalDevTeam/Principia-Fractalis` master
