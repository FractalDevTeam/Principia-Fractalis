# glimm_uhf_lean4_sidebar — Lean 4 source companion to the UHF paper

Companion to `Papers/glimm_uhf_lean4_2026-07-23.tex`.

The paper names its three headlines and the files that carry them. This
directory IS those files — the Lean 4 source itself — pinned at the
paper's HEAD so a reader can read the paper and the source in parallel.

## Pin (unchanged from the paper)

| | |
|---|---|
| HEAD | `91cc1a01` (2026-07-23) |
| Lean toolchain | `leanprover/lean4:v4.24.0-rc1` |
| mathlib commit | `eed770a434957369c6262aa3fb1d6426419016d4` |
| Repo | github.com/FractalDevTeam/Principia-Fractalis |
| Build | from `PF_Lean4_Code/`: `lake build PF` (4,472 jobs); `lake build` (8,930 jobs) |

The files in `lean/` are copies at this HEAD. To re-check against the
canonical source, checkout `91cc1a01` and diff.

## The three headlines

### 1. Faithfulness of the UHF trace
`lean/SubstrateCompletionFaithful.lean`, namespace
`PrincipiaTractalis.SubstrateCompletionFaithful`:

```lean
theorem UHF_trace_faithful (x : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) : x = 0
```

`#print axioms` →
`[propext, Classical.choice, Quot.sound]`

### 2. Simplicity of T∞ (Glimm, this algebra)
Same file:

```lean
theorem substrate_completion_simple_unconditional :
    ∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤
```

`#print axioms` →
`[propext, Classical.choice, Quot.sound]`

### 3. Uniqueness of the trace
`lean/SubstrateTraceUniqueness.lean`, namespace
`PrincipiaTractalis.SubstrateTraceUniqueness`:

```lean
theorem substrate_UHF_trace_unique (φ : TimelessFieldCompletion → ℂ)
    (hφ : IsTracialState φ) (x : TimelessFieldCompletion) :
    φ x = UHF_trace x
```

`#print axioms` →
`[propext, Classical.choice, Quot.sound]`

Zero project-level axioms. Zero `sorry`.

## Section-to-source map (paper → file)

| paper § | content | file |
|---|---|---|
| §2 | tower, limit, completion, instances | `SubstrateBase3Levels.lean`, `SubstrateBase3Embed.lean`, `SubstrateBase3Norm.lean`, `SubstrateBase3RingHom.lean`, `SubstrateDirectLimit.lean` |
| §3 | trace and soft properties | `SubstrateUHFTraceIsTracial.lean`, `SubstrateUHFTraceIsFaithful.lean`, `SubstrateUHFTraceIsPositive.lean`, `SubstrateUHFTraceIsStarPreserving.lean`, `SubstrateUHFTraceLipschitz.lean` |
| §4 (Cauchy–Schwarz) | | `SubstrateUHFTraceCauchySchwarz.lean` |
| §4 (null ideal) | | `SubstrateUHFTraceNullIdeal.lean` |
| §4 (Weyl averaging) | | `SubstrateMatrixUnitaryAveraging.lean` |
| §4 (direct-limit simplicity) | | `SubstrateDirectLimitSimplicity.lean` |
| §4 (four-fold equivalence) | | `SubstrateTraceDetectionAttempt.lean` |
| §5 (level expectation E_k) | | `SubstrateConditionalExpectation.lean` |
| §5 (2-norm contraction) | | `SubstrateCondExpContraction.lean` |
| §5 (operator-norm contraction) | | `SubstrateCondExpOpNorm.lean` |
| §5 (extension; faithfulness; simplicity) | | `SubstrateCompletionFaithful.lean` |
| §5 (uniqueness; factor capstone) | | `SubstrateTraceUniqueness.lean` |

## File manifest

20 files, 6,974 lines.

```
SubstrateBase3Levels.lean           # ternary tower M_{3^k}
SubstrateBase3Embed.lean            # A ↦ A ⊗ I_3 embeddings
SubstrateBase3Norm.lean             # operator norm per level
SubstrateBase3RingHom.lean          # ring-hom version of the embedding
SubstrateDirectLimit.lean           # pre-C* inductive limit

SubstrateUHFTraceIsTracial.lean         # τ_UHF is tracial
SubstrateUHFTraceIsFaithful.lean        # pre-level faithfulness
SubstrateUHFTraceIsPositive.lean        # τ_UHF ≥ 0 on x*x
SubstrateUHFTraceIsStarPreserving.lean  # τ(x*) = conj τ(x)
SubstrateUHFTraceLipschitz.lean         # τ_UHF is uniformly continuous

SubstrateUHFTraceCauchySchwarz.lean     # |τ(x*y)|² ≤ τ(x*x) τ(y*y)
SubstrateUHFTraceNullIdeal.lean         # trace-null set is an ideal
SubstrateMatrixUnitaryAveraging.lean    # Weyl averaging per level
SubstrateDirectLimitSimplicity.lean     # simplicity of the pre-C* limit
SubstrateTraceDetectionAttempt.lean     # 4-fold equivalence: trace-detects ↔ simple

SubstrateConditionalExpectation.lean    # E_k : T∞ → ι(M_{3^k})
SubstrateCondExpContraction.lean        # ‖E_k x‖₂ ≤ ‖x‖₂
SubstrateCondExpOpNorm.lean             # ‖E_k x‖_op ≤ ‖x‖_op

SubstrateCompletionFaithful.lean        # HEADLINE 1 & 2: faithfulness + simplicity
SubstrateTraceUniqueness.lean           # HEADLINE 3: trace uniqueness
```

## Reader's path

1. Read the paper up through §4 to understand the goal: UHF algebra +
   faithful + unique + simple.
2. For the formalization, follow files in the order above (left-to-right
   in the manifest). Each file imports only its predecessors.
3. The three headlines live in the last two files. Open them, scroll to
   the `theorem` lines quoted above, and read their proofs. Each is 10–20
   lines using landed primitives.

## What this directory is not

It is not a reproducible build on its own — the files depend on mathlib
and on their siblings in the full repo. To rebuild, use the full
`PF_Lean4_Code/` directory at HEAD `91cc1a01`. The sidebar's purpose is
reading, not building.
