# COMPLETION-SIDE WITNESS — statement cards for `substrate3Inf_TimelessFieldCompletion`

**Purpose.** Statement-card decomposition (per `FLT_LESSONS_FOR_PF_2026-09-08.md` §1) of the SubstrateRigidity scratch's `substrate3Inf_TimelessFieldCompletion` witness. Every field is proved on the specific `A = TimelessFieldCompletion` case using **only Pablo's existing kernel-verified ingredients** — no C1/C2/C3/C4 dependency, no new mathematics.

**Landing this arc alone closes half of `T_infinity_rigidity`:** it establishes that `TimelessFieldCompletion` IS a `Substrate3Inf`. The other half (any `Substrate3Inf A` is *-iso to the completion) needs C1–C4.

**Sequencing:** these five cards can be landed **in parallel with C1–C4**. They have no cross-dependency with the general-A Elliott back-and-forth. Farmable independently.

---

## CARD W1 — the tower

**Lean signature (immutable):**
```lean
noncomputable def substrateTFCtower : ℕ → StarSubalgebra ℂ TimelessFieldCompletion
```

**Semantic obligation:** For each `k`, produce the *-subalgebra of `TimelessFieldCompletion` whose carrier is (the image of) `substrateLevelToTimelessField k` — the isometric embedding of `M_{3^k}(ℂ)` into the completion.

**Proof sketch (Lean-ready):**
```lean
noncomputable def substrateTFCtower (k : ℕ) : StarSubalgebra ℂ TimelessFieldCompletion :=
  (substrateLevelToTimelessField k).range
```
using the fact that Pablo's `substrateLevelToTimelessField k : Matrix (Fin (3^k)) (Fin (3^k)) ℂ →⋆ₐ[ℂ] TimelessFieldCompletion` is a `StarAlgHom` (per `SubstrateTimelessFieldNorm.lean:*`) whose `.range` is a `StarSubalgebra`.

**Pablo primitives used:** `substrateLevelToTimelessField_opNorm_eq` (norm-preserving embedding, `SubstrateTimelessFieldNorm.lean:*`).

**Mathlib primitives:** `StarAlgHom.range` (`Mathlib/Algebra/Star/Subalgebra.lean:825`).

**Dependencies:** none.

**Read-back prompt (§H):** *"What is `substrateTFCtower 0`? What is `substrateTFCtower 1`? Are they contained in `TimelessFieldCompletion`?"*

---

## CARD W2 — matrix isomorphism per level

**Lean signature (immutable):**
```lean
lemma substrateTFCtower_matrix (k : ℕ) :
    Nonempty (substrateTFCtower k ≃⋆ₐ[ℂ]
              Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
```

**Semantic obligation:** For each `k`, exhibit a `StarAlgEquiv` between `substrateTFCtower k` (the range of the level-k embedding) and the source `M_{3^k}(ℂ)`.

**Proof sketch:** Since `substrateLevelToTimelessField k` is injective (implied by `_opNorm_eq` — an isometry is injective), the map factors as an isomorphism from the source onto its range. Use `StarAlgEquiv.ofInjective` at `Mathlib/Algebra/Star/Subalgebra.lean:~862`.

```lean
lemma substrateTFCtower_matrix (k : ℕ) :
    Nonempty (substrateTFCtower k ≃⋆ₐ[ℂ]
              Matrix (Fin (3^k)) (Fin (3^k)) ℂ) := by
  refine ⟨(StarAlgEquiv.ofInjective (substrateLevelToTimelessField k) ?_).symm⟩
  exact (Isometry.of_dist_eq (fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, substrateLevelToTimelessField_opNorm_eq]
  )).injective
```

**Pablo primitives used:** `substrateLevelToTimelessField_opNorm_eq`.

**Mathlib primitives:** `StarAlgEquiv.ofInjective`, `Isometry.injective`.

**Dependencies:** W1.

**Read-back prompt:** *"Is `substrateTFCtower_matrix 0` a nontrivial statement (given `M_{3^0} = M_1 = ℂ`)? What does the iso look like on `M_1 = ℂ`?"*

---

## CARD W3 — monotonicity of the tower

**Lean signature (immutable):**
```lean
lemma substrateTFCtower_mono : ∀ k, substrateTFCtower k ≤ substrateTFCtower (k+1)
```

**Semantic obligation:** For each `k`, the range of the level-k embedding is a *-subalgebra of the range of the level-(k+1) embedding.

**Proof sketch:** The commuting square `substrateLevelToTimelessField (k+1) ∘ substrateRingHomIter k (k+1) _ = substrateLevelToTimelessField k` (from the directed-system definition) gives the range inclusion directly: every element of the range of level-k is `substrateLevelToTimelessField k x = substrateLevelToTimelessField (k+1) (embed x)`, so it lies in the range of level-(k+1).

```lean
lemma substrateTFCtower_mono (k : ℕ) : substrateTFCtower k ≤ substrateTFCtower (k+1) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨substrateRingHomIter k (k+1) (Nat.le_succ k) x, ?_⟩
  -- commuting square identity from the directed-system definition
  exact substrateLevelToTimelessField_commute k (k+1) (Nat.le_succ k) x
```

(name `substrateLevelToTimelessField_commute` is the expected commuting-square lemma; verify FQN in the source — likely exists near `substrateRingHomIter_opNorm_eq`.)

**Pablo primitives used:** the commuting square from `SubstrateTimelessFieldNorm.lean` directed-system machinery.

**Mathlib primitives:** none new.

**Dependencies:** W1.

**Read-back prompt:** *"Does the commuting square hold definitionally, or does it require its own lemma? If the latter, verify the lemma exists in `SubstrateTimelessFieldNorm.lean`."*

**Verification queued:** grep `SubstrateTimelessFieldNorm.lean` for the commuting-square lemma name.

---

## CARD W4 — density of the tower's union

**Lean signature (immutable):**
```lean
lemma substrateTFCtower_dense :
    Dense (((⨆ k, substrateTFCtower k : StarSubalgebra ℂ TimelessFieldCompletion)
              : Set TimelessFieldCompletion))
```

**Semantic obligation:** The union of all `substrateTFCtower k` is dense in `TimelessFieldCompletion`.

**Proof sketch:** Pablo already has this: `substrate_UHF_denseRange` (or `substrate_finite_level_dense`) at `PF/SubstrateTimelessFieldCompletion.lean` — the finite-level embeddings' image is dense in the completion by `UniformSpace.Completion.denseInducing` machinery. Convert from "range of the family" to "union of subalgebra ranges" via `StarSubalgebra.iSup_toSet_eq` or similar.

```lean
lemma substrateTFCtower_dense :
    Dense (((⨆ k, substrateTFCtower k : StarSubalgebra ℂ TimelessFieldCompletion)
              : Set TimelessFieldCompletion)) := by
  -- Union of the tower ranges = image of the family
  -- Pablo's substrate_finite_level_dense witnesses the density
  have h := substrate_finite_level_dense
  -- rewrite to the subalgebra-supremum form
  simpa [StarSubalgebra.coe_iSup, Set.iUnion_image] using h
```

**Pablo primitives used:** `substrate_finite_level_dense` (or `substrate_UHF_denseRange`, per `SubstrateTimelessFieldCompletion.lean` §14).

**Mathlib primitives:** `StarSubalgebra.coe_iSup` (or `.mem_iSup`).

**Dependencies:** W1, W3.

**Read-back prompt:** *"What is the exact name of Pablo's density lemma? Is it stated as density of the image of the level-map family, or as density of the union of subalgebra ranges?"*

---

## CARD W5 — unique tracial linear functional

**Lean signature (immutable):**
```lean
lemma substrateTFCtower_trace_unique :
    ∃! τ : TimelessFieldCompletion → ℂ,
      IsTracialLinearFunctional TimelessFieldCompletion τ
```

**Semantic obligation:** Uniqueness of tracial linear functional on `TimelessFieldCompletion`.

**Proof sketch:** Existence: use `UHF_trace`. Show it satisfies each of the 5 `IsTracialLinearFunctional` fields by extracting from Pablo's `r113_substrate_UHF_factor_capstone`:
- `continuous`: from `UHF_trace` construction via completion extension of continuous matrix trace.
- `add`, `smul`, `tracial`, `unital`: these are the fields of Pablo's `IsTracialState` predicate, which `IsTracialState UHF_trace` proves via `r113`'s 2nd conjunct.

Uniqueness: transport from Pablo's `substrate_UHF_trace_unique`. That theorem says: any `IsTracialState`-satisfying `φ` equals `UHF_trace` pointwise. Since `IsTracialLinearFunctional` mirrors `IsTracialState` field-for-field, any `IsTracialLinearFunctional`-satisfying `τ` corresponds to an `IsTracialState` `τ`, so `τ = UHF_trace` by transport.

```lean
lemma substrateTFCtower_trace_unique :
    ∃! τ : TimelessFieldCompletion → ℂ,
      IsTracialLinearFunctional TimelessFieldCompletion τ := by
  refine ⟨UHF_trace, ?_, ?_⟩
  · -- IsTracialLinearFunctional UHF_trace
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact UHF_trace_continuous     -- discharged via r113 or explicit
    · intro x y
      exact (isTracialState_UHF_trace).add x y  -- extract from r113
    · intro c x
      exact (isTracialState_UHF_trace).smul c x
    · intro x y
      exact (isTracialState_UHF_trace).tracial x y
    · exact (isTracialState_UHF_trace).unital
  · intro τ hτ
    funext x
    -- convert IsTracialLinearFunctional τ to IsTracialState τ
    have hτ' : IsTracialState τ := ⟨hτ.continuous, hτ.add, hτ.smul, hτ.tracial, hτ.unital⟩
    exact substrate_UHF_trace_unique τ hτ' x
```

**Pablo primitives used:** `UHF_trace`, `substrate_UHF_trace_unique`, `r113_substrate_UHF_factor_capstone` (specifically the `IsTracialState UHF_trace` conjunct, which I'll call `isTracialState_UHF_trace` — may need to be extracted from r113's `∧`-tuple).

**Mathlib primitives:** none new.

**Dependencies:** the `IsTracialLinearFunctional` and `IsTracialState` predicates having field-for-field-identical shapes (which is why the conversion `⟨hτ.continuous, hτ.add, ...⟩` works). If they diverge in the future (see draft §12.2 upgrade paths for `star_hermitian` / positivity), this proof must be updated.

**Read-back prompt:** *"What exactly is the type of `r113_substrate_UHF_factor_capstone`? Extract the `IsTracialState UHF_trace` conjunct — is it a projection, or does it need `.2.1` chain?"*

---

## Aggregate: `substrate3Inf_TimelessFieldCompletion` assembled

```lean
noncomputable def substrate3Inf_TimelessFieldCompletion :
    Substrate3Inf TimelessFieldCompletion where
  tower         := substrateTFCtower
  tower_matrix  := substrateTFCtower_matrix
  tower_mono    := substrateTFCtower_mono
  tower_dense   := substrateTFCtower_dense
  trace_unique  := substrateTFCtower_trace_unique
```

5 cards total, each ~10–30 lines of Lean, all using only Pablo's existing kernel-verified material. **Total cost: ~15–30 minutes of prover-agent time when farmed in parallel.**

---

## Interaction with the C1–C4 arc

The W1–W5 cards close the **"completion IS a Substrate3Inf"** direction. The C1–C4 cards close the **"any Substrate3Inf is *-iso to a fixed reference"** direction. Together they give:

```lean
theorem T_infinity_rigidity
    (A : Type*) [CStarAlgebra A]
    (h : Substrate3Inf A) :
    Nonempty (A ≃⋆ₐ[ℂ] TimelessFieldCompletion) :=
  substrate3Inf_iso h substrate3Inf_TimelessFieldCompletion
```

where `substrate3Inf_iso` is C4 and `substrate3Inf_TimelessFieldCompletion` is this document's aggregate.

**W1–W5 can be landed first**, giving a partial-but-provable half of the theorem: `∃ (F : Substrate3Inf TimelessFieldCompletion), True` — the completion is in the class. This is the smallest possible non-`sorry` deliverable that consumes real substrate content.

---

## Full statement-card index for `T_infinity_rigidity`

| block | cards | direction | farmable | agent-time est. |
|---|---|---|---|---|
| C1 | 7 cards (C1.1–C1.7) | block-diagonal embedding | yes, parallel | ~30–60 min |
| C2 | ~10 cards (Noether–Skolem) | *-hom uniqueness up to inner unitary | partial | ~1–2 hours |
| C3 | ~5 cards | completion universal property, star-upgraded | yes | ~30 min |
| C4 | 1 main + ~10 cards | Elliott back-and-forth | needs coherent authoring | ~2–4 hours |
| W1–W5 | 5 cards | completion witness (this document) | yes, parallel | ~15–30 min |

**Total: ~38 cards, ~4–8 hours of parallel prover-agent work at Vinogradov cadence.** On dispatch with 3–8 concurrent sessions across Max-tier subscriptions (per FLT-lessons §7): achievable in a single day of coordinated work.

---

*Cards drafted 2026-09-10. Landing sequence: W1–W5 first (uses only existing material, gives partial deliverable), then C1 (independent), then C3 (independent), then C2 (independent), then C4 (needs C1+C2+C3). Public HEAD `96c71da7`. NO PUSH TO MASTER. Branch `r331b-provenance`.*
