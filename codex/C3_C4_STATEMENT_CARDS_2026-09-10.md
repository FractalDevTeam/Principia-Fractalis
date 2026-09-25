# C3 + C4 STATEMENT CARDS — completion universal property + Elliott back-and-forth

**Purpose.** Per `FLT_LESSONS_FOR_PF_2026-09-08.md` §1, decompose C3 and C4 of `PF/SubstrateRigidity.lean` into immutable statement-cards. Companion to `C1_STATEMENT_CARDS_2026-09-10.md` and `COMPLETION_WITNESS_STATEMENT_CARDS_2026-09-10.md`. C2 decomposed by sibling agent.

**Discipline (C1 doc):** immutable Lean sigs; multi-proofs/disproofs welcome; lands only when `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**Scope.** **C3** = star-upgrade of `UniformSpace.Completion.extensionHom` (`UniformRing.lean:128`). **C4** = Elliott back-and-forth on `3^∞`; consumes C1, C2, C3.

**Refs:** Elliott 1976; RLL §7; Bratteli 1972; Glimm 1960.



---

## Dependency graph

```
  Substrate3Inf (tower / tower_mono / tower_dense / connect_iso)
        │
        ├─► C3.1 → C3.2 → C3.3 → C3.4 → C3.5 [C3.main]
        │                                       │
  C1.5 ─┤                                       ▼
  C2.main─► C4.1 → C4.2 → C4.3 → C4.4 → C4.5 → (C4.6,C4.7)
                → (C4.8,C4.9) → (C4.10,C4.11) → C4.main
```

**C3** needs only `Substrate3Inf` + `Completion.extension` + `Dense.equalizer`; parallel with C1/C2. **C4** needs C1, C2, C3.

---

## Mathlib primitives (verified 2026-09-09; re-check in v3)

`UniformSpace.Completion.extension`; `UniformSpace.Completion.extensionHom` (`UniformRing.lean:128`); `Dense.equalizer`/`Continuous.ext_on`; `StarSubalgebra.inclusion`, `.subtype`, `.iSup`, `.mem_iSup`; `NonUnitalStarAlgHom.isometry`; `StarAlgEquiv.ofBijective`, `.symm`, `.trans`. **Verify:** `Completion.extensionStarAlgHom` (if present, collapses C3 to 2 cards); `StarAlgEquiv.ofStarAlgHom`; `StarSubalgebra.subtype_comp_inclusion`.

---

# §C3 — completion universal property (5 cards)

## CARD C3.1 — `tower_union_starHom`

**Lean signature (immutable):**
```lean
noncomputable def tower_union_starHom
    {A} [CStarAlgebra A] (h : Substrate3Inf A) {B} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k)) = fam k) :
    (⨆ k, h.tower k : StarSubalgebra ℂ A) →⋆ₐ[ℂ] B
```

**English:** From coherent `{fam k}`, build the single *-hom on `⨆ k, tower k`. Every element lies in some level; `compat` makes the value level-independent.

**Proof sketch:** Directed union under `tower_mono`; any `x` is `⟨y, hk⟩` with `y ∈ tower k`; well-definedness via `compat`. Package via `StarSubalgebra.iSup_induction`.

**Mathlib primitives:** `StarSubalgebra.iSup`, `.mem_iSup`, `StarAlgHom.mk`.

**Dependencies:** none beyond `Substrate3Inf`.

**Read-back prompt:** *"On `x ∈ tower k`, what value? Why level-independent?"*

---

## CARD C3.2 — `tower_union_starHom_uniformContinuous`

**Lean signature (immutable):**
```lean
lemma tower_union_starHom_uniformContinuous
    {A} [CStarAlgebra A] (h : Substrate3Inf A) {B} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k)) = fam k) :
    UniformContinuous (tower_union_starHom h fam compat)
```

**English:** Union-hom is uniformly continuous (in fact norm-decreasing) so lifts by density to the closure.

**Proof sketch:** Every C*-*-hom is norm-decreasing (RLL Prop 1.5.7). Each `fam k` gives `‖fam k y‖ ≤ ‖y‖`; on the union, evaluate at any containing level. 1-Lipschitz ⇒ `UniformContinuous`.

**Mathlib primitives:** `NonUnitalStarAlgHom.isometry` (or C*-contraction lemma), `LipschitzWith.uniformContinuous`.

**Dependencies:** C3.1.

**Read-back prompt:** *"Why is every C*-*-hom continuous? C* identity or submultiplicativity?"*

---

## CARD C3.3 — `tower_extension_map`

**Lean signature (immutable):**
```lean
noncomputable def tower_extension_map
    {A} [CStarAlgebra A] (h : Substrate3Inf A) {B} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k)) = fam k) :
    A → B
```

**English:** Bare-function extension via `tower_dense` + `DenseInducing.extend`. *-hom packaging in C3.4.

**Proof sketch:** `tower_dense` gives density; `A, B` complete C*-algebras. Apply `DenseInducing.extend` to the C3.2 uniformly-continuous map.

**Mathlib primitives:** `DenseInducing.extend`, `UniformSpace.Completion.extension`.

**Dependencies:** C3.1, C3.2.

**Read-back prompt:** *"Which lemma? What input beyond density + uniform continuity?"*

---

## CARD C3.4 — `tower_extension_starAlgHom`

**Lean signature (immutable):**
```lean
noncomputable def tower_extension_starAlgHom
    {A} [CStarAlgebra A] (h : Substrate3Inf A) {B} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k)) = fam k) :
    A →⋆ₐ[ℂ] B
```

**English:** Package `F₀ := tower_extension_map` as a full `StarAlgHom`. Each op `⊕`: both sides continuous, agree on dense `(⨆ tower k)²`, so agree on `A²`.

**Proof sketch:** Extend-by-density on seven fields (`map_add/mul/smul/star/one/zero/commutes'`), each via `Continuous.ext_on tower_dense`. Star uses `continuous_star`.

**Mathlib primitives:** `Continuous.ext_on`, `Dense.equalizer`, `StarAlgHom.mk`, `continuous_star`.

**Dependencies:** C3.3.

**Read-back prompt:** *"Which field is most nontrivial to extend by density?"*

---

## CARD C3.5 — `tower_universal_star_extension` (C3 main)

**Lean signature (immutable):**
```lean
lemma tower_universal_star_extension
    {A} [CStarAlgebra A]
    (h : Substrate3Inf A) {B} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k)) = fam k) :
    ∃! F : A →⋆ₐ[ℂ] B, ∀ k x, F ((h.tower k).subtype x) = fam k x
```

**English:** Full `∃!` — existence from C3.4, uniqueness by dense equalizer.

**Proof sketch:** **Existence:** `F := tower_extension_starAlgHom`; per-level identity holds by construction. **Uniqueness:** two continuous *-homs agreeing on every level agree on `⨆ tower k`, hence on the dense set, hence everywhere.

**Mathlib primitives:** `Continuous.ext_on tower_dense`, `StarAlgHom.ext`, `ExistsUnique.intro`.

**Dependencies:** C3.1–C3.4.

**Read-back prompt:** *"Where is `tower_dense` used in uniqueness?"*

---

**C3 agg:** discharges `SubstrateRigidity.lean:275`. Linear C3.1 → C3.5.

---

# §C4 — Elliott back-and-forth (11 cards + main)

**Strategy (Elliott 1976; RLL §7).** Both towers have `A_k ≃ M_{3^k} ≃ B_k`. Build compatible level *-isos; direct-limit via C3 to mutually inverse `A ↔ B`. `3^∞` simplification: by C2, all unital `M_{3^k} → M_{3^{k+1}}` embeddings are inner-conjugate to the C1 canonical embedding, so zig-zag runs at `k ↦ k`.

## CARD C4.1 — `tower_zero_iso`

**Lean signature (immutable):**
```lean
noncomputable def tower_zero_iso
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) :
    hA.tower 0 ≃⋆ₐ[ℂ] hB.tower 0
```

**English:** Base of zig-zag. Both levels are *-iso to `M_1(ℂ) = ℂ`; compose the two matrix-isos.

**Proof sketch:** `Classical.choice` on `tower_matrix 0` gives `φA, φB`; return `φA.trans φB.symm`.

**Mathlib primitives:** `StarAlgEquiv.trans`, `.symm`, `Classical.choice`.

**Dependencies:** none (uses `Substrate3Inf.tower_matrix`).

**Read-back prompt:** *"Is this iso unique? `M_1 = ℂ` has only phase unitaries."*

---

## CARD C4.2 — `tower_step_iso`

**Lean signature (immutable):**
```lean
noncomputable def tower_step_iso
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) (k : ℕ)
    (φ : hA.tower k ≃⋆ₐ[ℂ] hB.tower k) :
    hA.tower (k+1) ≃⋆ₐ[ℂ] hB.tower (k+1)
```

**English:** Lift level-k iso to level-(k+1) iso extending it. C1 provides canonical embedding; C2 aligns actual tower inclusion to it via inner conjugation.

**Proof sketch:** (1) Transport `φ` through `tower_matrix k` to `φ_M : M_{3^k} ≃⋆ₐ M_{3^k}`. (2) Level-(k+1) matrix-iso turns tower inclusions into unital *-homs `ψ_A, ψ_B : M_{3^k} → M_{3^{k+1}}`. (3) By C2, `ψ_B ∘ φ_M = U · ψ_A · U*` for unitary `U`. (4) Extend `ψ_A` via inner-`U` correction; transport back.

**Mathlib primitives:** `StarAlgEquiv.trans`, `.symm`, `Matrix.innerAut`, plus **C1.5** and **C2.main**.

**Dependencies:** C1.5, C2.main, `tower_matrix`, `tower_mono`.

**Read-back prompt:** *"Where is C2 used? Would *-hom existence (no inner uniqueness) suffice?"*

---

## CARD C4.3 — `tower_step_iso_compat`

**Lean signature (immutable):**
```lean
lemma tower_step_iso_compat
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) (k : ℕ)
    (φ : hA.tower k ≃⋆ₐ[ℂ] hB.tower k) (x : hA.tower k) :
    (tower_step_iso hA hB k φ).toStarAlgHom
      ((StarSubalgebra.inclusion (hA.tower_mono k)) x)
    = (StarSubalgebra.inclusion (hB.tower_mono k)) (φ x)
```

**English:** Step iso respects tower inclusions — the Elliott commuting square.

**Proof sketch:** By C4.2 construction: inner-conjugation was chosen so the extended iso matches `φ` post-inclusion. Unfold, apply C2 equation, use `tower_matrix` compatibility with `tower_mono`.

**Mathlib primitives:** `StarAlgHom.comp_apply`, `StarSubalgebra.inclusion_apply`.

**Dependencies:** C4.2.

**Read-back prompt:** *"Draw the square."*

---

## CARD C4.4 — `tower_iso_sequence`

**Lean signature (immutable):**
```lean
noncomputable def tower_iso_sequence
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) :
    ∀ k, hA.tower k ≃⋆ₐ[ℂ] hB.tower k
```

**English:** Iterate C4.1 and C4.2 via `Nat.rec`.

**Proof sketch:** `k=0`: `tower_zero_iso`. `k+1`: `tower_step_iso hA hB k` applied to the recursive result.

**Mathlib primitives:** `Nat.rec`.

**Dependencies:** C4.1, C4.2.

**Read-back prompt:** *"What is level-0 up to defeq?"*

---

## CARD C4.5 — `tower_iso_sequence_compat`

**Lean signature (immutable):**
```lean
lemma tower_iso_sequence_compat
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) (k : ℕ)
    (x : hA.tower k) :
    (tower_iso_sequence hA hB (k+1)).toStarAlgHom
      ((StarSubalgebra.inclusion (hA.tower_mono k)) x)
    = (StarSubalgebra.inclusion (hB.tower_mono k))
        (tower_iso_sequence hA hB k x)
```

**English:** Full-sequence compatibility with tower inclusions.

**Proof sketch:** Apply C4.3 with `φ := tower_iso_sequence hA hB k` — exactly the step used in C4.4's recursion.

**Mathlib primitives:** `Nat.rec` unfolding, `tower_step_iso_compat`.

**Dependencies:** C4.3, C4.4.

**Read-back prompt:** *"Defeq unfolding, or `Nat.rec_succ` rewrite?"*

---

## CARD C4.6 — `tower_family_A_to_B`

**Lean signature (immutable):**
```lean
noncomputable def tower_family_A_to_B
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) :
    ∀ k, hA.tower k →⋆ₐ[ℂ] B
```

**English:** Compose C4.4 level iso with `hB.tower k`.subtype`, giving the coherent C3-input family.

**Proof sketch:** `fun k => (hB.tower k).subtype.comp (tower_iso_sequence hA hB k).toStarAlgHom`.

**Mathlib primitives:** `StarSubalgebra.subtype`, `StarAlgHom.comp`, `StarAlgEquiv.toStarAlgHom`.

**Dependencies:** C4.4.

**Read-back prompt:** *"Why land in `B` not `hB.tower k`?"*

---

## CARD C4.7 — `tower_family_A_to_B_compat`

**Lean signature (immutable):**
```lean
lemma tower_family_A_to_B_compat
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) (k : ℕ) :
    (tower_family_A_to_B hA hB (k+1)).comp
      (StarSubalgebra.inclusion (hA.tower_mono k))
    = tower_family_A_to_B hA hB k
```

**English:** C3-hypothesis: `family (k+1) ∘ inclA_k = family k`.

**Proof sketch:** LHS = `(hB.tower (k+1)).subtype ∘ φ_{k+1} ∘ inclA_k`. C4.5 rewrites `φ_{k+1} ∘ inclA_k = inclB_k ∘ φ_k`. Chain-of-inclusions: `(hB.tower (k+1)).subtype ∘ inclB_k = (hB.tower k).subtype`.

**Mathlib primitives:** `StarAlgHom.comp_assoc`, `StarSubalgebra.subtype_comp_inclusion` (verify FQN; `ext` fallback).

**Dependencies:** C4.5, C4.6.

**Read-back prompt:** *"Verify: `S ≤ T ≤ A` implies `T.subtype.comp (inclusion h) = S.subtype`?"*

---

## CARD C4.8 — `substrate_forward_map`

**Lean signature (immutable):**
```lean
noncomputable def substrate_forward_map
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) : A →⋆ₐ[ℂ] B
```

**English:** Forward *-hom from feeding C4.6+C4.7 into C3.5.

**Proof sketch:** `(tower_universal_star_extension hA (tower_family_A_to_B hA hB) (tower_family_A_to_B_compat hA hB)).choose`.

**Mathlib primitives:** `ExistsUnique.choose`.

**Dependencies:** C3.5, C4.6, C4.7.

**Read-back prompt:** *"Value on `x ∈ hA.tower k`? On a limit element?"*

---

## CARD C4.9 — `substrate_backward_map`

**Lean signature (immutable):**
```lean
noncomputable def substrate_backward_map
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) : B →⋆ₐ[ℂ] A
```

**English:** Backward *-hom `B → A`, symmetric to C4.8 using `.symm` of the sequence.

**Proof sketch:** `tower_family_B_to_A k := (hA.tower k).subtype.comp (tower_iso_sequence hA hB k).symm.toStarAlgHom`. `compat` follows from `.symm` of C4.5. Feed to C3.5.

**Mathlib primitives:** `StarAlgEquiv.symm`, `StarAlgHom.comp`, `ExistsUnique.choose`.

**Dependencies:** C3.5, C4.4, C4.5.

**Read-back prompt:** *"Why does `.symm` preserve compatibility?"*

---

## CARD C4.10 — `substrate_maps_leftInverse`

**Lean signature (immutable):**
```lean
lemma substrate_maps_leftInverse
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) :
    (substrate_backward_map hA hB).comp (substrate_forward_map hA hB)
      = StarAlgHom.id ℂ A
```

**English:** `G ∘ F = id_A`.

**Proof sketch:** Both continuous *-homs `A → A`. `Continuous.ext_on tower_dense` reduces to `⨆ tower k`. On `x ∈ hA.tower k`: `F` restricts to `(hB.tower k).subtype ∘ φ_k`; `G` to `(hA.tower k).subtype ∘ φ_k.symm`; composite `= x` via `symm_apply_apply`.

**Mathlib primitives:** `StarAlgHom.ext`, `Continuous.ext_on`, `StarAlgEquiv.symm_apply_apply`.

**Dependencies:** C3.5, C4.8, C4.9, `hA.tower_dense`.

**Read-back prompt:** *"Is `tower_dense` needed, or does structure suffice?"*

---

## CARD C4.11 — `substrate_maps_rightInverse`

**Lean signature (immutable):**
```lean
lemma substrate_maps_rightInverse
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) :
    (substrate_forward_map hA hB).comp (substrate_backward_map hA hB)
      = StarAlgHom.id ℂ B
```

**English:** `F ∘ G = id_B`, mirror of C4.10 using `hB.tower_dense` and `apply_symm_apply`.

**Proof sketch:** Symmetric.

**Mathlib primitives:** same as C4.10.

**Dependencies:** C3.5, C4.8, C4.9, `hB.tower_dense`.

**Read-back prompt:** *"Share a helper with C4.10?"*

---

## CARD C4.main — `substrate3Inf_iso`

**Lean signature (immutable):**
```lean
theorem substrate3Inf_iso
    {A B} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) :
    Nonempty (A ≃⋆ₐ[ℂ] B)
```

**English:** Package the two maps and inverse laws into a `StarAlgEquiv`.

**Proof sketch:** `StarAlgEquiv.ofStarAlgHom` applied to `substrate_forward_map`, `substrate_backward_map`, and C4.10/C4.11. Fallback: `StarAlgEquiv.ofBijective` via `LeftInverse.injective` + `RightInverse.surjective`.

**Mathlib primitives:** `StarAlgEquiv.ofStarAlgHom` (verify FQN); `StarAlgEquiv.ofBijective` fallback.

**Dependencies:** C4.8–C4.11.

**Read-back prompt:** *"Two-inverse constructor in mathlib? Else shortest bijective path?"*

---

**C4 aggregate:** discharges `SubstrateRigidity.lean:291`; consumer `T_infinity_rigidity` (`:301`). Sequencing: C4.1 → C4.2 (needs C1.5+C2.main) → C4.3 → C4.4 → C4.5 → (C4.6∥C4.7) → (C4.8∥C4.9) → (C4.10∥C4.11) → C4.main.

---

## Cross-arc priority

1. **W1–W5** (5): immediate, parallel.
2. **C1** (7): linear to C1.3, then C1.4/C1.5 parallel.
3. **C2** (~10, sibling): must precede C4.2.
4. **C3** (5, linear): parallel with C1/C2.
5. **C4** (11 + main): starts once C1.5, C2.main, C3.5 cited.

**Total ~38 cards.** ~4–8h at Vinogradov cadence; critical path C1 → C2 → C4 → main, C3 in parallel.

---

*Drafted 2026-09-10 by C3/C4 planning agent. Awaiting v3 read-back. Merge with sibling C2 doc as `C_ALL_STATEMENT_CARDS_2026-09-10.md`. Public HEAD `96c71da7`. NO PUSH TO MASTER. Branch `r331b-provenance`.*
