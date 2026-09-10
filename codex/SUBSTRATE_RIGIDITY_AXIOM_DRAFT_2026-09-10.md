# SUBSTRATE RIGIDITY — STRUCTURE DRAFT (READ-BACK FORMAT)

**Purpose.** Draft the `structure Substrate3Inf` whose inhabitants are exactly the C*-algebras eligible to be the substrate `T_∞`, so `T_infinity_rigidity` can be stated cleanly:

> Any C*-algebra with a `Substrate3Inf` witness is *-isomorphic to `TimelessFieldCompletion`.

**Discipline reminders (per project rules and Pablo's 2026-09-10 clarification):**
- Every "axiom" in this document is a **hypothesis field of a `structure`**, not a Lean `axiom` declaration. `#print axioms` on the final theorem stays exactly `[propext, Classical.choice, Quot.sound]`.
- Every field must pass **per-field inhabitation**: given `TimelessFieldCompletion` itself, we must be able to construct that field from Pablo's already-proved ingredients (§1 of the program doc lists nine).
- Per **gate §H (read-back)**: this document renders every field as (a) Lean-shape, (b) English intent, (c) inhabitation source. The document is not a `.lean` file. It goes to an independent reader who returns a diff between the Lean-shape and the English intent, and Pablo signs the diff off, before any `.lean` is written.
- Per **`build-tree-discipline` memory**: when the module lands, `PF.lean` imports it AND the file carries `#print axioms T_infinity_rigidity`. Both, always.

**Status of this draft:** structural shell only. Exact mathlib primitives (typeclass names, direct-limit vs completion API, star-alg-equiv notation) are being fetched by a parallel agent — this document will be revised once those signatures are pinned. **Do not compile.** Do not commit as `.lean`.

---

## 0. WHAT WE ARE CHARACTERIZING, IN CLASSICAL LANGUAGE

The Glimm-Elliott classification specialised to supernatural number `3^∞` says:

> Up to *-isomorphism, there is exactly one unital simple separable C*-algebra that is the norm-closure of an inductive limit `⋃_k A_k` with `A_k ≅ M_{3^k}(ℂ)` and unital *-embedding connecting maps `A_k ↪ A_{k+1}`.

That object is what Pablo calls `TimelessFieldCompletion`. The structure below is the Lean-side statement of the italicized conditions, as **hypotheses** on an arbitrary candidate algebra `A`. Any `A` that satisfies the whole bundle must be *-iso to `T_∞`. That is the theorem.

---

## 1. STRUCTURE DRAFT — `Substrate3Inf` (REVISED 2026-09-10 after read-back)

**Revised 2026-09-10.** The v1 draft (§1v1 preserved for audit trail below) failed §H read-back on a **blocking type error**: it consumed `IsTracialState τ` for `τ : A → ℂ`, but `IsTracialState` at `PF/SubstrateTraceUniqueness.lean:164` is hard-wired to `TimelessFieldCompletion → ℂ` (not parametric in the ambient C\*-algebra). It would not elaborate. This is exactly the class of defect the read-back gate was built to catch pre-proof.

**Fix:** introduce a new predicate `IsTracialFunction A` in the new `SubstrateRigidity` module. Does not touch existing files.

```lean
/-- Tracial state on a C*-algebra `A`. Same shape as Pablo's per-completion
    `IsTracialState`, generalised to arbitrary `[CStarAlgebra A]`.
    NOTE: positivity is intentionally NOT required — matches the weaker
    predicate already used by `substrate_UHF_trace_unique`. See §12 for
    the semantic caveat this carries. -/
structure IsTracialFunction (A : Type*) [CStarAlgebra A] (φ : A → ℂ) : Prop where
  continuous : Continuous φ
  add        : ∀ x y, φ (x + y) = φ x + φ y
  smul       : ∀ (c : ℂ) x, φ (c • x) = c * φ x
  tracial    : ∀ x y, φ (x * y) = φ (y * x)
  unital     : φ 1 = 1

structure Substrate3Inf (A : Type*) [CStarAlgebra A] where
  -- FIELD 1. Ternary tower.
  tower         : ℕ → StarSubalgebra ℂ A
  tower_matrix  : ∀ k, Nonempty (tower k ≃⋆ₐ[ℂ] Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
  tower_mono    : ∀ k, tower k ≤ tower (k+1)

  -- FIELD 2. Density (subalgebra-supremum form; equivalent to set-union
  -- under a ≤-chain but cleaner to consume downstream).
  tower_dense   : Dense (((⨆ k, tower k : StarSubalgebra ℂ A) : Set A))

  -- FIELD 3. Unique tracial function.
  trace_unique  : ∃! τ : A → ℂ, IsTracialFunction A τ
```

**Coherence deliberately not asserted at hypothesis level** — the read-back auditor flagged this ("the intended UHF chain is under-specified"). The response is *not* to strengthen the hypothesis. The response is to make explicit that recovering coherence — the fact that the inclusion `tower k ↪ tower (k+1)` corresponds (up to inner unitary) to the canonical `x ↦ x ⊗ I_3` — is **exactly the work C2 does** (Noether–Skolem specialised to `M_n → M_{kn}`). If we assumed coherence, the structure would leak the classification result into the hypothesis. C2 pays that cost inside the proof, where it belongs.

**Derived, not assumed:**

```lean
-- Unital inclusions of unital subalgebras.
lemma Substrate3Inf.connect_unital (h : Substrate3Inf A) (k : ℕ) :
    (StarSubalgebra.inclusion (h.tower_mono k)) 1 = 1 := ...

-- Isometry — free from mathlib via `NonUnitalStarAlgHom.norm_map` for
-- injective *-hom between complex C*-algebras.
lemma Substrate3Inf.connect_iso (h : Substrate3Inf A) (k : ℕ) :
    Isometry (StarSubalgebra.inclusion (h.tower_mono k)) :=
  NonUnitalStarAlgHom.isometry _ (StarSubalgebra.inclusion_injective _)
```

**Three substantive hypothesis fields on the object, one auxiliary predicate.** FIELD 3 (`trace_unique`) is the classifying invariant. Everything else forces the local morphology.

### 1v1. First-draft record (for audit trail)

The v1 structure used `IsTracialState τ` (Pablo's per-completion predicate) as FIELD 5, using `Dense ((⨆ k, (tower k : Set A)) : Set A)` for FIELD 4. Read-back caught the type-error on FIELD 5. Recorded here so the diff between v1 and v2 is legible.

The classification theorem then reads:

```
theorem T_infinity_rigidity
    (A : Type*) [CStarAlgebra A]
    (h : Substrate3Inf A) :
    Nonempty (A ≃⋆ₐ[ℂ] TimelessFieldCompletion) := by
  ...  -- Elliott back-and-forth on h.tower vs Pablo's canonical M_{3^k} tower
```

`#print axioms T_infinity_rigidity` on completion returns `[propext, Classical.choice, Quot.sound]`. No project axioms; no `axiom` keyword anywhere in the file. Every hypothesis lives in `h : Substrate3Inf A` and any user of the theorem must build such an `h` to invoke it.

---

## 2. PER-FIELD INHABITATION CHECK

Every field must be inhabitable in the case `A = TimelessFieldCompletion` from Pablo's existing kernel-clean ingredients. If it isn't, the field is smuggling an assumption.

| field | inhabitation route on `TimelessFieldCompletion` | Pablo's existing artifact | conclusion |
|---|---|---|---|
| `tower` | The map `k ↦ image_of_M_{3^k}_in_TimelessFieldCompletion` — literally what Pablo's `TimelessFieldRing` builds. | `TimelessFieldRing` construction; `PF/SubstrateTimelessFieldNorm.lean` | **inhabitable** |
| `tower_matrix` | Each level is by construction `M_{3^k}(ℂ)`. | The definition of `TimelessFieldRing` as the algebraic direct limit of `M_{3^k}` | **inhabitable, essentially by unfolding a definition** |
| `tower_mono` | The connecting maps are by construction inclusions. | Same as above | **inhabitable, by definition** |
| `connect_unital` | The canonical `x ↦ diag(x, x, x)` sends `I_{3^k}` to `I_{3^{k+1}}`. | Direct calculation; may already be in `SubstrateTimelessFieldNorm.lean` — check | **inhabitable, needs one small lemma or already present** |
| `connect_iso` | Norm-preservation of the iterated ring hom. | `substrateRingHomIter_opNorm_eq` — this is exactly the theorem for it | **inhabitable — Pablo already proved this** |
| `tower_dense` | `UniformSpace.Completion` by definition has the original space as a dense subspace, and the tower's union is exactly that original space. | `TimelessFieldCompletion := UniformSpace.Completion TimelessFieldRing`; standard mathlib | **inhabitable via mathlib primitive** |
| `trace_unique` | Direct citation of Pablo's own theorem. | `substrate_UHF_trace_unique` in `PF/SubstrateTraceUniqueness.lean` | **inhabitable — Pablo already proved this** |

**Verdict of the inhabitation audit:** every field is inhabitable from existing kernel-clean material. **No field smuggles a claim.** The structure is a definition-with-hypotheses, not a hidden axiom bundle.

---

## 3. WHERE ANY REAL COST LIVES

**Revised 2026-09-10 with mathlib-gap detail from §9 AND with C0 corrected: Pablo already landed C0 at r59 (2026-07-06).**

**C0 — Register `CStarAlgebra TimelessFieldCompletion` as an actual typeclass `instance`. ✓ DONE.**
Grep of `PF/SubstrateTimelessFieldCompletion.lean` shows every mathlib-required typeclass is a proper `noncomputable instance` on `TimelessFieldCompletion`:
- r53: `UniformSpace`, `CompleteSpace`, `AddCommGroup`, `Ring`, `NormedAddCommGroup`, `NormedRing`, `NormedSpace ℂ` (auto from mathlib Completion)
- r54: `Star` (line 193)
- r55: `InvolutiveStar`, `StarAddMonoid`, `StarMul`, `StarRing`
- r56: `CStarRing`
- r57: `Algebra ℂ`, `NormedAlgebra ℂ`
- r58: `StarModule ℂ`
- **r59** (line 554): `CStarAlgebra TimelessFieldCompletion` — grand capstone.

Witness at line 578: `theorem substrate_UHF_CStarAlgebra_exists : Nonempty (CStarAlgebra TimelessFieldCompletion) := ⟨inferInstance⟩`. The `⟨inferInstance⟩` term proves the `Nonempty` by literally invoking typeclass search — proof that the instance registration works. Also **r60 is scaffolding nuclearity** (§15+ of the same file), which is one additional C*-algebra property beyond the program-doc §1 list.

Earlier claim in this draft ("must be built") was wrong. Total cost drops by C0's estimated ~3 lemmas.

**C1 — Block-diagonal unital *-embedding `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)`.**
Not packaged as a `StarAlgHom` in mathlib (verified `Mathlib/Analysis/CStarAlgebra/Matrix.lean` has `Matrix.blockDiagonal` and `Matrix.blockDiagonal'` but neither is a `StarAlgHom`). Once constructed, **isometry is free** via `NonUnitalStarAlgHom.norm_map` (`Mathlib/Analysis/CStarAlgebra/Hom.lean:104`) — huge win, halves the estimate. **Cost: ~5 lemmas** (down from ~15 in the earlier estimate) — the map, injectivity, star-preservation, ring-hom facts.

**C2 — Noether–Skolem / uniqueness of unital *-embeddings up to inner unitary.**
Any two unital *-homs `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` are conjugate by a unitary in `M_{kn}(ℂ)`. **Not in mathlib** (verified: no `IsInner`, no `automorphism-is-inner` lemma anywhere in `Mathlib/Analysis/CStarAlgebra/`). This is the classical Noether–Skolem theorem specialised. **Cost: ~10 lemmas** — one central "any *-endomorphism of `M_n(ℂ)` is inner", then the specialisation to embeddings between different sizes.

**C3 — Universal property of the C\*-completion of the pre-C\* direct-limit ring, upgraded to star.**
Mathlib has `UniformSpace.Completion.extensionHom` at the `RingHom` level (`Mathlib/Topology/Algebra/UniformRing.lean:128`), and Pablo has star lift to the completion in his `SubstrateTimelessFieldCompletion.lean`. What's missing at the mathlib level is a general `Completion.extensionStarAlgHom` — but for the classification proof we don't need the fully general lift; we only need: given a coherent family of *-homs `tower k → B` (B a C\*-algebra) with matched norms, extend uniquely to a *-hom on the completion. **Cost: ~5 lemmas** specialising `Completion.extension` and packaging with star preservation.

**C4 — Elliott back-and-forth on two `3^∞`-towers.**
Given `h_A : Substrate3Inf A` and `h_B : Substrate3Inf B`, zig-zag construct a coherent *-iso `A_k → B_{k+n}` using C1+C2+C3, pass to the norm limit via C3, get `A ≃⋆ₐ[ℂ] B`. Specialising to `B = TimelessFieldCompletion` closes `T_infinity_rigidity`. **Cost: ~10 lemmas, one main construction.** This is the intertwining spine.

**Total: ~30 named lemmas** (unchanged; C1 shrank, C0 added). Per FLT-lessons pattern (`codex/FLT_LESSONS_FOR_PF_2026-09-08.md`), C0/C1/C2 are ideal statement-card candidates (self-contained finite-dim matrix statements) — **50–60% farmable to parallel agents**. C3 and C4 need one coherent author for the intertwining logic. C0 is mechanical enough for a single-session pass.

**Free lunches from mathlib** that reduce the cost:
- `NonUnitalStarAlgHom.norm_map` — isometry from injective *-hom, drops FIELD-2's isometry from a hypothesis to a derived lemma
- `StarAlgEquiv.ofBijective` — package the bijective *-hom the Elliott intertwining produces as a `≃⋆ₐ[ℂ]`
- `StarAlgHom.range` — cleanly stating that the tower's algebraic union is a *-subalgebra
- `Matrix.instCStarAlgebra` (scoped in `Matrix.Norms.L2Operator`) — makes every `M_{3^k}(ℂ)` a C\*-algebra without work

**Contribution beyond mathlib** (of independent value as a mathlib PR chain):
- The C\*-completion star lift (Pablo already has this) — mathlib **wants this** and has no equivalent. `Completion.extensionStarAlgHom` would be a natural mathlib PR.
- Non-commutative C\*-algebraic direct limit (Pablo's `TimelessFieldRing` construction) — `Mathlib.Algebra.Colimit.Ring` requires `CommRing`; a non-commutative version would land cleanly.
- The `IsTracialState` predicate + basic API — mathlib has zero coverage; even a bare definition + a handful of lemmas would fill a real gap.
- Noether–Skolem for `M_n(ℂ)` (C2) — long-outstanding mathlib gap.

So `T_infinity_rigidity` is not only "the first formalization of Glimm 1960 in any prover" — its by-products are **four separable mathlib PRs**, each of which is publishable on its own.

---

## 4. WHAT WOULD REFUTE THE STRUCTURE

Per directive §8 (adversarial program), for each field an explicit failure mode:

- FIELD 1 fails: exhibit a C*-algebra with a `Substrate3Inf` witness whose tower is NOT `M_{3^k}`. (Blocked by `tower_matrix`.)
- FIELD 2 fails: exhibit an inclusion `M_{3^k} ↪ M_{3^{k+1}}` in some ambient algebra that is not isometric. (Blocked by finite-dimensional norm uniqueness.)
- FIELD 4 fails: exhibit an inhabitant where the union of the tower is dense in a proper C*-subalgebra of `A`. That would refute uniqueness — we would have two non-isomorphic completions of the same directed system, which contradicts standard completion universality.
- FIELD 5 fails: exhibit a second tracial state on `TimelessFieldCompletion`. Would falsify `substrate_UHF_trace_unique` and end the whole program.

The only field whose failure is not immediately blocked by finite-dimensional linear algebra is FIELD 5, and that failure would falsify existing kernel results. **The structure is defensible.**

---

## 5. READ-BACK PROMPT — for the §H auditor

An independent-reader agent will be given the following, verbatim, without seeing this document:

```
Translate to precise English prose the following Lean 4 structure. Unfold every project-local definition you cite. State each field's meaning in one sentence and list every hypothesis, implicit or explicit, that a term inhabiting the structure would have to satisfy.

structure Substrate3Inf (A : Type*) [CStarAlgebra A] where
  tower         : ℕ → StarSubalgebra ℂ A
  tower_matrix  : ∀ k, Nonempty (tower k ≃⋆ₐ[ℂ] Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
  tower_mono    : ∀ k, tower k ≤ tower (k+1)
  connect_unital : ∀ k, (StarSubalgebra.inclusion (tower_mono k)) 1 = 1
  connect_iso    : ∀ k, Isometry (StarSubalgebra.inclusion (tower_mono k))
  tower_dense   : Dense ((⨆ k, (tower k : Set A)) : Set A)
  trace_unique  : ∃! τ : StateSpace A, IsTracial τ
```

Pablo compares the returned English against the intent below:

> A `Substrate3Inf` witness on `A` says: `A` contains a nested tower of finite matrix subalgebras of sizes `3^k`, whose inclusions are unital and preserve the operator norm; their union is dense in `A`; and `A` has exactly one tracial state.

Any drift between the returned translation and this intent is a defect and must be closed before `.lean` is written.

---

## 6. INGREDIENT SIGNATURES — VERBATIM

Landed 2026-09-10. Every signature below is a kernel-clean theorem already in the tree, copied without modification. This appendix is what FIELD-by-FIELD inhabitation in §2 rests on, and it is the interface the classification proof will consume.

Two orthogonal observations from this pass:

- **Build-tree-discipline gap.** 7 of 9 ingredient theorems live in files with **no in-file `#print axioms` block**. Only `SubstrateTraceUniqueness.lean` and `AlphaFromSubstrateKTheory_r123.lean` carry them. Per `build-tree-discipline` memory (r123 unimported for 11 days, r212 file with zero audit blocks while agent reported "36 clean"), this is a prerequisite fix before `T_infinity_rigidity` inherits a clean chain per directive §7. The mechanical patch is: append `#print axioms <name>` for each listed theorem to its file's footer, recompile per-module, parse unwrapped output. Recorded again for §10.4b of the standing report.
- **`TimelessFieldCompletion` is definitionally `UniformSpace.Completion TimelessFieldRing`** (`SubstrateTimelessFieldCompletion.lean:82–83`). Mathlib's completion machinery is doing the metric/algebraic lift; the substrate lives on top of standard scaffolding.

### 6.1 Norm-preserving iterated embedding — FIELD-2 backing

**`substrateRingHomIter_opNorm_eq`** — `PF/SubstrateTimelessFieldNorm.lean:62`, audit block: **no**
```lean
theorem substrateRingHomIter_opNorm_eq (i : ℕ) :
    ∀ (j : ℕ) (h : i ≤ j) (A : Matrix (Fin (3^i)) (Fin (3^i)) ℂ),
    ‖substrateRingHomIter i j h A‖ = ‖A‖
```
*Consumed by* `Substrate3Inf.connect_iso` — this IS the isometry statement.

### 6.2 Norm submultiplicative + triangle — used to lift completion

**`norm_mul_le_TimelessField`** — line 174, audit: **no**
```lean
theorem norm_mul_le_TimelessField (x y : TimelessFieldRing) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖
```

**`norm_add_le_TimelessField`** — line 157, audit: **no**
```lean
theorem norm_add_le_TimelessField (x y : TimelessFieldRing) :
    ‖x + y‖ ≤ ‖x‖ + ‖y‖
```
*Both consumed implicitly by any C\*-algebra instance on `TimelessFieldCompletion`.*

### 6.3 Star-ring structure on the completion — typeclass backer

**`substrate_TimelessFieldCompletion_starRing_capstone`** — `PF/SubstrateTimelessFieldCompletion.lean:340`, audit: **no**
```lean
theorem substrate_TimelessFieldCompletion_starRing_capstone :
    Function.Involutive
      (star : TimelessFieldCompletion → TimelessFieldCompletion) ∧
    (∀ x y : TimelessFieldCompletion, star (x + y) = star x + star y) ∧
    (∀ x y : TimelessFieldCompletion, star (x * y) = star y * star x) ∧
    Nonempty (InvolutiveStar TimelessFieldCompletion) ∧
    Nonempty (StarAddMonoid TimelessFieldCompletion) ∧
    Nonempty (StarMul TimelessFieldCompletion) ∧
    Nonempty (StarRing TimelessFieldCompletion)
```
*This gives `StarRing TimelessFieldCompletion` for free; it is a witness for the typeclass hypothesis `[CStarAlgebra A]` on the completion case of `T_infinity_rigidity`.*

### 6.4 The C\*-identity — equality form, load-bearing

**`cstar_ineq_TimelessFieldCompletion`** — line 368, audit: **no**
```lean
theorem cstar_ineq_TimelessFieldCompletion (x : TimelessFieldCompletion) :
    ‖x‖ * ‖x‖ ≤ ‖star x * x‖
```

**`substrate_TimelessFieldCompletion_cstar_capstone`** — line 401, audit: **no**  (name found: has `substrate_TimelessFieldCompletion_` prefix, program-doc §1 shorthand was `..._cstar_capstone`)
```lean
theorem substrate_TimelessFieldCompletion_cstar_capstone :
    (∀ x : TimelessFieldCompletion, ‖x‖ * ‖x‖ ≤ ‖star x * x‖) ∧
    Nonempty (CStarRing TimelessFieldCompletion) ∧
    (∀ x : TimelessFieldCompletion, ‖star x * x‖ = ‖x‖ * ‖x‖)
```
*The third conjunct is the C\*-identity as an equality, exactly what the `CStarRing` typeclass demands. `TimelessFieldCompletion` is a C\*-algebra by this theorem, kernel-clean.*

### 6.5 Star is an isometry

**`isometry_star_TimelessField`** — line 174, audit: **no**
```lean
theorem isometry_star_TimelessField :
    Isometry (star : TimelessFieldRing → TimelessFieldRing)
```

### 6.6 Trace uniqueness — the classifying invariant, FIELD-5 backing

**`substrate_UHF_trace_unique`** — `PF/SubstrateTraceUniqueness.lean:239`, audit: **yes** ✓
```lean
theorem substrate_UHF_trace_unique (φ : TimelessFieldCompletion → ℂ)
    (hφ : IsTracialState φ) (x : TimelessFieldCompletion) :
    φ x = UHF_trace x
```
*Every tracial state equals `UHF_trace` pointwise. Uniqueness in the extensional sense.*

**`matrix_tracial_state_unique`** — line 77, audit: **yes** ✓
```lean
theorem matrix_tracial_state_unique {n : ℕ} [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hadd : ∀ A B, φ (A + B) = φ A + φ B)
    (hsmul : ∀ (c : ℂ) A, φ (c • A) = c * φ A)
    (htr : ∀ A B, φ (A * B) = φ (B * A))
    (hone : φ 1 = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    φ M = normalized_matrix_trace M
```
*Finite-level trace uniqueness on `M_n(ℂ)`. Base case for the tower.*

**`r113_substrate_UHF_factor_capstone`** — line 285, audit: **yes** ✓
```lean
theorem r113_substrate_UHF_factor_capstone :
    (∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ →
       ∀ x, φ x = UHF_trace x) ∧
    IsTracialState UHF_trace ∧
    (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0) ∧
    (∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤)
```
*Four-part UHF factor capstone: unique tracial state, faithful, simple. **This one artifact carries the whole classifying-invariant story** — trace exists, is tracial, is faithful, and the algebra has no non-trivial two-sided ideal.*

### 6.7 K-theoretic scaffolding — r123, referenced in FIELD-5 justification

**`substrate_level_projection_trace`** — `PF/AlphaFromSubstrateKTheory_r123.lean:249`, audit: **yes** ✓
```lean
theorem substrate_level_projection_trace {k : ℕ} (S : Finset (Fin (3 ^ k))) :
    haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
    normalized_matrix_trace (Matrix.diagonal (charDiag S))
      = (S.card : ℂ) / ((3 : ℂ) ^ k)
```

**`MemZ13`** — line 127 (definition, not theorem)
```lean
def MemZ13 (x : ℝ) : Prop := ∃ (m : ℤ) (k : ℕ), x = (m : ℝ) / 3 ^ k
```
*K₀ range is `ℤ[1/3]`. This is what makes the substrate's classifying invariant "ternary" in a substantive sense: projection traces are of the form `card / 3^k`.*

---

## 7. UPDATED INHABITATION TABLE — cross-referenced

Same table as §2, now with exact FQN citations from §6.

| structure field | inhabitation source in the tree | audit block |
|---|---|---|
| `tower` | `TimelessFieldRing` construction (algebraic direct limit) | — |
| `tower_matrix` | Unfolds the direct-limit definition | — |
| `tower_mono` | Directed-system definition | — |
| `connect_unital` | Definition of `substrateRingHomIter` at `i = j` gives identity; unital by construction | — |
| `connect_iso` | **`substrateRingHomIter_opNorm_eq`** (§6.1) | **missing** |
| `tower_dense` | `TimelessFieldCompletion := UniformSpace.Completion TimelessFieldRing` — density of the original space is a mathlib primitive | — |
| `trace_unique` | **`r113_substrate_UHF_factor_capstone` §1st conjunct + `substrate_UHF_trace_unique`** (§6.6) | **present** ✓ |

**Layered dependency notes:**

- `CStarRing TimelessFieldCompletion` typeclass instance is materialised by **`substrate_TimelessFieldCompletion_cstar_capstone` §2nd conjunct** (§6.4). So the `[CStarAlgebra A]` hypothesis on the completion case is discharged.
- `StarRing TimelessFieldCompletion` instance is materialised by **`substrate_TimelessFieldCompletion_starRing_capstone` §last conjunct** (§6.3).
- **Faithfulness and simplicity** of the trace/algebra come from **`r113_substrate_UHF_factor_capstone` §3rd–4th conjuncts** — these are what let the Elliott intertwining actually converge to a bijection.

---

## 9. MATHLIB API — PINNED FQNS

Landed 2026-09-10. Every FQN below is verified against mathlib4 HEAD.

**Wired directly:**
- `CStarAlgebra` — `Mathlib/Analysis/CStarAlgebra/Classes.lean:38`. Bundles `NormedRing`, `StarRing`, `CompleteSpace`, `CStarRing`, `NormedAlgebra ℂ`, `StarModule ℂ`. Fixed to `ℂ`.
- `StarAlgEquiv` — `Mathlib/Algebra/Star/StarAlgHom.lean:629`. Notation `A ≃⋆ₐ[R] B` at line 636.
- `StarAlgHom` — same file, line 286. `.comp`, `.range` (in `Mathlib/Algebra/Star/Subalgebra.lean:825`).
- `StarAlgEquiv.ofInjective` — `Mathlib/Algebra/Star/Subalgebra.lean:~862`. Takes an injective `StarAlgHom` to a `StarAlgEquiv` onto its range.
- `Matrix.instCStarAlgebra` — `Mathlib/Analysis/CStarAlgebra/Matrix.lean:307`. Scoped in `Matrix.Norms.L2Operator` — **must `open scoped`**. Operator norm, not Frobenius.
- `UniformSpace.Completion` — `Mathlib/Topology/UniformSpace/Completion.lean:291`. Extension: `.extension` (line 429), `.map` (line 477), uniqueness (line 460).
- `UniformSpace.Completion.extensionHom` (ring level) — `Mathlib/Topology/Algebra/UniformRing.lean:128`.
- `NonUnitalStarAlgHom.norm_map` — `Mathlib/Analysis/CStarAlgebra/Hom.lean:104`. **Injective *-alg-hom between complex C\*-algebras is automatically isometric.** This is the free lunch that killed `connect_iso` as a hypothesis.
- `StarSubalgebra` — `Mathlib/Algebra/Star/Subalgebra.lean`. `.inclusion` gives the embedding `sub₁ →⋆ₐ[R] sub₂` from `sub₁ ≤ sub₂`.

**NOT in mathlib — must be built in this file or a companion:**
- `IsTracialState` / `TracialState` — no coverage. Closest surrogate: `PositiveContinuousLinearMap` (notation `A →P[ℂ] ℂ`) at `Mathlib/Analysis/CStarAlgebra/PositiveLinearFunctional.lean`. Pablo already has `IsTracialState` as a project-local Prop, used in `substrate_UHF_trace_unique`. **Structure FIELD 3 uses Pablo's own predicate.**
- `Completion.starRing` / `Completion.instCStarAlgebra` — no. Pablo's `substrate_TimelessFieldCompletion_starRing_capstone` + `..._cstar_capstone` fill this specific gap for `TimelessFieldCompletion`. Generalisation to arbitrary pre-C\* rings is a natural mathlib PR.
- `Ring.DirectLimit` in `Mathlib/Algebra/Colimit/Ring.lean:54` requires `CommRing` — useless for `M_n(ℂ)` towers. Generic `DirectLimit` at `Mathlib/Algebra/Colimit/DirectLimit.lean:66` supports star but has no metric/completeness. **Pablo's `TimelessFieldRing` construction is the non-commutative direct-limit** — another natural mathlib PR candidate.
- Noether–Skolem / any "*-automorphism of `M_n(ℂ)` is inner" lemma — none. C2 above.
- Block-diagonal `M_n ↪ M_{kn}` as `StarAlgHom` — none. C1 above.

---

## 10. STATUS AT COMMIT TIME

- Structure fields: **4 substantive hypothesis fields**; 2 previously-drafted fields (`connect_unital`, `connect_iso`) reclassified as derived lemmas per §1.
- Classification theorem statement: drafted.
- Proof outline: C0 (register `CStarAlgebra TimelessFieldCompletion` instances), C1 (block-diagonal *-embedding), C2 (Noether–Skolem specialised), C3 (completion universal property, star-upgraded), C4 (Elliott back-and-forth). **~30 lemmas total, 50–60% FLT-farmable.**
- Ingredient signatures: **all 9 landed verbatim** (§6).
- Mathlib API: **pinned** (§9). Four separable mathlib PRs identifiable as by-products.
- Build-tree-discipline gap: **7 of 9 ingredient files lack `#print axioms` blocks**. Mechanical fix; do it before the T_infinity_rigidity chain lands so the classification inherits a clean audit spine.
- Read-back audit: **prompt drafted (§5), not dispatched.** Next mechanical step is to dispatch it.
- `.lean` file: **none.** By design — read-back-before-write per gate §H.

## 11. NEXT DECISIVE ACTIONS (per directive §11 ordering)

Ordered by (a) fastest to close, (b) prerequisite for the next.

1. **Dispatch the §5 read-back prompt** to an independent-reader agent. Wait ≤ 10 minutes. Compare returned English to §5 intent. Diff → sign-off or refinement.
2. **Land C0** (register `CStarAlgebra TimelessFieldCompletion` instances). Single Lean file edit, no new mathematics. Verifies the typeclass hypothesis on the `TimelessFieldCompletion` side of `T_infinity_rigidity`.
3. **Patch the 7 audit-block gaps** in the ingredient files. Mechanical `#print axioms` appends + per-module recompile + unwrapped-output parse. **Prerequisite** for the classification theorem to inherit a clean chain per directive §7.
4. **Write `PF/SubstrateRigidity.lean`** as a stub: `structure Substrate3Inf`, statement of `T_infinity_rigidity`, four `sorry`d C1–C4 lemmas as scaffolds. Wire into `PF.lean`. `#check @T_infinity_rigidity` should show the type unfolded, no unexpected implicits. **Do not commit if `sorry` is present** — this stub is a local `sorry`-checkpoint only, discharged before landing.
5. **Farm C1 + C2 out as statement cards** per FLT-lessons pattern. C1 (~5 lemmas) and C2's individual pieces (~10 lemmas) are pure finite-dim matrix theorems — statement-card canonical form. C3 and C4 stay with a single author.

*Public HEAD `96c71da7`. NO PUSH TO MASTER. Branch `r331b-provenance`. Draft only. Structure = 3 substantive hypothesis fields + 1 auxiliary predicate; every field inhabitable from kernel-clean material on the `TimelessFieldCompletion` case; every downstream mathlib gap enumerated; proof cost pinned at ~20–25 lemmas after C0 correction and mathlib free-lunch identifications, half farmable. No `axiom` keyword used or proposed anywhere in this document.*

---

## 12. READ-BACK FINDINGS AND SEMANTIC CAVEAT — RECORDED

### 12.1 Gate §H first-run findings (2026-09-10)

Independent-reader agent produced audit. Findings, in priority order:

1. **BLOCKING (fixed in §1v2):** `IsTracialState` type error. `IsTracialState` at `PF/SubstrateTraceUniqueness.lean:164` is `(φ : TimelessFieldCompletion → ℂ)`, not `(φ : A → ℂ)`. v1 draft would not elaborate for general `A`. **Response:** introduce `IsTracialFunction A φ` in the new module, parametric in `[CStarAlgebra A]`. v2 structure uses it.
2. **SEMANTIC (documented in §12.2):** `IsTracialState` (Pablo's per-completion predicate, and hence `IsTracialFunction`, which mirrors it) is **strictly weaker** than the standard mathematical "tracial state." Positivity is not required. ℂ-linearity is imposed where ℝ-linearity is standard. This is not a defect of the draft alone — it is inherited from Pablo's kernel-verified `substrate_UHF_trace_unique`. See §12.2 for what to do about it.
3. **SUBALGEBRA-VS-SET SUPREMUM (fixed in §1v2):** v1 used `⨆ k, (tower k : Set A)`. v2 uses `((⨆ k, tower k : StarSubalgebra ℂ A) : Set A)`. Equivalent under a `≤`-chain of star-subalgebras but the star-subalgebra form is the mathlib-idiomatic phrasing and avoids reader friction.
4. **COHERENCE OF THE UHF CHAIN (documented in §12.3):** `tower_matrix` supplies only *some* iso per level, no coherence with `tower_mono`. This is deliberate. Response is in §12.3.
5. **VACUITY of trivial tower (documented in §12.3):** blocked by `tower_matrix` for `k ≥ 1`. Non-issue.
6. **CIRCULARITY (documented in §12.4):** the enclosing theorem's conclusion (existence of a `≃⋆ₐ[ℂ]` to `TimelessFieldCompletion`) does *not* literally contain the `trace_unique` hypothesis, so this structure follows the same non-circular pattern as `AlphaSkeletonUniqueness_r128`. Documented for the record.

### 12.2 Semantic caveat: `IsTracialFunction` is weaker than "tracial state" — audit note

Standard tracial state (Dixmier, Blackadar, mathlib intent): a **norm-1 positive** ℂ-linear functional `φ : A → ℂ` on a unital C\*-algebra `A` satisfying `φ(x⁎y) = φ(y⁎x)`, i.e. `φ(ab) = φ(ba)`. Positivity means `φ(a⁎a) ≥ 0`. Norm-1 corresponds to `φ(1) = 1` on the unital case.

Pablo's `IsTracialState` (kernel-verified as consumed by `substrate_UHF_trace_unique`, `r113_substrate_UHF_factor_capstone`) has: continuity, ℂ-additivity, ℂ-scalar linearity, trace property, `φ(1) = 1`. **No positivity.** Missing standard content.

**Consequence for `T_infinity_rigidity`:** the classification theorem, as it will be written to consume `Substrate3Inf.trace_unique`, will conclude uniqueness up to *-iso in the class of C\*-algebras whose UNIQUE **linear trace-property functional with `φ(1)=1`** is fixed. That is a wider class than "UHF algebras with a unique tracial state." Two options:

- **(a) Ship as-is.** The class is still narrow enough for the Glimm-classification argument to run — Elliott's back-and-forth uses the trace as a K₀-labeled projection functional, and Pablo's `substrate_level_projection_trace` (`AlphaFromSubstrateKTheory_r123.lean:249`) shows `trace(proj) = card/3^k`, which is what the intertwining needs. Positivity is not *used* in Elliott specialised to `3^∞` — it *would* be used if we tried to run the general Elliott theorem where the ordered K₀ matters. For our specialisation, positivity is not load-bearing.
- **(b) Strengthen `IsTracialFunction` to include `∀ x, 0 ≤ (φ (star x * x)).re`.** Discharges cleanly on the `TimelessFieldCompletion` side via `substrate_level_projection_trace` composed with `UHF_trace ≥ 0` (which Pablo has implicitly via `card / 3^k` being a nonneg rational). Narrows the class slightly. Cost: one extra field + one extra inhabitation lemma.

**Recommendation:** ship (a) for v2 draft. If a referee objects that "unique tracial state" in the paper text isn't matched by the predicate name, either rename the predicate to `IsTracialLinearFunctional` or upgrade to (b) in v3. Not urgent for the mathematics.

### 12.3 Coherence: why we deliberately don't assume it

Read-back auditor: *"only existence of some iso per level is asserted; no coherence with `tower_mono` … one could pick isos level-by-level that respect no chain relation."*

Correct. And this is by design. Here is why.

The Glimm/Elliott classification theorem for UHF `3^∞` is the statement: *any two C\*-algebras with a `3^∞`-tower and unique tracial state (up to whatever we're calling it here) are *-isomorphic.* If we assumed the inclusions were the canonical block-diagonal `x ↦ x ⊗ I_3` embedding, the classification theorem would degenerate into "for any two objects with an EQUAL directed system, they're isomorphic" — trivial. The nontriviality of the theorem is precisely that the classification recovers coherence from bare cardinality data (`tower_matrix`) + inclusion (`tower_mono`) + density + trace.

**Noether–Skolem specialised to `M_n → M_{kn}` (block C2 in §3)** is the technical lemma that recovers coherence: any two unital *-embeddings `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` are conjugate by a unitary in `M_{kn}(ℂ)`. Once you have this, the tower's actual inclusion becomes (up to inner unitary) `x ↦ x ⊗ I_3` — coherence is a theorem, not a hypothesis.

So the auditor's flag is real but the response is *"yes, and C2 pays that cost — that's what C2 is for."*

### 12.4 Circularity: the trace-uniqueness hypothesis is not the conclusion

Enclosing theorem: `∀ A [CStarAlgebra A], Substrate3Inf A → Nonempty (A ≃⋆ₐ[ℂ] TimelessFieldCompletion)`. Conclusion is a `Nonempty (StarAlgEquiv …)`. Structure hypothesis is `∃! τ, IsTracialFunction A τ`. These are formally distinct types; the hypothesis is not the conclusion nor definitionally-equal to any conjunct of it. No forbidden circularity per directive §3.

**Semantic implication direction:** the conclusion implies the hypothesis (if `A ≃⋆ₐ[ℂ] TimelessFieldCompletion` and `TimelessFieldCompletion` has a unique tracial function, so does `A` via transport). That is exactly how uniqueness-up-to-iso theorems work: you isolate enough invariants that any inhabitant of the class must satisfy them, then prove the class has one member up to iso. `AlphaSkeletonUniqueness_r128` runs the same pattern (8 laws as hypotheses; uniqueness of α-tuple as conclusion). Same shape, same absence of circularity.

---

## 13. NEXT DECISIVE ACTIONS — REVISED

Ordered by prerequisite. Cost estimates in named-lemma counts.

1. **Dispatch a v2 read-back on the amended structure.** Confirm the type-error is resolved and no new drift introduced. Cost: 1 agent call, ~5 min.
2. **Write `PF/SubstrateRigidity.lean`** with `IsTracialFunction` + `Substrate3Inf` + statement of `T_infinity_rigidity` + four `sorry`d C1/C2/C3/C4 lemma scaffolds. Wire into `PF.lean`. Do not commit while `sorry` is present (local checkpoint only).
3. **Patch the 7 audit-block gaps** in ingredient files (append `#print axioms` directives). Recompile per-module. Parse unwrapped output. Directive §7 prerequisite.
4. **Farm C1 + C2 as statement cards** per FLT-lessons pattern. C1: block-diagonal `M_n →⋆ₐ M_{kn}` and injectivity — ~5 lemmas. C2: Noether–Skolem for `M_n(ℂ)` and specialisation to embeddings — ~10 lemmas. Both pure finite-dim matrix theorems; ideal for FLT-style parallel proving.
5. **Author C3 + C4 coherently** (completion universal property + Elliott back-and-forth). ~15 lemmas + one main construction. Single author, not farmable.
6. **Land `T_infinity_rigidity` with `#print axioms` returning the mathlib three**, wire into `PF.lean`, commit + push.

Total remaining named-lemma cost: **~25 lemmas** (C0 done; mathlib free lunches applied). 50–60% farmable.
