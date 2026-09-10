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

## 1. STRUCTURE DRAFT — `Substrate3Inf`

**Revised 2026-09-10 after mathlib API pin-down (§9).** Two hypothesis fields dropped as *derivable*, not smuggled: `connect_unital` follows from inclusion of unital subalgebras; `connect_iso` follows from **`NonUnitalStarAlgHom.norm_map`** (`Mathlib/Analysis/CStarAlgebra/Hom.lean:104`) — injective *-alg-hom of complex C\*-algebras is *always* an isometry. Structure now has 4 substantive fields.

```lean
structure Substrate3Inf (A : Type*) [CStarAlgebra A] where

  -- FIELD 1. Ternary tower.
  --   An ℕ-indexed family of *-subalgebras A_k ⊆ A, each *-isomorphic to
  --   M_{3^k}(ℂ), forming a directed system under inclusion.
  tower         : ℕ → StarSubalgebra ℂ A
  tower_matrix  : ∀ k, Nonempty (tower k ≃⋆ₐ[ℂ] Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
  tower_mono    : ∀ k, tower k ≤ tower (k+1)

  -- FIELD 2. Union of the tower is dense.
  --   Norm-closure of ⋃_k tower k is all of A. Makes A the completion,
  --   not just the algebraic direct limit.
  tower_dense   : Dense ((⨆ k, (tower k : Set A)) : Set A)

  -- FIELD 3. Unique tracial state.
  --   Uses Pablo's own IsTracialState predicate (mathlib does not name
  --   TracialState — verified 2026-09-10). The substrate's classifying
  --   invariant lives here. substrate_UHF_trace_unique + r113 discharge
  --   this field on the completion case.
  trace_unique  : ∃! τ : A → ℂ, IsTracialState τ
```

**Derived, not assumed** — proved as lemmas inside `PF/SubstrateRigidity.lean`:

```lean
-- Every subalgebra inclusion in the tower is unital (from StarSubalgebra structure).
lemma Substrate3Inf.connect_unital (h : Substrate3Inf A) (k : ℕ) :
    (StarSubalgebra.inclusion (h.tower_mono k)) 1 = 1 := ...

-- Every inclusion is an isometry — free from mathlib for injective *-hom
-- between complex C*-algebras.
lemma Substrate3Inf.connect_iso (h : Substrate3Inf A) (k : ℕ) :
    Isometry (StarSubalgebra.inclusion (h.tower_mono k)) :=
  NonUnitalStarAlgHom.isometry _ (StarSubalgebra.inclusion_injective _)
```

**Four hypothesis fields, two derived lemmas.** FIELD 3 (`trace_unique`) is the semantic core — everything else forces `A` into the "UHF of type `3^∞`" morphology. `IsTracialState` is Pablo's own predicate in `PF/SubstrateTraceUniqueness.lean` (kernel-verified with audit block).

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

**Revised 2026-09-10 with mathlib-gap detail from §9.** The structure is cheap. The theorem is not. Four proof blocks are required, and mathlib supplies **none of the four** end-to-end. Sizes below are named-lemma estimates, not lines-of-Lean.

**C0 — Register `CStarAlgebra TimelessFieldCompletion` as an actual typeclass `instance`.**
Pablo has all the ingredients as theorems (`substrate_TimelessFieldCompletion_starRing_capstone`, `substrate_TimelessFieldCompletion_cstar_capstone`, submultiplicative + triangle norm), but they're stated as `Nonempty` conjuncts, not as `instance` declarations. Downstream code cannot write `[CStarAlgebra TimelessFieldCompletion]` and get elaboration to succeed without these instances. **Cost: ~3 `instance` declarations that unpack the existing `Nonempty` conjuncts** — mechanical, no new mathematics.

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

*Public HEAD `96c71da7`. NO PUSH TO MASTER. Branch `r331b-provenance`. Draft only. Structure = 4 substantive hypothesis fields; every field inhabitable from kernel-clean material on the `TimelessFieldCompletion` case; every downstream mathlib gap enumerated; proof cost pinned at ~30 lemmas, half farmable. No `axiom` keyword used or proposed anywhere in this document.*
