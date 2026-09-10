# C1 STATEMENT CARDS — block-diagonal `M_n → M_{kn}` embedding

**Purpose.** Per `FLT_LESSONS_FOR_PF_2026-09-08.md` §1, decompose the C1 proof block (`SUBSTRATE_RIGIDITY_AXIOM_DRAFT_2026-09-10.md` §3) into immutable statement-cards ready for parallel prover-agent farming. Each card is a self-contained lemma with (a) Lean signature, (b) English intent, (c) proof sketch, (d) mathlib primitives, (e) dependencies, (f) read-back prompt.

**Discipline reminders:**
- Each card's Lean signature is what a prover-agent MUST match (Curry–Howard type-check enforces).
- The proof file is a separate object; a prover-agent may write any proof term whose type defeq-matches the card's type.
- Multiple independent proofs of the same card are welcome (per FLT-lessons §1). Disproofs (proof of `¬statement`) are first-class if the card is false.
- A card only lands when its `#print axioms` returns exactly `[propext, Classical.choice, Quot.sound]`.

**Scope of this document.** C1 = the block-diagonal unital *-embedding `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)`, sending `x ↦ diag(x, x, ..., x)` (`k` copies). Used by C4 (Elliott intertwining) as the canonical inclusion shape that C2 (Noether–Skolem) shows all inclusions are equivalent to.

---

## Mathlib primitives available (verified 2026-09-09)

- `Matrix.blockDiagonal : (o → Matrix m n α) → Matrix (m × o) (n × o) α` — the generic block-diagonal constructor, at `Mathlib/Data/Matrix/Block.lean`. Constant-family case gives us what we want.
- `Matrix.blockDiagonal_zero`, `blockDiagonal_add`, `blockDiagonal_one`, `blockDiagonal_mul` — algebra homomorphism lemmas already in mathlib.
- `Matrix.blockDiagonal_star` — star preservation (verify FQN in v3 read-back).
- `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` — the reindexing to collapse the product to a flat range, at `Mathlib/Logic/Equiv/Fin.lean`.
- `Matrix.reindex (e₁ e₂ : α ≃ β) : Matrix α α R ≃ₐ[R] Matrix β β R` — algebra-equivalence via reindexing, at `Mathlib/LinearAlgebra/Matrix/Reindex.lean`.
- `Matrix.reindexAlgEquiv` — the star-alg-equivalence version if it exists (else construct via `Matrix.reindex` + `StarAlgEquiv.mk`).
- `NonUnitalStarAlgHom.isometry` — for the isometry corollary (§C1.5).

**Presence to verify in v3 read-back:** `Matrix.blockDiagonal_star`, `Matrix.reindexAlgEquiv`, `Matrix.blockDiagonal_smul`.

---

## CARD C1.1 — `blockDiagonalConstMap`

**Lean signature (immutable):**
```lean
noncomputable def blockDiagonalConstMap (n k : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →+*
      Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ where
  toFun x := Matrix.blockDiagonal (fun _ : Fin k => x)
  map_zero' := Matrix.blockDiagonal_zero
  map_one'  := by rw [Matrix.blockDiagonal_one]; rfl
  map_add' _ _ := (Matrix.blockDiagonal_add _ _).symm
  map_mul' _ _ := by
    rw [← Matrix.blockDiagonal_mul]
```

**English:** `blockDiagonalConstMap n k` is the ring hom `x ↦ diag(x, x, ..., x)` from `M_n(ℂ)` to `M_{k × n}(ℂ)` (indexed by pairs), packaged as a `RingHom`.

**Proof sketch:** Direct application of `Matrix.blockDiagonal` on the constant family; the four `RingHom` fields discharge via mathlib's existing `blockDiagonal_*` lemmas.

**Mathlib primitives:** `Matrix.blockDiagonal_zero`, `blockDiagonal_one`, `blockDiagonal_add`, `blockDiagonal_mul`.

**Dependencies:** none.

**Read-back prompt (§H):** *"Translate to precise English. What are the domain and codomain of `blockDiagonalConstMap 2 3`, dimensionally? What does the underlying function do to a `2 × 2` matrix?"*

---

## CARD C1.2 — `blockDiagonalConstMap_star`

**Lean signature (immutable):**
```lean
lemma blockDiagonalConstMap_star (n k : ℕ) (x : Matrix (Fin n) (Fin n) ℂ) :
    blockDiagonalConstMap n k (star x)
      = star (blockDiagonalConstMap n k x)
```

**English:** The block-diagonal ring hom preserves `star`. I.e., `diag(x⁎, ..., x⁎) = (diag(x, ..., x))⁎`.

**Proof sketch:** `Matrix.blockDiagonal_star` on the constant family; both sides reduce to the same matrix by unfolding `blockDiagonal` and `star` entry-wise.

**Mathlib primitives:** `Matrix.blockDiagonal_star` (or entry-wise unfolding via `Matrix.star_apply`).

**Dependencies:** C1.1.

**Read-back prompt:** *"What is the mathematical content of this statement? Show it for a `2 × 2` `x` and `k = 3`."*

---

## CARD C1.3 — `blockDiagonalConstStarHom`

**Lean signature (immutable):**
```lean
noncomputable def blockDiagonalConstStarHom (n k : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ where
  toFun := blockDiagonalConstMap n k
  map_zero' := (blockDiagonalConstMap n k).map_zero
  map_one'  := (blockDiagonalConstMap n k).map_one
  map_add' := (blockDiagonalConstMap n k).map_add
  map_mul' := (blockDiagonalConstMap n k).map_mul
  commutes' c := by
    simp [Matrix.blockDiagonal_smul, Algebra.algebraMap_eq_smul_one]
  map_star' := blockDiagonalConstMap_star n k
```

**English:** Package C1.1's ring hom into a full `StarAlgHom` by adding `ℂ`-algebra scalar preservation (`commutes'`) and `star` preservation (from C1.2).

**Proof sketch:** All fields except `commutes'` are copied from C1.1 or C1.2. `commutes'` says `c • 1 ↦ c • 1`, which reduces to `blockDiagonal (fun _ => c • 1) = c • blockDiagonal (fun _ => 1)`, which is `Matrix.blockDiagonal_smul`.

**Mathlib primitives:** `Matrix.blockDiagonal_smul`, `Algebra.algebraMap_eq_smul_one`.

**Dependencies:** C1.1, C1.2.

**Read-back prompt:** *"What does the `commutes'` field mean here? What object does it show is preserved?"*

---

## CARD C1.4 — `blockDiagonalConstStarHom_injective`

**Lean signature (immutable):**
```lean
lemma blockDiagonalConstStarHom_injective (n k : ℕ) [NeZero k] :
    Function.Injective (blockDiagonalConstStarHom n k)
```

**English:** The block-diagonal *-hom is injective for `k > 0` — if two matrices produce the same block-diagonal image, they're equal.

**Proof sketch:** If `blockDiagonalConstMap n k x = blockDiagonalConstMap n k y`, evaluate at any pair `(0, a, b)` for `a, b : Fin n`; both give `x a b = y a b`. Since `Fin k` is inhabited (from `NeZero k`), we can pick `0 : Fin k`.

**Mathlib primitives:** `Matrix.blockDiagonal_apply_eq` (entry-wise unfolding), `Matrix.ext`, `Fin.mk_zero`.

**Dependencies:** C1.3.

**Read-back prompt:** *"Why does this require `[NeZero k]`? What breaks for `k = 0`?"*

---

## CARD C1.5 — `blockDiagonalStarAlgHom`

**Lean signature (immutable):**
```lean
noncomputable def blockDiagonalStarAlgHom (n k : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
  (Matrix.reindexStarAlgEquiv ℂ ℂ finProdFinEquiv).toStarAlgHom.comp
    (blockDiagonalConstStarHom n k)
```

**English:** Compose C1.3 with the reindexing `Fin k × Fin n ≃ Fin (k * n)` to get the target signature required by `PF/SubstrateRigidity.lean`'s C1 slot.

**Proof sketch:** `Matrix.reindexStarAlgEquiv` (or `Matrix.reindexAlgEquiv` upgraded to star-preserving) sends `Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ` to `Matrix (Fin (k*n)) (Fin (k*n)) ℂ` via `finProdFinEquiv`. This is a `StarAlgEquiv`, `.toStarAlgHom` gets the *-hom, `.comp` composes with C1.3.

**Mathlib primitives:** `Matrix.reindexStarAlgEquiv` (verify FQN; may need `StarAlgEquiv.trans` composition instead), `finProdFinEquiv`, `StarAlgHom.comp`.

**Dependencies:** C1.3.

**Read-back prompt:** *"Does `Matrix.reindexStarAlgEquiv` exist in mathlib4 HEAD 2026-09-09? If not, what's the shortest substitute path via `Matrix.reindexAlgEquiv` + a manual `StarAlgHom` upgrade?"*

**Verification queued:** the mathlib pin-down agent should check this specific name; if absent, fall back to `Matrix.reindexAlgEquiv` + manual `map_star`.

---

## CARD C1.6 — `blockDiagonalStarAlgHom_injective`

**Lean signature (immutable):**
```lean
lemma blockDiagonalStarAlgHom_injective (n k : ℕ) [NeZero k] :
    Function.Injective (blockDiagonalStarAlgHom n k) :=
  (Matrix.reindexStarAlgEquiv ℂ ℂ finProdFinEquiv).injective.comp
    (blockDiagonalConstStarHom_injective n k)
```

**English:** Injectivity follows from composition of two injective maps: C1.4 (block-diagonal is injective for `k > 0`) and the fact that `reindexStarAlgEquiv` is an equivalence (hence injective).

**Proof sketch:** `Function.Injective.comp` on the two components.

**Dependencies:** C1.4, C1.5.

**Read-back prompt:** *"Both components are injective by known lemmas; is the composition argument sound as stated?"*

---

## CARD C1.7 — `blockDiagonalStarAlgHom_unital`

**Lean signature (immutable):**
```lean
lemma blockDiagonalStarAlgHom_unital (n k : ℕ) :
    blockDiagonalStarAlgHom n k 1 = 1
```

**English:** The composite *-hom sends `I_n` to `I_{kn}`.

**Proof sketch:** `blockDiagonalConstStarHom n k 1 = blockDiagonal (fun _ => 1) = 1_{k×n}` (by `blockDiagonal_one`), then `reindexStarAlgEquiv` preserves `1` (all equivalences do).

**Dependencies:** C1.3, C1.5.

**Read-back prompt:** *"This is `map_one`. Isn't it automatic from the `StarAlgHom` structure? What is the redundant lemma buying us?"*

**Answer to the read-back's hypothetical question:** yes, `map_one` is automatic. This card is a **named-for-callers convenience lemma** — `SubstrateRigidity` will call `blockDiagonalStarAlgHom_unital` explicitly rather than expanding `map_one`. Cheap to include; readable to consumers.

---

## Aggregate C1 status when all seven cards land

- `blockDiagonalStarAlgHom : M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` **constructed** (C1.5).
- **Injective** (C1.6).
- **Unital** (C1.7).
- **Isometric** — automatic via `NonUnitalStarAlgHom.isometry _ (blockDiagonalStarAlgHom_injective n k)` at the call site.

Total: 7 cards, each ≤ 20 lines of Lean. Farmable in parallel. **Aggregate cost: ~5–8 minutes agent-per-card at Vinogradov cadence (per FLT-lessons quoted §7).**

---

## Sequencing constraint

C1.1 → C1.2 → C1.3 → (C1.4, C1.5) → C1.6 → C1.7. C1.4 and C1.5 can run in parallel. C1.6 needs both. C1.7 needs C1.3 and C1.5.

Prover-agent priorities: **run C1.1 first solo, then C1.2 solo, then C1.3 solo, then fan out C1.4/C1.5, then C1.6/C1.7.**

---

*Statement-cards drafted 2026-09-10. Awaiting v3 read-back on the enclosing `SubstrateRigidity.lean` scratch before landing any of these as prover-farmable jobs. Public HEAD `96c71da7`. NO PUSH TO MASTER. Branch `r331b-provenance`.*
