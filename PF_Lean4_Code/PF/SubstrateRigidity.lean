/-
# PF/SubstrateRigidity.lean

**The central theorem `T_infinity_rigidity` — the substrate is forced,
not chosen.** Any C*-algebra satisfying the `Substrate3Inf`
characterisation is *-isomorphic to `TimelessFieldCompletion`. This
is Glimm's 1960 UHF classification specialised to supernatural number
`3^∞`.

**Status: SORRY-SCAFFOLDED sketch-DAG (2026-09-10).** Follows the
FLT-lessons pattern (`codex/FLT_LESSONS_FOR_PF_2026-09-08.md` §1–§2):
every `sorry` here is a *statement card* whose type is immutable and
whose proof body will be filled by prover-agent farming per
`codex/C1_STATEMENT_CARDS_2026-09-10.md` and
`codex/COMPLETION_WITNESS_STATEMENT_CARDS_2026-09-10.md`.

**This module is NOT yet wired into `PF.lean`.** By design, per the
project's zero-sorry discipline for the main build. Wiring happens
only after every `sorry` here is discharged and `#print axioms
T_infinity_rigidity` returns exactly
`[propext, Classical.choice, Quot.sound]`.

**Program:** `codex/UNIFIED_THEORY_PROOF_PROGRAM.md` §1.
**Directive:** `codex/UNIFIED_THEORY_PROOF_DIRECTIVE_2026-09-07.md`.
**Structure design + read-back audit trail:**
`codex/SUBSTRATE_RIGIDITY_AXIOM_DRAFT_2026-09-10.md` (v2.2, three
read-back rounds closed).
**Landing scratch history:**
`codex/SUBSTRATE_RIGIDITY_LEAN_SCRATCH_2026-09-10.md`.

**Kernel discipline:**
- NO `axiom` keyword — every "axiom" of the substrate is a hypothesis
  field of the `Substrate3Inf` structure, not a kernel injection.
- NO `native_decide` anywhere.
- `sorry` present only inside the C1–C4 proof-block scaffolds and the
  five W1–W5 witness fields. Each is a farmable statement-card leaf.
- The `#print axioms` block at the bottom is COMMENTED OUT while
  `sorry`s remain — uncomment on completion and verify verdict is
  exactly `[propext, Classical.choice, Quot.sound]`.

**Full statement-card index (see `codex/COMPLETION_WITNESS_STATEMENT_CARDS_2026-09-10.md`):**
  W1–W5: completion-side witness (5 cards, ~15–30 min agent-time)
  C1:    block-diagonal embedding (7 cards, ~30–60 min)
  C2:    Noether–Skolem for `M_n(ℂ)` (~10 cards, ~1–2 h)
  C3:    completion universal property, star-upgraded (~5 cards, ~30 min)
  C4:    Elliott back-and-forth (~10 cards + 1 main, ~2–4 h)
  ~38 cards total, ~4–8 hours at Vinogradov cadence.

Author: Pablo Cohen + Claude Opus 4.7. 2026-09-10.
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.LinearAlgebra.Matrix.Reindex  -- for C1.1 (blockDiagonal reindex)
import PF.SubstrateTimelessFieldCompletion
import PF.SubstrateTraceUniqueness
import PF.AlphaFromSubstrateKTheory_r123

open scoped Matrix.Norms.L2Operator

namespace PrincipiaTractalis
namespace SubstrateRigidity

-- D1 fix from v3 read-back: TimelessFieldCompletion lives in
-- PrincipiaTractalis.SubstrateTimelessFieldCompletion. Open the
-- sibling namespaces so bare references resolve.
--
-- 2026-09-10 build-fix: the AlphaFromSubstrateKTheory_r123.lean FILE
-- declares its content inside namespace `AlphaFromSubstrateKTheory`
-- (no _r123 suffix on the namespace), so open that.
open SubstrateTimelessFieldCompletion
open SubstrateTraceUniqueness
open AlphaFromSubstrateKTheory
-- 2026-09-10 additional opens for the substrateLevelStarAlgHom helper (§3a):
open SubstrateDirectLimit
open SubstrateTimelessFieldNorm
open SubstrateUHFTraceIsFaithful
open SubstrateUHFTraceIsStarPreserving
open SubstrateDirectLimitSimplicity

/-! ## §1 — The tracial-linear-functional predicate

Local Prop, parametric in the ambient C*-algebra. Mirrors
`PF.SubstrateTraceUniqueness.IsTracialState` (which is per-completion)
but generalised so the classification structure can quantify over an
arbitrary `A`.

**Semantic caveat (see draft §12.2):** this predicate omits positivity
(`∀ x, 0 ≤ (φ (star x * x)).re`) and star-hermitianness
(`∀ x, φ (star x) = star (φ x)`). Sufficient for the Elliott
specialisation to `3^∞`. Three v3 upgrade paths recorded in the draft
if referees push for standard "tracial state" terminology.
-/

/-- A continuous unital ℂ-linear functional on `A` with the trace
    property. Does NOT include positivity or star-hermitianness — see
    draft §12.2 for the semantic caveat. -/
structure IsTracialLinearFunctional
    (A : Type*) [CStarAlgebra A] (φ : A → ℂ) : Prop where
  continuous : Continuous φ
  add        : ∀ x y : A, φ (x + y) = φ x + φ y
  smul       : ∀ (c : ℂ) (x : A), φ (c • x) = c * φ x
  tracial    : ∀ x y : A, φ (x * y) = φ (y * x)
  unital     : φ 1 = 1

/-! ## §2 — The `Substrate3Inf` characterisation -/

/-- A `Substrate3Inf A` witness places `A` in the class of C*-algebras
    characterised by:
      · a directed tower of `3^k`-dimensional matrix *-subalgebras;
      · dense union of the tower;
      · a unique tracial linear functional (in the sense of §1).

    By `T_infinity_rigidity` below, any such `A` is *-isomorphic to
    `TimelessFieldCompletion`. -/
structure Substrate3Inf (A : Type*) [CStarAlgebra A] where
  tower         : ℕ → StarSubalgebra ℂ A
  tower_matrix  : ∀ k, Nonempty
                    (tower k ≃⋆ₐ[ℂ] Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
  tower_mono    : ∀ k, tower k ≤ tower (k+1)
  tower_dense   : Dense (((⨆ k, tower k : StarSubalgebra ℂ A) : Set A))
  trace_unique  : ∃! τ : A → ℂ, IsTracialLinearFunctional A τ

namespace Substrate3Inf
variable {A : Type*} [CStarAlgebra A] (h : Substrate3Inf A)

/-- Every inclusion in the tower is unital — free from `StarSubalgebra`
    structure since unital subalgebras are preserved by inclusion. -/
lemma connect_unital (k : ℕ) :
    (StarSubalgebra.inclusion (h.tower_mono k)) 1 = 1 := by
  rfl

/-- Every inclusion in the tower is isometric.

    2026-09-10 build result: the intended one-liner
      `NonUnitalStarAlgHom.isometry _ (StarSubalgebra.inclusion_injective _)`
    failed to elaborate — mathlib typeclass search cannot bridge
    `StarSubalgebra.inclusion` (a `StarAlgHom`) to
    `NonUnitalStarAlgHomClass` without an explicit `[CStarAlgebra ↑S]`
    instance on the tower subalgebras, which mathlib does not always
    supply. Deferred as a leaf. Once `connect_iso` is discharged the
    body will be direct via `NonUnitalStarAlgHom.isometry` with the
    subalgebra `CStarAlgebra` instance made explicit. -/
lemma connect_iso (k : ℕ) :
    Isometry (StarSubalgebra.inclusion (h.tower_mono k)) :=
  sorry

end Substrate3Inf

/-! ## §3a — Helper: level embedding as `StarAlgHom`

W1's straightforward `.range` approach requires a bundled morphism.
`substrateLevelToTimelessField k` in Pablo's tree is a bare function;
its algebra-preservation lemmas exist as separate theorems. Bundle
them here into a `StarAlgHom`, then factor the completion coercion
via mathlib's `UniformSpace.Completion` machinery, and compose.

All six substrate-preservation lemmas exist and are kernel-clean:
  · substrate_quotient_add_same_level    (SubstrateDirectLimit)
  · substrate_quotient_mul_same_level    (SubstrateDirectLimit)
  · substrate_quotient_zero_same_level   (SubstrateUHFTraceIsFaithful)
  · substrate_quotient_one_same_level    (SubstrateDirectLimitSimplicity)
  · substrate_quotient_star_same_level   (SubstrateUHFTraceIsStarPreserving)
  · substrate_quotient_smul_same_level   (SubstrateTimelessFieldNorm)
-/

/-- Level embedding into `TimelessFieldRing` bundled as `StarAlgHom`. -/
noncomputable def substrateLevelToTimelessFieldStarAlgHom (k : ℕ) :
    Matrix (Fin (3^k)) (Fin (3^k)) ℂ →⋆ₐ[ℂ] TimelessFieldRing where
  toFun A := substrateLevelToTimelessField k A
  map_one'   := substrate_quotient_one_same_level k
  map_mul' A B := (substrate_quotient_mul_same_level k A B).symm
  map_zero'  := substrate_quotient_zero_same_level k
  map_add' A B := (substrate_quotient_add_same_level k A B).symm
  map_star' A := (substrate_quotient_star_same_level k A).symm
  commutes' c := by
    show substrateLevelToTimelessField k (algebraMap ℂ _ c) = algebraMap ℂ _ c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    show (⟦⟨k, c • (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)⟩⟧ : TimelessFieldRing)
         = c • (1 : TimelessFieldRing)
    rw [← substrate_quotient_one_same_level k,
        ← substrate_quotient_smul_same_level c k
            (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)]

/-- The completion coercion `TimelessFieldRing → TimelessFieldCompletion`
    as a `StarAlgHom`. -/
noncomputable def TimelessFieldRingToCompletionStarAlgHom :
    TimelessFieldRing →⋆ₐ[ℂ] TimelessFieldCompletion where
  toFun x := (x : TimelessFieldCompletion)
  map_one'    := UniformSpace.Completion.coe_one _
  map_mul' x y := UniformSpace.Completion.coe_mul x y
  map_zero'   := UniformSpace.Completion.coe_zero
  map_add' x y := UniformSpace.Completion.coe_add x y
  map_star' x  := (star_coe_TimelessFieldCompletion x).symm
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    show ((c • (1 : TimelessFieldRing) : TimelessFieldRing) : TimelessFieldCompletion)
         = c • ((1 : TimelessFieldCompletion))
    rw [UniformSpace.Completion.coe_smul, UniformSpace.Completion.coe_one]

/-- The composite: level embedding directly into the completion. -/
noncomputable def substrateLevelStarAlgHom (k : ℕ) :
    Matrix (Fin (3^k)) (Fin (3^k)) ℂ →⋆ₐ[ℂ] TimelessFieldCompletion :=
  TimelessFieldRingToCompletionStarAlgHom.comp
    (substrateLevelToTimelessFieldStarAlgHom k)

/-! ## §3 — W1–W5: completion-side witness

Each W-card is farmed independently. Uses ONLY existing
kernel-verified ingredients — no C1–C4 dependency.

Statement cards: `codex/COMPLETION_WITNESS_STATEMENT_CARDS_2026-09-10.md`.
-/

/-- **W1 — PROVED 2026-09-10.** The tower of finite-level embeddings on
    `TimelessFieldCompletion` as `StarSubalgebra` ranges. -/
noncomputable def substrateTFCtower :
    ℕ → StarSubalgebra ℂ TimelessFieldCompletion :=
  fun k => (substrateLevelStarAlgHom k).range

/-- **W2.** Each level of the tower is *-alg-isomorphic to
    `M_{3^k}(ℂ)`. -/
lemma substrateTFCtower_matrix (k : ℕ) :
    Nonempty (substrateTFCtower k ≃⋆ₐ[ℂ]
              Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :=
  sorry -- W2 leaf

/-- **W3.** The tower is monotone under inclusion. -/
lemma substrateTFCtower_mono (k : ℕ) :
    substrateTFCtower k ≤ substrateTFCtower (k+1) :=
  sorry -- W3 leaf

/-- **W4.** The union of the tower is dense in the completion. -/
lemma substrateTFCtower_dense :
    Dense (((⨆ k, substrateTFCtower k
              : StarSubalgebra ℂ TimelessFieldCompletion)
              : Set TimelessFieldCompletion)) :=
  sorry -- W4 leaf

/-- **W5.** Unique tracial linear functional on the completion —
    discharges via Pablo's `substrate_UHF_trace_unique` + `UHF_trace`. -/
lemma substrateTFCtower_trace_unique :
    ∃! τ : TimelessFieldCompletion → ℂ,
      IsTracialLinearFunctional TimelessFieldCompletion τ :=
  sorry -- W5 leaf

/-- The canonical `Substrate3Inf` witness on `TimelessFieldCompletion`.
    Assembled from W1–W5. -/
noncomputable def substrate3Inf_TimelessFieldCompletion :
    Substrate3Inf TimelessFieldCompletion where
  tower         := substrateTFCtower
  tower_matrix  := substrateTFCtower_matrix
  tower_mono    := substrateTFCtower_mono
  tower_dense   := substrateTFCtower_dense
  trace_unique  := substrateTFCtower_trace_unique

/-! ## §4 — C1: block-diagonal `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)`

Statement cards: `codex/C1_STATEMENT_CARDS_2026-09-10.md` (7 cards).
-/

section C1_BlockDiagonalEmbedding
variable (n k : ℕ)

/-- **C1.1 — PROVED 2026-09-10.** The block-diagonal ring hom
    `x ↦ diag(x, x, ..., x)`.

    NOTE: mathlib's `Matrix.blockDiagonal` uses convention
    `(o → Matrix m n α) → Matrix (m × o) (n × o) α` — row-then-family.
    Our target signature has `Fin k × Fin n` (family-then-row), so we
    compose with `Matrix.reindexAlgEquiv` via `Equiv.prodComm` to swap.
    On mathlib master this could use `Matrix.reindexRingEquiv`
    directly; pinned version `v4.24.0-rc1` requires the AlgEquiv
    downcast. -/
noncomputable def blockDiagonalConstMap :
    Matrix (Fin n) (Fin n) ℂ →+*
      Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ
      (Equiv.prodComm (Fin n) (Fin k))).toRingEquiv.toRingHom.comp
    ((Matrix.blockDiagonalRingHom (Fin n) (Fin k) ℂ).comp
      { toFun := fun x => fun _ : Fin k => x
        map_zero' := rfl
        map_one'  := rfl
        map_add'  := fun _ _ => rfl
        map_mul'  := fun _ _ => rfl })

/-- **C1.2.** The block-diagonal ring hom preserves `star`.

    Proof structure: each of the three composed layers preserves star.
    · Constant lift `fun _ : Fin k => x`: star pushes into each component.
    · `Matrix.blockDiagonal`: `blockDiagonal_conjTranspose` (mathlib
      `Mathlib/Data/Matrix/Block.lean:364`).
    · `Matrix.reindex e e`: `conjTranspose_reindex` (mathlib
      `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:428`) — this is
      definitionally `rfl` since `reindex e e` uses the same `e` for
      rows and cols.
    On `Matrix n n α`, `star = conjTranspose` by `Matrix.instStar`
    (`Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:392`). -/
lemma blockDiagonalConstMap_star (x : Matrix (Fin n) (Fin n) ℂ) :
    blockDiagonalConstMap n k (star x)
      = star (blockDiagonalConstMap n k x) := by
  show Matrix.reindex (Equiv.prodComm (Fin n) (Fin k))
        (Equiv.prodComm (Fin n) (Fin k))
        (Matrix.blockDiagonal (fun _ : Fin k => star x))
      = star (Matrix.reindex (Equiv.prodComm (Fin n) (Fin k))
                (Equiv.prodComm (Fin n) (Fin k))
                (Matrix.blockDiagonal (fun _ : Fin k => x)))
  rw [show (star :
        Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ →
        Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ)
        = Matrix.conjTranspose from rfl,
      Matrix.conjTranspose_reindex,
      Matrix.blockDiagonal_conjTranspose]
  rfl

/-- **C1.3 — PROVED 2026-09-10.** The block-diagonal *-alg-hom
    (packages C1.1 + C1.2).

    Structure: pack `blockDiagonalConstMap` (RingHom from C1.1) and
    `blockDiagonalConstMap_star` (C1.2) into a `StarAlgHom`. The
    `commutes'` field is not automatic since C1.1 delivers only a
    `RingHom`. We prove
      `blockDiagonalConstMap n k (algebraMap ℂ _ c) = algebraMap ℂ _ c`
    by unfolding `algebraMap` to `c • 1` via
    `Algebra.algebraMap_eq_smul_one`, then chaining through the three
    composed layers:
      · constant lift `fun _ : Fin k => c • 1` (defeq via `Pi.smul_def`);
      · `blockDiagonal_smul` + `blockDiagonal_one` on the middle layer;
      · `reindexAlgEquiv` is an `AlgEquiv` so its `RingHom` respects
        `smul` and `1`.
    Uses the same targeted `show` trick as C1.2 to peel the composed
    RingHom.comp layers to their fully-reduced form. -/
noncomputable def blockDiagonalConstStarHom :
    Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ where
  toFun     := blockDiagonalConstMap n k
  map_zero' := (blockDiagonalConstMap n k).map_zero
  map_one'  := (blockDiagonalConstMap n k).map_one
  map_add'  := (blockDiagonalConstMap n k).map_add
  map_mul'  := (blockDiagonalConstMap n k).map_mul
  commutes' c := by
    show Matrix.reindex (Equiv.prodComm (Fin n) (Fin k))
          (Equiv.prodComm (Fin n) (Fin k))
          (Matrix.blockDiagonal
            (fun _ : Fin k => (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)) c))
        = algebraMap ℂ (Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ) c
    simp only [Algebra.algebraMap_eq_smul_one, Pi.smul_def,
      Matrix.blockDiagonal_smul, Matrix.blockDiagonal_one,
      map_smul, _root_.map_one]
  map_star' := blockDiagonalConstMap_star n k

/-- **C1.4.** Block-diagonal *-alg-hom is injective for `k > 0`. -/
lemma blockDiagonalConstStarHom_injective [NeZero k] :
    Function.Injective (blockDiagonalConstStarHom n k) :=
  sorry

/-- **C1.5.** The `Fin (k * n)`-indexed version required by C4. -/
noncomputable def blockDiagonalStarAlgHom :
    Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
  sorry

/-- **C1.6.** The reindexed version is injective for `k > 0`. -/
lemma blockDiagonalStarAlgHom_injective [NeZero k] :
    Function.Injective (blockDiagonalStarAlgHom n k) :=
  sorry

/-- **C1.7.** The reindexed version is unital (convenience lemma; also
    automatic from the `StarAlgHom` structure). -/
lemma blockDiagonalStarAlgHom_unital :
    blockDiagonalStarAlgHom n k 1 = 1 :=
  sorry

end C1_BlockDiagonalEmbedding

/-! ## §5 — C2: Noether–Skolem for `M_n(ℂ)`

Any two unital *-homs `M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` are conjugate by a
unitary in `M_{kn}(ℂ)`. Not in mathlib as of 2026-09-09.
-/

section C2_NoetherSkolem
variable (n k : ℕ) [NeZero k]

/-- **C2 main.** Noether–Skolem specialised to `M_n → M_{kn}`. -/
lemma unital_star_hom_inner_unique
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
           Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    ∃ U : Matrix (Fin (k * n)) (Fin (k * n)) ℂ,
      U * star U = 1 ∧ star U * U = 1 ∧
      ∀ x, φ x = U * ψ x * (star U) :=
  sorry

end C2_NoetherSkolem

/-! ## §6 — C3: universal property of the C*-completion, star-upgraded

For a `Substrate3Inf A`: any coherent family of *-homs from the tower
to a C*-algebra `B` extends uniquely to a *-hom on `A`.

Specialisation of `UniformSpace.Completion.extensionHom` upgraded from
`RingHom` to `StarAlgHom` on our specific towered structure.
-/

section C3_CompletionUniversalProperty
variable {A : Type*} [CStarAlgebra A]

/-- **C3 main.** Universal extension of a coherent tower family. -/
lemma tower_universal_star_extension
    (h : Substrate3Inf A) {B : Type*} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k))
                     = fam k) :
    ∃! F : A →⋆ₐ[ℂ] B, ∀ k x, F ((h.tower k).subtype x) = fam k x :=
  sorry

end C3_CompletionUniversalProperty

/-! ## §7 — C4: Elliott back-and-forth on two `3^∞` towers

Given `Substrate3Inf` witnesses on both `A` and `B`, zig-zag construct
a coherent *-iso `A_k → B_{k+n}` and pass to the norm limit. Consumes
C1 + C2 + C3.
-/

/-- **C4 main.** Elliott back-and-forth specialised to `3^∞`. -/
theorem substrate3Inf_iso
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (hA : Substrate3Inf A) (hB : Substrate3Inf B) :
    Nonempty (A ≃⋆ₐ[ℂ] B) :=
  sorry

/-! ## §8 — The main theorem: `T_infinity_rigidity`

Combines C4 with the completion-side witness.
-/

/-- **`T_infinity_rigidity`.** Any C*-algebra with a `Substrate3Inf`
    witness is *-isomorphic to `TimelessFieldCompletion`. Glimm's UHF
    classification specialised to supernatural number `3^∞`. -/
theorem T_infinity_rigidity
    (A : Type*) [CStarAlgebra A]
    (h : Substrate3Inf A) :
    Nonempty (A ≃⋆ₐ[ℂ] TimelessFieldCompletion) :=
  substrate3Inf_iso h substrate3Inf_TimelessFieldCompletion

/-! ## §9 — Kernel audit block (COMMENTED OUT while sorries remain)

Per `build-tree-discipline` memory, a stone lands with:
  1. `PF.lean` importing this file, AND
  2. this file carrying `#print axioms` for every main theorem.

Both are held until every `sorry` above is discharged and this file is
kernel-clean. On completion:
  · uncomment the block below,
  · rebuild,
  · verify each print returns exactly
    `[propext, Classical.choice, Quot.sound]`,
  · then add the `import PF.SubstrateRigidity` line to `PF.lean`.
-/

-- #print axioms T_infinity_rigidity
-- #print axioms substrate3Inf_iso
-- #print axioms substrate3Inf_TimelessFieldCompletion
-- #print axioms Substrate3Inf.connect_iso
-- #print axioms Substrate3Inf.connect_unital
-- #print axioms IsTracialLinearFunctional

end SubstrateRigidity
end PrincipiaTractalis
