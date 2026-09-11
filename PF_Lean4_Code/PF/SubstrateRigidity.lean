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
-- 2026-09-10 W3: `substrateLevelToTimelessField_iter` (cocone identity).
open SubstrateCompletionFaithful
-- 2026-09-10 W5: exposes `UHF_trace` and `uhf_trace_isTracialState`.
open SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceIsTracial

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

/-- Directed-supremum ⇒ union of underlying sets, for `StarSubalgebra ℂ A`.
    Hoisted above §3a so W4 (`substrateTFCtower_dense`) can use it. The
    C3.1 helper `coe_iSup_of_directed_starSubalgebra` below is a
    section-local re-derivation on the same type family — kept there for
    locality of the C3.1 diff. -/
private lemma coe_iSup_of_directed_starSubalgebra_W4
    {A : Type*} [CStarAlgebra A]
    {ι : Type*} [Nonempty ι] {K : ι → StarSubalgebra ℂ A}
    (dir : Directed (· ≤ ·) K) :
    ((⨆ i, K i : StarSubalgebra ℂ A) : Set A) = ⋃ i, (K i : Set A) := by
  let S : StarSubalgebra ℂ A :=
    { toSubalgebra :=
        Subalgebra.copy _ _
          (Subalgebra.coe_iSup_of_directed
            (K := fun i => (K i).toSubalgebra)
            (fun i j => by
              obtain ⟨k, hik, hjk⟩ := dir i j
              exact ⟨k, hik, hjk⟩)).symm
      star_mem' := by
        intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        exact Set.mem_iUnion.2 ⟨i, star_mem (s := K i) hi⟩ }
  have hSU : (⨆ i, K i) = S := by
    apply le_antisymm
    · exact iSup_le (fun i => by
        intro x hx
        exact Set.mem_iUnion.2 ⟨i, hx⟩)
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact (le_iSup K i) hi
  rw [hSU]
  rfl

/-- **W1 — PROVED 2026-09-10.** The tower of finite-level embeddings on
    `TimelessFieldCompletion` as `StarSubalgebra` ranges. -/
noncomputable def substrateTFCtower :
    ℕ → StarSubalgebra ℂ TimelessFieldCompletion :=
  fun k => (substrateLevelStarAlgHom k).range

/-- **W2 — PROVED 2026-09-10.** Each level of the tower is
    *-alg-isomorphic to `M_{3^k}(ℂ)`.

    Strategy: `substrateLevelStarAlgHom k` is injective (composition of
    two injective *-alg-homs). Then `StarAlgEquiv.ofInjective` gives a
    `StarAlgEquiv` onto its range, i.e. onto `substrateTFCtower k` by
    definition. Take `.symm` for the direction from the range to the
    matrix algebra.

    Injectivity of the two factors:
      · `substrateLevelToTimelessFieldStarAlgHom k` is injective because
        `substrateLevelToTimelessField_opNorm_eq k` gives an isometry:
        `f A = 0 → ‖A‖ = ‖f A‖ = 0 → A = 0`, then chain via `map_sub`.
      · `TimelessFieldRingToCompletionStarAlgHom` is injective by
        `UniformSpace.Completion.coe_injective` (mathlib
        `Mathlib/Topology/UniformSpace/Completion.lean:356`, requires
        `T0Space TimelessFieldRing`, supplied by the `NormedAddCommGroup`
        instance from `SubstrateTimelessFieldNorm`). -/
lemma substrateTFCtower_matrix (k : ℕ) :
    Nonempty (substrateTFCtower k ≃⋆ₐ[ℂ]
              Matrix (Fin (3^k)) (Fin (3^k)) ℂ) := by
  -- Injectivity of the level→TimelessFieldRing factor via isometry.
  have hinj_level :
      Function.Injective (substrateLevelToTimelessFieldStarAlgHom k) := by
    intro A B hAB
    have hzero :
        substrateLevelToTimelessFieldStarAlgHom k (A - B) = 0 := by
      rw [map_sub, hAB, sub_self]
    have hf_zero : substrateLevelToTimelessField k (A - B) = 0 := hzero
    have hnorm :
        ‖substrateLevelToTimelessField k (A - B)‖ = ‖A - B‖ :=
      substrateLevelToTimelessField_opNorm_eq k (A - B)
    have hzero_norm : ‖A - B‖ = 0 := by
      rw [← hnorm, hf_zero, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero_norm)
  -- Injectivity of the TimelessFieldRing → Completion factor.
  have hinj_coe :
      Function.Injective TimelessFieldRingToCompletionStarAlgHom := by
    intro x y hxy
    exact UniformSpace.Completion.coe_injective TimelessFieldRing hxy
  -- Composition is injective.
  have hinj : Function.Injective (substrateLevelStarAlgHom k) :=
    hinj_coe.comp hinj_level
  -- Package via StarAlgEquiv.ofInjective (mathlib Star/Subalgebra.lean:817).
  exact ⟨(StarAlgEquiv.ofInjective (substrateLevelStarAlgHom k) hinj).symm⟩

/-- **W3 — PROVED 2026-09-10.** The tower is monotone under inclusion.

    Proof: for `x ∈ (substrateLevelStarAlgHom k).range`, write
    `x = substrateLevelStarAlgHom k A`; then take the preimage at level
    `k+1` to be `substrateRingHomIter k (k+1) (Nat.le_succ k) A`. The
    cocone identity `substrateLevelToTimelessField_iter` (from
    `PF/SubstrateCompletionFaithful.lean:97`) gives
      `substrateLevelToTimelessField (k+1) (substrateRingHomIter k (k+1) _ A)
        = substrateLevelToTimelessField k A`
    and pushing through the coercion `TimelessFieldRingToCompletionStarAlgHom`
    delivers equality in the completion. -/
lemma substrateTFCtower_mono (k : ℕ) :
    substrateTFCtower k ≤ substrateTFCtower (k+1) := by
  rintro _ ⟨A, rfl⟩
  refine ⟨substrateRingHomIter k (k+1) (Nat.le_succ k) A, ?_⟩
  -- Unfold `substrateLevelStarAlgHom` as
  -- `TimelessFieldRingToCompletionStarAlgHom.comp
  --    substrateLevelToTimelessFieldStarAlgHom`.
  show TimelessFieldRingToCompletionStarAlgHom
        (substrateLevelToTimelessFieldStarAlgHom (k+1)
          (substrateRingHomIter k (k+1) (Nat.le_succ k) A))
      = TimelessFieldRingToCompletionStarAlgHom
          (substrateLevelToTimelessFieldStarAlgHom k A)
  congr 1
  -- Reduce to the underlying-function identity in `TimelessFieldRing`.
  show substrateLevelToTimelessField (k+1)
        (substrateRingHomIter k (k+1) (Nat.le_succ k) A)
      = substrateLevelToTimelessField k A
  exact substrateLevelToTimelessField_iter k (k+1) (Nat.le_succ k) A

/-- **W4 — PROVED 2026-09-10.** The union of the tower is dense in the
    completion.

    Proof: `substrateTFCtower` is directed (monotone chain via
    `substrateTFCtower_mono`), so `coe_iSup_of_directed_starSubalgebra`
    reduces the goal to density of `⋃ k, range (substrateLevelStarAlgHom k)`.
    Pablo's `substrate_finite_level_dense` produces, for any
    `x : TimelessFieldCompletion` and `ε > 0`, a level `k` and matrix `a`
    whose image in the completion is within `ε` of `x`; that image lies in
    `range (substrateLevelStarAlgHom k)` by `⟨a, rfl⟩`. -/
lemma substrateTFCtower_dense :
    Dense (((⨆ k, substrateTFCtower k
              : StarSubalgebra ℂ TimelessFieldCompletion)
              : Set TimelessFieldCompletion)) := by
  have tower_le : ∀ m n, m ≤ n → substrateTFCtower m ≤ substrateTFCtower n := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | step _ ih => exact ih.trans (substrateTFCtower_mono _)
  have dir : Directed (· ≤ ·) substrateTFCtower := fun i j =>
    ⟨max i j, tower_le i _ (le_max_left _ _), tower_le j _ (le_max_right _ _)⟩
  rw [coe_iSup_of_directed_starSubalgebra_W4 dir]
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨k, a, hka⟩ := substrate_finite_level_dense x hε
  refine ⟨((substrateLevelToTimelessField k a : TimelessFieldRing) :
            TimelessFieldCompletion),
    Set.mem_iUnion.mpr ⟨k, ⟨a, rfl⟩⟩, hka⟩

/-- **W5 — PROVED 2026-09-10.** Unique tracial linear functional on the
    completion — discharges via Pablo's `substrate_UHF_trace_unique` +
    `UHF_trace` + `uhf_trace_isTracialState`. -/
lemma substrateTFCtower_trace_unique :
    ∃! τ : TimelessFieldCompletion → ℂ,
      IsTracialLinearFunctional TimelessFieldCompletion τ := by
  refine ⟨UHF_trace, ?_, ?_⟩
  · -- existence: UHF_trace is a tracial linear functional
    exact
      { continuous := uhf_trace_isTracialState.continuous
        add        := uhf_trace_isTracialState.add
        smul       := uhf_trace_isTracialState.smul
        tracial    := uhf_trace_isTracialState.tracial
        unital     := uhf_trace_isTracialState.unital }
  · -- uniqueness: any tracial linear functional agrees with UHF_trace pointwise
    intro τ hτ
    funext x
    have hτ' : IsTracialState τ :=
      { continuous := hτ.continuous
        add        := hτ.add
        smul       := hτ.smul
        tracial    := hτ.tracial
        unital     := hτ.unital }
    exact substrate_UHF_trace_unique τ hτ' x

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
    have h1 : (fun _ : Fin k => (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)) c)
              = c • (1 : Fin k → Matrix (Fin n) (Fin n) ℂ) := by
      funext i
      simp [Algebra.algebraMap_eq_smul_one]
    rw [h1, Matrix.blockDiagonal_smul, Matrix.blockDiagonal_one]
    show (Matrix.reindexAlgEquiv ℂ ℂ
            (Equiv.prodComm (Fin n) (Fin k))) (c • 1)
          = algebraMap ℂ _ c
    rw [map_smul, _root_.map_one, Algebra.algebraMap_eq_smul_one]
  map_star' := blockDiagonalConstMap_star n k

/-- **C1.4 — PROVED 2026-09-10.** Block-diagonal *-alg-hom is injective
    for `k > 0`.

    Proof structure: `blockDiagonalConstStarHom n k` is definitionally
    the composition
      `reindexAlgEquiv (prodComm) ∘ blockDiagonal ∘ (fun x => fun _ => x)`.
    Each factor is injective:
      · `reindexAlgEquiv` is an `AlgEquiv`, hence injective;
      · `Matrix.blockDiagonal_injective` (mathlib
        `Mathlib/Data/Matrix/Block.lean:506`);
      · the constant lift `x ↦ (fun _ : Fin k => x)` is injective when
        `Fin k` is inhabited — recover `x` by evaluating at any
        `i : Fin k`, which exists via `[NeZero k]`. -/
lemma blockDiagonalConstStarHom_injective [NeZero k] :
    Function.Injective (blockDiagonalConstStarHom n k) := by
  intro x y hxy
  -- Peel the StarAlgHom wrapper: underlying toFun is blockDiagonalConstMap.
  have h1 : blockDiagonalConstMap n k x = blockDiagonalConstMap n k y := hxy
  -- Unfold to the reindexed blockDiagonal of the constant family.
  have h2 : Matrix.reindex (Equiv.prodComm (Fin n) (Fin k))
              (Equiv.prodComm (Fin n) (Fin k))
              (Matrix.blockDiagonal (fun _ : Fin k => x))
            = Matrix.reindex (Equiv.prodComm (Fin n) (Fin k))
                (Equiv.prodComm (Fin n) (Fin k))
                (Matrix.blockDiagonal (fun _ : Fin k => y)) := h1
  -- Strip the reindex (it's an AlgEquiv, hence injective).
  have h3 : Matrix.blockDiagonal (fun _ : Fin k => x)
            = Matrix.blockDiagonal (fun _ : Fin k => y) :=
    (Matrix.reindexAlgEquiv ℂ ℂ
        (Equiv.prodComm (Fin n) (Fin k))).injective h2
  -- Strip blockDiagonal via mathlib's Matrix.blockDiagonal_injective.
  have h4 : (fun _ : Fin k => x) = (fun _ : Fin k => y) :=
    Matrix.blockDiagonal_injective h3
  -- Evaluate the equal constant functions at index 0 (exists via NeZero k).
  have hpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  exact congr_fun h4 ⟨0, hpos⟩

/-- **C1.5 — PROVED 2026-09-10.** The `Fin (k * n)`-indexed version
    required by C4. Compose C1.3 (`blockDiagonalConstStarHom`) with the
    reindex `Fin k × Fin n ≃ Fin (k * n)` from `finProdFinEquiv`.

    Mathlib v4.24.0-rc1 has `Matrix.reindexAlgEquiv` but no
    `Matrix.reindexStarAlgEquiv`. We upgrade `reindexAlgEquiv` to a
    `StarAlgHom` inline using `Matrix.conjTranspose_reindex`
    (`Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:428`) —
    definitionally `rfl` since `reindex e e` uses the same `e` for
    rows and cols (same pattern as C1.2).

    Note: the reindex equiv is specialised via `(finProdFinEquiv :
    Fin k × Fin n ≃ Fin (k * n))` to pin the `Fin` sizes, and we
    convert to `AlgHom` via `.toAlgHom` (not a coercion ascription)
    to avoid metavariable ambiguity in typeclass search. -/
noncomputable def blockDiagonalStarAlgHom :
    Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
  let e : Fin k × Fin n ≃ Fin (k * n) := finProdFinEquiv
  let reindexStar :
      Matrix (Fin k × Fin n) (Fin k × Fin n) ℂ →⋆ₐ[ℂ]
        Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
    { (Matrix.reindexAlgEquiv ℂ ℂ e).toAlgHom with
      map_star' := fun x => by
        change Matrix.reindex e e (star x) = star (Matrix.reindex e e x)
        rw [show (star :
              Matrix (Fin (k * n)) (Fin (k * n)) ℂ →
              Matrix (Fin (k * n)) (Fin (k * n)) ℂ)
              = Matrix.conjTranspose from rfl,
            Matrix.conjTranspose_reindex]
        rfl }
  reindexStar.comp (blockDiagonalConstStarHom n k)

/-- **C1.6 — PROVED 2026-09-10.** The reindexed version is injective
    for `k > 0`. Composition of two injective maps: the reindex layer
    is `Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv` (an `AlgEquiv`,
    hence injective) and the inner map is `blockDiagonalConstStarHom`
    (injective by C1.4). -/
lemma blockDiagonalStarAlgHom_injective [NeZero k] :
    Function.Injective (blockDiagonalStarAlgHom n k) := by
  intro x y hxy
  -- Peel the composition: blockDiagonalStarAlgHom is defeq to
  -- reindexStar.comp (blockDiagonalConstStarHom n k); applied to x
  -- this reduces to reindexAlgEquiv (blockDiagonalConstStarHom n k x).
  have h1 : (Matrix.reindexAlgEquiv ℂ ℂ
              (finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n)))
              (blockDiagonalConstStarHom n k x)
            = (Matrix.reindexAlgEquiv ℂ ℂ
              (finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n)))
              (blockDiagonalConstStarHom n k y) := hxy
  -- reindexAlgEquiv is an AlgEquiv, hence injective.
  have h2 : blockDiagonalConstStarHom n k x
            = blockDiagonalConstStarHom n k y :=
    (Matrix.reindexAlgEquiv ℂ ℂ
      (finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n))).injective h1
  -- Close with C1.4.
  exact blockDiagonalConstStarHom_injective n k h2

/-- **C1.7 — PROVED 2026-09-10.** The reindexed version is unital.
    Automatic from the `StarAlgHom` structure via `map_one`. -/
lemma blockDiagonalStarAlgHom_unital :
    blockDiagonalStarAlgHom n k 1 = 1 :=
  map_one _

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

/-- **C3.1 helper.** For a directed family `K : ι → StarSubalgebra ℂ A`,
    the underlying set of `⨆ i, K i` is the union of the underlying sets.
    Mirrors `NonUnitalStarSubalgebra.coe_iSup_of_directed` for the unital
    case, since mathlib does not yet ship this. -/
private lemma coe_iSup_of_directed_starSubalgebra
    {ι : Type*} [Nonempty ι] {K : ι → StarSubalgebra ℂ A}
    (dir : Directed (· ≤ ·) K) :
    ((⨆ i, K i : StarSubalgebra ℂ A) : Set A) = ⋃ i, (K i : Set A) := by
  let S : StarSubalgebra ℂ A :=
    { toSubalgebra :=
        Subalgebra.copy _ _
          (Subalgebra.coe_iSup_of_directed
            (K := fun i => (K i).toSubalgebra)
            (fun i j => by
              obtain ⟨k, hik, hjk⟩ := dir i j
              exact ⟨k, hik, hjk⟩)).symm
      star_mem' := by
        intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        exact Set.mem_iUnion.2 ⟨i, star_mem (s := K i) hi⟩ }
  have hSU : (⨆ i, K i) = S := by
    apply le_antisymm
    · exact iSup_le (fun i => by
        intro x hx
        exact Set.mem_iUnion.2 ⟨i, hx⟩)
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact (le_iSup K i) hi
  rw [hSU]
  rfl

/-- **C3.1.** From a coherent family of `*-alg-homs` out of each tower
    level, glue to a single `*-alg-hom` on `⨆ k, h.tower k`.

    Uses `Set.iUnionLift` on the underlying carrier, then packages the
    seven `StarAlgHom` fields via `iUnionLift_const`, `iUnionLift_binary`
    and `iUnionLift_unary`.

    The `compat` hypothesis feeds the well-definedness proof
    `(fam i x = fam j x on overlaps)` — using `tower_mono` to move both
    into a common level `k` reached from `i, j` via the directedness of
    the tower. -/
noncomputable def tower_union_starHom
    (h : Substrate3Inf A) {B : Type*} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k)) = fam k) :
    (⨆ k, h.tower k : StarSubalgebra ℂ A) →⋆ₐ[ℂ] B := by
  -- Monotone chain lemma (Nat).
  have tower_le : ∀ m n, m ≤ n → h.tower m ≤ h.tower n := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | step _ ih => exact ih.trans (h.tower_mono _)
  -- Directedness of the tower.
  have dir : Directed (· ≤ ·) h.tower := fun i j =>
    ⟨max i j, tower_le i _ (le_max_left _ _), tower_le j _ (le_max_right _ _)⟩
  -- Family compatibility on overlaps: `fam i x = fam j (inclusion x)` whenever
  -- j ≥ i, by induction on the gap using `compat`.
  have hf_step : ∀ n i (x : h.tower i),
      fam i x = fam (i + n)
        (StarSubalgebra.inclusion (tower_le i (i + n) (Nat.le_add_right _ _)) x) := by
    intro n
    induction n with
    | zero => intro i x; rfl
    | succ m ih =>
      intro i x
      have hcompat := congr_fun (congr_arg DFunLike.coe (compat (i + m)))
        (StarSubalgebra.inclusion (tower_le i (i + m) (Nat.le_add_right _ _)) x)
      -- compat (i+m) : (fam (i+m+1)).comp (inclusion (tower_mono (i+m))) = fam (i+m)
      -- so fam (i+m+1) (inclusion _ y) = fam (i+m) y  for y : h.tower (i+m)
      -- Chain from x : h.tower i → h.tower (i+m) → h.tower (i+m+1).
      -- goal: fam i x = fam (i + (m+1)) (inclusion _ x)
      rw [ih i x]
      -- now: fam (i+m) (inclusion (tower_le _ _ _) x) = fam (i+(m+1)) (inclusion _ x)
      rw [← hcompat]
      rfl
  have hf_le : ∀ i j (hij : h.tower i ≤ h.tower j) (x : h.tower i),
      fam i x = fam j (StarSubalgebra.inclusion hij x) := by
    intro i j hij x
    by_cases hle : i ≤ j
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hle
      exact hf_step n i x
    · push_neg at hle
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hle)
      -- i = j + m. Move fam j (inclusion hij x) forward to level i via step.
      have hstep := hf_step m j (StarSubalgebra.inclusion hij x)
      -- hstep : fam j (inclusion hij x) = fam (j+m) (inclusion _ (inclusion hij x))
      -- With j + m = i, the inner double-inclusion is inclusion (le_refl _), i.e. x.
      rw [hstep]
      subst hm
      rfl
  -- Set-level identity for the supremum.
  have hT_coe : ((⨆ k, h.tower k : StarSubalgebra ℂ A) : Set A)
                  = ⋃ k, ((h.tower k) : Set A) :=
    coe_iSup_of_directed_starSubalgebra dir
  -- Well-definedness on overlaps.
  have hwd : ∀ (i j : ℕ) (x : A) (hxi : x ∈ h.tower i) (hxj : x ∈ h.tower j),
      fam i ⟨x, hxi⟩ = fam j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    obtain ⟨k, hik, hjk⟩ := dir i j
    rw [hf_le i k hik ⟨x, hxi⟩, hf_le j k hjk ⟨x, hxj⟩]
    rfl
  -- Build the raw function first; collect field lemmas as `have`.
  set F : ((⨆ k, h.tower k : StarSubalgebra ℂ A)) → B :=
    Set.iUnionLift (fun k => ((h.tower k) : Set A))
      (fun k x => fam k x) (fun i j x hxi hxj => hwd i j x hxi hxj)
      (((⨆ k, h.tower k : StarSubalgebra ℂ A)) : Set A) hT_coe.subset with hF
  have F_one : F 1 = (1 : B) := by
    dsimp only [F]
    exact Set.iUnionLift_const (1 : (⨆ k, h.tower k : StarSubalgebra ℂ A))
      (fun k => (1 : h.tower k)) (fun _ => rfl) 1 (fun k => (fam k).map_one')
  have F_zero : F 0 = (0 : B) := by
    dsimp only [F]
    exact Set.iUnionLift_const (0 : (⨆ k, h.tower k : StarSubalgebra ℂ A))
      (fun k => (0 : h.tower k)) (fun _ => rfl) 0
      (fun k => (fam k).toAlgHom.toRingHom.map_zero)
  have F_mul : ∀ x y, F (x * y) = F x * F y := by
    intro x y
    dsimp only [F]
    exact Set.iUnionLift_binary (hT' := hT_coe) dir _ (fun _ => (· * ·))
      (fun _ _ _ => rfl) (fun a b => a * b)
      (fun k x y => (fam k).map_mul' x y) x y
  have F_add : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    dsimp only [F]
    exact Set.iUnionLift_binary (hT' := hT_coe) dir _ (fun _ => (· + ·))
      (fun _ _ _ => rfl) (fun a b => a + b)
      (fun k x y => (fam k).toAlgHom.toRingHom.map_add x y) x y
  have F_alg : ∀ r : ℂ,
      F (algebraMap ℂ (⨆ k, h.tower k : StarSubalgebra ℂ A) r)
        = algebraMap ℂ B r := by
    intro r
    dsimp only [F]
    exact Set.iUnionLift_const (algebraMap ℂ _ r)
      (fun k => algebraMap ℂ (h.tower k) r) (fun _ => rfl) (algebraMap ℂ B r)
      (fun k => (fam k).commutes' r)
  have F_star : ∀ x, F (star x) = star (F x) := by
    intro x
    dsimp only [F]
    exact Set.iUnionLift_unary (hT' := hT_coe) _
      (fun _ y => star y) (fun _ _ => rfl) (fun b => star b)
      (fun k y => (fam k).map_star' y) x
  exact
    { toFun := F
      map_one' := F_one
      map_mul' := F_mul
      map_zero' := F_zero
      map_add' := F_add
      commutes' := F_alg
      map_star' := F_star }

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
