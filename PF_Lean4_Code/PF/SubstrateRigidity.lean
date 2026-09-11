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
import Mathlib.LinearAlgebra.Matrix.Trace     -- for C2.7 (trace-of-projection)
import Mathlib.LinearAlgebra.Matrix.ToLin     -- for C2.7 (Matrix.toLin')
import Mathlib.LinearAlgebra.Trace            -- for C2.7 (IsProj.trace, trace_toLin'_eq)
import Mathlib.LinearAlgebra.Projection       -- for C2.7 (IsIdempotentElem.isProj_range)
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
  fun _ _ => rfl

/-- **C3.mid.1 — PROVED 2026-09-10.** Each tower level is a closed
    subalgebra of the ambient C*-algebra `A`.

    Proof strategy: use the finite-dimension route rather than the
    completeness-transfer route, because `StarAlgEquiv.isometry` in
    mathlib requires `NonUnitalCStarAlgebra` on the source, which is
    not synthesizable on a general `StarSubalgebra` until we already
    know it is closed (circular). Instead:
      1. Extract `e : h.tower k ≃⋆ₐ[ℂ] M_{3^k}(ℂ)` and view its
         `.symm.toLinearEquiv` as a `ℂ`-linear equivalence
         `M_{3^k}(ℂ) ≃ₗ[ℂ] ↥(h.tower k)`.
      2. `M_{3^k}(ℂ)` is finite-dimensional over `ℂ`
         (`Matrix.instFiniteDimensional`), so `LinearEquiv.finiteDimensional`
         (mathlib `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:240`)
         transfers `FiniteDimensional ℂ ↥(h.tower k)`.
      3. `Subalgebra.toSubmoduleEquiv` (mathlib
         `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:390`) is a
         linear equiv between the submodule and the subtype, so its
         `.symm` transfers finite-dimensionality to
         `Subalgebra.toSubmodule (h.tower k).toSubalgebra`.
      4. `Submodule.closed_of_finiteDimensional` (mathlib
         `Mathlib/Topology/Algebra/Module/FiniteDimension.lean:517`)
         yields `IsClosed ((toSubmodule (h.tower k).toSubalgebra) : Set A)`.
      5. `Subalgebra.coe_toSubmodule` (mathlib
         `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:285`) identifies
         the underlying set with `(h.tower k : Set A)`. -/
lemma tower_level_isClosed (k : ℕ) :
    IsClosed ((h.tower k : StarSubalgebra ℂ A) : Set A) := by
  -- Step 1: extract the matrix isomorphism.
  obtain ⟨e⟩ := h.tower_matrix k
  -- Step 2: transfer FiniteDimensional to the subtype via e.symm.
  have h_matrix_findim :
      FiniteDimensional ℂ (Matrix (Fin (3^k)) (Fin (3^k)) ℂ) := inferInstance
  have h_tower_findim : FiniteDimensional ℂ (h.tower k) :=
    LinearEquiv.finiteDimensional
      (e.symm.toAlgEquiv.toLinearEquiv :
        Matrix (Fin (3^k)) (Fin (3^k)) ℂ ≃ₗ[ℂ] ↥(h.tower k))
  -- Step 3: propagate to the underlying submodule.
  have h_submod_findim :
      FiniteDimensional ℂ (Subalgebra.toSubmodule (h.tower k).toSubalgebra) :=
    LinearEquiv.finiteDimensional
      (Subalgebra.toSubmoduleEquiv (h.tower k).toSubalgebra).symm
  -- Step 4: finite-dim submodule of a T2 topological ℂ-module is closed.
  have h_submod_closed :
      IsClosed ((Subalgebra.toSubmodule (h.tower k).toSubalgebra) : Set A) :=
    Submodule.closed_of_finiteDimensional _
  -- Step 5: the coercion agrees with (h.tower k : Set A) definitionally.
  exact h_submod_closed

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

/-! ### C2.1 – C2.5 — Matrix-unit calculus foundations

Per `codex/C2_STATEMENT_CARDS_2026-09-10.md`, these five sub-cards
establish the basic algebra of the target matrix units
`E^φ_{ij} := φ(single i j 1)`. They land as helpers for the main
`unital_star_hom_inner_unique` below.
-/

/-- **C2.1.** The φ-image of the standard matrix unit `e_{ij}`. -/
noncomputable def E_of
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) (i j : Fin n) :
    Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
  φ (Matrix.single i j 1)

/-- **C2.2.** Matrix-unit multiplication (matching middle indices). -/
lemma E_of_mul_same
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) (i j l : Fin n) :
    E_of n k φ i j * E_of n k φ j l = E_of n k φ i l := by
  unfold E_of
  rw [← map_mul, Matrix.single_mul_single_same, one_mul]

/-- **C2.3.** Matrix-unit orthogonality (mismatched middle indices). -/
lemma E_of_mul_diff
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ)
    (i j p l : Fin n) (h : j ≠ p) :
    E_of n k φ i j * E_of n k φ p l = 0 := by
  unfold E_of
  rw [← map_mul, Matrix.single_mul_single_of_ne (c := (1 : ℂ)) i j p h 1, map_zero]

/-- **C2.4.** Star of a matrix-unit image is the transposed matrix-unit image.
    Uses `Matrix.conjTranspose_single` (mathlib) via
    `Matrix.star_eq_conjTranspose`. -/
lemma E_of_star
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) (i j : Fin n) :
    star (E_of n k φ i j) = E_of n k φ j i := by
  unfold E_of
  rw [← map_star]
  congr 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]

/-- **C2.5.** Diagonal matrix-unit images resolve the identity:
    `Σ_i E^φ_{ii} = 1`. -/
lemma E_of_sum_diagonal
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    ∑ i : Fin n, E_of n k φ i i = 1 := by
  unfold E_of
  rw [← map_sum]
  convert map_one φ
  have hsum : ∑ i : Fin n, Matrix.single (α := ℂ) i i 1 = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext p q
    rw [Matrix.sum_apply, Matrix.one_apply]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl, Finset.sum_eq_single p]
      · simp [Matrix.single]
      · intro i _ hi; simp [Matrix.single]; exact hi
      · intro h; exact absurd (Finset.mem_univ p) h
    · rw [if_neg hpq]
      apply Finset.sum_eq_zero
      intro i _
      simp [Matrix.single]
      intro h1 h2
      exact absurd (h1.symm.trans h2) hpq
  exact hsum

/-- **C2.6.** For a unital *-hom `φ : M_n(ℂ) →⋆ₐ[ℂ] M_{k*n}(ℂ)`,
    the image `E_of φ i i` of a diagonal matrix unit is a self-adjoint
    idempotent (projection). Immediate from C2.2 (`E_of_mul_same`) and
    C2.4 (`E_of_star`). -/
lemma E_of_i_i_isProjection
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) (i : Fin n) :
    E_of n k φ i i * E_of n k φ i i = E_of n k φ i i ∧
    star (E_of n k φ i i) = E_of n k φ i i :=
  ⟨E_of_mul_same n k φ i i i, E_of_star n k φ i i⟩

/-- **C2.7 – helper A.** All diagonal `E_of φ i i` share a common `Matrix.trace`.
    Proof: `E_of i i = E_of i 0 * E_of 0 i` (by C2.2) and
    `E_of 0 0 = E_of 0 i * E_of i 0` (by C2.2); traces of `AB` and `BA` agree. -/
lemma E_of_i_i_trace_eq_00 [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) (i : Fin n) :
    Matrix.trace (E_of n k φ i i) = Matrix.trace (E_of n k φ ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩) := by
  set z : Fin n := ⟨0, Nat.pos_of_neZero n⟩ with hz
  have h1 : E_of n k φ i i = E_of n k φ i z * E_of n k φ z i :=
    (E_of_mul_same n k φ i z i).symm
  have h2 : E_of n k φ z z = E_of n k φ z i * E_of n k φ i z :=
    (E_of_mul_same n k φ z i z).symm
  rw [h1, h2, Matrix.trace_mul_comm]

/-- **C2.7 – helper B.** `Matrix.trace (E_of φ 0 0) = k` as a complex scalar.

    Proof: `∑_i E_of φ i i = 1` (C2.5); taking `Matrix.trace` gives
    `n • trace(E_of φ 0 0) = Matrix.trace (1 : M_{kn}) = kn`; divide by `n`. -/
lemma E_of_00_trace_eq_k [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    Matrix.trace (E_of n k φ ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩) = (k : ℂ) := by
  set z : Fin n := ⟨0, Nat.pos_of_neZero n⟩ with hz
  -- Sum of diagonals equals identity (C2.5); trace preserves sums.
  have hsum := E_of_sum_diagonal n k φ
  have htrace_sum :
      ∑ i : Fin n, Matrix.trace (E_of n k φ i i) =
        Matrix.trace (1 : Matrix (Fin (k * n)) (Fin (k * n)) ℂ) := by
    rw [← hsum, Matrix.trace_sum]
  -- Every diagonal has trace equal to E_of φ 0 0's trace.
  have hconst :
      ∀ i : Fin n, Matrix.trace (E_of n k φ i i) = Matrix.trace (E_of n k φ z z) :=
    fun i => E_of_i_i_trace_eq_00 n k φ i
  -- Turn LHS into `n • trace(E_of 0 0)`.
  have hLHS :
      ∑ i : Fin n, Matrix.trace (E_of n k φ i i) =
        (n : ℂ) * Matrix.trace (E_of n k φ z z) := by
    rw [Finset.sum_congr rfl (fun i _ => hconst i)]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- RHS: `trace (1 : M_{kn}) = k * n`.
  have hRHS :
      Matrix.trace (1 : Matrix (Fin (k * n)) (Fin (k * n)) ℂ) = ((k * n : ℕ) : ℂ) := by
    rw [Matrix.trace_one, Fintype.card_fin]
  -- Combine and divide by n.
  have hn_ne : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n).ne'
  have hcomb := htrace_sum
  rw [hLHS, hRHS] at hcomb
  -- Rearrange to `trace(E_of 0 0) * n = k * n` and cancel n.
  have hmul : Matrix.trace (E_of n k φ z z) * (n : ℂ) = (k : ℂ) * (n : ℂ) := by
    have hcast : ((k * n : ℕ) : ℂ) = (k : ℂ) * (n : ℂ) := by push_cast; ring
    rw [mul_comm]; rw [← hcast]; exact hcomb
  exact mul_right_cancel₀ hn_ne hmul

/-- **C2.7 (deepest single sub-card of the C2 arc).**
    For a unital *-hom `φ : M_n(ℂ) →⋆ₐ[ℂ] M_{k*n}(ℂ)`, the range of the
    projection `E_of φ 0 0` (viewed via `Matrix.toLin'`) has `finrank = k`.

    **Proof strategy.** By C2.6 the matrix `E := E_of φ 0 0` is idempotent
    (`E * E = E`). Hence `Matrix.toLin' E : ℂ^{kn} →ₗ ℂ^{kn}` is idempotent,
    which by `IsIdempotentElem.isProj_range` gives
    `IsProj (LinearMap.range (Matrix.toLin' E)) (Matrix.toLin' E)`. Then
    `IsProj.trace` yields
    `LinearMap.trace ℂ _ (Matrix.toLin' E) = finrank ℂ (range (Matrix.toLin' E))`
    (as a complex scalar). By `Matrix.trace_toLin'_eq` the LHS equals
    `Matrix.trace E`, which by `E_of_00_trace_eq_k` equals `k`. So the
    `finrank` (a `ℕ` embedded in `ℂ`) equals `k`; `Nat.cast_injective` closes. -/
lemma E_of_00_range_finrank [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    Module.finrank ℂ
      (LinearMap.range (Matrix.toLin'
        (E_of n k φ ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩))) = k := by
  set z : Fin n := ⟨0, Nat.pos_of_neZero n⟩ with hz
  set E := E_of n k φ z z with hE
  -- C2.6: E is idempotent as a matrix product.
  have hEE : E * E = E := (E_of_i_i_isProjection n k φ z).1
  -- Transport to `Matrix.toLin'` (which is an AlgHom on square matrices).
  have hidem : IsIdempotentElem (Matrix.toLin' E) := by
    show Matrix.toLin' E * Matrix.toLin' E = Matrix.toLin' E
    rw [show (Matrix.toLin' E * Matrix.toLin' E : Module.End ℂ _)
          = Matrix.toLin' E ∘ₗ Matrix.toLin' E from rfl,
        ← Matrix.toLin'_mul, hEE]
  -- Idempotent linear endomorphism is a projection onto its range.
  have hproj : LinearMap.IsProj (LinearMap.range (Matrix.toLin' E)) (Matrix.toLin' E) :=
    LinearMap.IsIdempotentElem.isProj_range _ hidem
  -- IsProj.trace: trace = finrank of range (as ℂ-scalar).
  have htr : LinearMap.trace ℂ _ (Matrix.toLin' E) =
      (Module.finrank ℂ (LinearMap.range (Matrix.toLin' E)) : ℂ) :=
    hproj.trace
  -- Matrix.trace_toLin'_eq bridges to Matrix.trace.
  have hbridge : LinearMap.trace ℂ _ (Matrix.toLin' E) = Matrix.trace E :=
    Matrix.trace_toLin'_eq E
  -- E_of_00_trace_eq_k: Matrix.trace E = k.
  have hval : Matrix.trace E = (k : ℂ) := E_of_00_trace_eq_k n k φ
  -- Combine: (finrank : ℂ) = k, then cast back to ℕ.
  have hcast : (Module.finrank ℂ (LinearMap.range (Matrix.toLin' E)) : ℂ) = (k : ℂ) := by
    rw [← htr, hbridge, hval]
  exact_mod_cast hcast

/-- **C2.8a.** Adapter: `E_of_00_range_finrank` transported to
    `Matrix.toEuclideanLin` (the `EuclideanSpace` version of `Matrix.toLin'`).

    **Mathlib citations.**
    - `Matrix.toEuclideanLin` = `Matrix.toLin' ≪≫ₗ arrowCongr ...`
      in `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.
    - `LinearEquiv.finrank_map_eq` in
      `Mathlib/LinearAlgebra/Dimension/Finrank.lean`. -/
lemma E_of_00_toEuclideanLin_range_finrank [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    Module.finrank ℂ
      (LinearMap.range (Matrix.toEuclideanLin
        (E_of n k φ ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩))) = k := by
  set E := E_of n k φ ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩ with hE
  -- toEuclideanLin E factors as an equiv-postcompose of (toLin' E ∘ equiv).
  set fψ : EuclideanSpace ℂ (Fin (k * n)) ≃ₗ[ℂ] (Fin (k * n) → ℂ) :=
    WithLp.linearEquiv 2 ℂ (Fin (k * n) → ℂ) with hfψ
  have hdecomp : Matrix.toEuclideanLin E =
      fψ.symm.toLinearMap ∘ₗ (Matrix.toLin' E ∘ₗ fψ.toLinearMap) := by
    ext v; rfl
  -- range (fψ.symm ∘ₗ (toLin' E ∘ₗ fψ)) = ((range (toLin' E ∘ₗ fψ))).map fψ.symm
  --                                    = ((range (toLin' E))).map fψ.symm (fψ is surjective)
  have hrange_inner : LinearMap.range (Matrix.toLin' E ∘ₗ fψ.toLinearMap)
      = LinearMap.range (Matrix.toLin' E) := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have hrange : LinearMap.range (Matrix.toEuclideanLin E)
      = (LinearMap.range (Matrix.toLin' E)).map fψ.symm.toLinearMap := by
    rw [hdecomp, LinearMap.range_comp, hrange_inner]
  rw [hrange, LinearEquiv.finrank_map_eq]
  exact E_of_00_range_finrank n k φ

/-- **C2.8b.** Standard orthonormal basis of `range(E_of φ 0 0)` viewed
    via `Matrix.toEuclideanLin`, indexed by `Fin k` (via `C2.8a`).

    **Mathlib citations.**
    - `stdOrthonormalBasis` in `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.
    - `OrthonormalBasis.reindex` with `finCongr`. -/
noncomputable def E_of_00_stdOrthonormalBasis [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    OrthonormalBasis (Fin k) ℂ
      (LinearMap.range (Matrix.toEuclideanLin
        (E_of n k φ ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩))) :=
  (stdOrthonormalBasis ℂ (LinearMap.range (Matrix.toEuclideanLin
    (E_of n k φ ⟨0, Nat.pos_of_neZero n⟩ ⟨0, Nat.pos_of_neZero n⟩)))).reindex
    (finCongr (E_of_00_toEuclideanLin_range_finrank n k φ))

/-- **C2.8c.** Transported family of vectors indexed by `Fin n × Fin k`:
    `phiONB_family φ (i, a) := E_of φ i 0 · (stdBasis a)`, where `stdBasis a`
    is the `a`-th vector of the standard ONB of `range(E_of φ 0 0)`
    (from C2.8b). This is a "partial isometry from level 0 to level i".

    Uses `Matrix.toEuclideanLin` to view `E_of φ i 0` as a linear map on
    `EuclideanSpace ℂ (Fin (k*n))`. -/
noncomputable def phiONB_family [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    (Fin n × Fin k) → EuclideanSpace ℂ (Fin (k * n)) :=
  fun p =>
    Matrix.toEuclideanLin (E_of n k φ p.1 ⟨0, Nat.pos_of_neZero n⟩)
      ((E_of_00_stdOrthonormalBasis n k φ p.2 : EuclideanSpace ℂ (Fin (k * n))))

/-- **C2.8d – helper 1.** `toEuclideanLin` respects matrix multiplication
    (applied form). -/
private lemma toEuclideanLin_mul_apply
    {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℂ) (v : EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, ← Matrix.mulVec_mulVec]

/-- **C2.8d – helper 2.** Inner-product / matrix-adjoint bridge:
    `⟨A x, y⟩ = ⟨x, (star A) y⟩` for `toEuclideanLin` applied vectors. -/
private lemma inner_toEuclideanLin_star
    {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (x y : EuclideanSpace ℂ (Fin N)) :
    (inner ℂ (Matrix.toEuclideanLin A x) y : ℂ)
      = inner ℂ x (Matrix.toEuclideanLin (star A) y) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      (Matrix.toEuclideanLin A).adjoint_inner_right]

/-- **C2.8d.** Orthonormality of the transported family `phiONB_family φ`.

    **Proof strategy.**
    `⟨E_i0 v_a, E_j0 v_b⟩ = ⟨v_a, (star E_i0) (E_j0 v_b)⟩
                          = ⟨v_a, (E_0i * E_j0) v_b⟩`
    (via `inner_toEuclideanLin_star` + `E_of_star` + `toEuclideanLin_mul_apply`).
    - Case `i ≠ j`: `E_0i * E_j0 = 0` (C2.3, middle indices `i ≠ j`), so
      `⟨v_a, 0⟩ = 0`.
    - Case `i = j`: `E_0i * E_i0 = E_00` (C2.2), so we need `⟨v_a, E_00 v_b⟩`.
      Since `v_b ∈ range(E_00)` and `E_00` is idempotent, `E_00 v_b = v_b`,
      giving `⟨v_a, v_b⟩ = δ_{ab}` by the stdONB orthonormality.

    **Mathlib citations.**
    - `orthonormal_iff_ite`
      (`Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`).
    - `LinearMap.adjoint_inner_right`,
      `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`
      (`Mathlib/Analysis/InnerProductSpace/Adjoint.lean`). -/
lemma phiONB_family_orthonormal [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    Orthonormal ℂ (phiONB_family n k φ) := by
  set z : Fin n := ⟨0, Nat.pos_of_neZero n⟩ with hz
  set E00 := E_of n k φ z z with hE00
  -- ONB of range of E00, with its orthonormality in the ambient space.
  set b := E_of_00_stdOrthonormalBasis n k φ with hb
  -- Fact: `E_00` fixes vectors in its range (idempotent projection).
  have hE00_fix : ∀ (a : Fin k),
      Matrix.toEuclideanLin E00 (b a : EuclideanSpace ℂ (Fin (k * n)))
        = (b a : EuclideanSpace ℂ (Fin (k * n))) := by
    intro a
    -- b a is in the range, so b a = toEuclideanLin E00 u for some u.
    have hmem : (b a : EuclideanSpace ℂ (Fin (k * n)))
        ∈ LinearMap.range (Matrix.toEuclideanLin E00) := (b a).2
    obtain ⟨u, hu⟩ := hmem
    have hEE : E00 * E00 = E00 := (E_of_i_i_isProjection n k φ z).1
    calc Matrix.toEuclideanLin E00 (b a : EuclideanSpace ℂ (Fin (k * n)))
        = Matrix.toEuclideanLin E00 (Matrix.toEuclideanLin E00 u) := by rw [hu]
      _ = Matrix.toEuclideanLin (E00 * E00) u := (toEuclideanLin_mul_apply E00 E00 u).symm
      _ = Matrix.toEuclideanLin E00 u := by rw [hEE]
      _ = (b a : EuclideanSpace ℂ (Fin (k * n))) := hu
  -- Orthonormality of `b` in the ambient space.
  have hb_amb : ∀ a₁ a₂ : Fin k,
      (inner ℂ (b a₁ : EuclideanSpace ℂ (Fin (k * n)))
              (b a₂ : EuclideanSpace ℂ (Fin (k * n))) : ℂ)
        = if a₁ = a₂ then 1 else 0 := by
    intro a₁ a₂
    have hON := b.orthonormal
    rw [orthonormal_iff_ite] at hON
    have := hON a₁ a₂
    rwa [Submodule.coe_inner] at this
  -- Main orthonormality.
  rw [orthonormal_iff_ite]
  rintro ⟨i, a⟩ ⟨j, b'⟩
  simp only [phiONB_family]
  -- Convert `⟨E_i0 v_a, E_j0 v_b'⟩` to `⟨v_a, (star E_i0 * E_j0) v_b'⟩`.
  rw [inner_toEuclideanLin_star, ← toEuclideanLin_mul_apply,
      show star (E_of n k φ i z) = E_of n k φ z i from E_of_star n k φ i z]
  by_cases hij : i = j
  · subst hij
    -- Case i = j: E_0i * E_i0 = E_00.
    have hprod : E_of n k φ z i * E_of n k φ i z = E00 :=
      E_of_mul_same n k φ z i z
    rw [hprod, hE00_fix, hb_amb]
    -- (a = b') iff ((i, a) = (i, b'))
    by_cases hab : a = b'
    · subst hab; simp
    · rw [if_neg hab, if_neg (fun h => hab (Prod.mk_inj.mp h).2)]
  · -- Case i ≠ j: E_0i * E_j0 = 0.
    have hprod : E_of n k φ z i * E_of n k φ j z = 0 :=
      E_of_mul_diff n k φ z i j z hij
    rw [hprod, LinearEquiv.map_zero (Matrix.toEuclideanLin), LinearMap.zero_apply,
        inner_zero_right]
    rw [if_neg (fun h => hij (Prod.mk_inj.mp h).1)]

/-- **C2.8e.** Assemble the transported family into a full orthonormal basis
    of `EuclideanSpace ℂ (Fin (k*n))` indexed by `Fin n × Fin k`.

    By C2.8d the family is orthonormal, and it has cardinality `n * k = k * n`
    matching `finrank ℂ (EuclideanSpace ℂ (Fin (k*n)))`. So
    `basisOfOrthonormalOfCardEqFinrank` builds a `Basis`, which
    `Basis.toOrthonormalBasis` upgrades to an `OrthonormalBasis`.

    **Mathlib citations.**
    - `basisOfOrthonormalOfCardEqFinrank`
      (`Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`).
    - `Module.Basis.toOrthonormalBasis`
      (`Mathlib/Analysis/InnerProductSpace/PiL2.lean`).
    - `finrank_euclideanSpace_fin`
      (`Mathlib/Analysis/InnerProductSpace/PiL2.lean`). -/
noncomputable def phiONB [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * n))) :=
  haveI : Nonempty (Fin n × Fin k) :=
    ⟨⟨⟨0, Nat.pos_of_neZero n⟩, ⟨0, Nat.pos_of_neZero k⟩⟩⟩
  have hcard : Fintype.card (Fin n × Fin k)
      = Module.finrank ℂ (EuclideanSpace ℂ (Fin (k * n))) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, finrank_euclideanSpace_fin,
        Nat.mul_comm]
  (basisOfOrthonormalOfCardEqFinrank (phiONB_family_orthonormal n k φ) hcard).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact phiONB_family_orthonormal n k φ)

/-- Reindexing bijection `Fin n × Fin k ≃ Fin (k*n)` (helper for C2.9). -/
noncomputable def phiIndexEquiv : Fin n × Fin k ≃ Fin (k * n) :=
  (Equiv.prodComm _ _).trans finProdFinEquiv

/-- **C2.9.** Change-of-ONB matrix for two orthonormal bases of
    `EuclideanSpace ℂ (Fin (k*n))` indexed by `Fin n × Fin k`,
    reindexed to `Fin (k*n)`. -/
noncomputable def unitaryOfONBpair
    (bφ bψ : OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * n)))) :
    Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
  Matrix.reindex (phiIndexEquiv n k) (phiIndexEquiv n k) (bψ.toBasis.toMatrix bφ.toBasis)

/-- **C2.10.** The change-of-ONB matrix `unitaryOfONBpair` is unitary
    (both `U * U* = 1` and `U* * U = 1`).

    **Mathlib citations.**
    - `OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose`
      and `OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self`
      in `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.
    - `Matrix.conjTranspose_reindex` in
      `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean`. -/
lemma unitaryOfONBpair_isUnitary
    (bφ bψ : OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * n)))) :
    unitaryOfONBpair n k bφ bψ * star (unitaryOfONBpair n k bφ bψ) = 1 ∧
    star (unitaryOfONBpair n k bφ bψ) * unitaryOfONBpair n k bφ bψ = 1 := by
  classical
  set M : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ := bψ.toBasis.toMatrix bφ.toBasis with hM
  have hMMh : M * Matrix.conjTranspose M = 1 :=
    bψ.toMatrix_orthonormalBasis_self_mul_conjTranspose bφ
  have hMhM : Matrix.conjTranspose M * M = 1 :=
    bψ.toMatrix_orthonormalBasis_conjTranspose_mul_self bφ
  set e : Fin n × Fin k ≃ Fin (k * n) := phiIndexEquiv n k with he
  -- Reindex distributes over multiplication (via submatrix_mul_equiv).
  have hmul_reindex : ∀ (A B : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ),
      Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
    intro A B
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    exact Equiv.sum_comp e.symm (fun t => A (e.symm i) t * B t (e.symm j))
  have hone_reindex :
      Matrix.reindex e e (1 : Matrix (Fin n × Fin k) (Fin n × Fin k) ℂ) = 1 := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
      e.symm.injective.eq_iff]
  have hstar : star (unitaryOfONBpair n k bφ bψ)
      = Matrix.reindex e e (Matrix.conjTranspose M) := by
    show Matrix.conjTranspose _ = _
    rw [unitaryOfONBpair, ← he, ← hM, Matrix.conjTranspose_reindex]
  refine ⟨?_, ?_⟩
  · rw [hstar]
    show Matrix.reindex e e M * Matrix.reindex e e (Matrix.conjTranspose M) = 1
    rw [hmul_reindex, hMMh, hone_reindex]
  · rw [hstar]
    show Matrix.reindex e e (Matrix.conjTranspose M) * Matrix.reindex e e M = 1
    rw [hmul_reindex, hMhM, hone_reindex]

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

/-- **C3.mid.3.** For a `Substrate3Inf A` and a coherent family of
    *-alg-homs `fam : ∀ k, h.tower k →⋆ₐ[ℂ] B` (with compatibility
    `compat`), the assembled `tower_union_starHom h fam compat` is
    uniformly continuous.

    Proof strategy:
      1. Each `h.tower k` is closed (`tower_level_isClosed`), so
         `StarSubalgebra.cstarAlgebra` unlocks a `CStarAlgebra` instance
         on each level.
      2. Each `fam k` is a *-alg-hom between C*-algebras, hence
         contractive by `NonUnitalStarAlgHom.norm_apply_le`
         (`Mathlib/Analysis/CStarAlgebra/Spectrum.lean:254`).
      3. For `x, y : ⨆ k, h.tower k`, directedness of the tower gives
         a common level `k` containing both underlying elements. On
         that level, `tower_union_starHom · = fam k ⟨·.val, _⟩` by
         essentially `Set.iUnionLift_of_mem`.  We punt on unfolding
         `tower_union_starHom` (opaque due to being built with
         `by ... exact { ... }`); instead we use the alternative
         `x.val = y.val` witness `hwd`-analogue via a fresh lift.

      4. `LipschitzWith.uniformContinuous`
         (`Mathlib/Topology/EMetricSpace/Lipschitz.lean:182`)
         closes the goal. -/
lemma tower_union_starHom_uniformContinuous
    (h : Substrate3Inf A) {B : Type*} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k)) = fam k) :
    UniformContinuous (tower_union_starHom h fam compat) := by
  -- Each tower level is closed (unlocks StarSubalgebra.cstarAlgebra instance).
  haveI : ∀ k, IsClosed ((h.tower k : StarSubalgebra ℂ A) : Set A) :=
    fun k => h.tower_level_isClosed k
  -- 1-Lipschitz suffices for uniform continuity.
  apply LipschitzWith.uniformContinuous (K := 1)
  intro x y
  rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul]
  apply ENNReal.ofReal_le_ofReal
  -- We'll show `dist (F x) (F y) ≤ dist x y` where `F = tower_union_starHom …`.
  -- First: normalise the goal to a `‖·‖` bound.
  rw [dist_eq_norm, dist_eq_norm]
  -- The map is additive (as a *-alg-hom), so `F x - F y = F (x - y)`.
  have h_map_sub : tower_union_starHom h fam compat x
                    - tower_union_starHom h fam compat y
                  = tower_union_starHom h fam compat (x - y) := by
    rw [map_sub]
  rw [h_map_sub]
  -- Set `z := x - y : ⨆ k, h.tower k`.
  set z := x - y with hz
  clear_value z
  -- Locate a tower level containing `z.val`.
  have tower_le : ∀ m n, m ≤ n → h.tower m ≤ h.tower n := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | step _ ih => exact ih.trans (h.tower_mono _)
  have dir : Directed (· ≤ ·) h.tower := fun i j =>
    ⟨max i j, tower_le i _ (le_max_left _ _), tower_le j _ (le_max_right _ _)⟩
  have hT_coe : ((⨆ k, h.tower k : StarSubalgebra ℂ A) : Set A)
                  = ⋃ k, ((h.tower k) : Set A) :=
    coe_iSup_of_directed_starSubalgebra dir
  have hzU : (z : A) ∈ ((⨆ k, h.tower k : StarSubalgebra ℂ A) : Set A) := z.2
  rw [hT_coe] at hzU
  obtain ⟨k, hzk⟩ := Set.mem_iUnion.1 hzU
  -- Key: `tower_union_starHom h fam compat z = fam k ⟨z.val, hzk⟩`.
  -- We prove this by treating `z` as `(inclusion ..) ⟨z.val, hzk⟩` and
  -- applying StarAlgHom composition on both sides at level k.
  have h_incl_le : h.tower k ≤ ⨆ k, h.tower k := le_iSup _ k
  have z_eq : z = StarSubalgebra.inclusion h_incl_le ⟨(z : A), hzk⟩ := by
    apply Subtype.ext
    rfl
  have hFz : tower_union_starHom h fam compat z = fam k ⟨(z : A), hzk⟩ := by
    -- Both sides equal `fam k ⟨z.val, hzk⟩` because
    -- `(tower_union_starHom).comp (inclusion) = fam k` on level k
    -- (this is how tower_union_starHom was constructed).
    -- We prove this by an induction climb: for each n, the composition
    -- of `tower_union_starHom` with `inclusion (tower k ≤ tower (k+n)) …`
    -- matches `fam (k+n)`. But it's easier: use that the coercion is
    -- extensional and matches on tower elements via `hwd`.
    -- Concrete: use `Set.iUnionLift_of_mem` after unfolding.
    unfold tower_union_starHom
    simp only [StarAlgHom.coe_mk]
    exact Set.iUnionLift_of_mem
      (S := fun k => ((h.tower k : StarSubalgebra ℂ A) : Set A))
      (f := fun k x => fam k x)
      (i := k) z hzk
  rw [hFz]
  -- Contractivity of `fam k`.
  have hcontract := NonUnitalStarAlgHom.norm_apply_le (fam k)
    (⟨(z : A), hzk⟩ : h.tower k)
  refine hcontract.trans ?_
  -- Subtype norm equals ambient norm.
  have h_norm_eq : ‖(⟨(z : A), hzk⟩ : h.tower k)‖ = ‖(z : A)‖ := rfl
  have h_norm_xy : ‖(z : (⨆ k, h.tower k : StarSubalgebra ℂ A))‖ = ‖(z : A)‖ := rfl
  rw [h_norm_eq, ← h_norm_xy, hz]
  -- goal: ‖x - y‖ ≤ ‖x - y‖
  -- (both x - y evaluated in the subtype; hz was `z := x - y`)

/-- **C3.mid.4 helper.** On any tower level `k`, the assembled
    union *-alg-hom coincides with `fam k`. Extracted from the same
    computation used in `tower_union_starHom_uniformContinuous`. -/
private lemma tower_union_starHom_apply_of_mem
    (h : Substrate3Inf A) {B : Type*} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k)) = fam k)
    (k : ℕ) (z : (⨆ k, h.tower k : StarSubalgebra ℂ A))
    (hzk : (z : A) ∈ h.tower k) :
    tower_union_starHom h fam compat z = fam k ⟨(z : A), hzk⟩ := by
  unfold tower_union_starHom
  simp only [StarAlgHom.coe_mk]
  exact Set.iUnionLift_of_mem
    (S := fun k => ((h.tower k : StarSubalgebra ℂ A) : Set A))
    (f := fun k x => fam k x)
    (i := k) z hzk

/-- **C3 main.** Universal extension of a coherent tower family. -/
lemma tower_universal_star_extension
    (h : Substrate3Inf A) {B : Type*} [CStarAlgebra B]
    (fam : ∀ k, h.tower k →⋆ₐ[ℂ] B)
    (compat : ∀ k, (fam (k+1)).comp
                    (StarSubalgebra.inclusion (h.tower_mono k))
                     = fam k) :
    ∃! F : A →⋆ₐ[ℂ] B, ∀ k x, F ((h.tower k).subtype x) = fam k x := by
  -- Notation for the union subalgebra.
  set T : StarSubalgebra ℂ A := ⨆ k, h.tower k with hT_def
  -- The glued *-alg-hom on the union.
  set g : T →⋆ₐ[ℂ] B := tower_union_starHom h fam compat with hg_def
  have hg_uc : UniformContinuous g :=
    tower_union_starHom_uniformContinuous h fam compat
  -- Density and dense-inducing witness for `Subtype.val : T → A`.
  have hs : Dense ((T : Set A)) := h.tower_dense
  have hDI : IsDenseInducing (Subtype.val : T → A) :=
    hs.isDenseInducing_val
  have hUI : IsUniformInducing (Subtype.val : T → A) :=
    isUniformInducing_val (T : Set A)
  have hdr : DenseRange (Subtype.val : T → A) := hs.denseRange_val
  -- The raw extension.
  set Fraw : A → B := hDI.extend g with hFraw_def
  have hFraw_uc : UniformContinuous Fraw :=
    uniformContinuous_uniformly_extend hUI hdr hg_uc
  have hFraw_cont : Continuous Fraw := hFraw_uc.continuous
  -- Extension identity on the dense subset.
  have hFraw_eq : ∀ z : T, Fraw (z : A) = g z := by
    intro z
    exact hDI.extend_eq hg_uc.continuous z
  -- Package the raw function as a *-alg-hom.
  have F_zero : Fraw 0 = 0 := by
    have h0 : (0 : A) = ((0 : T) : A) := rfl
    rw [h0, hFraw_eq, map_zero]
  have F_one : Fraw 1 = 1 := by
    have h1 : (1 : A) = ((1 : T) : A) := rfl
    rw [h1, hFraw_eq, map_one]
  have F_add : ∀ x y : A, Fraw (x + y) = Fraw x + Fraw y := by
    refine fun x y => DenseRange.induction_on₂ hdr ?_ (fun a b => ?_) x y
    · exact isClosed_eq (hFraw_cont.comp continuous_add)
        ((hFraw_cont.comp continuous_fst).add (hFraw_cont.comp continuous_snd))
    · have hab : (a : A) + (b : A) = ((a + b : T) : A) := rfl
      rw [hab, hFraw_eq, hFraw_eq, hFraw_eq, map_add]
  have F_mul : ∀ x y : A, Fraw (x * y) = Fraw x * Fraw y := by
    refine fun x y => DenseRange.induction_on₂ hdr ?_ (fun a b => ?_) x y
    · exact isClosed_eq (hFraw_cont.comp continuous_mul)
        ((hFraw_cont.comp continuous_fst).mul (hFraw_cont.comp continuous_snd))
    · have hab : (a : A) * (b : A) = ((a * b : T) : A) := rfl
      rw [hab, hFraw_eq, hFraw_eq, hFraw_eq, map_mul]
  have F_star : ∀ x : A, Fraw (star x) = star (Fraw x) := by
    refine fun x => DenseRange.induction_on hdr x ?_ (fun a => ?_)
    · exact isClosed_eq (hFraw_cont.comp continuous_star)
        (continuous_star.comp hFraw_cont)
    · have ha : star (a : A) = ((star a : T) : A) := rfl
      rw [ha, hFraw_eq, hFraw_eq, map_star]
  have F_alg : ∀ r : ℂ, Fraw (algebraMap ℂ A r) = algebraMap ℂ B r := by
    intro r
    have hr : algebraMap ℂ A r = ((algebraMap ℂ T r : T) : A) := rfl
    rw [hr, hFraw_eq, AlgHomClass.commutes]
  -- Assemble the *-alg-hom.
  let F : A →⋆ₐ[ℂ] B :=
    { toFun := Fraw
      map_one' := F_one
      map_mul' := F_mul
      map_zero' := F_zero
      map_add' := F_add
      commutes' := F_alg
      map_star' := F_star }
  -- Level-k identity: F ((h.tower k).subtype x) = fam k x.
  have hF_level : ∀ k (x : h.tower k), F ((h.tower k).subtype x) = fam k x := by
    intro k x
    have h_incl_le : h.tower k ≤ T := le_iSup _ k
    let z : T := StarSubalgebra.inclusion h_incl_le x
    have hz_val : (z : A) = (x : A) := rfl
    have hzk : (z : A) ∈ h.tower k := by
      rw [hz_val]; exact x.2
    show Fraw ((h.tower k).subtype x) = fam k x
    have hsubtype : (h.tower k).subtype x = (x : A) := rfl
    rw [hsubtype, ← hz_val, hFraw_eq z]
    rw [tower_union_starHom_apply_of_mem h fam compat k z hzk]
    rfl
  -- Existence + uniqueness.
  refine ⟨F, hF_level, ?_⟩
  intro G hG
  -- G is contractive (hence continuous) as a *-alg-hom between C*-algebras.
  have hG_cont : Continuous G := by
    have hlip : LipschitzWith 1 (G : A → B) := by
      intro x y
      rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul]
      apply ENNReal.ofReal_le_ofReal
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact NonUnitalStarAlgHom.norm_apply_le G (x - y)
    exact hlip.continuous
  have hF_cont : Continuous F := hFraw_cont
  -- Coincidence on the union: for z : T pick a level k containing z.val.
  have tower_le : ∀ m n, m ≤ n → h.tower m ≤ h.tower n := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | step _ ih => exact ih.trans (h.tower_mono _)
  have dir : Directed (· ≤ ·) h.tower := fun i j =>
    ⟨max i j, tower_le i _ (le_max_left _ _), tower_le j _ (le_max_right _ _)⟩
  have hT_coe : ((T : StarSubalgebra ℂ A) : Set A) = ⋃ k, ((h.tower k) : Set A) :=
    coe_iSup_of_directed_starSubalgebra dir
  have hGF_dense : ∀ z : T, G (z : A) = F (z : A) := by
    intro z
    have hzU : (z : A) ∈ ((T : StarSubalgebra ℂ A) : Set A) := z.2
    rw [hT_coe] at hzU
    obtain ⟨k, hzk⟩ := Set.mem_iUnion.1 hzU
    have hG_at : G (z : A) = fam k ⟨(z : A), hzk⟩ := by
      have hGk := hG k ⟨(z : A), hzk⟩
      simpa [StarSubalgebra.subtype_apply] using hGk
    have hF_at : F (z : A) = fam k ⟨(z : A), hzk⟩ := by
      have hFk := hF_level k ⟨(z : A), hzk⟩
      simpa [StarSubalgebra.subtype_apply] using hFk
    rw [hG_at, hF_at]
  -- Lift the pointwise coincidence to all of A via DenseRange.induction_on.
  ext x
  refine DenseRange.induction_on hdr x ?_ (fun z => ?_)
  · exact isClosed_eq hG_cont hF_cont
  · exact hGF_dense z

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
