/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection

/-!
# Unitary classification of unital `*`-homs `Mₙ(ℂ) → M_{kn}(ℂ)`

Any two unital `*`-homomorphisms from `Matrix (Fin n) (Fin n) ℂ` into
`Matrix (Fin (k*n)) (Fin (k*n)) ℂ` are conjugate by a unitary, and every such
`*`-hom is unitarily equivalent to the standard `k`-fold block-diagonal
amplification. Equivalently: `Mₙ(ℂ)` has, up to unitary equivalence, exactly one
unital `*`-representation of each multiplicity `k`, with the block-diagonal
amplification a complete set of representatives.

## Relation to what mathlib already has  (delta checked against master)

Mathlib master already proves Noether–Skolem for the **automorphism** case:
`StarAlgEquiv.eq_linearIsometryEquivConjStarAlgEquiv`
(`Mathlib/Analysis/Normed/Operator/ContinuousAlgEquiv.lean`, PR #33017) gives,
for a continuous `*`-equivalence `(V →L[𝕜] V) ≃⋆ₐ[𝕜] (W →L[𝕜] W)`, a unitary
`U : V ≃ₗᵢ[𝕜] W` with `f = U.conjStarAlgEquiv`; `AlgEquiv.eq_linearEquivConjAlgEquiv`
(PR #28100) is the non-star version. Both require `f` to be an **equivalence**
(bijective).

This file is the **rectangular `*`-hom** case, which those do not reach: `φ, ψ`
here are unital `*`-homs `Mₙ(ℂ) → M_{kn}(ℂ)` — injective but not surjective for
`k > 1`, hence not equivalences. The `k = 1` specialisation coincides with the
automorphism result; the content is the general `k`, i.e. the amplification /
embedding rigidity that the Glimm UHF classification consumes and that mathlib
does not currently have in any form (no `IsInner`, no amplification classification).

## Main results

* `unital_star_hom_inner_unique` — any two unital `*`-homs `Mₙ(ℂ) → M_{kn}(ℂ)`
  are conjugate by a unitary `U` (`U * star U = 1`, `star U * U = 1`,
  `∀ x, φ x = U * ψ x * star U`).
* `blockDiagonalStarAlgHom` — the standard `k`-fold block-diagonal amplification
  as a unital injective `StarAlgHom`.
* (corollary, assembled from the above) every unital `*`-hom `Mₙ(ℂ) → M_{kn}(ℂ)`
  is unitarily equivalent to `blockDiagonalStarAlgHom`.

The route is classical: matrix-unit calculus (`E_of_*`), a projection-trace count
fixing the multiplicity, an orthonormal basis built from the `*`-hom image
(`phiONB`), and the change-of-basis unitary (`unitaryOfONBpair`).

## STATUS — staged candidate, NOT a finished mathlib PR, NOT submitted

Verified axiom-clean (`[propext, Classical.choice, Quot.sound]`) against the
project's pinned mathlib `eed770a4` (≈ 7 months old). Remaining work before this
could be offered upstream, none of it done here and none of it verifiable without
a build against current master:

1. **Rebuild against mathlib master**, not the pin — the delta above was read
   from master source but the proofs have only been checked on the pin.
2. **mathlib naming + placement**: drop the `PrincipiaTractalis.SubstrateRigidity`
   namespace; rename to `Matrix.*`; split the generic matrix-unit lemmas into the
   file where they belong; align the statement with master's `conjStarAlgEquiv` /
   `unitary` bundling rather than a raw matrix `U` with two cancellation sides.
3. Strip this STATUS section (staging-only).
4. CLA, fork, branch, PR — an **external submission**, gated on the author's
   explicit decision and multi-model vetting. Not performed.

Proof text below is byte-identical to the verified
`PF/Upstream/NoetherSkolemC2.lean`; only this docstring differs.

Author: Pablo Cohen. Staged 2026-10-09.
-/

open scoped Matrix.Norms.L2Operator
open scoped Matrix  -- for the postfix conjTranspose notation

namespace PrincipiaTractalis.SubstrateRigidity

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

/-- **C2.9.** Change-of-ONB unitary for two orthonormal bases of
    `EuclideanSpace ℂ (Fin (k*n))` indexed by `Fin n × Fin k`.

    **Design.** We build the matrix in the *standard basis* so that
    `U · (bψ p) = bφ p` for every `p`.  Concretely, let

      Φ_{q, r} := bφ ((phiIndexEquiv).symm r) q       -- columns are φ-vectors
      Ψ_{q, r} := bψ ((phiIndexEquiv).symm r) q       -- columns are ψ-vectors

    Then `U := Φ · Ψᴴ`.  Applied to `bψ p`, the `Ψᴴ` factor "reads off"
    the `p`-th standard-basis vector (via orthonormality of `bψ`), and
    the `Φ` factor "writes down" `bφ p`. -/
noncomputable def unitaryOfONBpair
    (bφ bψ : OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * n)))) :
    Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
  let Φ : Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
    fun q r => bφ ((phiIndexEquiv n k).symm r) q
  let Ψ : Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
    fun q r => bψ ((phiIndexEquiv n k).symm r) q
  Φ * Ψᴴ

/-- **C2.10.** The change-of-ONB matrix `unitaryOfONBpair` is unitary
    (both `U * U* = 1` and `U* * U = 1`).

    **Proof outline.** With `Φ, Ψ` as in `unitaryOfONBpair`, the columns of
    each are an orthonormal basis of `EuclideanSpace ℂ (Fin (k*n))`, so
    `Φᴴ · Φ = 1` and `Ψᴴ · Ψ = 1` (Gram-matrix identities). Since the
    matrices are square over a commutative ring, `Matrix.mul_eq_one_comm`
    upgrades these to `Φ · Φᴴ = 1` and `Ψ · Ψᴴ = 1`. Then
    `U * Uᴴ = (Φ Ψᴴ)(Ψ Φᴴ) = Φ (Ψᴴ Ψ) Φᴴ = Φ Φᴴ = 1` and
    `Uᴴ * U = (Ψ Φᴴ)(Φ Ψᴴ) = Ψ (Φᴴ Φ) Ψᴴ = Ψ Ψᴴ = 1`.

    **Mathlib citations.**
    - `OrthonormalBasis.orthonormal` — orthonormality of the family.
    - `orthonormal_iff_ite` — pointwise inner-product characterisation.
    - `EuclideanSpace.inner_eq_star_dotProduct` — inner product as
      `y ⬝ᵥ star x` on `EuclideanSpace`.
    - `Matrix.mul_eq_one_comm` in
      `Mathlib/LinearAlgebra/Matrix/SemiringInverse.lean`. -/
lemma unitaryOfONBpair_isUnitary
    (bφ bψ : OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * n)))) :
    unitaryOfONBpair n k bφ bψ * star (unitaryOfONBpair n k bφ bψ) = 1 ∧
    star (unitaryOfONBpair n k bφ bψ) * unitaryOfONBpair n k bφ bψ = 1 := by
  classical
  set e : Fin n × Fin k ≃ Fin (k * n) := phiIndexEquiv n k with he
  set Φ : Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
    (fun q r => bφ (e.symm r) q) with hΦ
  set Ψ : Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
    (fun q r => bψ (e.symm r) q) with hΨ
  have hU : unitaryOfONBpair n k bφ bψ = Φ * Ψᴴ := rfl
  -- Gram-matrix identity: `Φᴴ * Φ = 1`.
  -- Generic gram-matrix identity for the "columns are ONB" construction.
  have hgram : ∀ (b : OrthonormalBasis (Fin n × Fin k) ℂ
                        (EuclideanSpace ℂ (Fin (k * n))))
                 (M : Matrix (Fin (k * n)) (Fin (k * n)) ℂ),
      M = (fun q r => b (e.symm r) q) → Mᴴ * M = 1 := by
    intro b M hMdef
    ext r s
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hMdef]
    -- ∑_q star (b (e.symm r) q) * b (e.symm s) q = ⟪b (e.symm r), b (e.symm s)⟫
    have hinner :
        (∑ q, star (b (e.symm r) q) * b (e.symm s) q)
          = (inner ℂ (b (e.symm r)) (b (e.symm s)) : ℂ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, mul_comm]
    rw [hinner]
    have honb := b.orthonormal
    rw [orthonormal_iff_ite] at honb
    rw [honb (e.symm r) (e.symm s)]
    by_cases h : r = s
    · subst h; simp
    · have h' : e.symm r ≠ e.symm s := fun hh => h (e.symm.injective hh)
      simp [h, h']
  have hΦgram : Φᴴ * Φ = 1 := hgram bφ Φ hΦ
  have hΨgram : Ψᴴ * Ψ = 1 := hgram bψ Ψ hΨ
  -- Upgrade: for square matrices, left-inverse ⇔ right-inverse.
  have hΦΦH : Φ * Φᴴ = 1 := Matrix.mul_eq_one_comm.mpr hΦgram
  have hΨΨH : Ψ * Ψᴴ = 1 := Matrix.mul_eq_one_comm.mpr hΨgram
  refine ⟨?_, ?_⟩
  · -- U * star U = (Φ Ψᴴ) * (Φ Ψᴴ)ᴴ = Φ (Ψᴴ Ψ) Φᴴ = Φ Φᴴ = 1
    show (Φ * Ψᴴ) * star (Φ * Ψᴴ) = 1
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    calc Φ * Ψᴴ * (Ψ * Φᴴ)
        = Φ * (Ψᴴ * Ψ) * Φᴴ := by simp [Matrix.mul_assoc]
      _ = Φ * 1 * Φᴴ := by rw [hΨgram]
      _ = Φ * Φᴴ := by rw [Matrix.mul_one]
      _ = 1 := hΦΦH
  · -- star U * U = (Φ Ψᴴ)ᴴ * (Φ Ψᴴ) = Ψ (Φᴴ Φ) Ψᴴ = Ψ Ψᴴ = 1
    show star (Φ * Ψᴴ) * (Φ * Ψᴴ) = 1
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    calc Ψ * Φᴴ * (Φ * Ψᴴ)
        = Ψ * (Φᴴ * Φ) * Ψᴴ := by simp [Matrix.mul_assoc]
      _ = Ψ * 1 * Ψᴴ := by rw [hΦgram]
      _ = Ψ * Ψᴴ := by rw [Matrix.mul_one]
      _ = 1 := hΨΨH

/-- **C2.11 – bridge.** Action of `unitaryOfONBpair (phiONB φ) (phiONB ψ)` on
    the `ψ`-ONB standard-basis picture: it sends `phiONB ψ p` to `phiONB φ p`.

    **Proof outline.** Write `U = Φ * Ψᴴ` per `unitaryOfONBpair`. Compute
    entry-wise `(U *ᵥ (bψ p))(r) = Σ_t Φ(r, t) * (Ψᴴ *ᵥ (bψ p))(t)`. The
    inner sum evaluates to `⟪bψ (e.symm t), bψ p⟫ = δ_{e.symm t, p}
    = δ_{t, e p}` via orthonormality (`orthonormal_iff_ite`). Collapsing the
    outer sum yields `Φ(r, e p) = bφ (e.symm (e p)) r = bφ p r`.

    **Mathlib citations.**
    - `Matrix.toEuclideanLin_apply` in `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.
    - `Matrix.mul_apply`, `Matrix.mulVec` in `Mathlib/Data/Matrix/Mul.lean`.
    - `EuclideanSpace.inner_eq_star_dotProduct`, `OrthonormalBasis.orthonormal`,
      `orthonormal_iff_ite`. -/
lemma unitaryOfONBpair_apply_phiONB [NeZero n]
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
           Matrix (Fin (k * n)) (Fin (k * n)) ℂ) (p : Fin n × Fin k) :
    Matrix.toEuclideanLin
        (unitaryOfONBpair n k (phiONB n k φ) (phiONB n k ψ))
        (phiONB n k ψ p)
      = phiONB n k φ p := by
  classical
  set e : Fin n × Fin k ≃ Fin (k * n) := phiIndexEquiv n k with he
  set bφ : OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * n))) :=
    phiONB n k φ with hbφ
  set bψ : OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * n))) :=
    phiONB n k ψ with hbψ
  set Φ : Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
    (fun q r => bφ (e.symm r) q) with hΦ
  set Ψ : Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
    (fun q r => bψ (e.symm r) q) with hΨ
  have hU : unitaryOfONBpair n k bφ bψ = Φ * Ψᴴ := rfl
  rw [hU]
  ext r
  -- `toEuclideanLin (Φ * Ψᴴ) (bψ p)` unfolds to `toLp _ ((Φ * Ψᴴ) *ᵥ (ofLp (bψ p)))`.
  -- After `ext r`, both sides project to their `r`-th component, so we may
  -- reduce to the plain pointwise identity.
  change ((Φ * Ψᴴ) *ᵥ (fun s => bψ p s)) r = bφ p r
  -- LHS r = ∑_s (Φ * Ψᴴ)(r,s) * (bψ p) s
  --       = ∑_s ∑_t Φ(r,t) * conj(bψ (e.symm t) s) * (bψ p) s
  -- Swap ∑_s and ∑_t (via Finset.sum_comm), then factor Φ(r,t) out:
  --       = ∑_t Φ(r,t) * ∑_s conj(bψ (e.symm t) s) * (bψ p) s
  --       = ∑_t Φ(r,t) * ⟪bψ (e.symm t), bψ p⟫
  -- Orthonormality collapses the inner product to `if e.symm t = p then 1 else 0`
  -- = `if t = e p then 1 else 0`.  Sum collapses to `Φ(r, e p) = bφ p r`.
  have honb := bψ.orthonormal
  rw [orthonormal_iff_ite] at honb
  have hstep :
      ((Φ * Ψᴴ) *ᵥ (fun s => bψ p s)) r
        = ∑ t, Φ r t * (if t = e p then (1 : ℂ) else 0) := by
    -- Unfold mulVec, mul, conjTranspose, Ψ.
    simp only [Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Matrix.conjTranspose_apply, hΨ, Finset.sum_mul]
    -- Now the LHS reads:
    --   ∑_s ∑_t (Φ(r,t) * star (bψ (e.symm t) s)) * (bψ p) s
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    -- Inner sum over s: ∑_s (Φ(r,t) * star (bψ (e.symm t) s)) * (bψ p) s
    --                = Φ(r,t) * ∑_s star (bψ (e.symm t) s) * (bψ p) s
    --                = Φ(r,t) * ⟪bψ (e.symm t), bψ p⟫
    --                = Φ(r,t) * (if e.symm t = p then 1 else 0)
    --                = Φ(r,t) * (if t = e p then 1 else 0).
    have hite_eq : (if e.symm t = p then (1 : ℂ) else 0)
                    = (if t = e p then (1 : ℂ) else 0) := by
      by_cases htp : t = e p
      · have : e.symm t = p := by rw [htp]; exact e.symm_apply_apply p
        simp [htp, this]
      · have : e.symm t ≠ p := by
          intro h; apply htp
          rw [← h]; exact (e.apply_symm_apply t).symm
        simp [htp, this]
    have hinner :
        (∑ s, star (bψ (e.symm t) s) * (bψ p) s)
          = (if e.symm t = p then (1 : ℂ) else 0) := by
      have := honb (e.symm t) p
      rw [← this, EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, mul_comm]
    calc (∑ s, Φ r t * star (bψ (e.symm t) s) * (bψ p) s)
        = Φ r t * ∑ s, star (bψ (e.symm t) s) * (bψ p) s := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun s _ => ?_); ring
      _ = Φ r t * (if e.symm t = p then (1 : ℂ) else 0) := by rw [hinner]
      _ = Φ r t * (if t = e p then (1 : ℂ) else 0) := by rw [hite_eq]
  -- Collapse the outer sum.
  have hcollapse :
      (∑ t, Φ r t * (if t = e p then (1 : ℂ) else 0)) = Φ r (e p) := by
    rw [Finset.sum_eq_single (e p)]
    · simp
    · intros b _ hb; simp [hb]
    · intro h; exact (h (Finset.mem_univ _)).elim
  -- RHS: bφ p r = Φ r (e p) (definition of Φ and e.symm ∘ e = id).
  have hrhs : (bφ p : EuclideanSpace ℂ (Fin (k * n))) r = Φ r (e p) := by
    simp only [hΦ, Equiv.symm_apply_apply]
  rw [hstep, hcollapse, hrhs]

/-- **C2.11 – helper A.** The `phiONB φ` orthonormal-basis vectors coincide
    with the underlying transported family `phiONB_family φ`. Immediate from
    `coe_basisOfOrthonormalOfCardEqFinrank` composed with
    `Module.Basis.coe_toOrthonormalBasis`. -/
lemma phiONB_apply_eq_family [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) (p : Fin n × Fin k) :
    (phiONB n k φ p : EuclideanSpace ℂ (Fin (k * n)))
      = phiONB_family n k φ p := by
  unfold phiONB
  rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]

/-- **C2.11 – helper B.** Action of `E_of φ i j` on `phiONB φ (m, a)`:
    diagonal-in-middle-index by C2.2/C2.3, sending to `phiONB φ (i, a)`
    when `j = m` and to `0` otherwise. -/
lemma E_of_apply_phiONB [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) (i j m : Fin n) (a : Fin k) :
    Matrix.toEuclideanLin (E_of n k φ i j)
        (phiONB n k φ (m, a) : EuclideanSpace ℂ (Fin (k * n)))
      = if j = m then (phiONB n k φ (i, a) : EuclideanSpace ℂ (Fin (k * n)))
                 else 0 := by
  set z : Fin n := ⟨0, Nat.pos_of_neZero n⟩ with hz
  set b := E_of_00_stdOrthonormalBasis n k φ with hb
  -- phiONB φ (m,a) = E_of φ m z · b a (via helper A / phiONB_family).
  have hphi_m : (phiONB n k φ (m, a) : EuclideanSpace ℂ (Fin (k * n)))
      = Matrix.toEuclideanLin (E_of n k φ m z) (b a) := by
    rw [phiONB_apply_eq_family]; rfl
  have hphi_i : (phiONB n k φ (i, a) : EuclideanSpace ℂ (Fin (k * n)))
      = Matrix.toEuclideanLin (E_of n k φ i z) (b a) := by
    rw [phiONB_apply_eq_family]; rfl
  rw [hphi_m, ← toEuclideanLin_mul_apply]
  by_cases hjm : j = m
  · subst hjm
    have hprod : E_of n k φ i j * E_of n k φ j z = E_of n k φ i z :=
      E_of_mul_same n k φ i j z
    rw [hprod, if_pos rfl, hphi_i]
  · have hprod : E_of n k φ i j * E_of n k φ m z = 0 :=
      E_of_mul_diff n k φ i j m z hjm
    rw [hprod, LinearEquiv.map_zero, LinearMap.zero_apply, if_neg hjm]

/-- **C2.11 – helper.** `toEuclideanLin 1 = id` on `EuclideanSpace ℂ (Fin (k*n))`. -/
private lemma toEuclideanLin_one_apply
    {N : ℕ} (v : EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ) v = v := by
  rw [Matrix.toEuclideanLin_apply, Matrix.one_mulVec]
  rfl

/-- **C2.11.** Conjugation identity on a single matrix unit.

    For `U := unitaryOfONBpair (phiONB φ) (phiONB ψ)`, the images
    `E_of φ i j` and `E_of ψ i j` are conjugate:
    `E_of φ i j = U * E_of ψ i j * star U`.

    **Proof outline.** By injectivity of `Matrix.toEuclideanLin`
    (`LinearEquiv.injective`) and `Basis.ext` on `(phiONB φ).toBasis`, it
    suffices to check equality after applying both sides as linear maps
    to each basis vector `phiONB φ (m, a)`. On that vector:
    - LHS: `toEuclideanLin (E_of φ i j) (phiONB φ (m, a))` equals
      `if j = m then phiONB φ (i, a) else 0` by `E_of_apply_phiONB`.
    - RHS: `toEuclideanLin (U * E_of ψ i j * Uᴴ) (phiONB φ (m, a))`
      decomposes via `toEuclideanLin_mul_apply`. First,
      `toEuclideanLin Uᴴ (phiONB φ (m, a)) = phiONB ψ (m, a)`, which
      follows from `unitaryOfONBpair_apply_phiONB` together with
      `star U * U = 1` (`unitaryOfONBpair_isUnitary`). Then
      `toEuclideanLin (E_of ψ i j) (phiONB ψ (m, a))
        = if j = m then phiONB ψ (i, a) else 0` by
      `E_of_apply_phiONB`. Finally
      `toEuclideanLin U (phiONB ψ (i, a)) = phiONB φ (i, a)` by
      `unitaryOfONBpair_apply_phiONB`.
    Both sides match. -/
lemma conjugation_identity_on_single [NeZero n]
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
           Matrix (Fin (k * n)) (Fin (k * n)) ℂ)
    (i j : Fin n) :
    E_of n k φ i j =
      unitaryOfONBpair n k (phiONB n k φ) (phiONB n k ψ)
        * E_of n k ψ i j
        * star (unitaryOfONBpair n k (phiONB n k φ) (phiONB n k ψ)) := by
  classical
  set U : Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
    unitaryOfONBpair n k (phiONB n k φ) (phiONB n k ψ) with hU_def
  set bφ : OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * n))) :=
    phiONB n k φ with hbφ
  set bψ : OrthonormalBasis (Fin n × Fin k) ℂ (EuclideanSpace ℂ (Fin (k * n))) :=
    phiONB n k ψ with hbψ
  -- Unitarity facts.
  have hstarUU : star U * U = 1 := (unitaryOfONBpair_isUnitary n k bφ bψ).2
  -- Forward bridge: `toEuclideanLin U (bψ p) = bφ p`.
  have hbridge_fwd : ∀ p : Fin n × Fin k,
      Matrix.toEuclideanLin U (bψ p : EuclideanSpace ℂ (Fin (k * n)))
        = (bφ p : EuclideanSpace ℂ (Fin (k * n))) := by
    intro p; exact unitaryOfONBpair_apply_phiONB n k φ ψ p
  -- Reverse-direction bridge: `toEuclideanLin (star U) (bφ p) = bψ p`.
  have hbridge_rev : ∀ p : Fin n × Fin k,
      Matrix.toEuclideanLin (star U) (bφ p : EuclideanSpace ℂ (Fin (k * n)))
        = (bψ p : EuclideanSpace ℂ (Fin (k * n))) := by
    intro p
    have hfwd := hbridge_fwd p
    have hpre : Matrix.toEuclideanLin (star U)
                    (Matrix.toEuclideanLin U (bψ p : EuclideanSpace ℂ (Fin (k * n))))
                  = Matrix.toEuclideanLin (star U)
                    (bφ p : EuclideanSpace ℂ (Fin (k * n))) := by
      rw [hfwd]
    rw [← toEuclideanLin_mul_apply, hstarUU, toEuclideanLin_one_apply] at hpre
    exact hpre.symm
  -- It suffices to prove equality of the two matrices via `Basis.ext` on the
  -- basis `bφ.toBasis`, after applying `toEuclideanLin` (which is injective).
  apply Matrix.toEuclideanLin.injective
  apply Module.Basis.ext bφ.toBasis
  intro p
  obtain ⟨m, a⟩ := p
  -- LHS on `bφ (m, a)`.
  rw [OrthonormalBasis.coe_toBasis]
  have hLHS :
      Matrix.toEuclideanLin (E_of n k φ i j)
          (bφ (m, a) : EuclideanSpace ℂ (Fin (k * n)))
        = if j = m then (bφ (i, a) : EuclideanSpace ℂ (Fin (k * n)))
                    else 0 := by
    simpa [hbφ] using E_of_apply_phiONB n k φ i j m a
  -- RHS on `bφ (m, a)`: unfold as `U * (E_of ψ) * (star U)` applied.
  have hstep1 :
      Matrix.toEuclideanLin (U * E_of n k ψ i j * star U)
          (bφ (m, a) : EuclideanSpace ℂ (Fin (k * n)))
        = Matrix.toEuclideanLin U
            (Matrix.toEuclideanLin (E_of n k ψ i j)
              (Matrix.toEuclideanLin (star U)
                (bφ (m, a) : EuclideanSpace ℂ (Fin (k * n))))) := by
    rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
  have hstep2 :
      Matrix.toEuclideanLin (star U)
          (bφ (m, a) : EuclideanSpace ℂ (Fin (k * n)))
        = (bψ (m, a) : EuclideanSpace ℂ (Fin (k * n))) :=
    hbridge_rev (m, a)
  have hstep3 :
      Matrix.toEuclideanLin (E_of n k ψ i j)
          (bψ (m, a) : EuclideanSpace ℂ (Fin (k * n)))
        = if j = m then (bψ (i, a) : EuclideanSpace ℂ (Fin (k * n)))
                    else 0 := by
    simpa [hbψ] using E_of_apply_phiONB n k ψ i j m a
  have hstep4 :
      Matrix.toEuclideanLin U (bψ (i, a) : EuclideanSpace ℂ (Fin (k * n)))
        = (bφ (i, a) : EuclideanSpace ℂ (Fin (k * n))) :=
    hbridge_fwd (i, a)
  rw [hstep1, hstep2, hstep3]
  by_cases hjm : j = m
  · rw [if_pos hjm, hstep4, hLHS, if_pos hjm]
  · rw [if_neg hjm, LinearMap.map_zero, hLHS, if_neg hjm]

/-- **C2 main.** Noether–Skolem specialised to `M_n → M_{kn}`.

    **Proof outline.** Split on `n`:
    - If `n = 0` then `Matrix (Fin (k*n)) (Fin (k*n)) ℂ = Matrix (Fin 0) (Fin 0) ℂ`
      is a `Subsingleton`, so `U = 1` works trivially.
    - Otherwise `[NeZero n]`, take `U := unitaryOfONBpair (phiONB φ) (phiONB ψ)`.
      Unitarity from `unitaryOfONBpair_isUnitary`. For the conjugation identity,
      decompose `x = Σᵢⱼ single i j (x i j) = Σᵢⱼ x i j • single i j 1` via
      `Matrix.matrix_eq_sum_single` and `Matrix.smul_single`. Then apply
      `map_sum`, `map_smul` on both `φ` and `ψ`, and use
      `conjugation_identity_on_single` pointwise plus bilinearity of
      matrix multiplication to conclude. -/
lemma unital_star_hom_inner_unique
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
           Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    ∃ U : Matrix (Fin (k * n)) (Fin (k * n)) ℂ,
      U * star U = 1 ∧ star U * U = 1 ∧
      ∀ x, φ x = U * ψ x * (star U) := by
  classical
  by_cases hn : n = 0
  · -- Degenerate case: matrices are `Fin 0 → Fin 0 → ℂ`, a subsingleton.
    subst hn
    refine ⟨1, ?_, ?_, ?_⟩
    · rw [star_one, mul_one]
    · rw [star_one, mul_one]
    · intro x
      haveI : Subsingleton (Matrix (Fin (k * 0)) (Fin (k * 0)) ℂ) := by
        rw [Nat.mul_zero]; infer_instance
      exact Subsingleton.elim _ _
  · haveI hNZn : NeZero n := ⟨hn⟩
    refine ⟨unitaryOfONBpair n k (phiONB n k φ) (phiONB n k ψ), ?_, ?_, ?_⟩
    · exact (unitaryOfONBpair_isUnitary n k (phiONB n k φ) (phiONB n k ψ)).1
    · exact (unitaryOfONBpair_isUnitary n k (phiONB n k φ) (phiONB n k ψ)).2
    · intro x
      set U : Matrix (Fin (k * n)) (Fin (k * n)) ℂ :=
        unitaryOfONBpair n k (phiONB n k φ) (phiONB n k ψ) with hU_def
      -- Coefficient function (avoids re-substitution during rewrites).
      let c : Fin n → Fin n → ℂ := fun i j => x i j
      -- Decompose x = ∑ i j, c i j • single i j 1 via matrix_eq_sum_single.
      have hxdec : x = ∑ i : Fin n, ∑ j : Fin n,
                        c i j • Matrix.single (α := ℂ) i j 1 := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single x]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        show Matrix.single i j (x i j) = c i j • Matrix.single i j 1
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      -- Distribute φ over the sum.
      have hφx : φ x = ∑ i : Fin n, ∑ j : Fin n,
                          c i j • E_of n k φ i j := by
        rw [hxdec, map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_smul]; rfl
      -- Distribute ψ over the sum similarly.
      have hψx : ψ x = ∑ i : Fin n, ∑ j : Fin n,
                          c i j • E_of n k ψ i j := by
        rw [hxdec, map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_smul]; rfl
      -- Apply conjugation identity pointwise, then push U, star U outside sums.
      calc φ x
          = ∑ i : Fin n, ∑ j : Fin n, c i j • E_of n k φ i j := hφx
        _ = ∑ i : Fin n, ∑ j : Fin n,
                c i j • (U * E_of n k ψ i j * star U) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [conjugation_identity_on_single n k φ ψ i j]
        _ = ∑ i : Fin n, ∑ j : Fin n,
                U * (c i j • E_of n k ψ i j) * star U := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [mul_smul_comm, smul_mul_assoc]
        _ = U * (∑ i : Fin n, ∑ j : Fin n,
                    c i j • E_of n k ψ i j) * star U := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum, Finset.sum_mul]
        _ = U * ψ x * star U := by rw [← hψx]

end C2_NoetherSkolem
end PrincipiaTractalis.SubstrateRigidity
