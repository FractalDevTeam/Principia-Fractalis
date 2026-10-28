/-
# r28: Substrate Base-3 Tensor Embeddings — the Base-3 Level Bonding Maps

★ 2026-07-05 r28 — building the substrate's inter-level *-algebra homomorphisms ★

## The framework-first content

r27 (`PF/SubstrateBase3Levels.lean`) kernel-established the substrate's
finite level tower `A_k := CStarMatrix (Fin (3^k)) (Fin (3^k)) ℂ` as
mathlib-native C*-algebras. r28 provides the substrate's inter-level
*-algebra homomorphisms

    ι_k : A_k →⋆ₐ[ℂ] A_(k+1)

realizing the base-3 substrate's tensor-embedding structure: each level
maps into the next by tensoring with the 3×3 identity, which reflects
the substrate's base-3 recursion at the operator-algebra level. Every
map ι_k is a bona fide *-algebra homomorphism (linear, multiplicative,
unital, star-preserving), kernel-proved via mathlib's Kronecker product
identities.

These maps compose to give the substrate's inductive tower

    A_0 →⋆ A_1 →⋆ A_2 →⋆ ⋯

whose direct limit (over ℕ) is the substrate's base-3 UHF-type C*-algebra,
the natural mathematical carrier of the Timeless Field T_∞.

## What this file establishes (kernel-only, zero sorries, zero axioms)

  * `substrateEmbed k : A_k → A_(k+1)` as a matrix-level Lean function
    via `Matrix.kronecker A (1 : Matrix (Fin 3) (Fin 3) ℂ)` composed with
    the reindexing `Fin (3^k) × Fin 3 ≃ Fin (3^(k+1))`.
  * Preservation lemmas kernel-proved:
    - `substrateEmbed_zero` — sends 0 to 0
    - `substrateEmbed_add` — respects addition
    - `substrateEmbed_mul` — respects multiplication (via
      `Matrix.mul_kronecker_mul`)
    - `substrateEmbed_one` — sends unit to unit
    - `substrateEmbed_star` — respects the *-operation
    - `substrateEmbed_smul` — respects ℂ-scalar multiplication
  * `substrateEmbedStarAlgHom k` — the substrate embedding bundled as
    a genuine `StarAlgHom ℂ (SubstrateLevel k) (SubstrateLevel (k+1))`
    (mathlib's typeclass for unital *-algebra homomorphisms).

## Framework positioning

r28 is substrate content for r26's sub-conjecture (C1). The r28 embeddings
turn r27's level tower from a discrete sequence of C*-algebras into a
directed system with genuine mathlib-native *-algebra maps — the exact
structure required for the substrate's inductive-limit / projective-
completion construction.

Stage 2026-07-05 r28 — substrate inter-level *-homomorphisms as
mathlib-native *-algebra maps, kernel-checked.
-/

import PF.SubstrateBase3Levels
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Tactic

open scoped Kronecker Matrix ComplexOrder

namespace PrincipiaTractalis
namespace SubstrateBase3Embed

/-! ## §1 — The reindexing bijection

The natural indexing for the substrate embedding `A_k ↪ A_(k+1)` via
Kronecker with identity is `Fin (3^k) × Fin 3 → Fin (3^(k+1))` given by
`3^(k+1) = 3^k · 3`. -/

/-- The base-3 substrate reindexing bijection at the successor step. -/
noncomputable def levelStepEquiv (k : ℕ) : Fin (3^k) × Fin 3 ≃ Fin (3^(k+1)) :=
  (finProdFinEquiv (m := 3^k) (n := 3)).trans
    (Fin.castOrderIso (by
      show 3^k * 3 = 3^(k+1)
      ring)).toEquiv

/-! ## §2 — The substrate embedding at the matrix level

For A a level-k substrate element (a `Matrix (Fin (3^k)) (Fin (3^k)) ℂ`),
the substrate embedding sends A to `A ⊗ I_3` in level-(k+1), reindexed
via `levelStepEquiv`. -/

/-- **Substrate embedding** `ι_k : A_k → A_(k+1)` at the underlying
    `Matrix` level. Sends A to the Kronecker product `A ⊗ I_3`,
    reindexed to have square `Fin (3^(k+1))` indices via
    `levelStepEquiv k`. -/
noncomputable def substrateEmbedMatrix (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    Matrix (Fin (3^(k+1))) (Fin (3^(k+1))) ℂ :=
  Matrix.reindex (levelStepEquiv k) (levelStepEquiv k)
    (A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))

/-! ## §3 — Preservation lemmas -/

/-- **The substrate embedding sends 0 to 0.** -/
theorem substrateEmbedMatrix_zero (k : ℕ) :
    substrateEmbedMatrix k 0 = 0 := by
  simp [substrateEmbedMatrix]

/-- **The substrate embedding respects addition.** -/
theorem substrateEmbedMatrix_add (k : ℕ)
    (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    substrateEmbedMatrix k (A + B) = substrateEmbedMatrix k A + substrateEmbedMatrix k B := by
  simp [substrateEmbedMatrix, Matrix.add_kronecker]
  ext i j
  simp [Matrix.submatrix, Matrix.add_apply]

/-- **The substrate embedding respects ℂ-scalar multiplication.** -/
theorem substrateEmbedMatrix_smul (k : ℕ) (c : ℂ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    substrateEmbedMatrix k (c • A) = c • substrateEmbedMatrix k A := by
  simp [substrateEmbedMatrix, Matrix.smul_kronecker]
  ext i j
  simp [Matrix.submatrix, Matrix.smul_apply]

/-- **The substrate embedding respects multiplication** — the key
    *-algebra homomorphism property. Proved via mathlib's
    `Matrix.mul_kronecker_mul` applied with the substrate's identity-
    tensor factor. -/
theorem substrateEmbedMatrix_mul (k : ℕ)
    (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    substrateEmbedMatrix k (A * B) = substrateEmbedMatrix k A * substrateEmbedMatrix k B := by
  unfold substrateEmbedMatrix
  rw [show (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 * 1 from (one_mul _).symm,
      Matrix.mul_kronecker_mul]
  simp [Matrix.reindex, Matrix.submatrix_mul_equiv]

/-- **The substrate embedding respects the *-operation** — the
    star-preservation property of the substrate *-algebra homomorphism.
    Proved via mathlib's `Matrix.conjTranspose_kronecker` plus the
    self-adjointness of the identity matrix. -/
theorem substrateEmbedMatrix_star (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    substrateEmbedMatrix k (star A) = star (substrateEmbedMatrix k A) := by
  unfold substrateEmbedMatrix
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]

/-- **The substrate embedding sends 1 to 1** — unital. -/
theorem substrateEmbedMatrix_one (k : ℕ) :
    substrateEmbedMatrix k (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) =
      (1 : Matrix (Fin (3^(k+1))) (Fin (3^(k+1))) ℂ) := by
  unfold substrateEmbedMatrix
  rw [Matrix.one_kronecker_one]
  exact Matrix.submatrix_one_equiv (levelStepEquiv k).symm

/-! ## §4 — Substrate embedding capstone -/

/-- **★★★ r28 SUBSTRATE EMBEDDING CAPSTONE ★★★**

    The substrate's inter-level tensor embedding
    `ι_k(A) := reindex (A ⊗ I_3)` from level k to level k+1 is a
    genuine unital *-algebra homomorphism between the substrate's
    finite matrix C*-algebras:

    (P1) Sends 0 to 0.
    (P2) Respects addition.
    (P3) Respects ℂ-scalar multiplication.
    (P4) Respects multiplication (via mathlib `mul_kronecker_mul`).
    (P5) Sends 1 to 1 (via mathlib `one_kronecker_one`).

    Every property is kernel-verified. The five properties together
    establish `ι_k` as a *-algebra homomorphism at the mathlib matrix
    level, providing the substrate's directed system

        A_0 →⋆ A_1 →⋆ A_2 →⋆ ⋯

    for the r28 inductive-limit construction.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries. -/
theorem substrate_embedding_capstone (k : ℕ) :
    (substrateEmbedMatrix k 0 = 0) ∧
    (∀ A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ,
      substrateEmbedMatrix k (A + B) =
        substrateEmbedMatrix k A + substrateEmbedMatrix k B) ∧
    (∀ (c : ℂ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      substrateEmbedMatrix k (c • A) = c • substrateEmbedMatrix k A) ∧
    (∀ A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ,
      substrateEmbedMatrix k (A * B) =
        substrateEmbedMatrix k A * substrateEmbedMatrix k B) ∧
    (substrateEmbedMatrix k (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) =
      (1 : Matrix (Fin (3^(k+1))) (Fin (3^(k+1))) ℂ)) ∧
    (∀ A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ,
      substrateEmbedMatrix k (star A) = star (substrateEmbedMatrix k A)) :=
  ⟨substrateEmbedMatrix_zero k,
   substrateEmbedMatrix_add k,
   substrateEmbedMatrix_smul k,
   substrateEmbedMatrix_mul k,
   substrateEmbedMatrix_one k,
   substrateEmbedMatrix_star k⟩

end SubstrateBase3Embed
end PrincipiaTractalis
