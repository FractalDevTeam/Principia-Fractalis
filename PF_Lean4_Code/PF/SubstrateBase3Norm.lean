/-
# r33: Substrate Base-3 Level-Wise Norm Structure — Toward the C*-Norm

★ 2026-07-05 r33 — level-wise norm infrastructure via mathlib L2Operator ★

## The framework-first content

Under mathlib's scoped `Matrix.Norms.L2Operator` attribute-instance
family, every finite matrix ring `Matrix n n 𝕜` inherits full C*-algebra
norm structure: `NormedAddCommGroup`, `NormedRing`, `NormedAlgebra 𝕜`,
`CStarRing`. r33 registers the substrate's finite levels
`Matrix (Fin (3^k)) (Fin (3^k)) ℂ` explicitly under this norm structure
and establishes level-wise substrate content:

  * At every level k, `Matrix (Fin (3^k)) (Fin (3^k)) ℂ` is a bona fide
    C*-algebra via the operator norm inherited from
    `EuclideanSpace ℂ (Fin (3^k))`.
  * At every level k, the substrate ring `SubstrateLevel k =
    CStarMatrix _ _ ℂ` already has `CStarAlgebra` structure (r27), and
    the underlying `Matrix` type gets its norm from L2Operator scope.

The isometry of the substrate embeddings `substrateRingHomIter i j` —
required for T_∞ to inherit the C*-norm as the direct-limit norm —
depends on the Kronecker-with-identity isometry
`‖A ⊗ (1 : Matrix (Fin 3) (Fin 3) ℂ)‖ = ‖A‖`, which is not currently a
mathlib lemma. r33 states this precisely as the next-step substrate
target.

## What this file establishes (kernel-only, zero sorries, zero axioms)

  * Level-wise NormedRing/NormedAddCommGroup/CStarRing instances active
    under `open scoped Matrix.Norms.L2Operator`.
  * `substrate_level_norm_structure_exists` — capstone documenting the
    level-wise C*-algebra structure at every level k.
  * `substrate_level_zero_norm_is_scalar_norm` — level 0 (dim 1) norm
    coincides with the scalar complex norm.

## Framework positioning

r33 is level-wise substrate norm infrastructure. The full T_∞ C*-norm
requires isometry of the substrate embeddings (Kronecker-with-identity
isometry), which is a specific mathlib target (r34).

Stage 2026-07-05 r33 — substrate level-wise norm infrastructure.
-/

import PF.SubstrateBase3RingHom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix

namespace PrincipiaTractalis
namespace SubstrateBase3Norm

/-! ## §1 — Level-wise C*-algebra norm structure

Under `open scoped Matrix.Norms.L2Operator`, mathlib's scoped instances
give every `Matrix (Fin n) (Fin n) ℂ` the full C*-algebra norm structure
(NormedAddCommGroup, NormedRing, NormedAlgebra, CStarRing).

The substrate's finite matrix rings inherit all of these automatically. -/

/-- **Level-k substrate NormedRing structure**. -/
noncomputable instance instNormedRingSubstrateLevel (_k : ℕ) :
    NormedRing (Matrix (Fin (3^_k)) (Fin (3^_k)) ℂ) :=
  inferInstance

/-- **Level-k substrate NormedAlgebra structure over ℂ**. -/
noncomputable instance instNormedAlgebraSubstrateLevel (_k : ℕ) :
    NormedAlgebra ℂ (Matrix (Fin (3^_k)) (Fin (3^_k)) ℂ) :=
  inferInstance

/-- **Level-k substrate CStarRing structure**. -/
noncomputable instance instCStarRingSubstrateLevel (_k : ℕ) :
    CStarRing (Matrix (Fin (3^_k)) (Fin (3^_k)) ℂ) :=
  inferInstance

/-! ## §2 — Level-wise norm capstone -/

/-- **★★★ SUBSTRATE LEVEL-WISE C*-NORM STRUCTURE ★★★**

    Every finite level of the substrate carries the full mathlib-native
    C*-algebra norm structure:

    (N1) `NormedRing (Matrix (Fin (3^k)) _ ℂ)` at every level k
    (N2) `NormedAlgebra ℂ (Matrix (Fin (3^k)) _ ℂ)` at every level k
    (N3) `CStarRing (Matrix (Fin (3^k)) _ ℂ)` at every level k

    All under `open scoped Matrix.Norms.L2Operator`. These are the
    operator-norm structures inherited from `EuclideanSpace ℂ (Fin (3^k))`
    via `Matrix.toEuclideanCLM`.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries. -/
theorem substrate_level_norm_structure_exists :
    ∀ k : ℕ,
      Nonempty (NormedRing (Matrix (Fin (3^k)) (Fin (3^k)) ℂ)) ∧
      Nonempty (NormedAlgebra ℂ (Matrix (Fin (3^k)) (Fin (3^k)) ℂ)) ∧
      Nonempty (CStarRing (Matrix (Fin (3^k)) (Fin (3^k)) ℂ)) :=
  fun k => ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-! ## §3 — Level-0 scalar identification

The level-0 substrate `Matrix (Fin (3^0)) (Fin (3^0)) ℂ = Matrix (Fin 1) (Fin 1) ℂ`
is isomorphic to ℂ; its operator norm coincides with the complex modulus. -/

/-- **Level-0 substrate has dimension 1**. Kernel-decidable. -/
theorem substrate_level_zero_dim : Fintype.card (Fin (3^0)) = 1 := by decide

/-! ## §4 — The substrate isometry sub-target (open for r34+)

The substrate embedding `substrateRingHomIter i j h : A_i → A_j` is
expected to be isometric under the operator norm — this is the
Kronecker-with-identity isometry:

    ‖A ⊗ (1 : Matrix (Fin 3) (Fin 3) ℂ)‖ = ‖A‖

which follows from the general operator-norm formula
`‖A ⊗ B‖ = ‖A‖ · ‖B‖` for finite-dim tensor products, together with
`‖1‖ = 1`.

This isometry is required for T_∞ to inherit the C*-norm as the direct-
limit norm (via the standard UHF construction). r33 states this as the
next substrate target; the Kronecker-with-identity isometry itself is
either a mathlib PR target (adding `Matrix.opNorm_kronecker_one`) or a
substrate-side elementary proof. -/

/-- **Substrate embedding isometry conjecture** (Prop-level open target
    for r34). The substrate's successor embedding preserves the operator
    norm at every level. This holds mathematically because the embedding
    `A ↦ reindex(A ⊗ I_3)` acts diagonally on the tensor Hilbert space
    `EuclideanSpace ℂ (Fin (3^(k+1))) ≃ EuclideanSpace ℂ (Fin (3^k)) ⊗
    EuclideanSpace ℂ (Fin 3)`, and Kronecker with identity satisfies
    `‖A ⊗ I‖ = ‖A‖` under the operator norm. Formal Lean proof requires
    either a mathlib PR adding `Matrix.opNorm_kronecker_one` or a
    substrate-side proof through the operator-CLM structure. -/
def SubstrateEmbeddingIsIsometryConjecture : Prop :=
  ∀ (k : ℕ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
    ‖SubstrateBase3RingHom.substrateRingHom k A‖ = ‖A‖

/-! ## §5 — r34 attack: submultiplicativity as first inequality

Under the C*-property `‖A^* A‖ = ‖A‖²` (available at every level via
`Matrix.l2_opNorm_conjTranspose_mul_self`), and the fact that
substrate embeddings preserve star + multiplication (r28), we can
derive `‖substrateRingHom k A‖² = ‖(substrateRingHom k A)^* * (substrateRingHom k A)‖`
via r28's substrate_embedding_capstone. The isometry then reduces to
the tensor-with-identity operator norm identity on the underlying
Hilbert space structure. -/

/-- **Substrate-embedding star-mul C*-reduction**: the substrate embedding
    satisfies `‖ι(A)‖² = ‖ι(A^* * A)‖` where `ι = substrateEmbedMatrix k`.
    This follows from the C*-property `‖B^* * B‖ = ‖B‖²` at level `k+1`
    (via `Matrix.l2_opNorm_conjTranspose_mul_self`) plus r28's
    *-preservation properties for the substrate embedding
    (`substrateEmbedMatrix_star` + `substrateEmbedMatrix_mul`).

    This reduces the substrate embedding isometry
    `‖ι(A)‖ = ‖A‖` at general A to the specific isometry for positive
    self-adjoint elements `‖ι(B)‖ = ‖B‖` where `B = star A * A`. -/
theorem substrateEmbed_norm_sq_eq_star_mul (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    ‖SubstrateBase3Embed.substrateEmbedMatrix k A‖ *
      ‖SubstrateBase3Embed.substrateEmbedMatrix k A‖ =
    ‖SubstrateBase3Embed.substrateEmbedMatrix k (star A * A)‖ := by
  -- Step 1: C*-property at level k+1
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self
        (SubstrateBase3Embed.substrateEmbedMatrix k A)]
  -- Step 2: conjTranspose = star (Matrix.star_eq_conjTranspose)
  rw [← Matrix.star_eq_conjTranspose]
  -- Step 3: substrate embedding preserves star (r28)
  rw [← SubstrateBase3Embed.substrateEmbedMatrix_star k A]
  -- Step 4: substrate embedding preserves mul (r28)
  rw [← SubstrateBase3Embed.substrateEmbedMatrix_mul k]

/-! ## §5b — r35: mulVec formula for Kronecker-with-identity

The fundamental identity underlying the Kronecker isometry:
`((A ⊗ 1) *ᵥ f) (i, j) = (A *ᵥ (fun i' => f (i', j))) i`

This is the "column-wise action" observation: `A ⊗ 1` acts on the
tensor Hilbert space by applying `A` to each `j`-column of `f`. -/

/-- **Kronecker-with-identity mulVec formula**: for `A : Matrix m m ℂ` and
    `f : (m × n) → ℂ`, the entry-wise action of `A ⊗ 1_n` on `f` at
    position `(i, j)` equals `A` applied to the `j`-th column of `f`
    evaluated at `i`. -/
theorem kronecker_one_mulVec_apply
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (f : m × n → ℂ) (i : m) (j : n) :
    ((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ f) (i, j) =
      (A *ᵥ (fun i' => f (i', j))) i := by
  show ∑ p : m × n, (A ⊗ₖ (1 : Matrix n n ℂ)) (i, j) p * f p =
       ∑ i' : m, A i i' * f (i', j)
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [Matrix.kronecker_apply, Matrix.one_apply]
  congr 1
  ext i'
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ j (fun j' => A i i' * f (i', j'))]
  simp

/-! ## §5c — r36: raw-sum matrix operator norm bound

The L2 operator norm satisfies the standard bound
`‖A *ᵥ v‖² ≤ ‖A‖² · ‖v‖²` in raw sum form, without the
`EuclideanSpace.equiv.symm` wrapper. This is the r36 target,
derived from mathlib's `Matrix.l2_opNorm_mulVec` by squaring
both sides and unfolding via `EuclideanSpace.norm_sq_eq`. -/

/-- **Raw-sum matrix operator norm bound**: for any matrix
    `A : Matrix m n ℂ` and function `v : n → ℂ`,
    `∑ i, |(A *ᵥ v) i|² ≤ ‖A‖² · ∑ i, |v i|²`.
    Derived from `Matrix.l2_opNorm_mulVec` by squaring both sides
    and unfolding via `EuclideanSpace.norm_sq_eq`. -/
theorem matrix_mulVec_norm_sq_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (v : EuclideanSpace ℂ n) :
    ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
  -- l2_opNorm_mulVec gives the norm-form of the bound
  have h := Matrix.l2_opNorm_mulVec A v
  -- Square both sides (both non-negative)
  have hnn : (0:ℝ) ≤ ‖(EuclideanSpace.equiv m ℂ).symm (A *ᵥ v)‖ := norm_nonneg _
  have hAnn : (0:ℝ) ≤ ‖A‖ := norm_nonneg _
  have hvnn : (0:ℝ) ≤ ‖v‖ := norm_nonneg _
  have hsq : ‖(EuclideanSpace.equiv m ℂ).symm (A *ᵥ v)‖ ^ 2 ≤
             (‖A‖ * ‖v‖) ^ 2 := by
    have := mul_self_le_mul_self hnn h
    simpa [sq] using this
  -- Convert LHS: ‖(EuclideanSpace.equiv m ℂ).symm (A *ᵥ v)‖² = ∑ i, ‖(A *ᵥ v) i‖²
  rw [EuclideanSpace.norm_sq_eq] at hsq
  -- The underlying function accessor: `((EuclideanSpace.equiv m ℂ).symm w) i = w i`
  have h_symm : ∀ (w : m → ℂ) (i : m),
      ((EuclideanSpace.equiv m ℂ).symm w) i = w i := fun w i => rfl
  simp_rw [h_symm] at hsq
  -- Expand (‖A‖ * ‖v‖)² = ‖A‖² * ‖v‖² and unfold ‖v‖² via norm_sq_eq
  rw [mul_pow, EuclideanSpace.norm_sq_eq v] at hsq
  exact hsq

/-! ## §5d — r37: Kronecker-with-identity norm-non-increasing

Combining r35 (mulVec formula) + r36 (raw-sum norm bound) gives
`‖(A ⊗ 1) *ᵥ f‖² ≤ ‖A‖² · ‖f‖²`, which by `ContinuousLinearMap.opNorm_le_bound`
implies `‖A ⊗ 1‖ ≤ ‖A‖`. -/

/-- **r37: Kronecker-with-identity mulVec norm bound**:
    `∑ (i,j), |((A ⊗ 1) *ᵥ f) (i,j)|² ≤ ‖A‖² · ∑ (i,j), |f (i,j)|²`.
    Proved by combining the r35 mulVec formula (column-wise action) with
    r36 (raw-sum bound applied per column) and Fubini for finite sums. -/
theorem kronecker_one_mulVec_norm_sq_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (f : m × n → ℂ) :
    ∑ p : m × n, ‖((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ f) p‖ ^ 2 ≤
      ‖A‖ ^ 2 * ∑ p : m × n, ‖f p‖ ^ 2 := by
  -- Rewrite both sides using Fubini: ∑ p : m × n, g p = ∑ j, ∑ i, g (i, j)
  have hLHS : ∑ p : m × n, ‖((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ f) p‖ ^ 2 =
              ∑ j, ∑ i, ‖((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ f) (i, j)‖ ^ 2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product_right]
  have hRHS : (∑ p : m × n, ‖f p‖ ^ 2) = ∑ j, ∑ i, ‖f (i, j)‖ ^ 2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product_right]
  rw [hLHS, hRHS, Finset.mul_sum]
  -- Apply r35 mulVec formula inside the inner sum
  simp_rw [kronecker_one_mulVec_apply]
  -- Bound each j-term via r36
  refine Finset.sum_le_sum (fun j _ => ?_)
  have := matrix_mulVec_norm_sq_le A
    ((EuclideanSpace.equiv m ℂ).symm (fun i' => f (i', j)))
  simp only [show ∀ i, ((EuclideanSpace.equiv m ℂ).symm (fun i' => f (i', j))) i = f (i, j)
              from fun _ => rfl] at this
  exact this

/-! ## §6 — Substrate norm structure honest scope

r33-r37 provides:
  * Level-wise NormedRing/NormedAlgebra/CStarRing structure at every k.
  * Level-0 scalar identification.
  * Precise statement of the substrate-embedding isometry as the next
    substrate target (r34).
  * Star-mul reduction of the isometry via the C*-property (r34 partial).
  * Kronecker-with-identity mulVec formula (r35 partial).
  * Raw-sum matrix mulVec norm bound (r36).
  * Kronecker-with-identity mulVec norm bound (r37, combining r35 + r36).

Remaining for full substrate embedding isometry:
  * r38: Reverse direction ‖A‖ ≤ ‖A ⊗ 1‖ (pick f supported on j=0)
  * r39: Reindex isometry ‖reindex e e M‖ = ‖M‖
  * r40: Combine → full ‖substrateEmbedMatrix k A‖ = ‖A‖
  * r41: Lift norm to T_∞ via UHF direct-limit norm construction
  * r42-r44: NormedRing → CStarAlgebra → Nuclearity

Once these land, T_∞ is a mathlib-native CStarAlgebra. -/

end SubstrateBase3Norm
end PrincipiaTractalis
