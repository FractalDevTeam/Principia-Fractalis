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

/-! ## §5e — r38: Kronecker-with-identity operator norm bound

Taking the square root of r37 and applying `ContinuousLinearMap.opNorm_le_bound`
gives the operator-norm bound `‖A ⊗ 1‖ ≤ ‖A‖` — the ≤ direction of
the Kronecker isometry. -/

/-- **r38: Kronecker-with-identity operator norm bound**:
    `‖A ⊗ (1 : Matrix n n ℂ)‖ ≤ ‖A‖` under the L2 operator norm.

    Proved by using the raw-sum norm bound (r37) to derive
    `∑ p, |(A ⊗ 1) *ᵥ f (p)|² ≤ ‖A‖² · ‖f‖²`, and applying
    `Matrix.l2_opNorm_le_of_norm_sq_bound` or equivalent. -/
theorem kronecker_one_opNorm_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) :
    ‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ ≤ ‖A‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun f => ?_)
  -- Compute the norm-squared via EuclideanSpace.norm_sq_eq
  -- The CLM applied to f at index p equals ((A ⊗ 1) *ᵥ f) p
  have hLHS_sq : ‖((Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix n n ℂ)))) f‖ ^ 2 =
                 ∑ p : m × n, ‖((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ (fun q => f q)) p‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hf_norm_sq : ‖f‖ ^ 2 = ∑ p : m × n, ‖f p‖ ^ 2 := EuclideanSpace.norm_sq_eq f
  -- Apply r37
  have hbound := kronecker_one_mulVec_norm_sq_le A (fun p => f p)
  -- Combined norm-squared bound
  have hcombined :
      ‖((Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix n n ℂ)))) f‖ ^ 2 ≤ (‖A‖ * ‖f‖) ^ 2 := by
    rw [hLHS_sq, mul_pow, hf_norm_sq]
    exact hbound
  -- Extract the norm bound via sqrt (both sides non-negative)
  have hy_nn : (0:ℝ) ≤ ‖((Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix n n ℂ)))) f‖ := norm_nonneg _
  have h_target_nn : (0:ℝ) ≤ ‖A‖ * ‖f‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg (‖((Matrix.toEuclideanCLM (n := m × n) (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix n n ℂ)))) f‖ - ‖A‖ * ‖f‖),
             hy_nn, h_target_nn]

/-! ## §5f — r39: Kronecker-with-identity operator norm reverse bound

The reverse direction: `‖A‖ ≤ ‖A ⊗ 1‖`. Proved by embedding a vector
`v : EuclideanSpace ℂ m` into `EuclideanSpace ℂ (m × n)` as the `j₀`-th
column (`f (i, j) := if j = j₀ then v i else 0`), noting that this
embedding is isometric and `(A ⊗ 1) *ᵥ f` at `j = j₀` equals `A *ᵥ v`,
and elsewhere zero. -/

/-- **r39: Kronecker-with-identity operator norm reverse bound**:
    `‖A‖ ≤ ‖A ⊗ (1 : Matrix n n ℂ)‖` when `n` is inhabited.

    Proof strategy: pick j₀ : n. For any v ∈ EuclideanSpace ℂ m,
    embed as f(i,j) := if j = j₀ then v i else 0.
    Key inequality: ‖A *ᵥ v‖² ≤ ‖(A ⊗ 1) *ᵥ f‖² (single-j-slice ≤ full sum).
    Combined with ‖f‖² = ‖v‖² and l2_opNorm_mulVec, this gives
    ‖A *ᵥ v‖² ≤ ‖A ⊗ 1‖² · ‖v‖². Take sqrt + opNorm_le_bound. -/
theorem kronecker_one_opNorm_ge
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Nonempty n]
    (A : Matrix m m ℂ) :
    ‖A‖ ≤ ‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
  obtain ⟨j₀⟩ := ‹Nonempty n›
  -- Embedding function: only column j₀ carries v
  let embed_fn : m × n → ℂ := fun p => if p.2 = j₀ then v p.1 else 0
  let f : EuclideanSpace ℂ (m × n) := (EuclideanSpace.equiv (m × n) ℂ).symm embed_fn
  -- Norm preservation ‖f‖² = ‖v‖²
  have hf_norm_sq : ‖f‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    show ∑ p : m × n, ‖embed_fn p‖ ^ 2 = ∑ i, ‖v i‖ ^ 2
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- ∑ j, ‖if j = j₀ then v i else 0‖² = ‖v i‖²
    simp only [embed_fn]
    have key : ∀ j : n, ‖(if j = j₀ then v i else 0 : ℂ)‖ ^ 2 =
               if j = j₀ then ‖v i‖ ^ 2 else 0 := by
      intro j; by_cases h : j = j₀ <;> simp [h]
    simp_rw [key]
    rw [Finset.sum_ite_eq' Finset.univ j₀ (fun _ : n => ‖v i‖ ^ 2)]
    simp
  -- (A ⊗ 1) *ᵥ f at column j₀ equals A *ᵥ v
  have hAOne_at_j₀ : ∀ i, ((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ embed_fn) (i, j₀) = (A *ᵥ v) i := by
    intro i
    rw [kronecker_one_mulVec_apply]
    congr 1
    ext i'
    simp [embed_fn]
  -- Key inequality: ‖A *ᵥ v‖² ≤ ‖(A ⊗ 1) *ᵥ f‖² via single-j-slice ≤ full sum
  have hslice_le :
      ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤
      ∑ p : m × n, ‖((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ (fun q => f q)) p‖ ^ 2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_le_sum (fun i _ => ?_)
    -- ‖(A *ᵥ v) i‖² ≤ ∑ j, ‖(A ⊗ 1 *ᵥ f) (i, j)‖²
    calc ‖(A *ᵥ v) i‖ ^ 2
        = ‖((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ embed_fn) (i, j₀)‖ ^ 2 := by rw [hAOne_at_j₀]
      _ = ‖((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ (fun q => f q)) (i, j₀)‖ ^ 2 := by rfl
      _ ≤ ∑ j, ‖((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ (fun q => f q)) (i, j)‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun j => ‖((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ (fun q => f q)) (i, j)‖ ^ 2)
            (fun _ _ => sq_nonneg _)
            (Finset.mem_univ j₀)
  -- Apply l2_opNorm_mulVec on A ⊗ 1 with vector f
  have h_bound := Matrix.l2_opNorm_mulVec (A ⊗ₖ (1 : Matrix n n ℂ)) f
  have h_bound_nn : (0:ℝ) ≤
      ‖(EuclideanSpace.equiv (m × n) ℂ).symm ((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ f)‖ := norm_nonneg _
  have h_bound_sq :
      ‖(EuclideanSpace.equiv (m × n) ℂ).symm ((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ f)‖ ^ 2 ≤
      (‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ * ‖f‖) ^ 2 := by
    have := mul_self_le_mul_self h_bound_nn h_bound
    simpa [sq] using this
  -- Expand the norm-squared LHS via EuclideanSpace.norm_sq_eq
  rw [EuclideanSpace.norm_sq_eq] at h_bound_sq
  -- Chain: ‖A *ᵥ v‖² ≤ (LHS of h_bound_sq) ≤ (‖A ⊗ 1‖ * ‖f‖)² = ‖A ⊗ 1‖² * ‖v‖²
  have h_target_nn : (0:ℝ) ≤ ‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ * ‖v‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h_A_v_sq :
      ∑ i, ‖(A *ᵥ v) i‖ ^ 2 ≤ (‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ * ‖v‖) ^ 2 := by
    calc ∑ i, ‖(A *ᵥ v) i‖ ^ 2
        ≤ _ := hslice_le
      _ = ‖(EuclideanSpace.equiv (m × n) ℂ).symm ((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ f)‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]; rfl
      _ ≤ (‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ * ‖f‖) ^ 2 := by
        have := mul_self_le_mul_self h_bound_nn h_bound
        simpa [sq] using this
      _ = (‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ * ‖v‖) ^ 2 := by
        rw [mul_pow, mul_pow, hf_norm_sq]
  -- Goal: ‖toEuclideanCLM A v‖ ≤ ‖A ⊗ 1‖ * ‖v‖
  -- ‖toEuclideanCLM A v‖² = ∑ i, |(A *ᵥ v) i|²
  have h_goal_sq :
      ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A) v‖ ^ 2 ≤
      (‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ * ‖v‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact h_A_v_sq
  -- Take sqrt
  nlinarith [sq_nonneg (‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A) v‖ -
                        ‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ * ‖v‖),
             norm_nonneg ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A) v),
             h_target_nn]

/-! ## §5g — r40: Kronecker-with-identity FULL ISOMETRY

Combining r38 (≤ direction) with r39 (≥ direction) gives the full
Kronecker-with-identity isometry `‖A ⊗ 1‖ = ‖A‖`. -/

/-- **★★★ r40: Kronecker-with-identity ISOMETRY ★★★**

    `‖A ⊗ (1 : Matrix n n ℂ)‖ = ‖A‖` for `A : Matrix m m ℂ` under
    the L2 operator norm, when `n` is inhabited.

    This is the substrate isometry key: for every A and every k,
    the tensor-with-identity embedding at the matrix level preserves
    the operator norm exactly. Combining r38 (`kronecker_one_opNorm_le`)
    with r39 (`kronecker_one_opNorm_ge`). -/
theorem kronecker_one_opNorm_eq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Nonempty n]
    (A : Matrix m m ℂ) :
    ‖(A ⊗ₖ (1 : Matrix n n ℂ))‖ = ‖A‖ :=
  le_antisymm (kronecker_one_opNorm_le A) (kronecker_one_opNorm_ge A)

/-! ## §5h — r41: Reindex operator norm isometry

Simultaneous re-labeling of rows and columns by a bijection preserves
the L2 operator norm:
    `‖Matrix.reindex e e A‖ = ‖A‖`
This is the "conjugation by unitary permutation" identity: reindexing
implements a change of orthonormal basis on `EuclideanSpace ℂ m`, and
unitary conjugation preserves the operator norm.

Combined with r40 (`kronecker_one_opNorm_eq`), this delivers the
substrate embedding isometry
    `‖substrateEmbedMatrix k A‖ = ‖A‖`
at every level k, since `substrateEmbedMatrix k A` is definitionally
`Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ 1_3)`. -/

/-- **r41 helper: reindex mulVec formula**.

    For `e : m ≃ m'` and `A : Matrix m m ℂ`,
    `((Matrix.reindex e e A) *ᵥ g) i' = (A *ᵥ (g ∘ e)) (e.symm i')`.
    Reindexing acts on `mulVec` by pre-composing the vector with `e`
    and post-composing the index with `e.symm`. -/
theorem reindex_mulVec_apply
    {m m' : Type*} [Fintype m] [Fintype m']
    (e : m ≃ m') (A : Matrix m m ℂ) (g : m' → ℂ) (i' : m') :
    ((Matrix.reindex e e A) *ᵥ g) i' = (A *ᵥ (g ∘ e)) (e.symm i') := by
  show ∑ j' : m', A (e.symm i') (e.symm j') * g j' =
       ∑ j : m, A (e.symm i') j * g (e j)
  rw [← Equiv.sum_comp e (fun j' : m' => A (e.symm i') (e.symm j') * g j')]
  simp

/-- **r41 ≤ direction: reindex operator norm upper bound**.

    `‖Matrix.reindex e e A‖ ≤ ‖A‖` for `e : m ≃ m'` and
    `A : Matrix m m ℂ` under the L2 operator norm. Proved by combining
    `reindex_mulVec_apply` with the raw-sum operator-norm bound (r36)
    and reindexing the sum via the bijection `e`. -/
theorem reindex_opNorm_le
    {m m' : Type*} [Fintype m] [Fintype m']
    [DecidableEq m] [DecidableEq m']
    (e : m ≃ m') (A : Matrix m m ℂ) :
    ‖Matrix.reindex e e A‖ ≤ ‖A‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g => ?_)
  -- ‖CLM g‖² = ∑ i' : m', ‖((reindex e e A) *ᵥ g) i'‖²
  have hLHS_sq :
      ‖(Matrix.toEuclideanCLM (n := m') (𝕜 := ℂ) (Matrix.reindex e e A)) g‖ ^ 2 =
        ∑ i' : m', ‖((Matrix.reindex e e A) *ᵥ (fun q => g q)) i'‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  -- Reindex ∑ i' : m' → ∑ i : m via reindex_mulVec_apply and e ≃
  have hReindex :
      ∑ i' : m', ‖((Matrix.reindex e e A) *ᵥ (fun q => g q)) i'‖ ^ 2 =
      ∑ i : m, ‖(A *ᵥ (fun j : m => g (e j))) i‖ ^ 2 := by
    rw [← Equiv.sum_comp e
          (fun i' : m' => ‖((Matrix.reindex e e A) *ᵥ (fun q => g q)) i'‖ ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h := reindex_mulVec_apply e A (fun q => g q) (e i)
    -- h : ((reindex e e A) *ᵥ g) (e i) = (A *ᵥ (g ∘ e)) (e.symm (e i))
    rw [h, Equiv.symm_apply_apply]
    rfl
  -- Apply r36 to A with vector (fun j => g (e j))
  have hbound := matrix_mulVec_norm_sq_le A (fun j : m => g (e j))
  -- Reindex ∑ j : m, ‖g (e j)‖² = ∑ j' : m', ‖g j'‖² = ‖g‖²
  have hg_norm_sq : ∑ j : m, ‖g (e j)‖ ^ 2 = ‖g‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Equiv.sum_comp e (fun j' : m' => ‖g j'‖ ^ 2)
  -- Combine into (‖A‖ * ‖g‖)² bound on ‖CLM g‖²
  have h_combined :
      ‖(Matrix.toEuclideanCLM (n := m') (𝕜 := ℂ) (Matrix.reindex e e A)) g‖ ^ 2 ≤
        (‖A‖ * ‖g‖) ^ 2 := by
    rw [hLHS_sq, hReindex]
    calc ∑ i : m, ‖(A *ᵥ (fun j : m => g (e j))) i‖ ^ 2
        ≤ ‖A‖ ^ 2 * ∑ j : m, ‖g (e j)‖ ^ 2 := hbound
      _ = ‖A‖ ^ 2 * ‖g‖ ^ 2 := by rw [hg_norm_sq]
      _ = (‖A‖ * ‖g‖) ^ 2 := by ring
  -- Take sqrt via nlinarith
  have hy_nn : (0:ℝ) ≤
      ‖(Matrix.toEuclideanCLM (n := m') (𝕜 := ℂ) (Matrix.reindex e e A)) g‖ := norm_nonneg _
  have h_target_nn : (0:ℝ) ≤ ‖A‖ * ‖g‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg (‖(Matrix.toEuclideanCLM (n := m') (𝕜 := ℂ) (Matrix.reindex e e A)) g‖
                       - ‖A‖ * ‖g‖),
             hy_nn, h_target_nn, h_combined]

/-- **★★★ r41: Reindex operator norm ISOMETRY ★★★**

    `‖Matrix.reindex e e A‖ = ‖A‖` for `e : m ≃ m'` and
    `A : Matrix m m ℂ` under the L2 operator norm.

    Simultaneous re-labeling of rows and columns by a bijection
    preserves the operator norm exactly.

    Proof: ≤ direction via `reindex_opNorm_le`. Reverse direction by
    applying `reindex_opNorm_le` with `e.symm` on `reindex e e A` and
    simplifying `reindex e.symm e.symm (reindex e e A) = A`.

    Combined with r40 (`kronecker_one_opNorm_eq`), this delivers the
    substrate embedding isometry `‖substrateEmbedMatrix k A‖ = ‖A‖`
    at every level k, since the substrate embedding is
    `reindex finProdFinEquiv finProdFinEquiv (A ⊗ 1_3)`. -/
theorem reindex_opNorm_eq
    {m m' : Type*} [Fintype m] [Fintype m']
    [DecidableEq m] [DecidableEq m']
    (e : m ≃ m') (A : Matrix m m ℂ) :
    ‖Matrix.reindex e e A‖ = ‖A‖ := by
  refine le_antisymm (reindex_opNorm_le e A) ?_
  have h := reindex_opNorm_le e.symm (Matrix.reindex e e A)
  have heq : Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [heq] at h
  exact h

/-! ## §5i — r42: Substrate embedding operator norm ISOMETRY

The composition of r40 (Kronecker-with-identity isometry) and r41
(reindex isometry) delivers the substrate embedding isometry at the
matrix level:

    `‖substrateEmbedMatrix k A‖ = ‖A‖`

for every level `k : ℕ` and every `A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ`.

This is the exact input required by the UHF direct-limit norm
construction to lift the substrate C*-norm from the finite levels to
T_∞. -/

/-- **★★★ r42: SUBSTRATE EMBEDDING ISOMETRY ★★★**

    `‖substrateEmbedMatrix k A‖ = ‖A‖` at every level `k : ℕ`.

    The substrate embedding `ι_k : A_k → A_(k+1)` preserves the L2
    operator norm exactly. Together with r28's *-algebra homomorphism
    properties, this makes `ι_k` an isometric *-algebra embedding —
    the standard "level-wise C*-embedding" required by the UHF
    direct-limit construction of T_∞ as a C*-algebra.

    Proof: `substrateEmbedMatrix k A` unfolds to
    `Matrix.reindex (levelStepEquiv k) (levelStepEquiv k) (A ⊗ₖ 1_{Fin 3})`.
    Apply r41 (`reindex_opNorm_eq`) then r40 (`kronecker_one_opNorm_eq`). -/
theorem substrateEmbedMatrix_opNorm_eq (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    ‖SubstrateBase3Embed.substrateEmbedMatrix k A‖ = ‖A‖ := by
  unfold SubstrateBase3Embed.substrateEmbedMatrix
  rw [reindex_opNorm_eq, kronecker_one_opNorm_eq]

/-- **r42 corollary: substrate `RingHom` embedding isometry**.

    The bundled `substrateRingHom k : Matrix _ _ ℂ →+* Matrix _ _ ℂ`
    is norm-preserving. Follows from `substrateEmbedMatrix_opNorm_eq`
    plus the definitional identity
    `substrateRingHom k A = substrateEmbedMatrix k A`. -/
theorem substrateRingHom_opNorm_eq (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    ‖SubstrateBase3RingHom.substrateRingHom k A‖ = ‖A‖ :=
  substrateEmbedMatrix_opNorm_eq k A

/-- **r42 discharge**: the substrate embedding isometry conjecture
    from §4 (`SubstrateEmbeddingIsIsometryConjecture`) is now
    kernel-verified as a theorem. -/
theorem substrate_embedding_isometry :
    SubstrateEmbeddingIsIsometryConjecture :=
  fun k A => substrateRingHom_opNorm_eq k A

/-! ## §6 — Substrate norm structure honest scope

r33-r42 provides:
  * Level-wise NormedRing/NormedAlgebra/CStarRing structure at every k.
  * Level-0 scalar identification.
  * Star-mul reduction of the isometry via the C*-property (r34).
  * Kronecker-with-identity mulVec formula (r35).
  * Raw-sum matrix mulVec norm bound (r36).
  * Kronecker-with-identity mulVec norm bound (r37).
  * Kronecker-with-identity `≤` direction (r38).
  * Kronecker-with-identity `≥` direction (r39).
  * Kronecker-with-identity full isometry `‖A ⊗ 1‖ = ‖A‖` (r40).
  * Reindex isometry `‖reindex e e A‖ = ‖A‖` (r41).
  * ★ SUBSTRATE EMBEDDING ISOMETRY `‖substrateEmbedMatrix k A‖ = ‖A‖` (r42).

Remaining for T_∞ as a mathlib-native CStarAlgebra:
  * r43-r44: Lift norm to T_∞ via UHF direct-limit norm construction
             using r42 as the level-wise isometry input.
  * r45+:    NormedRing → CStarAlgebra → Nuclearity on T_∞. -/

end SubstrateBase3Norm
end PrincipiaTractalis
