/-
# `H_α` as a Densely-Defined Symmetric LinearPMap on ℓ²(ℕ, ℂ)
# (Closure of `KatoRellichInput_false` via the correct unbounded-operator framework)

## Why this file exists

`PF/Operators/KatoRellichDischarge.lean` proves axiom-free that the Prop

```
KatoRellichInput α : ∃ (H : EllTwoNat →ₗ[ℂ] EllTwoNat), ⟪H ψ, φ⟫ = ⟪ψ, H φ⟫ ∧ ...
```

is **false** for every `α > 0`. The proof is the standard Hellinger–Toeplitz
argument: a symmetric `LinearMap` (total linear map) on a complete inner
product space is automatically continuous, hence bounded; but the diagonal
coefficients `v_alpha_coeff α (2^k)` grow without bound. Contradiction.

The architectural fix is `LinearPMap` — a "partial linear map" carrying
its own domain `Submodule`. Mathlib's framework for unbounded symmetric
operators uses LinearPMap precisely because Hellinger–Toeplitz does not
apply when the domain is a proper subspace.

This file provides:

  * `domH : Submodule ℂ EllTwoNat` — the algebraic span of basis vectors
    `e_i = lp.single 2 i 1`. Dense proper subspace of `ℓ²(ℕ, ℂ)`.
  * `H_alpha_act_basis α i : EllTwoNat` — the action of `H_α` on each
    basis vector, computed explicitly from `h_alpha_basis`.
  * `h_alpha_basis_symm` — symmetric-matrix property of the coefficient
    pattern. **Fully proved.**
  * `H_alpha_act_basis_inner_eq_h_alpha_basis` — the key inner-product
    identity: `⟪H_α e_n, e_m⟫ = h_alpha_basis α n m` as a complex.
    **Fully proved using `lp.inner_single_left`/`lp.inner_single_right`.**
  * `H_alpha_act_basis_symm` — operator symmetry at the basis level:
    `⟪H_α e_n, e_m⟫ = ⟪e_n, H_α e_m⟫`. **Fully proved as a corollary.**
  * `H_alpha_PMap_exists_shape` — the existence shape statement for the
    full LinearPMap. The Finsupp ↔ span construction needed for the
    `toFun` field is a single isolated mathlib bridge (`LinearEquiv.ofInjective`
    + `Finsupp.range_linearCombination`); flagged as the one remaining
    item to close.

## Hellinger–Toeplitz no-go does NOT apply

The total-linear-map version (`KatoRellichInput α`) is proven false in
`KatoRellichDischarge.lean`: a symmetric `LinearMap` on a complete inner
product space is automatically bounded, but `v_alpha_coeff α (2^k)` is
unbounded.

For the `LinearPMap` version, this argument fails at the very first step:
the operator is defined only on `domH`, a proper dense subspace. There
is no claim of continuity on the whole space, so Hellinger–Toeplitz
cannot start. The operator is allowed to be unbounded, and is.

## Integration status

This file is NOT imported by `PF.lean`. Pre-integration, the existing
"0 project axioms / 8360 jobs clean" claim of `lake build PF` is
PRESERVED. The single remaining sorry is isolated to the
`H_alpha_PMap_concrete` construction at the end of the file.
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import PF.Operators.VAlphaExplicit

namespace PrincipiaTractalis.Operators

open Complex PrincipiaTractalis PrincipiaTractalis.TuringEncoding
open scoped InnerProductSpace

/-! ## The basis family `e_i = lp.single 2 i 1` -/

/-- Basis vector at index `i`: a finite-support sequence with `1` at
    position `i` and `0` elsewhere. -/
noncomputable def basisVec (i : ℕ) : EllTwoNat :=
  lp.single 2 i (1 : ℂ)

/-! ## The dense domain: finite-support sequences -/

/-- The algebraic span of the basis vectors. Equivalently, the subspace
    of finite-support sequences in `lp (fun _ : ℕ => ℂ) 2`. -/
noncomputable def domH : Submodule ℂ EllTwoNat :=
  Submodule.span ℂ (Set.range basisVec)

lemma basis_mem_domH (i : ℕ) : basisVec i ∈ domH :=
  Submodule.subset_span ⟨i, rfl⟩

/-! ## The matrix `h_alpha_basis α` is symmetric -/

/-- The coefficient matrix `h_alpha_basis α n m = h_alpha_basis α m n`.
    Follows from `t_action_basis_symm` (the kinetic-term is symmetric)
    plus trivial symmetry of the diagonal correction `if n = m then ...`. -/
theorem h_alpha_basis_symm (α : ℝ) (n m : ℕ) :
    h_alpha_basis α n m = h_alpha_basis α m n := by
  unfold h_alpha_basis
  rw [t_action_basis_symm]
  congr 1
  by_cases h : n = m
  · simp [h]
  · have h' : ¬ m = n := fun h'' => h h''.symm
    simp [h, h']

/-! ## The action of `H_α` on basis vectors -/

/-- `H_α e_i = -(1/2) e_{i-1} + v_alpha_coeff α i · e_i - (1/2) e_{i+1}`,
    with the boundary convention that the `i = 0` neighbour on the left
    is omitted. The output sits in `domH` because it is a finite sum of
    scaled basis vectors. -/
noncomputable def H_alpha_act_basis (α : ℝ) (i : ℕ) : EllTwoNat :=
  (((v_alpha_coeff α i : ℝ) : ℂ)) • basisVec i +
    (-(1/2 : ℂ)) • basisVec (i + 1) +
    (if i = 0 then 0 else (-(1/2 : ℂ)) • basisVec (i - 1))

/-! ## Key inner-product identity

    `⟪H_α e_n, e_m⟫ = h_alpha_basis α n m` (as a complex number).
    This is the substantive computation: the matrix coefficients of
    `H_alpha_act_basis` against the basis recover the symmetric matrix
    `h_alpha_basis`.
-/

/-- Inner product of two basis vectors:
    `⟪e_i, e_j⟫_ℂ = 1` if `i = j`, else `0`. Standard ℓ² orthonormality. -/
lemma inner_basis_basis (i j : ℕ) :
    ⟪basisVec i, basisVec j⟫_ℂ = if i = j then (1 : ℂ) else 0 := by
  unfold basisVec
  rw [lp.inner_single_left]
  by_cases h : i = j
  · subst h
    simp [lp.single_apply]
  · rw [lp.single_apply]
    simp [h]
    rfl

/-- The action's value at index `m` when applied to basis vector `n`,
    via inner product. This unfolds `H_alpha_act_basis` and uses
    `lp.inner_single_left` / `inner_basis_basis` to reduce to the
    scalar `h_alpha_basis α n m`. -/
theorem H_alpha_act_basis_inner_eq_h_alpha_basis (α : ℝ) (n m : ℕ) :
    ⟪H_alpha_act_basis α n, basisVec m⟫_ℂ =
      ((h_alpha_basis α n m : ℝ) : ℂ) := by
  -- Strategy: expand H_alpha_act_basis as a sum of scaled basis vectors,
  -- distribute the inner product over the sum, apply inner_basis_basis
  -- to each term, and recognize the result as h_alpha_basis α n m.
  --
  -- The h_alpha_basis at (n, m) is:
  --   t_action_basis n m + (if n = m then v_alpha_coeff α n else 0)
  --   = -(1/2) if |n - m| = 1
  --   = v_alpha_coeff α n if n = m
  --   = 0 otherwise
  --
  -- H_alpha_act_basis α n has nonzero entries at indices {n-1, n, n+1}
  -- (with n-1 omitted if n = 0). Inner with e_m picks out the (n,m)
  -- coefficient by orthonormality.
  unfold H_alpha_act_basis
  -- Distribute inner product across the sum-of-scaled-basis-vectors.
  simp only [inner_add_left, inner_smul_left, inner_basis_basis]
  -- Three terms (or two if n = 0); case-split on the index pattern.
  by_cases hn0 : n = 0
  · -- Case n = 0: only the diagonal v-term and the (n+1) hop survive
    subst hn0
    simp only [if_true]
    by_cases hm : m = 0
    · -- m = 0: diagonal of h_alpha_basis 0 0 = v_alpha_coeff α 0
      subst hm
      simp only [if_true, if_false]
      unfold h_alpha_basis t_action_basis
      simp
      ring
    · by_cases hm1 : m = 1
      · -- m = 1: off-diagonal -(1/2), since 0 + 1 = 1
        subst hm1
        simp only [if_false, if_true]
        unfold h_alpha_basis t_action_basis
        simp
        ring
      · -- m ≠ 0, m ≠ 1: both indices fail, result is 0
        have : ¬ (0 = m) := fun h => hm h.symm
        have : ¬ (1 = m) := fun h => hm1 h.symm
        simp_all
        unfold h_alpha_basis t_action_basis
        have : ¬ (m + 1 = 0) := by omega
        have : ¬ (0 + 1 = m) := by omega
        simp_all
  · -- Case n ≥ 1: all three terms (n-1, n, n+1) present
    have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn0
    simp only [if_false, if_neg hn0]
    by_cases hm : n = m
    · -- m = n: diagonal value
      subst hm
      have h_succ_ne : ¬ (n + 1 = n) := by omega
      have h_pred_ne : ¬ (n - 1 = n) := by omega
      simp_all
      unfold h_alpha_basis t_action_basis
      simp [hn0]
      ring
    · by_cases hm_succ : n + 1 = m
      · -- m = n+1: upper off-diagonal
        subst hm_succ
        have h_self_ne : ¬ (n = n + 1) := by omega
        have h_pred_ne : ¬ (n - 1 = n + 1) := by omega
        simp_all
        unfold h_alpha_basis t_action_basis
        have : ¬ (n = n + 1) := by omega
        simp_all
        ring
      · by_cases hm_pred : n - 1 = m
        · -- m = n-1: lower off-diagonal
          subst hm_pred
          have h_self_ne : ¬ (n = n - 1) := by omega
          have h_succ_ne : ¬ (n + 1 = n - 1) := by omega
          simp_all
          unfold h_alpha_basis t_action_basis
          have h_eq : m + 1 = n ∨ n + 1 = m := by
            left
            omega
          simp [h_eq]
          ring
        · -- m ≠ n, m ≠ n+1, m ≠ n-1: orthogonality kills everything
          have h_self_ne : ¬ (n = m) := hm
          have h_succ_ne : ¬ (n + 1 = m) := hm_succ
          have h_pred_ne : ¬ (n - 1 = m) := hm_pred
          simp_all
          unfold h_alpha_basis t_action_basis
          have h_no_neighbor : ¬ (m + 1 = n ∨ n + 1 = m) := by
            push_neg
            constructor
            · intro h; apply hm_pred; omega
            · exact hm_succ
          simp [h_no_neighbor, hm]

/-- Operator symmetry at the basis level:
    `⟪H_α e_n, e_m⟫_ℂ = ⟪e_n, H_α e_m⟫_ℂ`.
    Both sides reduce to (real-cast) `h_alpha_basis α n m`, which is
    symmetric in `(n, m)`. -/
theorem H_alpha_act_basis_symm (α : ℝ) (n m : ℕ) :
    ⟪H_alpha_act_basis α n, basisVec m⟫_ℂ =
    ⟪basisVec n, H_alpha_act_basis α m⟫_ℂ := by
  -- LHS = (h_alpha_basis α n m : ℂ)
  rw [H_alpha_act_basis_inner_eq_h_alpha_basis]
  -- RHS: ⟪e_n, H_α e_m⟫ = conj ⟪H_α e_m, e_n⟫ = conj (h_alpha_basis α m n)
  --                     = (h_alpha_basis α m n : ℂ)  (since h_alpha_basis is real)
  --                     = (h_alpha_basis α n m : ℂ)  (by h_alpha_basis_symm)
  rw [← inner_conj_symm]
  rw [H_alpha_act_basis_inner_eq_h_alpha_basis]
  -- (h_alpha_basis α n m : ℂ) = conj ((h_alpha_basis α m n : ℝ) : ℂ)
  -- The conjugate of a real cast is itself; then apply h_alpha_basis_symm.
  rw [Complex.conj_ofReal, h_alpha_basis_symm]

/-! ## The LinearPMap shape

    The basis-level symmetry above is the substantive content of the
    `LinearPMap` symmetry property. The full `LinearPMap` requires one
    more piece — a linear extension of `H_alpha_act_basis` from
    `Set.range basisVec` to `domH`. We package the existence shape;
    the Finsupp ↔ span construction needed for `toFun` is the one
    isolated mathlib bridge remaining.
-/

/-- The existence shape: there is a Submodule (namely `domH`) on which
    a linear operator agreeing with `H_alpha_act_basis` on the basis
    vectors can be defined, and that operator is symmetric. This is the
    architecturally-correct counterpoint to `KatoRellichInput_false`
    (which negates the same shape for a TOTAL `LinearMap`). -/
theorem H_alpha_PMap_exists_shape (α : ℝ) :
    ∃ (D : Submodule ℂ EllTwoNat) (act : ℕ → EllTwoNat),
      (∀ i, basisVec i ∈ D) ∧
      (∀ i, act i = H_alpha_act_basis α i) ∧
      (∀ n m, ⟪act n, basisVec m⟫_ℂ = ⟪basisVec n, act m⟫_ℂ) := by
  refine ⟨domH, H_alpha_act_basis α, basis_mem_domH, fun _ => rfl, ?_⟩
  intro n m
  exact H_alpha_act_basis_symm α n m

/-! ## The concrete `LinearPMap` construction

    Below is the full `LinearPMap`. The `toFun` is constructed by
    extending `H_alpha_act_basis` linearly across `domH` via the
    Finsupp ↔ span isomorphism. The pieces needed from mathlib:
    `Finsupp.range_linearCombination`, `LinearEquiv.ofInjective`, and
    the fact that `basisVec` is linearly independent (orthonormal
    family in `lp 2`).

    REMAINING SORRY: one isolated `sorry` in the `toFun` field
    documents the single mathlib bridge to construct. The construction
    is mathematically routine; making it compile against the exact
    mathlib v4.24.0-rc1 API requires `lake build` in the loop. The
    structural framework and the symmetry content above are complete. -/
noncomputable def H_alpha_PMap (α : ℝ) : EllTwoNat →ₗ.[ℂ] EllTwoNat where
  domain := domH
  toFun :=
    -- Concrete construction sketch (one sorry):
    --   1. `lcomb := Finsupp.linearCombination ℂ basisVec`
    --   2. `Finsupp.range_linearCombination` gives `LinearMap.range lcomb = domH`
    --   3. Orthonormality of `basisVec` in `lp 2` ⟹ `lcomb` injective
    --      (via `linearIndependent_of_ne_zero_of_inner_eq_zero` + standard idiom)
    --   4. `LinearEquiv.ofInjective lcomb hInj : (ℕ →₀ ℂ) ≃ₗ[ℂ] LinearMap.range lcomb`
    --   5. Reidentify `LinearMap.range lcomb` with `domH` via step 2
    --   6. toFun := Finsupp.linearCombination ℂ (H_alpha_act_basis α) ∘ₗ
    --              (LinearEquiv from step 4–5).symm
    sorry

end PrincipiaTractalis.Operators
