/-
# r371: the new factor is a unit, the witness is unconditional, and the
product weight is POSITIVE — steps (1) and (2)

★ 2026-10-28 r371 — r370's last hypothesis discharged, and the weights become
states ★

## What this closes

r370 left one honest input: `productTypeFamily_escapes_scalar_collapse` assumed
`NontrivialDynamics (newFactor 0 (x 0))`. §2 **discharges it**, so the escape
from r369's scalar collapse is now unconditional.

And r370's weights were merely *invertible*. A KMS **state** needs positive
weights (r364), so §3 supplies positivity — which needs one lemma mathlib does
not have.

## §1–§2: the new factor is a unit, and it inherits non-commutation

`newFactor` is multiplicative in its argument and unital, so `newFactor k x` is
a unit whenever `x` is — proved by exhibiting `newFactor k x⁻¹` as the inverse,
with no determinant computed. And `newFactor k` is **injective** (the `1 ⊗ₖ ·`
map reads off its second slot), so a non-commuting pair stays non-commuting
after embedding. Together with r370's explicit `3×3` witness that gives

    nontrivialDynamics_newFactor_witness :
      NontrivialDynamics (newFactor 0 witnessWeight)

and hence `productWeight_nontrivial`, unconditionally.

## §3: a lemma mathlib does not have

> `A`, `B` positive semidefinite ⟹ `A ⊗ₖ B` positive semidefinite.

**Measured absent** at this pin: searching mathlib for `PosSemidef` together
with `kronecker`, in either order, returns nothing. Proved here by exactly
r365's trick — exhibit the thing as `MᴴM`:

    (√A ⊗ₖ √B)ᴴ (√A ⊗ₖ √B) = (√Aᴴ√A) ⊗ₖ (√Bᴴ√B) = A ⊗ₖ B

using `conjTranspose_kronecker`, `mul_kronecker_mul`, and that a positive
semidefinite square root is Hermitian. No spectral theorem, no eigenvalues.
The `PosDef` version follows by `PosSemidef.posDef_iff_isUnit`, with the unit
supplied by `A⁻¹ ⊗ₖ B⁻¹`.

This matters beyond here: `substrateEmbedMatrix` *is* `reindex (· ⊗ₖ 1)`, so
"the substrate embedding preserves positivity" is a corollary, and it was not
available in the corpus before.

## The payoff

r370's `embed_mul_newFactor` already showed `X(k+1) = reindex (X k ⊗ₖ x k)`.
So the product-type weight is a **reindexed kronecker product**, and §3 gives:

* `productWeight_posDef` — if every `x k` is positive definite then every
  `productWeight x k` is positive definite.

With r364 that makes `ω_{X k}` a genuine **state** at every level, and with
r370 the family is non-scalar. So the construction now has both properties
r369 showed `TowerCompatible` could not have at once.

## What is NOT claimed

Not claimed here: the intertwining under `ProductTypeFamily` or the descent to
`T_∞` (that is step (3), the next file); that the limit state is non-tracial;
anything about `Out(T_∞)` or the `C*` completion. Note also that a positive
weight is **not** `exp(-βH)` — r365 supplies that form, and `x k := exp(-β hₖ)`
for Hermitian `hₖ` is how one instantiates §3's hypothesis with a temperature.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.ProductTypeFamily_r370

set_option autoImplicit false

namespace PF.KMS

open Matrix
open scoped Kronecker
-- `Matrix.PosSemidef`/`PosDef` over `ℂ` need the complex order, and a scoped
-- open does not cross an import (the r362 lesson, applied in advance).
open scoped ComplexOrder
open PrincipiaTractalis.SubstrateBase3Embed

/-! ## §1 — `newFactor` is multiplicative, unital, a unit, and injective -/

lemma newFactor_mul (k : ℕ) (x y : Matrix (Fin 3) (Fin 3) ℂ) :
    newFactor k x * newFactor k y = newFactor k (x * y) := by
  unfold newFactor
  rw [show (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) ⊗ₖ (x * y)
      = ((1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) * 1) ⊗ₖ (x * y) by simp,
    Matrix.mul_kronecker_mul]
  simp [Matrix.reindex, Matrix.submatrix_mul_equiv]

@[simp] lemma newFactor_one (k : ℕ) :
    newFactor k (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
  unfold newFactor
  simp [Matrix.one_kronecker_one, Matrix.reindex]

/-- `newFactor k x` is a unit when `x` is — its inverse is `newFactor k x⁻¹`,
so no determinant is computed. -/
lemma newFactor_isUnit_det (k : ℕ) {x : Matrix (Fin 3) (Fin 3) ℂ}
    (hx : IsUnit x.det) : IsUnit (newFactor k x).det := by
  -- matrices are not a `CommMonoid`, so `isUnit_of_mul_eq_one` does not apply;
  -- the matrix-specific right-inverse lemma does.
  refine Matrix.isUnit_det_of_right_inverse (B := newFactor k x⁻¹) ?_
  rw [newFactor_mul, Matrix.mul_nonsing_inv x hx, newFactor_one]

/-- `newFactor k` is injective: the `1 ⊗ₖ ·` map reads its second slot off. -/
lemma newFactor_injective (k : ℕ) {x y : Matrix (Fin 3) (Fin 3) ℂ}
    (h : newFactor k x = newFactor k y) : x = y := by
  unfold newFactor at h
  have h' : (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) ⊗ₖ x
      = (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) ⊗ₖ y := by
    have := congrArg (fun M => Matrix.reindex (levelStepEquiv k).symm
      (levelStepEquiv k).symm M) h
    simpa [Matrix.reindex] using this
  ext i j
  have hij := congrArg (fun M => M (⟨0, by positivity⟩, i) (⟨0, by positivity⟩, j)) h'
  simpa [Matrix.kroneckerMap_apply, Matrix.one_apply_eq] using hij

/-! ## §2 — The witness, unconditionally -/

lemma newFactor_not_commute (k : ℕ) {x y : Matrix (Fin 3) (Fin 3) ℂ}
    (h : x * y ≠ y * x) :
    newFactor k x * newFactor k y ≠ newFactor k y * newFactor k x := by
  intro heq
  rw [newFactor_mul, newFactor_mul] at heq
  exact h (newFactor_injective k heq)

/-- **★★★ r371: r370's remaining hypothesis, discharged ★★★** -/
theorem nontrivialDynamics_newFactor_witness :
    NontrivialDynamics (newFactor 0 witnessWeight) :=
  ⟨newFactor 0 witnessElem,
    modularAut_ne_id_of_not_commute
      (newFactor_isUnit_det 0 witnessWeight_isUnit_det)
      (newFactor_not_commute 0 witnessWeight_not_commute)⟩

/-- **★★★ r371: the product-type family has nontrivial dynamics ★★★**

Unconditional. Compare `towerCompatible_isScalar` (r369), under which the
dynamics was forced to be the identity. -/
theorem productWeight_nontrivial
    (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) (hx0 : x 0 = witnessWeight) :
    NontrivialDynamics (productWeight x 1) := by
  refine productTypeFamily_escapes_scalar_collapse x ?_
  rw [hx0]
  exact nontrivialDynamics_newFactor_witness

/-! ## §3 — Positivity of a kronecker product (absent from mathlib) -/

/-- **★★★ r371: `PosSemidef` is preserved by the kronecker product ★★★**

Proved by exhibiting `A ⊗ₖ B` as `MᴴM`, exactly r365's trick. No spectral
theorem. -/
theorem posSemidef_kronecker {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊗ₖ B).PosSemidef := by
  -- `mul_kronecker_mul` is oriented with the kronecker-of-products on the
  -- left, so the ← direction folds a product of kroneckers into one.
  have key : (hA.sqrt ⊗ₖ hB.sqrt)ᴴ * (hA.sqrt ⊗ₖ hB.sqrt) = A ⊗ₖ B := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hA.posSemidef_sqrt.isHermitian.eq, hB.posSemidef_sqrt.isHermitian.eq,
      hA.sqrt_mul_self, hB.sqrt_mul_self]
  rw [← key]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The `PosDef` version: positive semidefinite plus a unit. -/
theorem posDef_kronecker {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    {B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    (A ⊗ₖ B).PosDef := by
  refine ((posSemidef_kronecker hA.posSemidef hB.posSemidef).posDef_iff_isUnit).mpr ?_
  rw [Matrix.isUnit_iff_isUnit_det]
  refine Matrix.isUnit_det_of_right_inverse (B := A⁻¹ ⊗ₖ B⁻¹) ?_
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv A (posDef_isUnit_det hA),
    Matrix.mul_nonsing_inv B (posDef_isUnit_det hB), Matrix.one_kronecker_one]

/-! ## §4 — The product weight is positive definite -/

/-- Reindexing by an equivalence preserves positive definiteness. Stated for
arbitrary index types, because the tower equivalence `levelStepEquiv` has a
**product** domain `Fin (3^k) × Fin 3`, not a `Fin`. -/
lemma posDef_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (e : ι ≃ κ) {M : Matrix κ κ ℂ} (hM : M.PosDef) :
    (M.submatrix e e).PosDef := by
  -- r364's `posDef_isUnit_det` is typed for `Fin n`; derive it generally here.
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  refine ((Matrix.posSemidef_submatrix_equiv e).mpr hM.posSemidef).posDef_iff_isUnit.mpr ?_
  rw [Matrix.isUnit_iff_isUnit_det]
  refine Matrix.isUnit_det_of_right_inverse (B := M⁻¹.submatrix e e) ?_
  rw [Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv M hdet,
    Matrix.submatrix_one_equiv]

/-- **★★★ r371: the product-type weight is positive definite ★★★**

So by r364 it carries a genuine state at every level, and by r370 the family is
not scalar — the two properties r369 showed `TowerCompatible` cannot combine. -/
theorem productWeight_posDef (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hx : ∀ k, (x k).PosDef) : ∀ k, (productWeight x k).PosDef := by
  intro k
  induction k with
  | zero =>
      show (1 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ).PosDef
      exact Matrix.PosDef.one
  | succ k ih =>
      rw [productWeight, embed_mul_newFactor, Matrix.reindex_apply]
      exact posDef_submatrix (levelStepEquiv k).symm (posDef_kronecker ih (hx k))

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.newFactor_mul
#print axioms PF.KMS.newFactor_isUnit_det
#print axioms PF.KMS.newFactor_injective
#print axioms PF.KMS.nontrivialDynamics_newFactor_witness
#print axioms PF.KMS.productWeight_nontrivial
#print axioms PF.KMS.posSemidef_kronecker
#print axioms PF.KMS.posDef_kronecker
#print axioms PF.KMS.posDef_submatrix
#print axioms PF.KMS.productWeight_posDef
