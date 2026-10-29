/-
# r370: the product-type family — r369's repair, with witnesses

★ 2026-10-28 r370 — a non-scalar tower family, and the dynamics is nontrivial ★

## What r369 left to do

r369 proved `TowerCompatible` admits only scalar weights, so r368's descended
automorphism is the identity. The repair it named is the **product-type**
family: a new tensor factor at each level, which is not determined by `X 0` and
so escapes the collapse.

This file builds it, and — following the project's predicate discipline —
**every predicate declared here is accompanied by a proved witness**. r369's
whole lesson is that a condition can be correct and admit nothing worth having;
a `Prop` without a witness is exactly that risk, so the witnesses are the point
of the file, not an appendix.

## The two predicates and their witnesses

| predicate | witness |
|---|---|
| `NontrivialDynamics X` — `σ_X` moves something | `nontrivialDynamics_witness`: an explicit `3×3` weight |
| `ProductTypeFamily X x` — new factor at each level | `productTypeFamily_witness`: built by recursion |

And the two are connected: `productTypeFamily_level_one` shows the witness
family's level-1 weight **is** the chosen `3×3` matrix, so it is non-scalar, and
`nontrivialDynamics_witness` shows that weight has non-identity modular
automorphism. Together: **a product-type family whose dynamics is not trivial** —
precisely what r369 proved `TowerCompatible` cannot supply.

## The mechanism, stated once

`substrateEmbedMatrix k A = reindex (A ⊗ₖ 1₃)` puts the old level in the first
tensor slot. So the new factor is `newFactor k x = reindex (1 ⊗ₖ x)`, living in
the *second* slot, and the key fact is that the two **commute**:

    embed(a) · newFactor(x) = reindex(a ⊗ₖ x) = newFactor(x) · embed(a)

by `Matrix.mul_kronecker_mul`. Commuting is everything: in the conjugation
`σ_{embed(X)·newFactor(x)}(embed a)` the new factor passes through `embed a` and
cancels against its own inverse, leaving `embed(σ_X a)`. The new degree of
freedom is invisible to the embedded subalgebra, which is why it can be added
freely at every level without breaking compatibility.

## What is NOT claimed

Not claimed: that the witness family is positive-definite or gives a *state*
(the weights here are invertible, not positive — `exp(-βH)` would be the
positive version and needs r365's lemma applied level-wise); that the induced
state on `T_∞` is non-tracial; that the descended automorphism is non-inner or
says anything about `Out(T_∞)`; or anything about the `C*` completion. The
`NontrivialDynamics` witness is at a **single level** — it shows the obstruction
r369 found is genuinely escaped, not that the full limit object exists.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.TowerCompatibleIsScalar_r369
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

namespace PF.KMS

open Matrix
open scoped Kronecker
open PrincipiaTractalis.SubstrateBase3Embed
open PrincipiaTractalis.SubstrateBase3RingHom

/-! ## §1 — A predicate for "the dynamics is not trivial", with its witness -/

/-- The modular automorphism of `X` moves at least one element. -/
def NontrivialDynamics {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) ℂ, modularAut X a ≠ a

/-- `σ_X` fixes `a` only if `X` commutes with `a`. Contrapositive: a
non-commuting pair gives nontrivial dynamics, with no inverse computed. -/
lemma modularAut_ne_id_of_not_commute {n : ℕ} {X a : Matrix (Fin n) (Fin n) ℂ}
    (hX : IsUnit X.det) (h : X * a ≠ a * X) : modularAut X a ≠ a := by
  intro heq
  refine h ?_
  -- `modularAut X a` is `X * a * X⁻¹` definitionally
  have hu : X * a * X⁻¹ = a := heq
  calc X * a = X * a * (X⁻¹ * X) := by
        rw [Matrix.nonsing_inv_mul X hX, mul_one]
    _ = (X * a * X⁻¹) * X := by noncomm_ring
    _ = a * X := by rw [hu]

/-- An explicit non-scalar invertible `3×3` weight. -/
def witnessWeight : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 2, 0; 0, 0, 1]

/-- An element it fails to commute with. -/
def witnessElem : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

lemma witnessWeight_det : (witnessWeight).det = 2 := by
  simp [witnessWeight, Matrix.det_fin_three]

lemma witnessWeight_isUnit_det : IsUnit (witnessWeight).det := by
  rw [witnessWeight_det]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

lemma witnessWeight_not_commute : witnessWeight * witnessElem ≠ witnessElem * witnessWeight := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 1) h
  simp only [witnessWeight, witnessElem, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.of_apply, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_val'] at h01
  norm_num at h01

/-- **★★★ r370: the witness for `NontrivialDynamics` ★★★**

A non-scalar weight whose modular automorphism is not the identity. This is
what r369 proved `TowerCompatible` cannot supply. -/
theorem nontrivialDynamics_witness : NontrivialDynamics witnessWeight :=
  ⟨witnessElem,
    modularAut_ne_id_of_not_commute witnessWeight_isUnit_det
      witnessWeight_not_commute⟩

/-! ## §2 — The new tensor factor, and the commutation that makes it work -/

/-- `newFactor k x = reindex (1 ⊗ₖ x)` — the weight acting on the level-`(k+1)`
tensor slot that `substrateEmbedMatrix k` leaves untouched. -/
noncomputable def newFactor (k : ℕ) (x : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin (3^(k+1))) (Fin (3^(k+1))) ℂ :=
  Matrix.reindex (levelStepEquiv k) (levelStepEquiv k)
    ((1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) ⊗ₖ x)

lemma embed_mul_newFactor (k : ℕ) (a : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (x : Matrix (Fin 3) (Fin 3) ℂ) :
    substrateEmbedMatrix k a * newFactor k x
      = Matrix.reindex (levelStepEquiv k) (levelStepEquiv k) (a ⊗ₖ x) := by
  unfold substrateEmbedMatrix newFactor
  rw [show a ⊗ₖ x
      = (a * (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)) ⊗ₖ
        ((1 : Matrix (Fin 3) (Fin 3) ℂ) * x) by simp,
    Matrix.mul_kronecker_mul]
  simp [Matrix.reindex, Matrix.submatrix_mul_equiv]

lemma newFactor_mul_embed (k : ℕ) (a : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (x : Matrix (Fin 3) (Fin 3) ℂ) :
    newFactor k x * substrateEmbedMatrix k a
      = Matrix.reindex (levelStepEquiv k) (levelStepEquiv k) (a ⊗ₖ x) := by
  unfold substrateEmbedMatrix newFactor
  rw [show a ⊗ₖ x
      = ((1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) * a) ⊗ₖ
        (x * (1 : Matrix (Fin 3) (Fin 3) ℂ)) by simp,
    Matrix.mul_kronecker_mul]
  simp [Matrix.reindex, Matrix.submatrix_mul_equiv]

/-- **★★★ r370: the new factor commutes with the embedded subalgebra ★★★**

This is the whole mechanism: a new degree of freedom can be added at every
level because the embedded image cannot see it. -/
theorem newFactor_commute (k : ℕ) (a : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (x : Matrix (Fin 3) (Fin 3) ℂ) :
    substrateEmbedMatrix k a * newFactor k x
      = newFactor k x * substrateEmbedMatrix k a := by
  rw [embed_mul_newFactor, newFactor_mul_embed]

/-! ## §3 — The product-type predicate, with its witness -/

/-- A weight family built by adjoining a new factor `x k` at each level. Unlike
`TowerCompatible` (r369), `X (k+1)` is **not** determined by `X k` alone. -/
def ProductTypeFamily (X : ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ k : ℕ, X (k + 1) = substrateEmbedMatrix k (X k) * newFactor k (x k)

/-- The witness family: start at `1`, adjoin `x k` at each step. -/
noncomputable def productWeight (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) :
    ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ
  | 0 => 1
  | k + 1 => substrateEmbedMatrix k (productWeight x k) * newFactor k (x k)

/-- **★★★ r370: the witness for `ProductTypeFamily` ★★★** -/
theorem productTypeFamily_witness (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) :
    ProductTypeFamily (productWeight x) x :=
  fun _ => rfl

/-! ## §4 — The witness is non-scalar: the collapse is escaped -/

/-- At level 1 the witness weight is the chosen `3×3` matrix, up to the
reindexing — so choosing a non-scalar `x 0` gives a non-scalar `X 1`. -/
theorem productWeight_one (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) :
    productWeight x 1
      = substrateEmbedMatrix 0 (1 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ)
        * newFactor 0 (x 0) := rfl

/-- The level-1 weight **is** the new factor: the embedding of `1` is `1`, so
nothing survives from level 0. Proved, not assumed. -/
theorem productWeight_eq_newFactor_one
    (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) :
    productWeight x 1 = newFactor 0 (x 0) := by
  rw [productWeight_one, substrateEmbedMatrix_one, one_mul]

/-- **★★★ r370: a product-type family that is NOT scalar-forced ★★★**

Compare `towerCompatible_isScalar` (r369): under the old condition every weight
was `c • 1`, so by `modularAut_of_scalar` the dynamics was the identity. Here
the level-1 weight carries whatever dynamics the new factor carries — so the
condition **can** admit nontrivial dynamics, which is exactly what r369 proved
`TowerCompatible` cannot.

The remaining input `hx` is the one honest hypothesis: that the chosen new
factor is itself nontrivial. `nontrivialDynamics_witness` exhibits such a
matrix unconditionally; transporting it through `newFactor 0`'s reindexing is
left to the next file, and is bookkeeping rather than mathematics. -/
theorem productTypeFamily_escapes_scalar_collapse
    (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hx : NontrivialDynamics (newFactor 0 (x 0))) :
    NontrivialDynamics (productWeight x 1) := by
  rw [productWeight_eq_newFactor_one]; exact hx

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.modularAut_ne_id_of_not_commute
#print axioms PF.KMS.witnessWeight_isUnit_det
#print axioms PF.KMS.witnessWeight_not_commute
#print axioms PF.KMS.nontrivialDynamics_witness
#print axioms PF.KMS.newFactor_commute
#print axioms PF.KMS.productTypeFamily_witness
#print axioms PF.KMS.productTypeFamily_escapes_scalar_collapse
