/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Data.Real.Basic

/-!
# Linear independence from a nonvanishing Gram determinant

For a symmetric biadditive form `B : G → G → ℝ` on an abelian group `G`, a
family `P : Fin n → G` whose Gram matrix `(B (P i) (P j))` has nonzero
determinant is `ℤ`-linearly independent, and consequently
`n ≤ Module.rank ℤ G`.

The proof is short: a relation `∑ vᵢ • Pᵢ = 0` pairs against each `P j` to put
`v` in the kernel of the Gram matrix, and a square matrix over a field with a
nonzero kernel vector has vanishing determinant
(`Matrix.exists_mulVec_eq_zero_iff`).

This is the standard criterion behind regulator arguments for Mordell–Weil
groups of elliptic curves, where `B` is the Néron–Tate height pairing, but
nothing here refers to elliptic curves or to heights.

## Main results

* `AddBilin.linearIndependent_of_gramDet_ne_zero`
* `AddBilin.rank_ge_of_gramDet_ne_zero`
-/

namespace AddBilin

variable {G : Type*} [AddCommGroup G]

/-- A real-valued form on an abelian group, additive in the first argument and
symmetric.  Additivity in the second argument follows. -/
structure IsAddBilin (B : G → G → ℝ) : Prop where
  add_left : ∀ x y z : G, B (x + y) z = B x z + B y z
  symm : ∀ x y : G, B x y = B y x

variable {B : G → G → ℝ}

theorem IsAddBilin.zero_left (hB : IsAddBilin B) (y : G) : B 0 y = 0 := by
  have h := hB.add_left 0 0 y
  simp only [add_zero] at h
  linarith [h]

/-- Pairing against a fixed element, as an additive homomorphism. -/
def IsAddBilin.toAddMonoidHom (hB : IsAddBilin B) (y : G) : G →+ ℝ where
  toFun x := B x y
  map_zero' := hB.zero_left y
  map_add' x x' := hB.add_left x x' y

theorem IsAddBilin.zsmul_left (hB : IsAddBilin B) (x y : G) (k : ℤ) :
    B (k • x) y = (k : ℝ) * B x y := by
  have h := (hB.toAddMonoidHom y).map_zsmul x k
  simp only [toAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rw [h, zsmul_eq_mul]

theorem IsAddBilin.sum_left (hB : IsAddBilin B) {n : ℕ} (v : Fin n → ℤ)
    (P : Fin n → G) (y : G) :
    B (∑ i, v i • P i) y = ∑ i, (v i : ℝ) * B (P i) y := by
  have h := map_sum (hB.toAddMonoidHom y) (fun i => v i • P i) Finset.univ
  simp only [toAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => hB.zsmul_left (P i) y (v i)

variable {n : ℕ}

/-- The Gram matrix of `B` at a finite family of points. -/
def gramMatrix (B : G → G → ℝ) (P : Fin n → G) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => B (P i) (P j)

theorem gramMatrix_mulVec_eq_zero (hB : IsAddBilin B) (P : Fin n → G)
    {v : Fin n → ℤ} (hrel : ∑ i, v i • P i = 0) :
    (gramMatrix B P).mulVec (fun i => (v i : ℝ)) = 0 := by
  funext j
  have h : B (∑ i, v i • P i) (P j) = 0 := by rw [hrel, hB.zero_left]
  rw [hB.sum_left v P (P j)] at h
  simp only [Matrix.mulVec, dotProduct, gramMatrix, Matrix.of_apply,
    Pi.zero_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by rw [hB.symm (P i) (P j)]; ring

/-- A nonvanishing Gram determinant forces every `ℤ`-relation to be trivial. -/
theorem eq_zero_of_gramDet_ne_zero (hB : IsAddBilin B) (P : Fin n → G)
    (hdet : (gramMatrix B P).det ≠ 0) {v : Fin n → ℤ}
    (hrel : ∑ i, v i • P i = 0) : v = 0 := by
  by_contra hv
  apply hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun i => (v i : ℝ), ?_, gramMatrix_mulVec_eq_zero hB P hrel⟩
  intro h0
  apply hv
  funext i
  have hi : ((v i : ℝ)) = 0 := congrFun h0 i
  exact_mod_cast hi

/-- `v ↦ ∑ vᵢ • Pᵢ`, as a `ℤ`-linear map. -/
def sumSmulMap (P : Fin n → G) : (Fin n → ℤ) →ₗ[ℤ] G where
  toFun v := ∑ i, v i • P i
  map_add' u v := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
      mul_smul]

theorem linearIndependent_of_gramDet_ne_zero (hB : IsAddBilin B) (P : Fin n → G)
    (hdet : (gramMatrix B P).det ≠ 0) :
    Function.Injective (sumSmulMap P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  exact eq_zero_of_gramDet_ne_zero hB P hdet hv

/-- **A nonvanishing Gram determinant bounds the rank from below.** -/
theorem rank_ge_of_gramDet_ne_zero {G : Type} [AddCommGroup G]
    {B : G → G → ℝ} {n : ℕ} (hB : IsAddBilin B) (P : Fin n → G)
    (hdet : (gramMatrix B P).det ≠ 0) :
    (n : Cardinal) ≤ Module.rank ℤ G := by
  have hrank := LinearMap.lift_rank_le_of_injective (sumSmulMap P)
    (linearIndependent_of_gramDet_ne_zero hB P hdet)
  rw [rank_fin_fun n] at hrank
  exact Cardinal.lift_le.mp hrank

end AddBilin
