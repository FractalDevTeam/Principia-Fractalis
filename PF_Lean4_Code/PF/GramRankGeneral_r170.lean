/-
# PF.GramRankGeneral_r170

★★★ 2026-07-31 — NONZERO GRAM DETERMINANT ⟹ rank ≥ n, IN GENERAL ★★★

r152 proved the 2×2 case for 389a1 and r168 the 3×3 case for 5077a1, each tied
to its curve.  Neither needed to be.  The statement is pure linear algebra over
an arbitrary abelian group:

> Let `G` be an abelian group and `B : G → G → ℝ` symmetric and additive in its
> first slot.  If `P : Fin n → G` has nonzero Gram determinant
> `det (B (P i) (P j)) ≠ 0`, then `n ≤ Module.rank ℤ G`.

Stated for `G : Type`, which is where elliptic-curve point groups live
(`WeierstrassCurve.Affine.Point` over `ℚ`).  The universe-polymorphic version is
identical apart from a `Cardinal.lift` on the right-hand side.

No elliptic curve, no height, no analysis.  The proof is three lines of content:
a relation `∑ vᵢ • Pᵢ = 0` pairs against each `Pⱼ` to give `Gram *ᵥ v = 0`, and a
matrix over a field with a nonzero kernel vector has zero determinant.

## Why this is the right abstraction

It subsumes r152 and r168, and it makes rank ≥ 4, 5, … a matter of *supplying
points* rather than redoing the argument.  Everything curve-specific in the
5077a1 arc lives in establishing that `ĥ` is a quadratic form (r156–r167); once
that is done, this file is all that stands between a Gram determinant and a rank
bound, for any curve and any `n`.

The bi-additivity hypothesis is exactly what r167 supplies via Jordan–von
Neumann, and `symm` is immediate from the definition of the height pairing.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Matrix.Basic

namespace PrincipiaTractalis.GramRankGeneral

variable {G : Type} [AddCommGroup G]

/-- A real-valued form on an abelian group, additive in the first slot and
symmetric.  (Additivity in the second slot then follows.) -/
structure BiAdditive (B : G → G → ℝ) : Prop where
  add_left : ∀ x y z : G, B (x + y) z = B x z + B y z
  symm : ∀ x y : G, B x y = B y x

namespace BiAdditive

variable {B : G → G → ℝ} (hB : BiAdditive B)

include hB

theorem zero_left (y : G) : B 0 y = 0 := by
  have h := hB.add_left 0 0 y
  simp only [add_zero] at h
  linarith [h]

/-- Pairing against a fixed `y`, as an additive homomorphism. -/
def hom (y : G) : G →+ ℝ where
  toFun x := B x y
  map_zero' := hB.zero_left y
  map_add' x x' := hB.add_left x x' y

theorem zsmul_left (x y : G) (k : ℤ) : B (k • x) y = (k : ℝ) * B x y := by
  have h := (hB.hom y).map_zsmul x k
  simp only [hom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rw [h, zsmul_eq_mul]

theorem sum_left {n : ℕ} (v : Fin n → ℤ) (P : Fin n → G) (y : G) :
    B (∑ i, v i • P i) y = ∑ i, (v i : ℝ) * B (P i) y := by
  have h := map_sum (hB.hom y) (fun i => v i • P i) Finset.univ
  simp only [hom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => hB.zsmul_left (P i) y (v i)

end BiAdditive

/-! ## The theorem -/

variable {B : G → G → ℝ} {n : ℕ}

/-- The Gram matrix of `B` at the points `P`. -/
def gram (B : G → G → ℝ) (P : Fin n → G) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => B (P i) (P j)

/-- A relation among the `Pᵢ` puts its coefficient vector in the kernel of the
Gram matrix. -/
theorem gram_mulVec_eq_zero (hB : BiAdditive B) (P : Fin n → G) {v : Fin n → ℤ}
    (hrel : ∑ i, v i • P i = 0) :
    (gram B P).mulVec (fun i => (v i : ℝ)) = 0 := by
  funext j
  have h : B (∑ i, v i • P i) (P j) = 0 := by rw [hrel, hB.zero_left]
  rw [hB.sum_left v P (P j)] at h
  simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply, Pi.zero_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by rw [hB.symm (P i) (P j)]; ring

/-- **A nonzero Gram determinant forces independence.** -/
theorem eq_zero_of_gram_det_ne_zero (hB : BiAdditive B) (P : Fin n → G)
    (hdet : (gram B P).det ≠ 0) {v : Fin n → ℤ}
    (hrel : ∑ i, v i • P i = 0) : v = 0 := by
  by_contra hv
  apply hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun i => (v i : ℝ), ?_, gram_mulVec_eq_zero hB P hrel⟩
  intro h0
  apply hv
  funext i
  have : ((v i : ℝ)) = 0 := congrFun h0 i
  exact_mod_cast this

/-- `(m : Fin n → ℤ) ↦ ∑ mᵢ • Pᵢ`, as a `ℤ`-linear map. -/
def sumMap (P : Fin n → G) : (Fin n → ℤ) →ₗ[ℤ] G where
  toFun v := ∑ i, v i • P i
  map_add' u v := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
      mul_smul]

/-- **★★★ r170 — NONZERO GRAM DETERMINANT ⟹ rank ≥ n ★★★**

Curve-independent, `n`-independent.  Subsumes r152 (n = 2, 389a1) and r168
(n = 3, 5077a1). -/
theorem rank_ge_of_gram_det_ne_zero (hB : BiAdditive B) (P : Fin n → G)
    (hdet : (gram B P).det ≠ 0) :
    (n : Cardinal) ≤ Module.rank ℤ G := by
  have hinj : Function.Injective (sumMap P) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact eq_zero_of_gram_det_ne_zero hB P hdet hv
  have hrank := LinearMap.lift_rank_le_of_injective (sumMap P) hinj
  have hn : Module.rank ℤ (Fin n → ℤ) = n := rank_fin_fun n
  rw [hn] at hrank
  exact Cardinal.lift_le.mp hrank

end PrincipiaTractalis.GramRankGeneral

#print axioms PrincipiaTractalis.GramRankGeneral.BiAdditive.sum_left
#print axioms PrincipiaTractalis.GramRankGeneral.gram_mulVec_eq_zero
#print axioms PrincipiaTractalis.GramRankGeneral.eq_zero_of_gram_det_ne_zero
#print axioms PrincipiaTractalis.GramRankGeneral.rank_ge_of_gram_det_ne_zero
