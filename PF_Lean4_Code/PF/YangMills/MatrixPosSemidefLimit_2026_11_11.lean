/-
# PF.YangMills.MatrixPosSemidefLimit_2026_11_11

**Step 4 of the YM L²-extension plan:** `Matrix.PosSemidef` is preserved
under entrywise limits.

Specifically: given a sequence of K×K complex matrices `M_n`, each
`PosSemidef`, and a matrix `M` with entries `M i j = lim_n (M_n n) i j`,
the matrix `M` is itself `PosSemidef`.

This is a generic linear-algebra fact; it is placed under `PF/YangMills`
for the moment because its only intended caller is the YM-lane L²
extension. A future refactor could promote it to a `Mathlib.PR.`-style
generic file.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.LeftRightNhds

namespace PF.YangMills

open scoped ComplexOrder Topology
open Filter Matrix

/-- **`Matrix.PosSemidef` is preserved under entrywise limits (sequential).**
For a sequence `M_n` of `K×K` complex matrices, each `PosSemidef`, if
`M_n i j → M i j` for every `(i, j)`, then `M` is `PosSemidef`. -/
theorem Matrix.PosSemidef.of_tendsto_entries {K : ℕ}
    {M : Matrix (Fin K) (Fin K) ℂ}
    {M_n : ℕ → Matrix (Fin K) (Fin K) ℂ}
    (hPSD : ∀ n, (M_n n).PosSemidef)
    (h_limit : ∀ i j, Tendsto (fun n => (M_n n) i j) atTop (𝓝 (M i j))) :
    M.PosSemidef := by
  refine ⟨?_, ?_⟩
  · -- Hermiticity: star (M j i) = M i j, pointwise.
    ext i j
    have h_herm : ∀ n, star ((M_n n) j i) = (M_n n) i j := by
      intro n
      have := (hPSD n).1  -- IsHermitian
      have := congrFun (congrFun this i) j
      simpa [Matrix.conjTranspose_apply] using this
    have hs : Tendsto (fun n => star ((M_n n) j i)) atTop (𝓝 (star (M j i))) :=
      (continuous_star.tendsto _).comp (h_limit j i)
    have h_eq : (fun n => star ((M_n n) j i)) = (fun n => (M_n n) i j) :=
      funext h_herm
    rw [h_eq] at hs
    exact tendsto_nhds_unique hs (h_limit i j) |>.symm |> Eq.symm
  · -- Quadratic form: 0 ≤ star v ⬝ᵥ M.mulVec v.
    intro v
    -- Each `star v ⬝ᵥ (M_n n).mulVec v` is a sum of pointwise products of
    -- entries that converge.  Expand the dotProduct and mulVec explicitly.
    have h_expand : ∀ (A : Matrix (Fin K) (Fin K) ℂ),
        star v ⬝ᵥ A.mulVec v
          = ∑ i : Fin K, ∑ j : Fin K, star (v i) * A i j * v j := by
      intro A
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    have h_tend_entry : ∀ i j : Fin K,
        Tendsto (fun n => star (v i) * (M_n n) i j * v j) atTop
          (𝓝 (star (v i) * M i j * v j)) := by
      intro i j
      exact ((h_limit i j).const_mul (star (v i))).mul_const (v j)
    have h_tend : Tendsto (fun n =>
          ∑ i : Fin K, ∑ j : Fin K, star (v i) * (M_n n) i j * v j) atTop
            (𝓝 (∑ i : Fin K, ∑ j : Fin K, star (v i) * M i j * v j)) := by
      refine tendsto_finset_sum _ (fun i _ => ?_)
      refine tendsto_finset_sum _ (fun j _ => ?_)
      exact h_tend_entry i j
    -- Each prefactored value is ≥ 0.
    have h_nonneg : ∀ n,
        0 ≤ (∑ i : Fin K, ∑ j : Fin K, star (v i) * (M_n n) i j * v j) := by
      intro n
      rw [← h_expand]
      exact (hPSD n).2 v
    rw [h_expand]
    exact ge_of_tendsto' h_tend h_nonneg

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.Matrix.PosSemidef.of_tendsto_entries
