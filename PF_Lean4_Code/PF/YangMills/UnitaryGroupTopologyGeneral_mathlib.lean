/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The unitary and special unitary matrix groups are compact topological groups

`Matrix.unitaryGroup n 𝕜` and `Matrix.specialUnitaryGroup n ℂ` carry the
subspace topology from `Matrix n n ℂ`, but mathlib provides no topological
companion to the group structure. This file supplies it for any finite index
type: both groups are topological groups, and both are compact.

## Main results

* `Matrix.unitaryGroup_isClosed`, `Matrix.specialUnitaryGroup_isClosed` — each
  group is a closed subset of `Matrix n n ℂ`, being cut out by the polynomial
  equations `A * star A = 1` and (for the special group) `det A = 1`.
* `Matrix.norm_le_one_of_mem_unitaryGroup` — every entry of a unitary matrix
  has norm at most one.
* `Matrix.frobenius_norm_le_card_of_mem_unitaryGroup` — the Frobenius norm of a
  unitary matrix is at most `Fintype.card n`. (The exact value is
  `Real.sqrt (Fintype.card n)`; this weaker bound is what boundedness needs.)
* `Matrix.instCompactSpaceUnitaryGroup`,
  `Matrix.instCompactSpaceSpecialUnitaryGroup` — compactness, via Heine–Borel
  on the finite-dimensional normed space `Matrix n n ℂ`.
* `Matrix.instIsTopologicalGroupUnitaryGroup`,
  `Matrix.instIsTopologicalGroupSpecialUnitaryGroup`.

## Implementation notes

Inversion on these groups is `star`, which is continuous on `Matrix n n ℂ`, so
`ContinuousInv` transfers through `continuous_induced_rng` exactly as it does
for `unitary` in `Mathlib/Topology/Algebra/Star/Unitary.lean`.

Boundedness is proved in the Frobenius norm, activated locally, because
`Matrix n n ℂ` has no global norm instance. Compactness of the underlying set is
a statement about the subspace topology and so does not depend on which of the
equivalent norms is used.

## Tags

unitary group, special unitary group, compact group, topological group
-/

namespace PFMathlibCandidate

-- instance order matches mathlib's `unitaryGroup`: DecidableEq before Fintype
variable {n : Type*} [DecidableEq n] [Fintype n]

/-! ## Topological group structure -/

instance instContinuousMulUnitaryGroup :
    ContinuousMul (Matrix.unitaryGroup n ℂ) := by infer_instance

instance instContinuousMulSpecialUnitaryGroup :
    ContinuousMul (Matrix.specialUnitaryGroup n ℂ) := by infer_instance

instance instContinuousInvUnitaryGroup :
    ContinuousInv (Matrix.unitaryGroup n ℂ) where
  continuous_inv := by
    show Continuous (fun A : Matrix.unitaryGroup n ℂ => A⁻¹)
    exact continuous_induced_rng.mpr continuous_subtype_val.star

instance instContinuousInvSpecialUnitaryGroup :
    ContinuousInv (Matrix.specialUnitaryGroup n ℂ) where
  continuous_inv := by
    show Continuous (fun A : Matrix.specialUnitaryGroup n ℂ => A⁻¹)
    exact continuous_induced_rng.mpr continuous_subtype_val.star

instance instIsTopologicalGroupUnitaryGroup :
    IsTopologicalGroup (Matrix.unitaryGroup n ℂ) where

instance instIsTopologicalGroupSpecialUnitaryGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup n ℂ) where

/-! ## Closedness -/

/-- `unitaryGroup n ℂ` is the preimage of `{1}` under the continuous map
`A ↦ A * star A`, hence closed. -/
theorem unitaryGroup_isClosed :
    IsClosed { A : Matrix n n ℂ | A ∈ Matrix.unitaryGroup n ℂ } := by
  have hcont : Continuous fun A : Matrix n n ℂ => A * star A :=
    continuous_id.mul continuous_star
  have hpre : { A : Matrix n n ℂ | A ∈ Matrix.unitaryGroup n ℂ }
      = (fun A : Matrix n n ℂ => A * star A) ⁻¹' {1} := by
    ext A
    simp [Matrix.mem_unitaryGroup_iff]
  rw [hpre]
  exact isClosed_singleton.preimage hcont

/-- `{A | A.det = 1}` is closed: the determinant is a continuous polynomial in
the entries. -/
theorem det_eq_one_isClosed :
    IsClosed { A : Matrix n n ℂ | A.det = 1 } := by
  have hcont : Continuous fun A : Matrix n n ℂ => A.det := continuous_id.matrix_det
  have hpre : { A : Matrix n n ℂ | A.det = 1 }
      = (fun A : Matrix n n ℂ => A.det) ⁻¹' {1} := by
    ext A; simp
  rw [hpre]
  exact isClosed_singleton.preimage hcont

/-- `specialUnitaryGroup n ℂ` is closed, being the intersection of the unitary
condition with `det = 1`. -/
theorem specialUnitaryGroup_isClosed :
    IsClosed { A : Matrix n n ℂ | A ∈ Matrix.specialUnitaryGroup n ℂ } := by
  have hinter : { A : Matrix n n ℂ | A ∈ Matrix.specialUnitaryGroup n ℂ }
      = { A : Matrix n n ℂ | A ∈ Matrix.unitaryGroup n ℂ } ∩ { A | A.det = 1 } := by
    ext A
    simp [Matrix.mem_specialUnitaryGroup_iff]
  rw [hinter]
  exact unitaryGroup_isClosed.inter det_eq_one_isClosed

/-! ## Boundedness and compactness -/

section Compact

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup
    Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- Every entry of a unitary matrix has norm at most one: the `i`-th diagonal
entry of `A * star A` is `∑ k, ‖A i k‖ ^ 2 = 1`, a sum of nonnegative terms. -/
theorem norm_le_one_of_mem_unitaryGroup {A : Matrix n n ℂ}
    (hA : A ∈ Matrix.unitaryGroup n ℂ) (i j : n) : ‖A i j‖ ≤ 1 := by
  rw [Matrix.mem_unitaryGroup_iff] at hA
  have h_diag : (A * star A) i i = 1 := by rw [hA]; simp
  have h_sum_C : ∑ k, A i k * star (A i k) = 1 := by
    rw [← h_diag]
    simp [Matrix.mul_apply, Matrix.star_apply]
  have h_sum_sq_C : (∑ k, (‖A i k‖ : ℂ) ^ 2) = 1 := by
    rw [← h_sum_C]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (RCLike.mul_conj (A i k)).symm
  have h_sum_sq_real : (∑ k, ‖A i k‖ ^ 2 : ℝ) = 1 := by exact_mod_cast h_sum_sq_C
  have h_split : ∑ k, ‖A i k‖ ^ 2
      = ‖A i j‖ ^ 2 + ∑ k ∈ Finset.univ.erase j, ‖A i k‖ ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_comm]
  have h_erase_nn : 0 ≤ ∑ k ∈ Finset.univ.erase j, ‖A i k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have h_sq_le : ‖A i j‖ ^ 2 ≤ 1 := by linarith
  nlinarith [h_sq_le, norm_nonneg (A i j)]

/-- The Frobenius norm of a unitary matrix is at most `Fintype.card n`. The
exact value is `Real.sqrt (Fintype.card n)`; this bound suffices for
boundedness and avoids a square root. -/
theorem frobenius_norm_le_card_of_mem_unitaryGroup {A : Matrix n n ℂ}
    (hA : A ∈ Matrix.unitaryGroup n ℂ) : ‖A‖ ≤ (Fintype.card n : ℝ) := by
  rw [Matrix.frobenius_norm_def]
  have h_sq_bound : ∀ i j : n, ‖A i j‖ ^ (2 : ℝ) ≤ 1 := by
    intro i j
    have hcast : ‖A i j‖ ^ (2 : ℝ) = ‖A i j‖ ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rw [hcast]
    nlinarith [norm_le_one_of_mem_unitaryGroup hA i j, norm_nonneg (A i j)]
  have h_sum_bound : (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ))
      ≤ (Fintype.card n : ℝ) * (Fintype.card n : ℝ) := by
    calc (∑ i : n, ∑ j : n, ‖A i j‖ ^ (2 : ℝ))
        ≤ ∑ _i : n, ∑ _j : n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_sq_bound i j
      _ = (Fintype.card n : ℝ) * (Fintype.card n : ℝ) := by
          simp [Finset.card_univ]
  have h_sum_nn : 0 ≤ ∑ i : n, ∑ j : n, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) 2
  have h_rpow_le : (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ((Fintype.card n : ℝ) * (Fintype.card n : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow h_sum_nn h_sum_bound (by norm_num)
  have h_c : ((Fintype.card n : ℝ) * (Fintype.card n : ℝ)) ^ (1 / 2 : ℝ)
      = (Fintype.card n : ℝ) := by
    rw [← sq, ← Real.rpow_natCast ((Fintype.card n : ℝ)) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  linarith [h_rpow_le, h_c]

theorem unitaryGroup_isBounded :
    Bornology.IsBounded { A : Matrix n n ℂ | A ∈ Matrix.unitaryGroup n ℂ } := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨(Fintype.card n : ℝ), fun A hA => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact frobenius_norm_le_card_of_mem_unitaryGroup hA

theorem specialUnitaryGroup_isBounded :
    Bornology.IsBounded { A : Matrix n n ℂ | A ∈ Matrix.specialUnitaryGroup n ℂ } := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨(Fintype.card n : ℝ), fun A hA => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact frobenius_norm_le_card_of_mem_unitaryGroup
    (Matrix.specialUnitaryGroup_le_unitaryGroup hA)

theorem unitaryGroup_isCompact :
    IsCompact { A : Matrix n n ℂ | A ∈ Matrix.unitaryGroup n ℂ } := by
  haveI : ProperSpace (Matrix n n ℂ) := FiniteDimensional.proper ℂ _
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨unitaryGroup_isClosed, unitaryGroup_isBounded⟩

theorem specialUnitaryGroup_isCompact :
    IsCompact { A : Matrix n n ℂ | A ∈ Matrix.specialUnitaryGroup n ℂ } := by
  haveI : ProperSpace (Matrix n n ℂ) := FiniteDimensional.proper ℂ _
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨specialUnitaryGroup_isClosed, specialUnitaryGroup_isBounded⟩

instance instCompactSpaceUnitaryGroup : CompactSpace (Matrix.unitaryGroup n ℂ) :=
  isCompact_iff_compactSpace.mp unitaryGroup_isCompact

instance instCompactSpaceSpecialUnitaryGroup :
    CompactSpace (Matrix.specialUnitaryGroup n ℂ) :=
  isCompact_iff_compactSpace.mp specialUnitaryGroup_isCompact

end Compact

end PFMathlibCandidate
