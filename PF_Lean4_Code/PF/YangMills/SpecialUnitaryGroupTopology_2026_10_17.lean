/-
# Yang-Mills — Topological-group + CompactSpace for `specialUnitaryGroup (Fin 2) ℂ`

**Rio's YM scoping, 2026-10-17** (codex `f85c078b`): the single blocker
between the pin and the first genuine Yang-Mills theorem (Wilson measure
reflection positivity) is that mathlib's
`Matrix.specialUnitaryGroup (Fin 2) ℂ` lacks the `CompactSpace` and
topological-group instances. The group structure is defined
(`UnitaryGroup.lean:231`), but there is no topology-side companion.

### What this file provides

* `IsTopologicalGroup (specialUnitaryGroup (Fin 2) ℂ)` — matrix
  multiplication and `star`-inversion are continuous on the ambient
  `Matrix (Fin 2) (Fin 2) ℂ`, and the Submonoid inherits the subspace
  topology.
* `CompactSpace (specialUnitaryGroup (Fin 2) ℂ)` — via Heine-Borel on
  the finite-dimensional ℂ-normed space `Matrix (Fin 2) (Fin 2) ℂ`:
  SU(2) is closed (polynomial equations `A·A* = 1` and `det A = 1`)
  and bounded (unitarity ⇒ Frobenius norm `≤ √n`).

Three-axiom bar: every declaration kernel-clean
`[propext, Classical.choice, Quot.sound]`. No sorry.

### Deferred to a follow-up

* Haar measure on `specialUnitaryGroup (Fin 2) ℂ` — follows from
  compact + topological group (mathlib has `MeasureTheory.Measure.haar`
  for compact topological groups).
* Wilson measure on a finite lattice (`Measure.pi` + Haar + Wilson
  action).
* Reflection positivity of the Wilson measure (consumes the existing
  rank-K Gram-PSD algebra; this is the first genuine YM theorem).

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

namespace PF.YangMills

open Matrix

noncomputable section

/-! ## §1 — Topological structure on `Matrix (Fin 2) (Fin 2) ℂ`.

The default `TopologicalSpace (Matrix n m α)` instance is the pi topology
through `Pi.instTopologicalSpace` applied twice. For `α = ℂ`, this makes
matrix multiplication and `star` continuous (polynomial / linear
operations on the entries). -/

example : TopologicalSpace (Matrix (Fin 2) (Fin 2) ℂ) := inferInstance

example : ContinuousStar (Matrix (Fin 2) (Fin 2) ℂ) := inferInstance

/-! ## §2 — The subspace topology on `specialUnitaryGroup`.

`specialUnitaryGroup n α : Submonoid (Matrix n n α)` has the Subtype
topology via `Submonoid`'s coercion to `Subtype`. This gives
`TopologicalSpace` for free. -/

example : TopologicalSpace (specialUnitaryGroup (Fin 2) ℂ) := inferInstance

/-! ## §3 — Continuous multiplication inherited from Matrix. -/

example : ContinuousMul (Matrix (Fin 2) (Fin 2) ℂ) := inferInstance

/-- Multiplication is continuous on `specialUnitaryGroup (Fin 2) ℂ` (inherited
from the ambient `Matrix (Fin 2) (Fin 2) ℂ` via `Submonoid.topologicalClosure`
style inheritance). -/
instance specialUnitaryGroup_continuousMul :
    ContinuousMul (specialUnitaryGroup (Fin 2) ℂ) := by infer_instance

/-! ## §4 — Continuous `star`-inversion.

`specialUnitaryGroup`'s `inv` is defined as `star` (via
`UnitaryGroup.lean:226`). Since `star` is continuous on
`Matrix (Fin 2) (Fin 2) ℂ`, the restriction to the Submonoid is also
continuous. -/

/-- `star`-inversion is continuous on `specialUnitaryGroup (Fin 2) ℂ`. -/
instance specialUnitaryGroup_continuousInv :
    ContinuousInv (specialUnitaryGroup (Fin 2) ℂ) where
  continuous_inv := by
    show Continuous (fun A : specialUnitaryGroup (Fin 2) ℂ => A⁻¹)
    -- A⁻¹ = star A (from `inv := star` in `UnitaryGroup.lean:226`).
    -- `star` on `Submonoid` is `continuous_induced_rng.mpr continuous_subtype_val.star`
    -- analogous to `unitary` in `Topology.Algebra.Star.Unitary.lean:22`.
    exact continuous_induced_rng.mpr continuous_subtype_val.star

/-! ## §5 — Topological-group instance on `specialUnitaryGroup (Fin 2) ℂ`. -/

/-- **★ `specialUnitaryGroup (Fin 2) ℂ` is a topological group ★**:
continuous multiplication and continuous inversion. The first instance
mathlib does not provide for this specific group at the pin. -/
instance specialUnitaryGroup_isTopologicalGroup :
    IsTopologicalGroup (specialUnitaryGroup (Fin 2) ℂ) where

/-! ## §6 — Closedness of `specialUnitaryGroup` as a subset of `Matrix (Fin 2) (Fin 2) ℂ`.

The ambient `Set` is defined by `A * star A = 1` (unitarity) and
`det A = 1` (special), each of which is a continuous polynomial
equation in the matrix entries. The preimage of the singleton `{1}`
under each continuous map is closed; their intersection is closed. -/

/-- `A ∈ unitaryGroup n α ↔ A * star A = 1` (mathlib `mem_unitaryGroup_iff`).
Reformulating this as a preimage: `unitaryGroup n α = φ⁻¹({1})` where
`φ A = A * star A`. Since `φ` is continuous and `{1}` is closed in
Hausdorff `Matrix n n ℂ`, `unitaryGroup` is a closed set. -/
lemma unitaryGroup_isClosed_set :
    IsClosed { A : Matrix (Fin 2) (Fin 2) ℂ | A ∈ Matrix.unitaryGroup (Fin 2) ℂ } := by
  have hcont : Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => A * star A :=
    continuous_id.mul continuous_star
  have hclosed_one : IsClosed ({(1 : Matrix (Fin 2) (Fin 2) ℂ)} : Set _) :=
    isClosed_singleton
  have hpre : { A : Matrix (Fin 2) (Fin 2) ℂ | A ∈ Matrix.unitaryGroup (Fin 2) ℂ }
      = (fun A => A * star A) ⁻¹' {1} := by
    ext A
    simp [Matrix.mem_unitaryGroup_iff]
  rw [hpre]
  exact hclosed_one.preimage hcont

/-- `{A | A.det = 1}` is closed in `Matrix (Fin 2) (Fin 2) ℂ`: the determinant
is a continuous polynomial in the matrix entries, and `{1}` is closed. -/
lemma det_eq_one_isClosed :
    IsClosed { A : Matrix (Fin 2) (Fin 2) ℂ | A.det = 1 } := by
  have hcont : Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det :=
    continuous_id.matrix_det
  have hclosed_one : IsClosed ({(1 : ℂ)} : Set _) := isClosed_singleton
  have hpre : { A : Matrix (Fin 2) (Fin 2) ℂ | A.det = 1 }
      = (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det) ⁻¹' {1} := by
    ext A; simp
  rw [hpre]
  exact hclosed_one.preimage hcont

/-- **`specialUnitaryGroup (Fin 2) ℂ` is a closed subset of `Matrix (Fin 2) (Fin 2) ℂ`.**
Defined as `unitaryGroup ⊓ MonoidHom.mker detMonoidHom`, so an intersection of two
closed sets. -/
lemma specialUnitaryGroup_isClosed_set :
    IsClosed { A : Matrix (Fin 2) (Fin 2) ℂ
                | A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ } := by
  have hinter : { A : Matrix (Fin 2) (Fin 2) ℂ
                   | A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ }
      = { A | A ∈ Matrix.unitaryGroup (Fin 2) ℂ } ∩ { A | A.det = 1 } := by
    ext A
    simp [Matrix.mem_specialUnitaryGroup_iff]
  rw [hinter]
  exact unitaryGroup_isClosed_set.inter det_eq_one_isClosed

/-! ## §7 — Boundedness via the Frobenius norm, and the compactness instance.

Activates `frobeniusNormedAddCommGroup` + `frobeniusNormedSpace` as local
instances so `Matrix (Fin 2) (Fin 2) ℂ` acquires a NormedAddCommGroup
structure. For unitary `A ∈ Matrix (Fin 2) (Fin 2) ℂ`: `A·A* = 1` ⇒
`(A·A*)ᵢᵢ = Σₖ|Aᵢₖ|² = 1`, so each entry `|Aᵢⱼ| ≤ 1`, hence
`‖A‖_F² = Σᵢⱼ|Aᵢⱼ|² ≤ 4`, so `‖A‖_F ≤ 2`. -/

section Compact

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup
    Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- Each entry of a unitary matrix has absolute value at most 1. Follows from
`(A·star A)ᵢᵢ = Σₖ|Aᵢₖ|² = 1`: the sum of non-negative squared norms equals 1,
so each term is at most 1. -/
lemma unitary_entry_norm_le_one {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (i j : Fin 2) : ‖A i j‖ ≤ 1 := by
  rw [Matrix.mem_unitaryGroup_iff] at hA
  have h_diag : (A * star A) i i = 1 := by rw [hA]; simp
  have h_sum_C : ∑ k, A i k * star (A i k) = 1 := by
    rw [← h_diag]
    simp [Matrix.mul_apply, Matrix.star_apply]
  have h_sum_sq_C : (∑ k, (‖A i k‖ : ℂ)^2) = 1 := by
    rw [← h_sum_C]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (RCLike.mul_conj (A i k)).symm
  have h_sum_sq_real : (∑ k, ‖A i k‖^2 : ℝ) = 1 := by exact_mod_cast h_sum_sq_C
  have h_pos : ∀ k, 0 ≤ ‖A i k‖^2 := fun k => sq_nonneg _
  have h_split : ∑ k, ‖A i k‖^2 = ‖A i j‖^2 + ∑ k ∈ Finset.univ.erase j, ‖A i k‖^2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_comm]
  have h_erase_nn : 0 ≤ ∑ k ∈ Finset.univ.erase j, ‖A i k‖^2 :=
    Finset.sum_nonneg fun k _ => h_pos k
  have h_sq_le : ‖A i j‖^2 ≤ 1 := by linarith
  have h_abs_nn : 0 ≤ ‖A i j‖ := norm_nonneg _
  nlinarith [h_sq_le, h_abs_nn]

/-- **Frobenius-norm bound on unitary matrices**: for `A ∈ unitaryGroup (Fin 2) ℂ`,
`‖A‖_F ≤ 2`. (True bound is `‖A‖_F = √n = √2`; the loose `≤ 2` is enough for
boundedness.) -/
lemma unitary_frobenius_norm_le_two {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) : ‖A‖ ≤ 2 := by
  rw [Matrix.frobenius_norm_def]
  have h_entry : ∀ i j : Fin 2, ‖A i j‖ ≤ 1 := unitary_entry_norm_le_one hA
  have h_sq_bound : ∀ i j : Fin 2, ‖A i j‖ ^ (2 : ℝ) ≤ 1 := by
    intro i j
    have h : ‖A i j‖ ^ (2 : ℝ) = ‖A i j‖ ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rw [h]
    have := h_entry i j
    nlinarith [norm_nonneg (A i j)]
  have h_sum_bound : (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ≤ 4 := by
    calc (∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖ ^ (2 : ℝ))
        ≤ ∑ i : Fin 2, ∑ _j : Fin 2, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_sq_bound i j
      _ = 4 := by simp; ring
  have h_sum_nn : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) 2
  have h_rpow_le : (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow h_sum_nn h_sum_bound (by norm_num)
  have h_four : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2^2 from by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  linarith [h_rpow_le, h_four]

/-- **Boundedness of `specialUnitaryGroup (Fin 2) ℂ`** as a subset of
`Matrix (Fin 2) (Fin 2) ℂ` under the Frobenius norm. -/
lemma specialUnitaryGroup_isBounded_set :
    Bornology.IsBounded { A : Matrix (Fin 2) (Fin 2) ℂ
                          | A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ } := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨2, ?_⟩
  intro A hA
  rw [Metric.mem_closedBall, dist_zero_right]
  exact unitary_frobenius_norm_le_two
    (Matrix.specialUnitaryGroup_le_unitaryGroup hA)

/-- **Compactness of `specialUnitaryGroup (Fin 2) ℂ`** as a subset. Heine-Borel
on the finite-dimensional ℂ-normed space `Matrix (Fin 2) (Fin 2) ℂ`. -/
lemma specialUnitaryGroup_isCompact_set :
    IsCompact { A : Matrix (Fin 2) (Fin 2) ℂ
                | A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ } := by
  haveI : ProperSpace (Matrix (Fin 2) (Fin 2) ℂ) := FiniteDimensional.proper ℂ _
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨specialUnitaryGroup_isClosed_set, specialUnitaryGroup_isBounded_set⟩

/-- **★ `specialUnitaryGroup (Fin 2) ℂ` is a compact topological group ★** —
the final instance that unlocks Haar measure on SU(2) at the pin. -/
instance specialUnitaryGroup_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  have h : IsCompact ((Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ))) :=
    specialUnitaryGroup_isCompact_set
  exact isCompact_iff_compactSpace.mp h

end Compact

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.specialUnitaryGroup_continuousMul
#print axioms PF.YangMills.specialUnitaryGroup_continuousInv
#print axioms PF.YangMills.specialUnitaryGroup_isTopologicalGroup
#print axioms PF.YangMills.unitaryGroup_isClosed_set
#print axioms PF.YangMills.det_eq_one_isClosed
#print axioms PF.YangMills.specialUnitaryGroup_isClosed_set
#print axioms PF.YangMills.unitary_entry_norm_le_one
#print axioms PF.YangMills.unitary_frobenius_norm_le_two
#print axioms PF.YangMills.specialUnitaryGroup_isBounded_set
#print axioms PF.YangMills.specialUnitaryGroup_isCompact_set
#print axioms PF.YangMills.specialUnitaryGroup_compactSpace
