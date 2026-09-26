/-
# Layer-5 no-uniqueness: trace does not determine a symmetric matrix

## Purpose

Formalizes the *purely mathematical* no-uniqueness fact identified in
§3.2 of `codex/CHURN_TO_STRESS_TENSOR_BRIDGE_AUDIT_2026-09-14.md`: for
`n ≥ 2`, the trace map on symmetric `n × n` real matrices is not
injective. Explicit witnesses `A ≠ B` with the same trace `χ` exhibit
the underdetermination.

Corollary: no function `f : ℝ → Matrix (Fin n) (Fin n) ℝ` can be a
right-inverse of `Matrix.trace` on the symmetric-matrix subspace. In
particular no scalar-in / symmetric-tensor-out "bridge" from a
churn-scalar to a spacetime stress tensor `C^{μν}` can pin `C` from
its trace alone.

## What this file explicitly does NOT do

- Does NOT propose any physical bridge from `χ_k` to `C^{μν}`.
- Does NOT claim any spacetime, manifold, metric, or connection is
  constructed.
- Does NOT reference EEG, consciousness, or Layer 2 / Layer 3 content.
- Does NOT interpret the trace as an energy density or the shift
  matrix as anisotropic stress.

The theorem is a purely algebraic non-injectivity claim about
`Matrix.trace` restricted to symmetric matrices, in the spirit of
finite-dimensional linear algebra — used *only* to document the
audit's §2.8 assertion in Lean kernel.

## Corpus reference

- Audit document: `codex/CHURN_TO_STRESS_TENSOR_BRIDGE_AUDIT_2026-09-14.md`,
  §3.2 (formalization decision), §2.8 (scalar-cannot-pin-tensor).
- No dependency on `FrobeniusChurn.lean`, `TimelessField.lean`, or any
  physics-adjacent PF module. This module is stand-alone.

Zero project axioms; all principal declarations audit to
`[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis.Consciousness.ChurnStressTensorNoUniqueness

open scoped BigOperators
open Matrix Finset

/-! ## §1 — Isotropic (trace-carrying) witness

`isotropicWitness n χ = (χ / n) • 1` — the scalar multiple of the
identity by `χ / n`. Diagonal with `χ/n` on the diagonal, zero off. -/

/-- **Isotropic witness matrix.** Diagonal matrix with `χ / n` on
    every entry of the main diagonal, zero off-diagonal.
    Symmetric; trace equals `χ` when `n > 0`. -/
noncomputable def isotropicWitness (n : ℕ) (χ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (χ / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)

lemma isotropicWitness_isSymm (n : ℕ) (χ : ℝ) :
    (isotropicWitness n χ).IsSymm := by
  unfold isotropicWitness
  show ((χ / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ))ᵀ
      = (χ / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)
  rw [Matrix.transpose_smul, Matrix.transpose_one]

lemma isotropicWitness_trace {n : ℕ} (hn : 0 < n) (χ : ℝ) :
    Matrix.trace (isotropicWitness n χ) = χ := by
  unfold isotropicWitness
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  show (χ / (n : ℝ)) • ((n : ℝ)) = χ
  rw [smul_eq_mul]
  field_simp

/-! ## §2 — Off-diagonal traceless symmetric shift

`offDiagonalShift n` is the symmetric matrix with a `1` at positions
`(0, 1)` and `(1, 0)`, and `0` elsewhere. Constructed via `Matrix.of`
so that both positions carry the shared value from a symmetric
predicate on the index pair. Trace is `0` because the diagonal is
identically zero. Nonzero as soon as `n ≥ 2`. -/

/-- **Off-diagonal shift matrix.** A specific symmetric matrix with
    `1` at `(0, 1)` and `(1, 0)` and `0` elsewhere. Trace 0
    (diagonal is all zeros). Nonzero for `n ≥ 2`.
    Serves as the "traceless residual" of the audit §2.8
    decomposition. -/
noncomputable def offDiagonalShift (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j : Fin n =>
    if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0)
    then (1 : ℝ)
    else (0 : ℝ))

lemma offDiagonalShift_isSymm (n : ℕ) :
    (offDiagonalShift n).IsSymm := by
  unfold offDiagonalShift
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  by_cases h1 : i.val = 0 ∧ j.val = 1
  · rw [if_pos (Or.inl h1), if_pos (Or.inr ⟨h1.2, h1.1⟩)]
  · by_cases h2 : i.val = 1 ∧ j.val = 0
    · rw [if_pos (Or.inr h2), if_pos (Or.inl ⟨h2.2, h2.1⟩)]
    · have h3 : ¬ ((i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0)) := by
        rintro (h | h)
        · exact h1 h
        · exact h2 h
      have h4 : ¬ ((j.val = 0 ∧ i.val = 1) ∨ (j.val = 1 ∧ i.val = 0)) := by
        rintro (h | h)
        · exact h2 ⟨h.2, h.1⟩
        · exact h1 ⟨h.2, h.1⟩
      rw [if_neg h3, if_neg h4]

lemma offDiagonalShift_trace (n : ℕ) :
    Matrix.trace (offDiagonalShift n) = 0 := by
  unfold offDiagonalShift Matrix.trace Matrix.diag
  simp only [Matrix.of_apply]
  apply Finset.sum_eq_zero
  intros i _
  have h : ¬ ((i.val = 0 ∧ i.val = 1) ∨ (i.val = 1 ∧ i.val = 0)) := by
    rintro (⟨h0, h1⟩ | ⟨h1, h0⟩) <;> omega
  rw [if_neg h]

lemma offDiagonalShift_apply_zero_one {n : ℕ} (hn : 2 ≤ n) :
    offDiagonalShift n (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 1 := by
  unfold offDiagonalShift
  simp [Matrix.of_apply]

lemma offDiagonalShift_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    offDiagonalShift n ≠ (0 : Matrix (Fin n) (Fin n) ℝ) := by
  intro heq
  have h1 : offDiagonalShift n (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = 1 :=
    offDiagonalShift_apply_zero_one hn
  have h0 : (0 : Matrix (Fin n) (Fin n) ℝ) (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
              = (0 : ℝ) := rfl
  rw [heq, h0] at h1
  linarith

/-! ## §3 — Combined witnesses: `A` isotropic, `B = A + shift`

Both are symmetric with trace `χ`; they differ by the nonzero
`offDiagonalShift`. -/

/-- **Second witness matrix.** Isotropic `(χ/n) • 1` plus the
    off-diagonal shift. Trace equals `χ` (isotropic contributes `χ`,
    shift contributes `0`). Symmetric (both summands are). Distinct
    from `isotropicWitness n χ` for `n ≥ 2`. -/
noncomputable def shiftedWitness (n : ℕ) (χ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  isotropicWitness n χ + offDiagonalShift n

lemma shiftedWitness_isSymm (n : ℕ) (χ : ℝ) :
    (shiftedWitness n χ).IsSymm := by
  unfold shiftedWitness
  show (isotropicWitness n χ + offDiagonalShift n)ᵀ
      = isotropicWitness n χ + offDiagonalShift n
  rw [Matrix.transpose_add, isotropicWitness_isSymm n χ,
      offDiagonalShift_isSymm n]

lemma shiftedWitness_trace {n : ℕ} (hn : 0 < n) (χ : ℝ) :
    Matrix.trace (shiftedWitness n χ) = χ := by
  unfold shiftedWitness
  rw [Matrix.trace_add, isotropicWitness_trace hn, offDiagonalShift_trace,
      add_zero]

lemma isotropic_ne_shifted {n : ℕ} (hn : 2 ≤ n) (χ : ℝ) :
    isotropicWitness n χ ≠ shiftedWitness n χ := by
  intro heq
  -- heq : isotropicWitness n χ = isotropicWitness n χ + offDiagonalShift n
  -- Subtracting the isotropic from both sides gives offDiagonalShift n = 0,
  -- contradicting offDiagonalShift_ne_zero.
  have hshift_zero : offDiagonalShift n = 0 := by
    have h := heq
    have : offDiagonalShift n = shiftedWitness n χ - isotropicWitness n χ := by
      unfold shiftedWitness; abel
    rw [this, ← h, sub_self]
  exact offDiagonalShift_ne_zero hn hshift_zero

/-! ## §4 — Main theorem: trace does not determine a symmetric matrix -/

/-- **Main theorem (Layer-5 no-uniqueness).** For every `n ≥ 2` and
    every `χ : ℝ`, there exist two distinct symmetric `n × n` real
    matrices `A ≠ B` with `Matrix.trace A = Matrix.trace B = χ`.

    This documents the audit's §2.8 assertion in Lean kernel: the
    trace map on symmetric matrices has fibers of positive dimension
    for `n ≥ 2`, so no scalar `χ` alone can pin a symmetric rank-2
    tensor. -/
theorem trace_underdetermines_symmetric_matrix {n : ℕ} (hn : 2 ≤ n)
    (χ : ℝ) :
    ∃ (A B : Matrix (Fin n) (Fin n) ℝ),
      A.IsSymm ∧ B.IsSymm ∧
      Matrix.trace A = χ ∧ Matrix.trace B = χ ∧
      A ≠ B := by
  have hn_pos : 0 < n := by omega
  refine ⟨isotropicWitness n χ, shiftedWitness n χ, ?_, ?_, ?_, ?_, ?_⟩
  · exact isotropicWitness_isSymm n χ
  · exact shiftedWitness_isSymm n χ
  · exact isotropicWitness_trace hn_pos χ
  · exact shiftedWitness_trace hn_pos χ
  · exact isotropic_ne_shifted hn χ

/-! ## §5 — Corollary: no scalar-in bridge pins a symmetric matrix

For any candidate map `f : ℝ → Matrix (Fin n) (Fin n) ℝ` that would
try to reconstruct a symmetric matrix from its trace alone, there is
a symmetric matrix `M` that `f (trace M)` fails to reproduce. -/

/-- **Corollary (no scalar bridge).** For every `n ≥ 2` and every
    function `f : ℝ → Matrix (Fin n) (Fin n) ℝ`, there exists a
    symmetric matrix `M` with `M ≠ f (Matrix.trace M)`.

    Consequence for the audit: no map `f` sending a scalar (e.g. the
    Frobenius churn `χ_k`) to a symmetric rank-2 tensor (e.g. the
    consciousness stress tensor `C^{μν}` at a point) can be a
    right-inverse of the trace on the symmetric-matrix subspace.
    Whatever `f` is, at least one symmetric matrix with a given
    trace is *not* produced by `f` on that trace. -/
theorem no_scalar_bridge_pins_symmetric_matrix {n : ℕ} (hn : 2 ≤ n)
    (f : ℝ → Matrix (Fin n) (Fin n) ℝ) :
    ∃ (M : Matrix (Fin n) (Fin n) ℝ),
      M.IsSymm ∧ M ≠ f (Matrix.trace M) := by
  -- Consider the two symmetric matrices A, B with trace 0 from the
  -- main theorem at χ = 0. Since A ≠ B, at most one equals f 0.
  obtain ⟨A, B, hAsym, hBsym, hAtr, hBtr, hAB⟩ :=
    trace_underdetermines_symmetric_matrix hn (0 : ℝ)
  by_cases hAf : A = f (0 : ℝ)
  · -- A = f 0. Then B ≠ A = f 0 = f (trace B).
    refine ⟨B, hBsym, ?_⟩
    rw [hBtr, ← hAf]
    exact fun h => hAB h.symm
  · -- A ≠ f 0 = f (trace A).
    refine ⟨A, hAsym, ?_⟩
    rw [hAtr]
    exact hAf

/-! ## §6 — In-file axiom audit -/

section AxiomAudit

#print axioms isotropicWitness
#print axioms isotropicWitness_isSymm
#print axioms isotropicWitness_trace
#print axioms offDiagonalShift
#print axioms offDiagonalShift_isSymm
#print axioms offDiagonalShift_trace
#print axioms offDiagonalShift_apply_zero_one
#print axioms offDiagonalShift_ne_zero
#print axioms shiftedWitness
#print axioms shiftedWitness_isSymm
#print axioms shiftedWitness_trace
#print axioms isotropic_ne_shifted
#print axioms trace_underdetermines_symmetric_matrix
#print axioms no_scalar_bridge_pins_symmetric_matrix

end AxiomAudit

end PrincipiaTractalis.Consciousness.ChurnStressTensorNoUniqueness
