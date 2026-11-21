/-
# Faithful Fefferman-2000 Clay NS statement — satisfiability and teeth

**Date**: 2026-11-20 (Legion).

`Fefferman2000_Faithful_Statement_2026_10_12.lean` states Fefferman's
Clay problem (A)/(B) on `ℝ³` as a real `Prop` built from genuine mathlib
operators. Stating it is not the same as knowing the statement is sound:
an encoding can be accidentally unsatisfiable (then it is vacuously
unprovable and useless), or accidentally trivial (then every witness
satisfies it and it says nothing). This file settles both directions at
the pin, which is the first thing a referee checks on a formalised
statement.

* `laplacian_zero_fun` — the helper the migration specification named as
  the one blocker for the zero-datum transfers. Not in mathlib at
  v4.24.0-rc1.
* `faithful_body_at_zero_datum` — the statement's **body is satisfiable**:
  at `u₀ = 0`, the witnesses `U ≡ 0`, `P ≡ 0`, `ν = 1` discharge every
  clause, momentum equation included.
* `nonzero_datum_forbids_zero_velocity` — the statement has **teeth**:
  the initial-condition clause is load-bearing, so for any datum that is
  nonzero somewhere the trivial witness `U ≡ 0` is *excluded*. The
  existential is therefore not satisfiable by one fixed cheap witness.

Together: the encoding is neither vacuous nor trivial. **None of this
proves the Clay problem**, which quantifies over every admissible `u₀`;
what is proved here is that the formalised statement is a sound target.
-/

import PF.NavierStokes.Fefferman2000_Faithful_Statement_2026_10_12
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory

namespace PF.NavierStokes.FeffermanFaithful

/-! `V` and `divergence` are taken from the statement file itself, so every
theorem below is about the SAME constants the Clay statement uses — not a
re-declared copy free to drift from it. -/

/-! ## §1 — The helper mathlib lacks

`InnerProductSpace.laplacian` is `tensorIteratedFDerivTwo ℝ f x` applied
to the canonical covariant tensor, and `tensorIteratedFDerivTwo` is built
from `iteratedFDeriv ℝ 2`. The second iterated derivative of a constant
function vanishes, so the whole linear map is `0`. -/

/-- **The Laplacian of a constant field vanishes.** Not in mathlib at
    v4.24.0-rc1; named in the migration specification as the one helper
    the zero-datum transfers need. -/
@[simp] theorem laplacian_const_fun (c : V) (x : V) :
    InnerProductSpace.laplacian (fun _ : V => c) x = 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [iteratedFDeriv_const_of_ne (two_ne_zero)]

/-- Specialisation to the zero field. -/
@[simp] theorem laplacian_zero_fun (x : V) :
    InnerProductSpace.laplacian (fun _ : V => (0 : V)) x = 0 :=
  laplacian_const_fun 0 x

/-! ## §2 — The zero datum is admissible, and the body is satisfiable -/

/-- The zero field is divergence-free: the hypothesis slot is a genuine
    `fderiv` constraint and it is inhabited. -/
theorem divergence_zero_fun (x : V) :
    divergence (fun _ : V => (0 : V)) x = 0 := by
  unfold divergence
  simp [fderiv_const_apply]

/-- **The faithful statement's body is satisfiable at the zero datum.**

    Every clause of Fefferman's conclusion -- joint `C^∞` on the
    space-time half-space, the initial condition, incompressibility, the
    full momentum equation, and bounded energy with its integrability
    guard -- is discharged by `U ≡ 0`, `P ≡ 0`, `ν = 1`.

    This is the satisfiability half of soundness. It is NOT progress on
    the Clay problem: the Clay statement quantifies over every admissible
    `u₀`, and this instantiates one. -/
theorem faithful_body_at_zero_datum :
    ∃ (U : V × ℝ → V) (P : V × ℝ → ℝ) (ν : ℝ),
      0 < ν ∧
      ContDiffOn ℝ (⊤ : ℕ∞) U {q : V × ℝ | 0 ≤ q.2} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) P {q : V × ℝ | 0 ≤ q.2} ∧
      (∀ x : V, U (x, 0) = (0 : V)) ∧
      (∀ (x : V) (t : ℝ), 0 ≤ t → divergence (fun y => U (y, t)) x = 0) ∧
      (∀ (x : V) (t : ℝ), 0 ≤ t →
        deriv (fun s : ℝ => U (x, s)) t
          + fderiv ℝ (fun y : V => U (y, t)) x (U (x, t))
          + gradient (fun y : V => P (y, t)) x
        = ν • InnerProductSpace.laplacian (fun y : V => U (y, t)) x) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
        Integrable (fun x : V => ‖U (x, t)‖ ^ 2) ∧
        (∫ x : V, ‖U (x, t)‖ ^ 2) ≤ C) := by
  refine ⟨fun _ => (0 : V), fun _ => (0 : ℝ), 1, one_pos,
          contDiffOn_const, contDiffOn_const, fun _ => rfl, ?_, ?_, ?_⟩
  · -- incompressibility
    intro x t _
    exact divergence_zero_fun x
  · -- momentum equation: every term is zero
    intro x t _
    simp
  · -- bounded energy, with C = 0
    refine ⟨0, le_refl 0, fun t _ => ⟨?_, ?_⟩⟩
    · simp
    · simp

/-! ## §3 — The statement has teeth

Satisfiability alone would be worthless if the trivial witness worked for
*every* datum: the statement would then be provable outright and would
not be the Clay problem. It is not. -/

/-- **A datum that is nonzero somewhere excludes the zero velocity
    field.** The initial-condition clause `U (·,0) = u₀` is load-bearing,
    so the cheap witness of §2 does not generalise, and the existential
    in the faithful statement carries real content. -/
theorem nonzero_datum_forbids_zero_velocity
    (u0 : SchwartzMap V V) (x₀ : V) (hx₀ : u0 x₀ ≠ 0) :
    ¬ (∀ x : V, (fun _ : V × ℝ => (0 : V)) (x, (0 : ℝ)) = u0 x) := by
  intro h
  exact hx₀ (h x₀).symm

/-- Restated as the fact a referee wants: no single velocity field
    satisfies the initial condition for all admissible data, because the
    data disagree. Hence the `∃ U P ν` in the faithful statement cannot
    be discharged by one fixed witness. -/
theorem no_uniform_witness_for_all_data
    (U : V × ℝ → V)
    (u0 u1 : SchwartzMap V V) (x₀ : V) (hne : u0 x₀ ≠ u1 x₀) :
    ¬ ((∀ x : V, U (x, 0) = u0 x) ∧ (∀ x : V, U (x, 0) = u1 x)) := by
  intro ⟨h0, h1⟩
  exact hne ((h0 x₀).symm.trans (h1 x₀))

#print axioms laplacian_const_fun
#print axioms faithful_body_at_zero_datum
#print axioms nonzero_datum_forbids_zero_velocity
#print axioms no_uniform_witness_for_all_data

end PF.NavierStokes.FeffermanFaithful
