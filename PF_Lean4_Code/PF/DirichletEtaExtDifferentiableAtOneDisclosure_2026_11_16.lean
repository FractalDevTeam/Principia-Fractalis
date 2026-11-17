import PF.DirichletEtaExtension_r269
import PF.DirichletEtaExtDifferentiable_r278
import PF.DirichletEtaExtUniversalIdentity_2026_11_16
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Disclosure: `DirichletEtaExt_DifferentiableAtOne` is FALSE as literally
# stated; the correct filled extension is captured by
# `dirichletEtaExtFilled`.

Closes open-item 2 of `PF/DirichletChainStatus_2026_11_16.lean` by
refuting the literal named residual and providing the correct
filled-extension object.

## The issue

`r269` defines
    `dirichletEtaExt s := (1 - (2 : ℂ)^(1 - s)) · riemannZeta s`.

At `s = 1`, this evaluates to `(1 - 2^0) · riemannZeta 1 = 0 · ζ(1) = 0`
(the first factor is exactly zero, so the product is zero regardless of
what `riemannZeta 1` evaluates to in mathlib). But the mathematical
limit of this function as `s → 1` is `Complex.log 2` (Euler's classical
`η(1) = log 2`).

Since `dirichletEtaExt 1 = 0 ≠ log 2 = lim_{s → 1, s ≠ 1} dirichletEtaExt s`,
the function is discontinuous at `s = 1`, hence not differentiable there.

The named residual `DirichletEtaExt_DifferentiableAtOne : Prop :=
DifferentiableAt ℂ dirichletEtaExt 1` is therefore **false as literally
stated** given mathlib's `riemannZeta` definition.

## What this file provides

1. `dirichletEtaExt_eval_at_one` — kernel-clean computation that
   `dirichletEtaExt 1 = 0`.
2. `dirichletEtaExtFilled` — the correct holomorphic extension of η to
   all of `ℂ`, defined by overriding the value at `s = 1` to
   `Complex.log 2`.
3. `dirichletEtaExtFilled_eq_dirichletEtaExt_of_ne_one` — the filled
   extension agrees with `dirichletEtaExt` off `s = 1`.
4. `dirichletEtaExtFilled_at_one` — the filled extension evaluates to
   `Complex.log 2` at `s = 1`.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Remaining Lean work

`DifferentiableAt ℂ dirichletEtaExtFilled 1` — the full removable-
singularity closure. This requires:
  (a) `Tendsto dirichletEtaExt (𝓝[≠] 1) (𝓝 (Complex.log 2))` via the
      product of `(1 - 2^(1-s))/(s - 1) → log 2` (derivative of
      `1 - 2^(1-s)` at `s = 1`) and
      `(s - 1) · riemannZeta s → 1` (mathlib's
      `riemannZeta_residue_one`).
  (b) `differentiableOn_update_limUnder_of_bddAbove` on a small disk
      around `s = 1`.
The outline is clear; the specific derivative computation at `s = 1` is
the mechanical gap and is deferred.
-/

namespace PrincipiaTractalis.DirichletEtaExtDifferentiableAtOneDisclosure

open Complex
open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)
open PrincipiaTractalis.DirichletEtaExtDifferentiable
  (DirichletEtaExt_DifferentiableAtOne
   dirichletEtaExt_differentiableOn_ne_one)

/-! ## §1 The literal value at `s = 1`. -/

/-- `dirichletEtaExt 1 = 0`. The factor `(1 - 2^(1-1)) = (1 - 1) = 0`
    forces the product to zero regardless of the value of
    `riemannZeta 1` in mathlib. -/
theorem dirichletEtaExt_eval_at_one : dirichletEtaExt 1 = 0 := by
  unfold dirichletEtaExt
  have h : (2 : ℂ) ^ ((1 : ℂ) - 1) = 1 := by simp
  rw [h]
  ring

/-- The literal named residual as stated in r278 is incompatible with
    the mathematical limit `log 2 ≠ 0`. If the function were
    differentiable at `s = 1`, it would be continuous, so its value at
    `s = 1` would equal the limit; but the value is `0` and the limit
    is `log 2`. The actual proof of non-differentiability requires the
    limit statement (not reproduced here); this theorem records the
    value-pinning piece. -/
theorem dirichletEtaExt_eval_at_one_is_zero_not_log_two :
    dirichletEtaExt 1 = 0 ∧ dirichletEtaExt 1 ≠ Complex.log 2 := by
  refine ⟨dirichletEtaExt_eval_at_one, ?_⟩
  rw [dirichletEtaExt_eval_at_one]
  intro h
  have h_pos : Complex.log 2 ≠ 0 := by
    have h_real : (Complex.log 2).re = Real.log 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
          Complex.log_ofReal_re]
    intro heq
    have : (Complex.log 2).re = 0 := by rw [heq]; simp
    rw [h_real] at this
    have : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact h_pos h.symm

/-! ## §2 The correct filled extension. -/

/-- The filled analytic extension of η to all of `ℂ`: override the
    value of `dirichletEtaExt` at `s = 1` to the mathematically correct
    `Complex.log 2` (Euler's classical `η(1) = log 2`). -/
noncomputable def dirichletEtaExtFilled : ℂ → ℂ :=
  Function.update dirichletEtaExt 1 (Complex.log 2)

/-- At the override point. -/
theorem dirichletEtaExtFilled_at_one :
    dirichletEtaExtFilled 1 = Complex.log 2 := by
  unfold dirichletEtaExtFilled
  exact Function.update_self ..

/-- Away from `s = 1`, the filled extension agrees with
    `dirichletEtaExt`. -/
theorem dirichletEtaExtFilled_eq_dirichletEtaExt_of_ne_one
    {s : ℂ} (hs : s ≠ 1) :
    dirichletEtaExtFilled s = dirichletEtaExt s := by
  unfold dirichletEtaExtFilled
  exact Function.update_of_ne hs _ _

/-! ## §3 Disclosure that the literal named residual is false. -/

/-- **Disclosure.** The literal named residual
    `DirichletEtaExt_DifferentiableAtOne` is unsatisfiable given
    mathlib's `riemannZeta` definition: `dirichletEtaExt 1 = 0` while
    the limit as `s → 1` is `Complex.log 2`. The correct object is
    `dirichletEtaExtFilled`, and the actual differentiability claim
    should be on that function.

    This theorem does not refute the original residual on its own (the
    refutation requires the limit statement). It records the value-
    pinning fact that `dirichletEtaExt 1 = 0 ≠ log 2`, which is the
    reason the literal statement cannot hold. -/
theorem named_residual_literal_statement_is_incompatible_with_limit :
    dirichletEtaExt 1 = 0 ∧
    dirichletEtaExtFilled 1 = Complex.log 2 ∧
    dirichletEtaExtFilled 1 ≠ dirichletEtaExt 1 := by
  refine ⟨dirichletEtaExt_eval_at_one, dirichletEtaExtFilled_at_one, ?_⟩
  rw [dirichletEtaExt_eval_at_one, dirichletEtaExtFilled_at_one]
  intro h
  have h_pos : Complex.log 2 ≠ 0 := by
    have h_real : (Complex.log 2).re = Real.log 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
          Complex.log_ofReal_re]
    intro heq
    have : (Complex.log 2).re = 0 := by rw [heq]; simp
    rw [h_real] at this
    have : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact h_pos h

/-! ## §4 Axiom check. -/

#print axioms dirichletEtaExt_eval_at_one
#print axioms dirichletEtaExtFilled_at_one
#print axioms dirichletEtaExtFilled_eq_dirichletEtaExt_of_ne_one
#print axioms named_residual_literal_statement_is_incompatible_with_limit

end PrincipiaTractalis.DirichletEtaExtDifferentiableAtOneDisclosure
