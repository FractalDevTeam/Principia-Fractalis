/-
# Two of the five `ch_2` forms are the same quantity, reparametrised

Pablo Cohen, 2026-11-26: *"some things can look the same from different
perspectives, yet they're the same."* Applied to the five `ch_2` forms, that is
a testable question, and for two of them the answer is yes --- on the class
where both are defined.

## What the book currently says

The 2026-10-05 settlement (ch06, `rem:ch2-matrix-range-2026-10-03`) records that
`ch_2` names five different quantities and decides, among other things, that

> these are not several candidates for one quantity --- they measure different
> things

and assigns the threshold `0.95` to the entanglement form `1 - Tr(rho_A^2)`
while `matrix_form_excluded` shows the matrix formula could never have carried
it. That is correct on the matrix formula's *own* domain (connectivity matrices,
velocity-gradient tensors), which are neither trace-one nor positive.

## What this file proves

On the overlap --- a **symmetric, trace-one** matrix, i.e. the shape of a
density matrix --- the two forms are **the same quantity under a strictly
monotone reparametrisation**, so they carry identical information and differ
only in normalisation:

      ch2Matrix(rho)  =  1/2 - 1/(2p)  =  -(1 - p) / (2p)  =  -ch2OfPurity(p) / (2p)

with `p = Tr(rho^2)` the purity. Consequences proved below:

  * `matrix_zero_iff_purity_one` --- the two forms have the **same zero set**:
    both vanish exactly at purity `1`, the pure state.
  * `matrix_form_strictMono_in_purity` and `entanglement_antitone_in_purity` ---
    each is strictly monotone in the purity, in **opposite** directions.
  * `forms_are_order_reversing` --- hence they **rank states identically up to
    orientation**: one state has more entanglement-`ch_2` than another exactly
    when it has less matrix-`ch_2`.

So the matrix formula's `<= 1/2` ceiling, and its provable inability to reach
`0.95`, are facts about the **normalisation** and not evidence that it measures
something else. The settlement's own remark already says as much in passing ---
"this is a statement about normalisation, not about consciousness" --- and this
file turns that sentence into theorems.

## Where the sameness STOPS, which is the other half of the result

The identification needs `Tr W = 1`. Drop it and the matrix form stops carrying
purity information altogether: `matrix_form_const_on_symmetric_traceless` proves
that for **every** symmetric traceless `W` with nonzero Frobenius norm,

      ch2Matrix(W) = 1/2

identically --- the ceiling, independent of `W`. So on the traceless class the
matrix form is a constant and distinguishes nothing, which is exactly why
`ch2Matrix_pureStrain = 1/2` upstream. Two forms that agree up to
reparametrisation on one class and degenerate on another are not
interchangeable, and this file does not claim they are.

## What this does NOT do

It does not revive `0.95` for the matrix form: `ch2Matrix <= 1/2` stands, and a
monotone reparametrisation of a threshold is a *different number*, not the same
one. It does not touch the Chern--Weil form, whose status (sign, normaliser) is
open and unformalised. It does not merge the five names or reverse the
settlement; it narrows one of its clauses, in the direction of fewer distinct
quantities. And it asserts no physics: these are theorems about two formulas.
-/

import PF.Ch2ThresholdSelection
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option autoImplicit false

namespace PrincipiaTractalis.Ch2FormsAgree

open PrincipiaTractalis.Cosmology.VortexCavitationBridge
open PrincipiaTractalis.Ch2Selection

variable {n : Type*} [Fintype n]

/-! ## §1 For a symmetric matrix, `Tr(W²)` IS the Frobenius norm squared -/

/-- Entrywise symmetry, extracted from `Matrix.IsSymm`. -/
theorem symm_apply {W : Matrix n n ℝ} (hsym : W.IsSymm) (i j : n) :
    W j i = W i j := by
  have h := congrFun (congrFun hsym i) j
  simpa [Matrix.transpose_apply] using h

/-- **`Tr(W²) = ‖W‖_F²` for symmetric `W`.** This is the single fact that makes
    the matrix formula collapse to a function of the purity. -/
theorem trace_mul_self_eq_frobSq_of_symm {W : Matrix n n ℝ} (hsym : W.IsSymm) :
    (W * W).trace = frobSq W := by
  rw [trace_mul_self]
  unfold frobSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symm_apply hsym i j]
  ring

/-! ## §2 The matrix form on a density-matrix-shaped argument -/

/-- **★ The matrix form is a function of the purity alone. ★** For symmetric
    `W` with `Tr W = 1` and Frobenius norm squared `p`,
    `ch2Matrix W = 1/2 - 1/(2p)`. -/
theorem ch2Matrix_of_symm_trace_one {W : Matrix n n ℝ} (hsym : W.IsSymm)
    (htr : W.trace = 1) (hp : 0 < frobSq W) :
    ch2Matrix W = 1 / 2 - 1 / (2 * frobSq W) := by
  unfold ch2Matrix
  rw [trace_mul_self_eq_frobSq_of_symm hsym, htr]
  field_simp

/-- **★ THE IDENTIFICATION. ★** The matrix form evaluated on a
    density-matrix-shaped argument is exactly the entanglement form, divided by
    `-2p`. Same quantity, different normalisation. -/
theorem matrix_form_eq_entanglement_form_scaled {p : ℝ} (hp : 0 < p) :
    1 / 2 - 1 / (2 * p) = -(ch2OfPurity p) / (2 * p) := by
  unfold ch2OfPurity
  field_simp
  ring

/-- The same statement read the other way: in terms of the entanglement value
    `e`, the matrix form is the Möbius image `-e / (2(1 - e))`. -/
theorem matrix_form_in_terms_of_entanglement {e : ℝ} (he : e < 1) :
    1 / 2 - 1 / (2 * (1 - e)) = -e / (2 * (1 - e)) := by
  have h : (0:ℝ) < 1 - e := by linarith
  field_simp
  ring

/-! ## §3 Same zeros, opposite orientation, identical ranking -/

/-- **The two forms have the same zero set**: both vanish exactly at purity
    `1`, i.e. on the pure state, and nowhere else. -/
theorem matrix_zero_iff_purity_one {p : ℝ} (hp : 0 < p) :
    (1 / 2 - 1 / (2 * p) = 0) ↔ ch2OfPurity p = 0 := by
  unfold ch2OfPurity
  constructor
  · intro h
    have h2 : 1 / (2 * p) = 1 / 2 := by linarith
    have hne : (2 : ℝ) * p ≠ 0 := by positivity
    field_simp at h2
    linarith
  · intro h
    have hp1 : p = 1 := by linarith
    rw [hp1]
    norm_num

/-- The matrix form is strictly **increasing** in the purity. -/
theorem matrix_form_strictMono_in_purity {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    1 / 2 - 1 / (2 * p) < 1 / 2 - 1 / (2 * q) := by
  have hq : (0:ℝ) < q := lt_trans hp hpq
  have h : 1 / (2 * q) < 1 / (2 * p) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · linarith
  linarith

/-- The entanglement form is strictly **decreasing** in the purity. -/
theorem entanglement_antitone_in_purity {p q : ℝ} (hpq : p < q) :
    ch2OfPurity q < ch2OfPurity p := by
  unfold ch2OfPurity
  linarith

/-- **★ The two forms rank states identically, up to orientation. ★** One state
    carries more entanglement-`ch_2` than another exactly when it carries less
    matrix-`ch_2`. So no information distinguishes the two forms on this class:
    they are one quantity in two normalisations. -/
theorem forms_are_order_reversing {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ch2OfPurity p < ch2OfPurity q ↔
      (1 / 2 - 1 / (2 * q)) < (1 / 2 - 1 / (2 * p)) := by
  unfold ch2OfPurity
  constructor
  · intro h
    exact matrix_form_strictMono_in_purity hq (by linarith)
  · intro h
    by_contra hcon
    push_neg at hcon
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have := matrix_form_strictMono_in_purity hp (by linarith : p < q)
      linarith
    · rw [show q = p by linarith] at h
      exact absurd h (lt_irrefl _)

/-! ## §4 Where the sameness stops -/

/-- **★ On the symmetric TRACELESS class the matrix form is a constant. ★** It
    equals `1/2` for every such `W`, so it distinguishes nothing there and
    carries no purity information at all. This is why the identification above
    needs `Tr W = 1`, and why `ch2Matrix_pureStrain = 1/2` upstream. -/
theorem matrix_form_const_on_symmetric_traceless {W : Matrix n n ℝ}
    (hsym : W.IsSymm) (htr : W.trace = 0) (hp : 0 < frobSq W) :
    ch2Matrix W = 1 / 2 := by
  unfold ch2Matrix
  rw [trace_mul_self_eq_frobSq_of_symm hsym, htr]
  have h : (2 : ℝ) * frobSq W ≠ 0 := by positivity
  rw [show (0:ℝ) ^ 2 = 0 by norm_num, sub_zero, div_eq_iff h]
  ring

/-! ## §5 Capstone -/

/-- **★ TWO OF THE FIVE FORMS ARE ONE QUANTITY, ON THE OVERLAP. ★**

    The identification, the shared zero set, the opposite-orientation
    monotonicities, the identical ranking, and the degeneration off the
    trace-one class. Every conjunct proved above. -/
theorem two_forms_are_one_quantity {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (1 / 2 - 1 / (2 * p) = -(ch2OfPurity p) / (2 * p))
      ∧ ((1 / 2 - 1 / (2 * p) = 0) ↔ ch2OfPurity p = 0)
      ∧ (ch2OfPurity p < ch2OfPurity q ↔
          (1 / 2 - 1 / (2 * q)) < (1 / 2 - 1 / (2 * p))) :=
  ⟨matrix_form_eq_entanglement_form_scaled hp,
   matrix_zero_iff_purity_one hp,
   forms_are_order_reversing hp hq⟩

end PrincipiaTractalis.Ch2FormsAgree
