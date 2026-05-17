/-
# Cell Midpoint Enumeration

Explicit enumeration of the level-`n` cell midpoints of the
Cantor IFS via length-`n` boolean lists. Each binary word
`(b_0, ..., b_{n-1}) ∈ {0, 1}^n` selects a cell at level `n`
via the IFS-word application

  `cellMidpointOfBools bs := f_{b_{n-1}} ∘ ⋯ ∘ f_{b_0}(1/2)`

(applied innermost-first, matching the `List` head-tail structure).

This file:
* Defines `cellMidpointOfBools` recursively.
* Establishes explicit values at low levels (`n = 1, 2`).
* States the connection to `cantorDiscMeasure n` as a finite
  Dirac sum (the structural identity is documented; the full
  Finset-sum proof requires the boolean enumeration infrastructure).

Stage L4+ — explicit cell-midpoint enumeration.
-/

import PF.Analytic.Hutchinson

namespace PrincipiaTractalis.Analytic

open Set MeasureTheory

/-! ## Definition -/

/-- **Cell midpoint** indexed by a length-`n` boolean word:

      `cellMidpointOfBools [] := 1/2`
      `cellMidpointOfBools (false :: bs) := f₁(cellMidpointOfBools bs)`
      `cellMidpointOfBools (true :: bs) := f₂(cellMidpointOfBools bs)`

    Iterates the IFS contractions starting from the center `1/2`,
    one step per boolean in the list. The length of the list
    determines the IFS level. -/
noncomputable def cellMidpointOfBools : List Bool → ℝ
  | [] => 1/2
  | false :: bs => cantorContraction1 (cellMidpointOfBools bs)
  | true :: bs => cantorContraction2 (cellMidpointOfBools bs)

/-! ## Base + recursion -/

/-- Base: empty word gives center of `[0, 1]`. -/
theorem cellMidpointOfBools_nil : cellMidpointOfBools [] = 1/2 := rfl

/-- Recursion (false head): `false :: bs ↦ f₁(cellMidpointOfBools bs)`. -/
theorem cellMidpointOfBools_false_cons (bs : List Bool) :
    cellMidpointOfBools (false :: bs) =
    cantorContraction1 (cellMidpointOfBools bs) := rfl

/-- Recursion (true head): `true :: bs ↦ f₂(cellMidpointOfBools bs)`. -/
theorem cellMidpointOfBools_true_cons (bs : List Bool) :
    cellMidpointOfBools (true :: bs) =
    cantorContraction2 (cellMidpointOfBools bs) := rfl

/-! ## Explicit values at low levels -/

/-- Level 1, left cell: midpoint of `[0, 1/3]` is `1/6`. -/
theorem cellMidpointOfBools_false : cellMidpointOfBools [false] = 1/6 := by
  show cantorContraction1 (cellMidpointOfBools []) = 1/6
  unfold cantorContraction1
  show (cellMidpointOfBools []) / 3 = 1/6
  show ((1:ℝ)/2) / 3 = 1/6
  norm_num

/-- Level 1, right cell: midpoint of `[2/3, 1]` is `5/6`. -/
theorem cellMidpointOfBools_true : cellMidpointOfBools [true] = 5/6 := by
  show cantorContraction2 (cellMidpointOfBools []) = 5/6
  unfold cantorContraction2
  show (cellMidpointOfBools [] + 2) / 3 = 5/6
  show ((1:ℝ)/2 + 2) / 3 = 5/6
  norm_num

/-- Level 2, `[false, false]`: midpoint of `[0, 1/9]` is `1/18`. -/
theorem cellMidpointOfBools_ff : cellMidpointOfBools [false, false] = 1/18 := by
  show cantorContraction1 (cellMidpointOfBools [false]) = 1/18
  rw [cellMidpointOfBools_false]
  unfold cantorContraction1
  norm_num

/-- Level 2, `[true, false]`: midpoint of `[2/9, 1/3]` is `13/18`.
    (head=true → outermost f₂, applied last to `f₁(1/2) = 1/6`.) -/
theorem cellMidpointOfBools_tf : cellMidpointOfBools [true, false] = 13/18 := by
  show cantorContraction2 (cellMidpointOfBools [false]) = 13/18
  rw [cellMidpointOfBools_false]
  unfold cantorContraction2
  norm_num

/-- Level 2, `[false, true]`: midpoint of `[2/3, 7/9]` is `5/18`.
    (head=false → outermost f₁, applied last to `f₂(1/2) = 5/6`.) -/
theorem cellMidpointOfBools_ft : cellMidpointOfBools [false, true] = 5/18 := by
  show cantorContraction1 (cellMidpointOfBools [true]) = 5/18
  rw [cellMidpointOfBools_true]
  unfold cantorContraction1
  norm_num

/-- Level 2, `[true, true]`: midpoint of `[8/9, 1]` is `17/18`. -/
theorem cellMidpointOfBools_tt : cellMidpointOfBools [true, true] = 17/18 := by
  show cantorContraction2 (cellMidpointOfBools [true]) = 17/18
  rw [cellMidpointOfBools_true]
  unfold cantorContraction2
  norm_num

/-! ## Documentation: cantorDiscMeasure as a sum of Diracs over boolean words

By induction on `n` (using `hutchinsonOp_dirac` to split each Dirac
into two children at each iteration step), we have:

  `cantorDiscMeasure n = (1/2^n) · Σ_{bs : List Bool, bs.length = n}
                          δ_{cellMidpointOfBools bs}`

For example:
* Level 0: `(1/1) · δ_{1/2}`
* Level 1: `(1/2) · (δ_{1/6} + δ_{5/6})`  (proven explicitly in `cantorDiscMeasure_one`)
* Level 2: `(1/4) · (δ_{1/18} + δ_{5/18} + δ_{13/18} + δ_{17/18})`

The integral of any function `f` against `cantorDiscMeasure n` is
therefore the average over the `2^n` boolean words:

  `∫ f d(cantorDiscMeasure n) = (1/2^n) · Σ_{bs} f(cellMidpointOfBools bs)`

This is the explicit finite-sum form. Proving it in full generality
requires enumerating the boolean words via a Finset structure
(`Fin (2^n)` or `List Bool` of length `n`), which the framework
infrastructure supports.

The level-1 explicit identity is `cantorDiscMeasure_one` in
`Hutchinson.lean`; higher levels follow by repeated `hutchinsonOp_dirac`
application + measure-additivity / scalar.
-/

end PrincipiaTractalis.Analytic
