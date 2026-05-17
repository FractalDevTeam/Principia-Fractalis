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

/-! ## ★ Cell midpoint range bounds ★ -/

/-- **★ Cell midpoint range bound ★**: for any length-`n` boolean
    word `bs`, the cell midpoint `cellMidpointOfBools bs` lies in
    `[0, 1]`. Proven by induction on `bs`:

    * Base `[]`: `1/2 ∈ [0, 1]`.
    * Inductive step (`false :: bs`): `f₁(x) = x/3` maps `[0, 1]` to
      `[0, 1/3] ⊆ [0, 1]`.
    * Inductive step (`true :: bs`): `f₂(x) = (x + 2)/3` maps `[0, 1]`
      to `[2/3, 1] ⊆ [0, 1]`.

    Confirms that all level-`n` Dirac points of `cantorDiscMeasure n`
    are supported in the unit interval `[0, 1]`, consistent with the
    Hutchinson invariant measure `μ_H` being supported on the Cantor
    set `⊆ [0, 1]`. -/
theorem cellMidpointOfBools_mem_Icc (bs : List Bool) :
    cellMidpointOfBools bs ∈ Set.Icc (0 : ℝ) 1 := by
  induction bs with
  | nil =>
    rw [cellMidpointOfBools_nil]
    constructor
    · norm_num
    · norm_num
  | cons b bs ih =>
    cases b
    · -- false :: bs
      rw [cellMidpointOfBools_false_cons]
      unfold cantorContraction1
      obtain ⟨h1, h2⟩ := ih
      constructor
      · -- x/3 ≥ 0 since x ≥ 0
        linarith
      · -- x/3 ≤ 1 since x ≤ 1 and 1/3 ≤ 1
        linarith
    · -- true :: bs
      rw [cellMidpointOfBools_true_cons]
      unfold cantorContraction2
      obtain ⟨h1, h2⟩ := ih
      constructor
      · -- (x + 2)/3 ≥ 0 since x ≥ 0 (so x + 2 ≥ 2 > 0)
        linarith
      · -- (x + 2)/3 ≤ 1 since x ≤ 1 (so x + 2 ≤ 3, x + 2)/3 ≤ 1)
        linarith

/-- **Cell midpoint non-negativity**: `cellMidpointOfBools bs ≥ 0`. -/
theorem cellMidpointOfBools_nonneg (bs : List Bool) :
    0 ≤ cellMidpointOfBools bs :=
  (cellMidpointOfBools_mem_Icc bs).1

/-- **Cell midpoint upper bound**: `cellMidpointOfBools bs ≤ 1`. -/
theorem cellMidpointOfBools_le_one (bs : List Bool) :
    cellMidpointOfBools bs ≤ 1 :=
  (cellMidpointOfBools_mem_Icc bs).2

/-- **Cell midpoint left-half range** (`false :: bs`): for words
    starting with `false`, the midpoint is in `[0, 1/3]`. -/
theorem cellMidpointOfBools_false_cons_mem_Icc (bs : List Bool) :
    cellMidpointOfBools (false :: bs) ∈ Set.Icc (0 : ℝ) (1/3) := by
  rw [cellMidpointOfBools_false_cons]
  unfold cantorContraction1
  obtain ⟨h1, h2⟩ := cellMidpointOfBools_mem_Icc bs
  constructor
  · linarith
  · linarith

/-- **Cell midpoint right-half range** (`true :: bs`): for words
    starting with `true`, the midpoint is in `[2/3, 1]`. -/
theorem cellMidpointOfBools_true_cons_mem_Icc (bs : List Bool) :
    cellMidpointOfBools (true :: bs) ∈ Set.Icc (2/3 : ℝ) 1 := by
  rw [cellMidpointOfBools_true_cons]
  unfold cantorContraction2
  obtain ⟨h1, h2⟩ := cellMidpointOfBools_mem_Icc bs
  constructor
  · linarith
  · linarith

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
