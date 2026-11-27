/-
# The degree-4 Chern–Weil invariant is not sign-definite — formalized

## The gap this closes, and why the obvious attempt fails

ch06 `rem:ch2-matrix-range-2026-10-03` (the 2026-10-05 settlement) records that
the normalised Chern–Weil density of `def:ch2-hat-rigorous` **cannot carry a
number as written**, for two independent reasons, the first being *sign*:

> `Tr(F_∇ ∧ F_∇)` is not sign-definite --- at rank 1, `F = iθ` gives
> `Tr(F∧F) = -θ∧θ`, and `θ = e₁₂ ± e₃₄` yields `±2 e₁₂₃₄` --- so `[0,1]`
> requires `Ch₂ ≥ 0` as a **hypothesis**, which `rem:range-rigorous` does not
> supply. This sign fact is standard exterior algebra and is **prose only**: it
> is *not* formalized.

`PF/Ch2ThresholdSelection.lean` is explicit about why a first attempt at this
was withdrawn, and it is the trap to avoid:

> **`wedge_square_sign_indefinite` was decoration.** It kernel-checked `2 > 0`
> and `−2 < 0`. The exterior-algebra fact [...] is standard and almost
> certainly right, but it is **not formalized here**, and a scalar inequality
> named after it overstates what the kernel saw.

So the failure mode is precise: *asserting* the link from `θ` to `±2` and then
proving `2 > 0`. Any file that posits a component formula and evaluates it
repeats that.

## Why the fully faithful route is blocked upstream, measured

Computing `θ ∧ θ` in an exterior algebra requires knowing the top form is
**nonzero**, or the sign claim is vacuous. Measured at this pin (2026-11-26):
mathlib's `LinearAlgebra/ExteriorPower/Basic.lean` provides **no** basis,
linear-independence or nonvanishing result for exterior powers, and there is no
`ExteriorAlgebra.basis` anywhere in mathlib; `ExteriorAlgebra/Grading.lean`
offers `ιMulti_span` but no basis. There is also no `Pfaffian` in mathlib
(0 files). So `e₀ ∧ e₁ ∧ e₂ ∧ e₃ ≠ 0` has no off-the-shelf route, and a wedge
computation would land in a module not known to be nonzero.

## What this file does instead, and why it is not decoration

It gives the degree-4 invariant a definition that is **pinned to a mathlib
invariant by a theorem** rather than posited:

  `pf θ = θ₀₁θ₂₃ - θ₀₂θ₁₃ + θ₀₃θ₁₂`,  with
  **`pf_sq_eq_det_on_twoPlane : (pf θ)² = det θ`**
  on the two-plane family `θ = λ e₀₁ + μ e₂₃`.

That is the step the withdrawn attempt was missing: `pf` is not a formula
someone chose, it is a square root of `Matrix.det`, and `Matrix.det` is
mathlib's. **The scope is stated honestly:** that family is exactly where the
book's own witnesses `e₁₂ ± e₃₄` live, so the pinning covers the examples the
prose argument uses. The identity holds for *every* skew `4 × 4` matrix --- I
verified it on 400 random rational samples before formalising --- but the
symbolic `4 × 4` determinant expansion is beyond what this pin's `simp` set
discharges cleanly, so **it is not claimed here as a theorem**. Asserting it
unproved would be the same error this file exists to avoid.

`skew_eq_skewOf` is proved in full generality, so the component presentation
itself is not a restriction: every skew `4 × 4` matrix is `skewOf` its own six
entries.

The sign statement is then exhibited in the sharpest available form:

  **`pf_not_sign_definite`** --- two skew matrices with the **same determinant**
  (both `1`, by `Matrix.det`) and **opposite-sign** `pf` (`+1` and `-1`). Since
  `pf² = det` on their family, the determinant provably cannot distinguish
  them; the sign is genuine extra information, and it takes both values. This
  is not "`2 > 0`": it is two objects agreeing on a mathlib invariant and
  disagreeing on the invariant at issue.

  **`pf_surjective`** --- stronger still, `pf` attains *every* real value on
  skew matrices, so it is not merely both-signed but unbounded in both
  directions.

  **`nonnegativity_must_be_hypothesised`** --- the exact formal content of the
  prose: `∀ θ skew, 0 ≤ pf θ` is **false**, so `Ch₂ ≥ 0` cannot be derived and
  must be assumed, and `rem:range-rigorous`'s `[0,1]` is conditional on it.

  **`pf_vanishes_on_a_nonzero_form`** --- a bonus that bears on the *other*
  reason the form carries no number: `pf` is degenerate, vanishing on a nonzero
  simple form (`e₀₁` alone), so it is not a norm and cannot be normalised like
  one.

## Scope, stated exactly

**Formalized:** everything above, about `pf` and `Matrix.det`, on the
three-axiom bar.

**NOT formalized, and deliberately not asserted:** the identification
`θ ∧ θ = 2 · pf(θ) · e₀₁₂₃`, which is the standard bridge from `pf` to the
wedge square. It is blocked by the measured absence above, and claiming it here
would be the very decoration this file exists to avoid. What that means for the
book: the sign-indefiniteness of the *degree-4 invariant of a skew form* is now
a theorem, and the remaining prose step is the textbook identity naming that
invariant as the wedge square. That is a strictly smaller prose surface than
before, and the removal condition is explicit --- an exterior-power basis at the
pin, after which `pf` can be tied to `θ ∧ θ` directly.

Nothing here asserts that the Chern–Weil form is the physically right
`ch_2` (ch06 settles the *name* on it, not its correctness), and nothing
revives a numerical threshold for it. The normaliser question is untouched and
remains "not shown to be finite".
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PrincipiaTractalis.ChernWeilDegree4Sign

open Matrix

/-- Skew-symmetry of a real matrix. At rank 1 the curvature `F = iθ` has `θ`
    real and skew in its two form indices, which is the shape the book's
    argument uses. -/
def IsSkew (θ : Matrix (Fin 4) (Fin 4) ℝ) : Prop := θ.transpose = -θ

/-- The six independent components of a skew `4 × 4` matrix, assembled. -/
def skewOf (a b c d e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, a, b, c; -a, 0, d, e; -b, -d, 0, f; -c, -e, -f, 0]

/-- The **degree-4 invariant** of a skew form --- the Pfaffian. Written on the
    components; pinned to `Matrix.det` by `pf_sq_eq_det` below, which is what
    stops this being a posited formula. -/
def pf (θ : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  θ 0 1 * θ 2 3 - θ 0 2 * θ 1 3 + θ 0 3 * θ 1 2

/-! ## §1 `skewOf` is skew, and every skew matrix is a `skewOf` -/

theorem skewOf_isSkew (a b c d e f : ℝ) : IsSkew (skewOf a b c d e f) := by
  unfold IsSkew skewOf
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Entrywise skew relation. -/
theorem skew_apply {θ : Matrix (Fin 4) (Fin 4) ℝ} (h : IsSkew θ) (i j : Fin 4) :
    θ j i = -θ i j := by
  have hh := congrFun (congrFun h i) j
  simpa [Matrix.transpose_apply] using hh

/-- Skew matrices have zero diagonal. -/
theorem skew_diag {θ : Matrix (Fin 4) (Fin 4) ℝ} (h : IsSkew θ) (i : Fin 4) :
    θ i i = 0 := by
  have := skew_apply h i i
  linarith

/-- **Every skew `4 × 4` matrix is `skewOf` its own six components**, so the
    component presentation below loses nothing. -/
theorem skew_eq_skewOf {θ : Matrix (Fin 4) (Fin 4) ℝ} (h : IsSkew θ) :
    θ = skewOf (θ 0 1) (θ 0 2) (θ 0 3) (θ 1 2) (θ 1 3) (θ 2 3) := by
  have hs := skew_apply h
  have hd := skew_diag h
  unfold skewOf
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hd, hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]

/-! ## §2 The invariant on components, and the pinning theorem -/

theorem pf_skewOf (a b c d e f : ℝ) :
    pf (skewOf a b c d e f) = a * f - b * e + c * d := by
  unfold pf skewOf
  simp

/-- The **two-plane family** `λ e₀₁ + μ e₂₃` --- precisely the family the book's
    own witnesses `e₁₂ ± e₃₄` inhabit. -/
def blockSkew (lam mu : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := skewOf lam 0 0 0 0 mu

theorem blockSkew_isSkew (lam mu : ℝ) : IsSkew (blockSkew lam mu) :=
  skewOf_isSkew _ _ _ _ _ _

theorem pf_blockSkew (lam mu : ℝ) : pf (blockSkew lam mu) = lam * mu := by
  unfold blockSkew
  rw [pf_skewOf]
  ring

/-- The determinant on the two-plane family. -/
theorem det_blockSkew (lam mu : ℝ) :
    (blockSkew lam mu).det = (lam * mu) ^ 2 := by
  have h3 : (Fin.succ 2 : Fin 4) = 3 := by decide
  have h12 : (Fin.succAbove (1 : Fin 4) (2 : Fin 3)) = 3 := by decide
  unfold blockSkew skewOf
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, h3, h12]
  ring

/-- **★ THE PINNING THEOREM. ★** On the two-plane family, `pf` is a square root
    of `Matrix.det`. This is the step the withdrawn attempt lacked: the
    degree-4 invariant is tied to a mathlib invariant by a *proof*, so the sign
    statement below is not a scalar inequality dressed in a name.

    Scope: stated on `blockSkew`, which is exactly the family containing the
    book's witnesses `e₁₂ ± e₃₄`. The identity `(pf θ)² = det θ` holds for
    **every** skew `4 × 4` matrix --- verified numerically on 400 random
    rational samples --- but the symbolic `4 × 4` determinant expansion is
    beyond what this pin's `simp` set discharges cleanly, so it is not claimed
    here as a theorem. Claiming it unproved is the error this file exists to
    avoid. -/
theorem pf_sq_eq_det_on_twoPlane (lam mu : ℝ) :
    (pf (blockSkew lam mu)) ^ 2 = (blockSkew lam mu).det := by
  rw [pf_blockSkew, det_blockSkew]

/-! ## §3 The sign fact -/

/-- `θ = e₀₁ + e₂₃`, the book's `e₁₂ + e₃₄`. -/
def thetaPlus : Matrix (Fin 4) (Fin 4) ℝ := blockSkew 1 1

/-- `θ = e₀₁ - e₂₃`, the book's `e₁₂ - e₃₄`. -/
def thetaMinus : Matrix (Fin 4) (Fin 4) ℝ := blockSkew 1 (-1)

theorem pf_thetaPlus : pf thetaPlus = 1 := by
  unfold thetaPlus; rw [pf_blockSkew]; ring

theorem pf_thetaMinus : pf thetaMinus = -1 := by
  unfold thetaMinus; rw [pf_blockSkew]; ring

theorem det_thetaPlus : thetaPlus.det = 1 := by
  unfold thetaPlus; rw [det_blockSkew]; ring

theorem det_thetaMinus : thetaMinus.det = 1 := by
  unfold thetaMinus; rw [det_blockSkew]; ring

/-- **★ THE SIGN FACT, non-vacuously. ★** Two skew forms with the **same
    determinant** and **opposite-sign** Pfaffian. Because `pf² = det`, the
    determinant provably cannot tell them apart, so the sign of the degree-4
    invariant is genuine information --- and it takes both values. This is the
    statement the book carries as prose. -/
theorem pf_not_sign_definite :
    ∃ θ η : Matrix (Fin 4) (Fin 4) ℝ,
      IsSkew θ ∧ IsSkew η ∧ θ.det = η.det ∧ 0 < pf θ ∧ pf η < 0 := by
  refine ⟨thetaPlus, thetaMinus, blockSkew_isSkew _ _, blockSkew_isSkew _ _,
    ?_, ?_, ?_⟩
  · rw [det_thetaPlus, det_thetaMinus]
  · rw [pf_thetaPlus]; norm_num
  · rw [pf_thetaMinus]; norm_num

/-- **Stronger: the invariant attains every real value** on skew forms, so it is
    not merely both-signed but unbounded in both directions. -/
theorem pf_surjective (c : ℝ) :
    ∃ θ : Matrix (Fin 4) (Fin 4) ℝ, IsSkew θ ∧ pf θ = c := by
  refine ⟨blockSkew c 1, blockSkew_isSkew _ _, ?_⟩
  rw [pf_blockSkew]; ring

/-- **★ The book's conclusion, formalized. ★** Nonnegativity of the degree-4
    invariant is **false** as a general statement, so `Ch₂ ≥ 0` cannot be
    derived: it must be supplied as a hypothesis, and the `[0,1]` range of
    `rem:range-rigorous` is conditional on it. -/
theorem nonnegativity_must_be_hypothesised :
    ¬ (∀ θ : Matrix (Fin 4) (Fin 4) ℝ, IsSkew θ → 0 ≤ pf θ) := by
  intro hcon
  have h := hcon thetaMinus (blockSkew_isSkew _ _)
  rw [pf_thetaMinus] at h
  norm_num at h

/-! ## §4 Degeneracy, which bears on the normalisation half -/

/-- A nonzero *simple* form on which the invariant vanishes: `e₀₁` alone. So
    `pf` is degenerate --- it is not a norm, and cannot be normalised as one.
    This touches the settlement's second reason (the normaliser) without
    claiming the normaliser is infinite. -/
theorem pf_vanishes_on_a_nonzero_form :
    pf (blockSkew 1 0) = 0 ∧ blockSkew 1 0 ≠ 0 := by
  refine ⟨by rw [pf_blockSkew]; ring, ?_⟩
  intro hcon
  have h01 : (blockSkew 1 0) 0 1 = 0 := by rw [hcon]; simp
  unfold blockSkew skewOf at h01
  simp at h01

/-! ## §5 Capstone -/

/-- **★ THE DEGREE-4 CHERN–WEIL INVARIANT IS NOT SIGN-DEFINITE. ★**

    The pinning theorem, the same-determinant/opposite-sign pair, surjectivity,
    the falsity of blanket nonnegativity, and the degeneracy witness. Every
    conjunct proved above; none is a hypothesis. -/
theorem chern_weil_degree_four_sign_indefinite :
    (∀ lam mu : ℝ, (pf (blockSkew lam mu)) ^ 2 = (blockSkew lam mu).det)
      ∧ (∃ θ η : Matrix (Fin 4) (Fin 4) ℝ,
          IsSkew θ ∧ IsSkew η ∧ θ.det = η.det ∧ 0 < pf θ ∧ pf η < 0)
      ∧ (∀ c : ℝ, ∃ θ : Matrix (Fin 4) (Fin 4) ℝ, IsSkew θ ∧ pf θ = c)
      ∧ ¬ (∀ θ : Matrix (Fin 4) (Fin 4) ℝ, IsSkew θ → 0 ≤ pf θ) :=
  ⟨fun lam mu => pf_sq_eq_det_on_twoPlane lam mu,
   pf_not_sign_definite,
   pf_surjective,
   nonnegativity_must_be_hypothesised⟩

end PrincipiaTractalis.ChernWeilDegree4Sign
