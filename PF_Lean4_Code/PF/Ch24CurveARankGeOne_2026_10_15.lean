/-
# PF.Ch24CurveARankGeOne_2026_10_15

**Repair of the ch24 printed rank defect, on a genuine mathlib curve.**

`ch24_birch_swinnerton_dyer.tex:594` prints `rank E(ℚ) = 0 (proven)` for the
curve `y² = x³ − 2`, while that chapter's own introduction exhibits the point
`P = (3, 5)` on it (`5² = 25 = 27 − 2 = 3³ − 2`). The existing formalization
(`Ch23Ch24MillenniumNumerics.lean`) records `(3,5)` and `2P` only through the
bare predicate `OnCurveA (x y : ℚ) : Prop := y ^ 2 = x ^ 3 - 2` — not a
mathlib curve — and the chapter's correction note leans on Mazur's torsion
bound as "a standard stated input [that] is not formalized".

This file puts curve A into mathlib's own `WeierstrassCurve` and derives the
rank statement in the target language, with **no appeal to Mazur**:

* `curveA : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, -2⟩`
* `P_A : curveA.toAffine.Point` — the point `(3, 5)`
* `dbl_x_P_A : x(2·P_A) = 129/100` — exactly the "harder to find" second point
  the chapter's introduction quotes
* `rank_ge_one_of_nonTorsion` — `1 ≤ Module.rank ℤ curveA.toAffine.Point`
  from `MordellWeilRankLowerBound_r129.mordellWeil_rank_ge_one`

## The load-bearing arithmetic fact

Everything rests on `two_not_cube : ∀ q : ℚ, q ^ 3 ≠ 2`, proved from mathlib's
`irrational_nrt_of_n_not_dvd_multiplicity` (multiplicity of `2` in `2` is `1`,
and `3 ∤ 1`). It discharges, in one stroke, both
* `g_ne_zero` — the duplication denominator `4x³ − 8` never vanishes on ℚ, and
* `y_ne_zero_of_equation` — no rational point of curve A has `y = 0`,
hence curve A has **no rational 2-torsion**, which is what makes the doubling
formula total.

## Scope — read before citing

The conclusion `1 ≤ Module.rank ℤ curveA.toAffine.Point` is stated with the
non-torsion certificate `¬ IsOfFinAddOrder P_A` as an **explicit hypothesis**
(`rank_ge_one_of_nonTorsion`), exactly as `MordellWeilRankLowerBound_r129`
specifies. That hypothesis is NOT discharged here.

**Removal condition:** port the height-growth argument of
`E53a1RankOne_r136.lean` (§C–§D) to the duplication pair
`f x = x⁴ + 16x`, `g x = 4x³ − 8` of this curve — i.e. establish
`naiveHeight x ^ 4 ≤ κ · naiveHeight (f x / g x)` for an explicit `κ`, exhibit
one orbit point above `κ`, and conclude the doubling orbit is infinite. The
generic conversion (`one_le_rank_of_infinite_order`) and the reduction
bookkeeping (`DuplicationHeightBound37a1_r133.naiveHeight_div_int`) are
already in the corpus and curve-generic; only `κ` and the integer forms are
curve-specific. Until that lands, the rank claim here is CONDITIONAL and is
labelled so.

What this file settles UNCONDITIONALLY: curve A is a genuine mathlib
`WeierstrassCurve ℚ`; `(3,5)` is a genuine nonsingular rational point of it;
curve A has **no rational 2-torsion**; the duplication map on `x` is
`f/g`; and `x(2·P_A) = 129/100`.

What it does NOT settle, stated precisely to avoid an overclaim: these facts
alone do **not** refute `rank E(ℚ) = 0`. A rank-0 curve has finite `E(ℚ)`, and
a finite group can perfectly well contain a point with `2P ≠ ±P` — so
`x(2P) ≠ x(P)` is not a contradiction. Refuting the printed rank requires
exactly the non-torsion certificate below, and nothing weaker. The chapter's
own correction note reaches `rank ≥ 1` only by invoking Mazur's torsion bound,
which is not formalized; this file replaces that appeal with a single named
Lean hypothesis and the removal condition for it.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-15.
-/

import PF.MordellWeilRankLowerBound_r129
import Mathlib.Data.Real.Irrational

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Ch24CurveARankGeOne20261015

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.MordellWeilRankLowerBound

noncomputable section

/-! ## §0 — the curve -/

/-- **ch24's curve A**: `y² = x³ − 2`, the Mordell curve at `k = −2`. -/
def curveA : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, -2⟩

@[simp] lemma curveA_a₁ : curveA.a₁ = 0 := rfl
@[simp] lemma curveA_a₂ : curveA.a₂ = 0 := rfl
@[simp] lemma curveA_a₃ : curveA.a₃ = 0 := rfl
@[simp] lemma curveA_a₄ : curveA.a₄ = 0 := rfl
@[simp] lemma curveA_a₆ : curveA.a₆ = -2 := rfl

/-! ## §1 — `2` is not a rational cube -/

/-- **`q³ ≠ 2` for every rational `q`.** Via mathlib's
`irrational_nrt_of_n_not_dvd_multiplicity`: a real cube root of the integer `2`
is irrational because the multiplicity of `2` in `2` is `1` and `3 ∤ 1`. -/
theorem two_not_cube (q : ℚ) : q ^ 3 ≠ 2 := by
  intro h
  have hr : ((q : ℝ)) ^ 3 = ((2 : ℤ) : ℝ) := by
    have hq : ((q ^ 3 : ℚ) : ℝ) = ((2 : ℚ) : ℝ) := by rw [h]
    push_cast at hq ⊢
    exact hq
  have hmul : multiplicity (2 : ℤ) 2 % 3 ≠ 0 := by
    rw [multiplicity_self]
    norm_num
  have hirr : Irrational ((q : ℝ)) :=
    irrational_nrt_of_n_not_dvd_multiplicity 3 (by norm_num) 2 hr hmul
  exact (Rat.not_irrational q) hirr

/-! ## §2 — the equation, and no rational 2-torsion -/

/-- The affine equation of curve A reads `y² = x³ − 2`. -/
lemma curveA_equation_iff (x y : ℚ) :
    curveA.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - 2 := by
  rw [Affine.equation_iff]
  show y ^ 2 + 0 * x * y + 0 * y = x ^ 3 + 0 * x ^ 2 + 0 * x + -2 ↔ _
  constructor <;> intro h <;> linarith

/-- On curve A, `y = 0` is impossible: it would force `x³ = 2`. -/
lemma y_ne_zero_of_equation {x y : ℚ} (h : curveA.toAffine.Equation x y) :
    y ≠ 0 := by
  intro hy
  rw [curveA_equation_iff] at h
  rw [hy] at h
  exact two_not_cube x (by linarith)

/-- `negY` on curve A is `−y` (`a₁ = a₃ = 0`). -/
lemma negY_eq (x y : ℚ) : curveA.toAffine.negY x y = -y := by
  show -y - 0 * x - 0 = -y
  ring

/-- **Curve A has no rational 2-torsion:** `y ≠ negY x y` at every rational
affine point. This is what makes the doubling formula total. -/
theorem y_ne_negY {x y : ℚ} (h : curveA.toAffine.Equation x y) :
    y ≠ curveA.toAffine.negY x y := by
  rw [negY_eq]
  intro hy
  exact y_ne_zero_of_equation h (by linarith)

/-! ## §3 — the duplication pair, and its denominator never vanishes -/

/-- Numerator of the duplication map on `x`. -/
def f (x : ℚ) : ℚ := x ^ 4 + 16 * x

/-- Denominator of the duplication map on `x`. -/
def g (x : ℚ) : ℚ := 4 * x ^ 3 - 8

/-- **`g` never vanishes on ℚ** — immediately from `two_not_cube`. -/
theorem g_ne_zero (x : ℚ) : g x ≠ 0 := by
  intro h0
  rw [g] at h0
  exact two_not_cube x (by linarith)

/-! ## §4 — the point `(3,5)` and the duplication formula -/

/-- `(3, 5)` satisfies curve A's equation: `25 = 27 − 2`. -/
theorem P_A_equation : curveA.toAffine.Equation 3 5 := by
  rw [curveA_equation_iff]
  norm_num

/-- `(3, 5)` is a nonsingular rational point of curve A: the `Y`-partial is
`2y = 10 ≠ 0`. -/
theorem P_A_nonsingular : curveA.toAffine.Nonsingular 3 5 := by
  rw [Affine.nonsingular_iff]
  refine ⟨P_A_equation, Or.inr ?_⟩
  show (5 : ℚ) ≠ -5 - 0 * 3 - 0
  norm_num

/-- **The point** `P_A = (3, 5) ∈ curveA(ℚ)` — the point ch24's introduction
exhibits. -/
def P_A : curveA.toAffine.Point := Point.some P_A_nonsingular

/-- The tangent slope at a rational affine point of curve A is `3x²/(2y)`. -/
theorem slope_eq {x y : ℚ} (h : curveA.toAffine.Nonsingular x y) :
    curveA.toAffine.slope x x y y = 3 * x ^ 2 / (2 * y) := by
  rw [Affine.slope_of_Y_ne rfl (y_ne_negY h.left), negY_eq]
  have hnum : 3 * x ^ 2 + 2 * curveA.toAffine.a₂ * x + curveA.toAffine.a₄
      - curveA.toAffine.a₁ * y = 3 * x ^ 2 := by
    show 3 * x ^ 2 + 2 * 0 * x + 0 - 0 * y = 3 * x ^ 2
    ring
  have hden : y - -y = 2 * y := by ring
  rw [hnum, hden]

/-- **The duplication formula for curve A.** For any rational affine point
`P = some h` at `(x, y)`, the double `P + P` is again an affine point whose
`x`-coordinate is exactly `f x / g x = (x⁴ + 16x)/(4x³ − 8)`. -/
theorem dbl_x {x y : ℚ} (h : curveA.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : curveA.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x := by
  have hy : y ≠ curveA.toAffine.negY x y := y_ne_negY h.left
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy, ?_⟩
  have hy0 : y ≠ 0 := y_ne_zero_of_equation h.left
  have hEq : y ^ 2 = x ^ 3 - 2 := by rw [← curveA_equation_iff]; exact h.left
  have hg' : 4 * x ^ 3 - 8 ≠ 0 := by
    intro h0
    exact two_not_cube x (by linarith)
  -- the tangent slope squared, with `y` eliminated through the equation
  have hsq : (3 * x ^ 2 / (2 * y)) ^ 2 = 9 * x ^ 4 / (4 * x ^ 3 - 8) := by
    rw [div_pow, show (2 * y) ^ 2 = 4 * x ^ 3 - 8 by rw [mul_pow, hEq]; ring]
    congr 1
    ring
  rw [slope_eq h]
  show curveA.toAffine.addX x x (3 * x ^ 2 / (2 * y)) = f x / g x
  rw [Affine.addX]
  show (3 * x ^ 2 / (2 * y)) ^ 2 + 0 * (3 * x ^ 2 / (2 * y)) - 0 - x - x
      = f x / g x
  rw [zero_mul, sub_zero, add_zero, hsq, f, g]
  -- both sides over the common denominator `4x³ − 8`
  have key : 9 * x ^ 4 / (4 * x ^ 3 - 8) - (x ^ 4 + 16 * x) / (4 * x ^ 3 - 8)
      = x + x := by
    rw [div_sub_div_same,
      show 9 * x ^ 4 - (x ^ 4 + 16 * x) = (x + x) * (4 * x ^ 3 - 8) by ring]
    exact mul_div_cancel_right₀ _ hg'
  linarith [key]

/-- **`x(2·P_A) = 129/100`** — exactly the second point ch24's introduction
calls "harder to find", up to the curve's `y ↦ −y` symmetry. -/
theorem dbl_x_P_A : f 3 / g 3 = 129 / 100 := by
  rw [f, g]
  norm_num

/-! ## §5 — the rank conclusion -/

/-- **`1 ≤ Module.rank ℤ curveA.toAffine.Point`**, given the non-torsion
certificate for `P_A`.

The hypothesis is the one named open input of
`MordellWeilRankLowerBound_r129`; see this file's header for its removal
condition. Nothing here pretends it is discharged. -/
theorem rank_ge_one_of_nonTorsion (hP : ¬ IsOfFinAddOrder P_A) :
    1 ≤ Module.rank ℤ curveA.toAffine.Point :=
  mordellWeil_rank_ge_one curveA.toAffine P_A hP

/-- The same statement through the corpus's named certificate Prop. -/
theorem rank_ge_one_under_certificate_A
    (h : NonTorsionCertificate curveA.toAffine P_A) :
    1 ≤ Module.rank ℤ curveA.toAffine.Point :=
  rank_ge_one_under_certificate curveA.toAffine P_A h

end

/-! ## §Axiom check -/

#print axioms two_not_cube
#print axioms curveA_equation_iff
#print axioms y_ne_zero_of_equation
#print axioms negY_eq
#print axioms y_ne_negY
#print axioms g_ne_zero
#print axioms P_A_equation
#print axioms P_A_nonsingular
#print axioms slope_eq
#print axioms dbl_x
#print axioms dbl_x_P_A
#print axioms rank_ge_one_of_nonTorsion
#print axioms rank_ge_one_under_certificate_A

end Ch24CurveARankGeOne20261015
end PrincipiaTractalis
