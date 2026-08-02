/-
# PF.SecantUniversal_r181

★★★ 2026-08-01 — THE SECANT SIDE GOES UNIVERSAL TOO ★★★

## Why this file exists — a scope correction

r174–r180 made the *duplication* half of the canonical-height machinery
curve-independent, and I said so.  Checking the dependency graph afterwards
showed the claim was narrower than it sounded: `rank` needs bi-additivity, which
needs the **parallelogram** law, which runs through the *secant* estimates
r160–r163 — and those were still hand-built per curve.  The universal chain
covered duplication only.

This stone closes that gap at the algebraic level: the sum-and-product formulas
for `x(P+Q)` and `x(P−Q)`, universally, in the b-invariant basis.

## The formulas

Both are symmetric in the `y`'s, so both eliminate `y₁, y₂` entirely:

  `x(P+Q) + x(P−Q) = [2x₁x₂(x₁+x₂) + b₂x₁x₂ + b₄(x₁+x₂) + b₆] / (x₁−x₂)²`
  `x(P+Q) · x(P−Q) = [x₁²x₂² − b₄x₁x₂ − b₆(x₁+x₂) − b₈] / (x₁−x₂)²`

The same b-invariant basis that made r174 tractable works here.

## Validation

At `(b₂,b₄,b₆,b₈) = (0,−14,25,−49)` these are *exactly* r160's hand-derived
5077a1 forms

  `Sfnum = 2x₁²x₂ + 2x₁x₂² − 14x₁ − 14x₂ + 25`
  `Prnum = x₁²x₂² + 14x₁x₂ − 25x₁ − 25x₂ + 49`

— the second independent confirmation, after r180's `f`/`g` = `φ`/`ψ`, that the
universal derivation reproduces hand computation on the nose.

**And it corrects a note I had recorded**: the sum certificate cofactors are
`2, 2`.  I had written that down as "structural for `a₁=0, a₃=1`".  Wrong — they
are `2, 2` *universally*, for every Weierstrass curve.  The product cofactors are
genuinely large (19 and 17 terms).

## What remains after this

The formulas, not yet the *estimates*.  r161–r163 turn `Sfnum`/`Prnum` into the
quasi-parallelogram defect bound via content and size arguments; those are the
r174/r175 analogues on this side and are the next stones.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-01.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace PrincipiaTractalis.SecantUniversal

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- Numerator of `x(P+Q) + x(P−Q)`. -/
def sumNum (x₁ x₂ : F) : F :=
  2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆

/-- Numerator of `x(P+Q) · x(P−Q)`. -/
def prdNum (x₁ x₂ : F) : F :=
  x₁ ^ 2 * x₂ ^ 2 - W.b₄ * x₁ * x₂ - W.b₆ * (x₁ + x₂) - W.b₈

variable {W}

/-- `addX` at a slope written over `x₁ − x₂`, with the denominator pulled out. -/
theorem addX_div {x₁ x₂ : F} (N : F) (hD : x₁ - x₂ ≠ 0) :
    W.addX x₁ x₂ (N / (x₁ - x₂))
      = (N ^ 2 + W.a₁ * N * (x₁ - x₂) - (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2)
        / (x₁ - x₂) ^ 2 := by
  simp only [WeierstrassCurve.Affine.addX]
  field_simp
  ring

/-- **Sum of the two `x`-coordinates**, universally.  Certificate: `2·E₁ + 2·E₂`. -/
theorem addX_add_addX_negY {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
        + W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))
      = sumNum W x₁ x₂ / (x₁ - x₂) ^ 2 := by
  have hD : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [W.slope_of_X_ne hx, W.slope_of_X_ne hx, addX_div _ hD, addX_div _ hD,
    div_add_div_same]
  congr 1
  rw [WeierstrassCurve.Affine.equation_iff] at h₁ h₂
  simp only [sumNum, WeierstrassCurve.Affine.negY, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination (2 : F) * h₁ + (2 : F) * h₂

/-- **Product of the two `x`-coordinates**, universally. -/
theorem addX_mul_addX_negY {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
        * W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))
      = prdNum W x₁ x₂ / (x₁ - x₂) ^ 2 := by
  have hD : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hD2 : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  rw [W.slope_of_X_ne hx, W.slope_of_X_ne hx, addX_div _ hD, addX_div _ hD,
    div_mul_div_comm]
  rw [div_eq_div_iff (mul_ne_zero hD2 hD2) hD2]
  rw [WeierstrassCurve.Affine.equation_iff] at h₁ h₂
  simp only [prdNum, WeierstrassCurve.Affine.negY, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination
    ((x₁ - x₂) ^ 2 *
      (W.a₁ ^ 2 * x₁ * x₂ - W.a₁ ^ 2 * x₂ ^ 2 + W.a₁ * W.a₃ * x₁ - W.a₁ * W.a₃ * x₂
        + W.a₁ * x₁ * y₁ - 2 * W.a₁ * x₂ * y₂ - W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂
        - 2 * W.a₂ * x₂ ^ 2 + W.a₃ * y₁ - 2 * W.a₃ * y₂ + W.a₄ * x₁ + W.a₆
        - x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 2 * x₂ ^ 3
        + y₁ ^ 2 - 2 * y₂ ^ 2)) * h₁
    + ((x₁ - x₂) ^ 2 *
      (-(W.a₁ ^ 2 * x₁ ^ 2) + W.a₁ ^ 2 * x₁ * x₂ - W.a₁ * W.a₃ * x₁ + W.a₁ * W.a₃ * x₂
        + W.a₁ * x₂ * y₂ - 4 * W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂ - W.a₂ * x₂ ^ 2
        + W.a₃ * y₂ - 2 * W.a₄ * x₁ + W.a₄ * x₂ - W.a₆
        - 4 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - x₂ ^ 3
        + y₂ ^ 2)) * h₂

end PrincipiaTractalis.SecantUniversal

#print axioms PrincipiaTractalis.SecantUniversal.addX_div
#print axioms PrincipiaTractalis.SecantUniversal.addX_add_addX_negY
#print axioms PrincipiaTractalis.SecantUniversal.addX_mul_addX_negY
