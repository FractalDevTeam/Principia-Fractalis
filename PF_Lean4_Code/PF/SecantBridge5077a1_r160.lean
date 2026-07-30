/-
# PF.SecantBridge5077a1_r160

★★★ 2026-07-30 — r160: THE SECANT BRIDGE FOR 5077a1 ★★★

Connects mathlib's *actual* group law on `E5077a1` to the bihomogeneous
addition forms of r157.  For two rational affine points with distinct
x-coordinates,

  `x(P₁+P₂) + x(P₁−P₂) = Sfnum(x₁,x₂) / (x₁−x₂)²`
  `x(P₁+P₂) · x(P₁−P₂) = Prnum(x₁,x₂) / (x₁−x₂)²`

with `Sfnum = 2x₁²x₂ + 2x₁x₂² − 14x₁ − 14x₂ + 25` and
`Prnum = x₁²x₂² + 14x₁x₂ − 25x₁ − 25x₂ + 49` — the dehomogenizations of
r157's `Sf` and `Pf`.

Since `a₁ = a₂ = 0` on this curve, `addX x₁ x₂ λ = λ² − x₁ − x₂`, so the
secant numerators carry `(x₁+x₂)` rather than 389a1's `(1+x₁+x₂)`.

## The y-elimination certificates

Both computed by reduction modulo `(E₁, E₂)` and verified to remainder
exactly `0`, then cross-checked numerically: `N₃/dd` and `N₄/dd` agree with
the group law's `x(P₁±P₂)` in exact rational arithmetic on all ten distinct
pairs from `{P, 2P, 3P, 4P, 5P}`, `P = (−2,3)`.

  * sum:     `N₃ + N₄ − Sfnum = 2·E₁ + 2·E₂`
  * product: `N₃·N₄ − dd·Prnum = cP₁·E₁ + cP₂·E₂`

The sum cofactors are `2, 2` — **identical to 389a1's**, which is not an
accident: `N₃ + N₄ = 2(y₁²+y₁) + 2(y₂²+y₂) + 1 − 2(x₁+x₂)dd` on any curve
with `a₁ = 0`, `a₃ = 1`, so the `y`'s always cancel at the cost of exactly
`2E₁ + 2E₂`.  Only the product cofactors are curve-specific.

This is the stone that makes the quasi-parallelogram inequality a purely
arithmetic assembly: heights of `x(P±Q)` are now controlled by r158's
content bound (`∣ 5⁴·5077⁴`) and r159's size bounds (`≤ 114·H₁²H₂²`).

HONEST SCOPE.  Algebraic identities for the addition law only.  No height
inequality, no canonical-height statement, no parallelogram law, no rank
claim.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-30.
-/
import PF.E5077a1RankOne_r144

namespace PrincipiaTractalis.SecantBridge5077a1

open PrincipiaTractalis.E5077a1RankOne
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the symmetric-function numerators -/

/-- Numerator of `x(P₁+P₂) + x(P₁−P₂)`; the dehomogenization of r157's `Sf`. -/
def Sfnum (x₁ x₂ : ℚ) : ℚ :=
  2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 14 * x₁ - 14 * x₂ + 25

/-- Numerator of `x(P₁+P₂) · x(P₁−P₂)`; the dehomogenization of r157's `Pf`. -/
def Prnum (x₁ x₂ : ℚ) : ℚ :=
  x₁ ^ 2 * x₂ ^ 2 + 14 * x₁ * x₂ - 25 * x₁ - 25 * x₂ + 49

/-- `dd·x(P₁+P₂)`, the secant numerator.  No `1 +` here: `a₂ = 0`. -/
def N3 (x₁ x₂ y₁ y₂ : ℚ) : ℚ :=
  (y₁ - y₂) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2

/-- `dd·x(P₁−P₂)`, the co-secant numerator (slope through `−P₂`). -/
def N4 (x₁ x₂ y₁ y₂ : ℚ) : ℚ :=
  (y₁ + y₂ + 1) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2

/-! ## §2 — the y-elimination certificates (verified, remainder 0) -/

/-- **The sum certificate.**  On-curve, `N₃ + N₄ = Sfnum`; the `y`'s cancel
at the cost of only `2·E₁ + 2·E₂`. -/
theorem N3_add_N4 {x₁ x₂ y₁ y₂ : ℚ}
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 - 7 * x₁ + 6)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 - 7 * x₂ + 6) :
    N3 x₁ x₂ y₁ y₂ + N4 x₁ x₂ y₁ y₂ = Sfnum x₁ x₂ := by
  simp only [N3, N4, Sfnum]
  linear_combination 2 * hE₁ + 2 * hE₂

/-- **The product certificate.**  On-curve, `N₃·N₄ = (x₁−x₂)²·Prnum`. -/
theorem N3_mul_N4 {x₁ x₂ y₁ y₂ : ℚ}
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 - 7 * x₁ + 6)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 - 7 * x₂ + 6) :
    N3 x₁ x₂ y₁ y₂ * N4 x₁ x₂ y₁ y₂ = (x₁ - x₂) ^ 2 * Prnum x₁ x₂ := by
  simp only [N3, N4, Prnum]
  linear_combination
    (-x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 7 * x₁ - 2 * x₂ ^ 3
        + y₁ ^ 2 + y₁ - 2 * y₂ ^ 2 - 2 * y₂ + 6) * hE₁
      + (-4 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 + 14 * x₁ - x₂ ^ 3
        - 7 * x₂ + y₂ ^ 2 + y₂ - 6) * hE₂

/-! ## §3 — the mathlib bridge: `addX ∘ slope` in secant position -/

/-- The x-coordinate produced by mathlib's secant construction. -/
noncomputable def xAdd (x₁ x₂ y₁ y₂ : ℚ) : ℚ :=
  E5077a1.toAffine.addX x₁ x₂ (E5077a1.toAffine.slope x₁ x₂ y₁ y₂)

/-- In secant position, mathlib's `addX ∘ slope` is `N₃/(x₁−x₂)²`. -/
theorem xAdd_eq (x₁ x₂ y₁ y₂ : ℚ) (hx : x₁ ≠ x₂) :
    xAdd x₁ x₂ y₁ y₂ = N3 x₁ x₂ y₁ y₂ / (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  simp only [xAdd, N3, Affine.slope_of_X_ne hx, Affine.addX,
    E5077a1_a₁, E5077a1_a₂]
  field_simp
  ring

/-- Replacing `y₂` by `negY x₂ y₂ = −y₂ − 1` gives `N₄/(x₁−x₂)²` — the
x-coordinate of `P₁ − P₂`. -/
theorem xAdd_negY_eq (x₁ x₂ y₁ y₂ : ℚ) (hx : x₁ ≠ x₂) :
    xAdd x₁ x₂ y₁ (E5077a1.toAffine.negY x₂ y₂)
      = N4 x₁ x₂ y₁ y₂ / (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hneg : E5077a1.toAffine.negY x₂ y₂ = -y₂ - 1 := negY_eq x₂ y₂
  simp only [xAdd, N4, hneg, Affine.slope_of_X_ne hx, Affine.addX,
    E5077a1_a₁, E5077a1_a₂]
  field_simp
  ring

/-! ## §4 — the capstones: the addition quadratic -/

/-- **★ SUM ★** — `x(P₁+P₂) + x(P₁−P₂) = Sfnum/(x₁−x₂)²`. -/
theorem xAdd_sum {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 - 7 * x₁ + 6)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 - 7 * x₂ + 6) :
    xAdd x₁ x₂ y₁ y₂ + xAdd x₁ x₂ y₁ (E5077a1.toAffine.negY x₂ y₂)
      = Sfnum x₁ x₂ / (x₁ - x₂) ^ 2 := by
  rw [xAdd_eq x₁ x₂ y₁ y₂ hx, xAdd_negY_eq x₁ x₂ y₁ y₂ hx, div_add_div_same,
    N3_add_N4 hE₁ hE₂]

/-- **★ PRODUCT ★** — `x(P₁+P₂) · x(P₁−P₂) = Prnum/(x₁−x₂)²`. -/
theorem xAdd_prod {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 - 7 * x₁ + 6)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 - 7 * x₂ + 6) :
    xAdd x₁ x₂ y₁ y₂ * xAdd x₁ x₂ y₁ (E5077a1.toAffine.negY x₂ y₂)
      = Prnum x₁ x₂ / (x₁ - x₂) ^ 2 := by
  have hd : ((x₁ - x₂) ^ 2 : ℚ) ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
  rw [xAdd_eq x₁ x₂ y₁ y₂ hx, xAdd_negY_eq x₁ x₂ y₁ y₂ hx, div_mul_div_comm,
    N3_mul_N4 hE₁ hE₂]
  rw [div_eq_div_iff (by positivity) hd]
  ring

/-- **The addition quadratic.**  `x(P₁+P₂)` and `x(P₁−P₂)` are exactly the
two roots of `T² − (Sfnum/dd)·T + (Prnum/dd)`.  This is the interface the
quasi-parallelogram inequality consumes: the coefficients are r157's forms,
whose content is bounded by r158 (`∣ 5⁴·5077⁴`) and whose size is bounded by
r159 (`≤ 114·H₁²H₂²`). -/
theorem addition_quadratic {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 - 7 * x₁ + 6)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 - 7 * x₂ + 6) :
    (xAdd x₁ x₂ y₁ y₂ + xAdd x₁ x₂ y₁ (E5077a1.toAffine.negY x₂ y₂)
        = Sfnum x₁ x₂ / (x₁ - x₂) ^ 2) ∧
    (xAdd x₁ x₂ y₁ y₂ * xAdd x₁ x₂ y₁ (E5077a1.toAffine.negY x₂ y₂)
        = Prnum x₁ x₂ / (x₁ - x₂) ^ 2) :=
  ⟨xAdd_sum hx hE₁ hE₂, xAdd_prod hx hE₁ hE₂⟩

/-! ## §5 — tie to the homogeneous forms of r157

Dehomogenization sanity: with `x = a/b`, `Sfnum` and `Prnum` are the
`b₁²b₂²`-scaled versions of r157's `Sf`, `Pf`. -/

theorem Sfnum_homog (a₁ b₁ a₂ b₂ : ℚ) (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0) :
    b₁ ^ 2 * b₂ ^ 2 * Sfnum (a₁ / b₁) (a₂ / b₂)
      = 2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁ - 14 * a₁ * b₁ * b₂ ^ 2
        - 14 * a₂ * b₁ ^ 2 * b₂ + 25 * b₁ ^ 2 * b₂ ^ 2 := by
  simp only [Sfnum]
  field_simp

theorem Prnum_homog (a₁ b₁ a₂ b₂ : ℚ) (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0) :
    b₁ ^ 2 * b₂ ^ 2 * Prnum (a₁ / b₁) (a₂ / b₂)
      = a₁ ^ 2 * a₂ ^ 2 + 14 * a₁ * a₂ * b₁ * b₂ - 25 * a₁ * b₁ * b₂ ^ 2
        - 25 * a₂ * b₁ ^ 2 * b₂ + 49 * b₁ ^ 2 * b₂ ^ 2 := by
  simp only [Prnum]
  field_simp

end PrincipiaTractalis.SecantBridge5077a1

#print axioms PrincipiaTractalis.SecantBridge5077a1.N3_add_N4
#print axioms PrincipiaTractalis.SecantBridge5077a1.N3_mul_N4
#print axioms PrincipiaTractalis.SecantBridge5077a1.xAdd_eq
#print axioms PrincipiaTractalis.SecantBridge5077a1.xAdd_negY_eq
#print axioms PrincipiaTractalis.SecantBridge5077a1.xAdd_sum
#print axioms PrincipiaTractalis.SecantBridge5077a1.xAdd_prod
#print axioms PrincipiaTractalis.SecantBridge5077a1.addition_quadratic
#print axioms PrincipiaTractalis.SecantBridge5077a1.Sfnum_homog
#print axioms PrincipiaTractalis.SecantBridge5077a1.Prnum_homog
