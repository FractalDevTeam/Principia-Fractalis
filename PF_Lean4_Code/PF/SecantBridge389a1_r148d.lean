/-
# PF.SecantBridge389a1_r148d

★★★ 2026-07-28 — r148d (W2d): THE SECANT BRIDGE ★★★

Connects mathlib's *actual* group law on `E389a1` to the bihomogeneous
addition forms of r148a.  For two rational affine points with distinct
x-coordinates, the x-coordinates of `P₁ + P₂` and `P₁ − P₂` are the two
roots of an explicit quadratic:

  `x(P₁+P₂) + x(P₁−P₂) = Sfnum(x₁,x₂) / (x₁−x₂)²`
  `x(P₁+P₂) · x(P₁−P₂) = Prnum(x₁,x₂) / (x₁−x₂)²`

with `Sfnum = 2x₁²x₂ + 2x₁x₂² + 4x₁x₂ − 4x₁ − 4x₂ + 1` and
`Prnum = x₁²x₂² + 4x₁x₂ − x₁ − x₂ + 3` — precisely the dehomogenizations
of r148a's `Sf` and `Pf`.

The y-elimination certificates were computed and verified to remainder
exactly `0` (`codex/W2_CERTIFICATES_389a1.md` §"SECANT BRIDGE"):

  * sum:     `N₃ + N₄ − Sfnum = 2·E₁ + 2·E₂`      (strikingly simple)
  * product: `N₃·N₄ − dd·Prnum = cP₁·E₁ + cP₂·E₂`  (cofactors below)

This is the stone that makes the quasi-parallelogram inequality (r148e) a
purely arithmetic assembly: heights of `x(P±Q)` are now controlled by
r148b's content bound and r148c's size bounds.

HONEST SCOPE.  Algebraic identities for the addition law only.  No height
inequality, no canonical-height statement, no rank claim.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.E389a1RankOne_r143

namespace PrincipiaTractalis.SecantBridge389a1

open PrincipiaTractalis.E389a1RankOne
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the symmetric-function numerators -/

/-- Numerator of `x(P₁+P₂) + x(P₁−P₂)`; the dehomogenization of r148a's `Sf`. -/
def Sfnum (x₁ x₂ : ℚ) : ℚ :=
  2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 + 4 * x₁ * x₂ - 4 * x₁ - 4 * x₂ + 1

/-- Numerator of `x(P₁+P₂) · x(P₁−P₂)`; the dehomogenization of r148a's `Pf`. -/
def Prnum (x₁ x₂ : ℚ) : ℚ :=
  x₁ ^ 2 * x₂ ^ 2 + 4 * x₁ * x₂ - x₁ - x₂ + 3

/-- `dd·x(P₁+P₂)`, the secant numerator. -/
def N3 (x₁ x₂ y₁ y₂ : ℚ) : ℚ :=
  (y₁ - y₂) ^ 2 - (1 + x₁ + x₂) * (x₁ - x₂) ^ 2

/-- `dd·x(P₁−P₂)`, the "co-secant" numerator (slope through `−P₂`). -/
def N4 (x₁ x₂ y₁ y₂ : ℚ) : ℚ :=
  (y₁ + y₂ + 1) ^ 2 - (1 + x₁ + x₂) * (x₁ - x₂) ^ 2

/-! ## §2 — the y-elimination certificates (sympy-verified, remainder 0) -/

/-- **The sum certificate.**  On-curve, `N₃ + N₄ = Sfnum` — the `y`'s
cancel completely, at the cost of only `2·E₁ + 2·E₂`. -/
theorem N3_add_N4 {x₁ x₂ y₁ y₂ : ℚ}
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 + x₁ ^ 2 - 2 * x₁)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 + x₂ ^ 2 - 2 * x₂) :
    N3 x₁ x₂ y₁ y₂ + N4 x₁ x₂ y₁ y₂ = Sfnum x₁ x₂ := by
  simp only [N3, N4, Sfnum]
  linear_combination 2 * hE₁ + 2 * hE₂

/-- **The product certificate.**  On-curve,
`N₃·N₄ = (x₁−x₂)²·Prnum`. -/
theorem N3_mul_N4 {x₁ x₂ y₁ y₂ : ℚ}
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 + x₁ ^ 2 - 2 * x₁)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 + x₂ ^ 2 - 2 * x₂) :
    N3 x₁ x₂ y₁ y₂ * N4 x₁ x₂ y₁ y₂ = (x₁ - x₂) ^ 2 * Prnum x₁ x₂ := by
  simp only [N3, N4, Prnum]
  linear_combination
    (-x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ - x₁ ^ 2 + 2 * x₁ * x₂ ^ 2 + 4 * x₁ * x₂
        - 2 * x₁ - 2 * x₂ ^ 3 - 2 * x₂ ^ 2 + y₁ ^ 2 + y₁ - 2 * y₂ ^ 2
        - 2 * y₂) * hE₁
      + (-4 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ - 4 * x₁ ^ 2 + 2 * x₁ * x₂ ^ 2
        + 4 * x₁ * x₂ + 4 * x₁ - x₂ ^ 3 - x₂ ^ 2 - 2 * x₂ + y₂ ^ 2
        + y₂) * hE₂

/-! ## §3 — the mathlib bridge: `addX ∘ slope` in secant position -/

/-- The x-coordinate produced by mathlib's secant construction. -/
noncomputable def xAdd (x₁ x₂ y₁ y₂ : ℚ) : ℚ :=
  E389a1.toAffine.addX x₁ x₂ (E389a1.toAffine.slope x₁ x₂ y₁ y₂)

/-- In secant position, mathlib's `addX ∘ slope` is `N₃/(x₁−x₂)²`. -/
theorem xAdd_eq (x₁ x₂ y₁ y₂ : ℚ) (hx : x₁ ≠ x₂) :
    xAdd x₁ x₂ y₁ y₂ = N3 x₁ x₂ y₁ y₂ / (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  simp only [xAdd, N3, Affine.slope_of_X_ne hx, Affine.addX, E389a1_a₁, E389a1_a₂]
  field_simp
  ring

/-- Replacing `y₂` by `negY x₂ y₂ = −y₂ − 1` gives `N₄/(x₁−x₂)²` — this is
the x-coordinate of `P₁ − P₂`. -/
theorem xAdd_negY_eq (x₁ x₂ y₁ y₂ : ℚ) (hx : x₁ ≠ x₂) :
    xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂)
      = N4 x₁ x₂ y₁ y₂ / (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hneg : E389a1.toAffine.negY x₂ y₂ = -y₂ - 1 := negY_eq x₂ y₂
  simp only [xAdd, N4, hneg, Affine.slope_of_X_ne hx, Affine.addX,
    E389a1_a₁, E389a1_a₂]
  field_simp
  ring

/-! ## §4 — the capstones: the addition quadratic -/

/-- **★ SUM ★** — `x(P₁+P₂) + x(P₁−P₂) = Sfnum/(x₁−x₂)²`. -/
theorem xAdd_sum {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 + x₁ ^ 2 - 2 * x₁)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 + x₂ ^ 2 - 2 * x₂) :
    xAdd x₁ x₂ y₁ y₂ + xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂)
      = Sfnum x₁ x₂ / (x₁ - x₂) ^ 2 := by
  rw [xAdd_eq x₁ x₂ y₁ y₂ hx, xAdd_negY_eq x₁ x₂ y₁ y₂ hx, div_add_div_same,
    N3_add_N4 hE₁ hE₂]

/-- **★ PRODUCT ★** — `x(P₁+P₂) · x(P₁−P₂) = Prnum/(x₁−x₂)²`. -/
theorem xAdd_prod {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 + x₁ ^ 2 - 2 * x₁)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 + x₂ ^ 2 - 2 * x₂) :
    xAdd x₁ x₂ y₁ y₂ * xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂)
      = Prnum x₁ x₂ / (x₁ - x₂) ^ 2 := by
  have hd : ((x₁ - x₂) ^ 2 : ℚ) ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
  rw [xAdd_eq x₁ x₂ y₁ y₂ hx, xAdd_negY_eq x₁ x₂ y₁ y₂ hx, div_mul_div_comm,
    N3_mul_N4 hE₁ hE₂]
  rw [div_eq_div_iff (by positivity) hd]
  ring

/-- **The addition quadratic.**  `x(P₁+P₂)` and `x(P₁−P₂)` are exactly the
two roots of `T² − (Sfnum/dd)·T + (Prnum/dd)`.  This is the interface the
quasi-parallelogram inequality consumes: the coefficients are r148a's
forms, whose content is bounded by r148b (`∣ 389⁴`) and whose size is
bounded by r148c (`≤ 17·H₁²H₂²`). -/
theorem addition_quadratic {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 + x₁ ^ 2 - 2 * x₁)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 + x₂ ^ 2 - 2 * x₂) :
    (xAdd x₁ x₂ y₁ y₂ + xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂)
        = Sfnum x₁ x₂ / (x₁ - x₂) ^ 2) ∧
    (xAdd x₁ x₂ y₁ y₂ * xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂)
        = Prnum x₁ x₂ / (x₁ - x₂) ^ 2) :=
  ⟨xAdd_sum hx hE₁ hE₂, xAdd_prod hx hE₁ hE₂⟩

/-! ## §5 — tie to the homogeneous forms of r148a

Dehomogenization sanity: with `x = a/b`, `Sfnum` and `Prnum` are the
`b₁²b₂²`-scaled versions of r148a's `Sf`, `Pf`. -/

theorem Sfnum_homog (a₁ b₁ a₂ b₂ : ℚ) (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0) :
    b₁ ^ 2 * b₂ ^ 2 * Sfnum (a₁ / b₁) (a₂ / b₂)
      = 2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁ + 4 * a₁ * a₂ * b₁ * b₂
        - 4 * a₁ * b₁ * b₂ ^ 2 - 4 * a₂ * b₁ ^ 2 * b₂ + b₁ ^ 2 * b₂ ^ 2 := by
  simp only [Sfnum]
  field_simp

theorem Prnum_homog (a₁ b₁ a₂ b₂ : ℚ) (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0) :
    b₁ ^ 2 * b₂ ^ 2 * Prnum (a₁ / b₁) (a₂ / b₂)
      = a₁ ^ 2 * a₂ ^ 2 + 4 * a₁ * a₂ * b₁ * b₂ - a₁ * b₁ * b₂ ^ 2
        - a₂ * b₁ ^ 2 * b₂ + 3 * b₁ ^ 2 * b₂ ^ 2 := by
  simp only [Prnum]
  field_simp

end PrincipiaTractalis.SecantBridge389a1

#print axioms PrincipiaTractalis.SecantBridge389a1.N3_add_N4
#print axioms PrincipiaTractalis.SecantBridge389a1.N3_mul_N4
#print axioms PrincipiaTractalis.SecantBridge389a1.xAdd_eq
#print axioms PrincipiaTractalis.SecantBridge389a1.xAdd_sum
#print axioms PrincipiaTractalis.SecantBridge389a1.xAdd_prod
#print axioms PrincipiaTractalis.SecantBridge389a1.addition_quadratic
#print axioms PrincipiaTractalis.SecantBridge389a1.Sfnum_homog
#print axioms PrincipiaTractalis.SecantBridge389a1.Prnum_homog
