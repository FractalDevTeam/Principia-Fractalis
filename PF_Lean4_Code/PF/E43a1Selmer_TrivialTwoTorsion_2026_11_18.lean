import PF.E43a1Selmer_NoRationalRoot_2026_11_18
import PF.E43a1RankOne_r135
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# E_43a1 Selmer rank-1, brick 2 — trivial rational 2-torsion

**Headline.** For E_43a1 : `y² + y = x³ + x²`,

```
E43a1_two_torsion_trivial :
    ∀ P : E43a1.toAffine.Point, 2 • P = 0 → P = 0
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## The chain

Brick 1 (`PF.E43a1Selmer_NoRationalRoot_2026_11_18`) proved
`4x³ + 4x² + 1 ≠ 0` for every `x : ℚ`. This file plumbs that into the
group-theoretic 2-torsion statement using mathlib's `add_self_of_Y_ne`
/ `add_self_of_Y_eq` lemmas on `WeierstrassCurve.Affine.Point`.

For `E43a1 = ⟨0, 1, 1, 0, 0⟩` (long Weierstrass, same `(a₁, a₃) = (0, 1)`
as E_37a1), `negY x y = -y - 1`, so `2 • P = 0` for `P = some h` at
`(x, y)` forces `y = -1/2`. The Weierstrass equation then becomes
`1/4 - 1/2 = x³ + x²`, equivalently `4x³ + 4x² + 1 = 0`, which brick 1
rules out.

Parallel to E_37a1 brick 2 (`PF.E37a1Selmer_TrivialTwoTorsion_2026_11_18`).
-/

namespace PrincipiaTractalis.E43a1Selmer_TrivialTwoTorsion_2026_11_18

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.E43a1RankOne (E43a1)
open PrincipiaTractalis.E43a1Selmer_NoRationalRoot_2026_11_18
  (no_rational_root_4x3_plus_4x2_plus_1)

/-- **Brick 2 of the E_43a1 Selmer rank-1 attack.**
    The only rational 2-torsion point on E_43a1 : `y² + y = x³ + x²` is
    the point at infinity. -/
theorem E43a1_two_torsion_trivial :
    ∀ P : E43a1.toAffine.Point, 2 • P = 0 → P = 0 := by
  intro P hP
  rcases P with _ | @⟨x, y, h₁⟩
  · rfl
  · exfalso
    have h2 : (2 : ℕ) • (Point.some h₁ : E43a1.toAffine.Point) =
        Point.some h₁ + Point.some h₁ := two_nsmul _
    rw [h2] at hP
    by_cases hY : y = E43a1.toAffine.negY x y
    · -- y = -y - 1, so y = -1/2
      have hy_half : y = -(1/2 : ℚ) := by
        have h := hY
        simp only [WeierstrassCurve.Affine.negY, E43a1] at h
        linarith
      -- Equation y² + y = x³ + x²; at y = -1/2, 4x³ + 4x² + 1 = 0
      have hE := h₁.1
      rw [WeierstrassCurve.Affine.equation_iff] at hE
      simp only [E43a1] at hE
      rw [hy_half] at hE
      have hpoly : 4 * x ^ 3 + 4 * x ^ 2 + 1 = 0 := by linarith
      exact no_rational_root_4x3_plus_4x2_plus_1 x hpoly
    · have hne : Point.some h₁ + Point.some h₁ ≠ (0 : E43a1.toAffine.Point) := by
        rw [Point.add_self_of_Y_ne hY]
        exact Point.some_ne_zero _
      exact hne hP

#print axioms E43a1_two_torsion_trivial

end PrincipiaTractalis.E43a1Selmer_TrivialTwoTorsion_2026_11_18
