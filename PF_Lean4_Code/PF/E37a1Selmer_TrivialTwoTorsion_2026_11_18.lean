import PF.E37a1Selmer_NoRationalRoot_2026_11_18
import PF.DuplicationFormula37a1_r132
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# E_37a1 Selmer rank-1, brick 2 — trivial rational 2-torsion

**Headline.** For E_37a1 : `y² + y = x³ - x`,

```
E37a1_two_torsion_trivial :
    ∀ P : E37a1.toAffine.Point, 2 • P = 0 → P = 0
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## The chain

Brick 1 (`PF.E37a1Selmer_NoRationalRoot_2026_11_18`) proved
`4x³ - 4x + 1 ≠ 0` for every `x : ℚ`. This file plumbs that into the
group-theoretic 2-torsion statement using mathlib's `add_self_of_Y_ne` /
`add_self_of_Y_eq` lemmas on `WeierstrassCurve.Affine.Point`.

For `E37a1 = ⟨0, 0, 1, -1, 0⟩` (long Weierstrass), `negY x y = -y - 1`,
so `2 • P = 0` for `P = some (h : Nonsingular x y)` forces `y = -y - 1`,
i.e. `y = -1/2`. The Weierstrass equation then becomes
`1/4 - 1/2 = x³ - x`, equivalently `4x³ - 4x + 1 = 0`, which brick 1
rules out.

## Next brick (3)

With trivial 2-torsion in hand, the quotient `E_37a1(ℚ) / 2·E_37a1(ℚ)`
has order `2^rank` (Mordell–Weil). The Selmer rank-1 attack then
reduces to a **Selmer upper bound of 2** on `Sel_2(E_37a1/ℚ)`, which
combined with `E37a1_rank_ge_one` (already in the corpus) closes
`rank = 1` exactly.
-/

namespace PrincipiaTractalis.E37a1Selmer_TrivialTwoTorsion_2026_11_18

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.DuplicationFormula37a1 (E37a1)
open PrincipiaTractalis.E37a1Selmer_NoRationalRoot_2026_11_18
  (no_rational_root_4x3_minus_4x_plus_1)

/-- **Brick 2 of the E_37a1 Selmer rank-1 attack.**
    The only rational 2-torsion point on E_37a1 : `y² + y = x³ - x` is
    the point at infinity. -/
theorem E37a1_two_torsion_trivial :
    ∀ P : E37a1.toAffine.Point, 2 • P = 0 → P = 0 := by
  intro P hP
  rcases P with _ | @⟨x, y, h₁⟩
  · rfl
  · exfalso
    -- 2 • some h₁ = some h₁ + some h₁.
    have h2 : (2 : ℕ) • (Point.some h₁ : E37a1.toAffine.Point) =
        Point.some h₁ + Point.some h₁ := two_nsmul _
    rw [h2] at hP
    -- Case: y = negY x y vs y ≠ negY x y.
    by_cases hY : y = E37a1.toAffine.negY x y
    · -- y = -y - 1, so 2y = -1, so y = -1/2.
      have hy_half : y = -(1/2 : ℚ) := by
        have h := hY
        simp only [WeierstrassCurve.Affine.negY, E37a1] at h
        linarith
      -- Equation: y² + y = x³ - x.
      have hE := h₁.1
      rw [WeierstrassCurve.Affine.equation_iff] at hE
      simp only [E37a1] at hE
      rw [hy_half] at hE
      -- Rearrange to 4x³ - 4x + 1 = 0.
      have hpoly : 4 * x ^ 3 - 4 * x + 1 = 0 := by linarith
      exact no_rational_root_4x3_minus_4x_plus_1 x hpoly
    · -- y ≠ negY x y → some h₁ + some h₁ = some _ ≠ 0, contradiction with hP.
      have hne : Point.some h₁ + Point.some h₁ ≠ (0 : E37a1.toAffine.Point) := by
        rw [Point.add_self_of_Y_ne hY]
        exact Point.some_ne_zero _
      exact hne hP

#print axioms E37a1_two_torsion_trivial

end PrincipiaTractalis.E37a1Selmer_TrivialTwoTorsion_2026_11_18
