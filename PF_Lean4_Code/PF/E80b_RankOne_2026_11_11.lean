/-
# PF.E80b_RankOne_2026_11_11 — curve facts for y² = x³ − 25x

The per-curve obligations for the congruent-number curve
`E_80b : y² = x³ − 25x`, which has LMFDB rank 1 and FULL rational
2-torsion `{O, (0, 0), (5, 0), (−5, 0)}` (so this is the n = 5 congruent
number curve). The non-torsion generator is `(−4, 6)`.

**Delta from the 91a1/131a1/141a1 scaffolds.** Those curves have NO
rational 2-torsion, so the Ψ denominator has no rational root and
`Psi_ne_zero_at` holds at EVERY rational. Here the Ψ denominator
factors as

  `Psi 0 (-50) 0 X Y = 4·X·Y·(X − 5Y)·(X + 5Y)`

which vanishes at `x ∈ {0, 5, -5}` — exactly the x-coordinates of the
three rational 2-torsion points. So the per-point route of E_102a1
applies, specialised to this full-rational-2-torsion setting; the
curve-specific lemma is the straightforward

  `x ∉ {0, 5, -5} ⟹ 2 • Point.some h ≠ 0`.

which uses only that y = negY → y = 0 (since `a₁ = a₃ = 0`), and that
the curve equation then forces `x · (x - 5) · (x + 5) = 0`.

**What this file delivers, axiom-free, kernel-only:**
  * b-invariants of E_80b: `(b₂, b₄, b₆, b₈) = (0, -50, 0, -625)`.
  * Discriminant nonzero: `Disc 0 (-50) 0 (-625) ≠ 0`.
  * r174 Weierstrass relation `4·b₈ = b₂·b₆ − b₄²`.
  * `Psi_factorisation`: `Psi 0 (-50) 0 X Y = 4·X·Y·(X - 5·Y)·(X + 5·Y)`.
  * `Psi_ne_zero_at_not_torsion`: Ψ ≠ 0 at `(x.num, x.den)` for every
    rational `x ∉ {0, 5, -5}`.
  * `two_smul_ne_zero_of_x_not_torsion`: the curve-specific 2-torsion
    lemma.

**What this file does NOT establish:** the `rank_ge_one` theorem itself
— that requires the orbit computation and goes in the companion
capstone file.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.DuplicationBezoutUniversal_r174
import PF.DuplicationHeightUniversal_r176
import PF.PointParallelogramUniversal_r199
import PF.CanheightParallelogramUniversal_r200
import Mathlib.Tactic.NormNum

namespace PrincipiaTractalis
namespace E80b_RankOne20261111

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal

/-! ## §1 — the curve -/

/-- **E_80b : y² = x³ − 25x.**  LMFDB-like label; this is the n = 5
congruent-number curve (5 is a congruent number, witnessed by the
right triangle `(3/2, 20/3, 41/6)`). Full rational 2-torsion. -/
def E_80b : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -25
  a₆ := 0

/-! ## §2 — the b-invariants, in the integer form the universal layers want -/

theorem b₂_eq : (E_80b.toAffine).b₂ = ((0 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₂, E_80b]

theorem b₄_eq : (E_80b.toAffine).b₄ = ((-50 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₄, E_80b]
  norm_num

theorem b₆_eq : (E_80b.toAffine).b₆ = ((0 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₆, E_80b]

theorem b₈_eq : (E_80b.toAffine).b₈ = ((-625 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₈, E_80b]
  norm_num

/-! ## §3 — the Weierstrass relation and nonzero discriminant -/

/-- r174's `hrel` hypothesis `4·b₈ = b₂·b₆ − b₄²`. For E_80b:
`4·(-625) = 0·0 − (-50)² = -2500`. -/
theorem hrel80b : 4 * (-625 : ℤ) = 0 * 0 - (-50) ^ 2 := by decide

/-- The discriminant of E_80b at `(0, -50, 0, -625)` is nonzero. -/
theorem hΔ80b : Disc 0 (-50) 0 (-625) ≠ 0 := by decide

/-! ## §4 — the Ψ factorisation

On E_80b, `Ψ` splits into FOUR linear factors (each 2-torsion x-value):

  `Psi 0 (-50) 0 X Y = 4·X³·Y − 100·X·Y³ = 4·X·Y·(X² − 25·Y²)`
                    `= 4·X·Y·(X − 5·Y)·(X + 5·Y)`.
-/

theorem Psi_factorisation (X Y : ℤ) :
    Psi 0 (-50) 0 X Y = 4 * X * Y * (X - 5 * Y) * (X + 5 * Y) := by
  simp [Psi]
  ring

/-- **`Ψ ≠ 0` at every rational `x` whose numerator is not 0, ±5·(denom).**
Equivalent to `x ∉ {0, 5, -5}`. -/
theorem Psi_ne_zero_at_not_torsion (x : ℚ)
    (hx0 : x ≠ 0) (hx5 : x ≠ 5) (hxn5 : x ≠ -5) :
    Psi 0 (-50) 0 x.num (x.den : ℤ) ≠ 0 := by
  rw [Psi_factorisation]
  have hden : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  have hnum : x.num ≠ 0 := Rat.num_ne_zero.mpr hx0
  -- Show the two linear factors X ∓ 5Y are nonzero at (x.num, x.den).
  have hden_q : (x.den : ℚ) > 0 := by exact_mod_cast x.pos
  have hden_ne_q : (x.den : ℚ) ≠ 0 := ne_of_gt hden_q
  have h5 : x.num - 5 * (x.den : ℤ) ≠ 0 := by
    intro h
    apply hx5
    -- x = x.num / x.den; if x.num = 5·x.den then x = 5.
    have h1 : (x.num : ℚ) = 5 * (x.den : ℚ) := by
      have : ((x.num - 5 * (x.den : ℤ) : ℤ) : ℚ) = 0 := by exact_mod_cast h
      push_cast at this
      linarith
    have h2 : (x.num : ℚ) / (x.den : ℚ) = x := Rat.num_div_den x
    rw [h1] at h2
    field_simp at h2
    linarith
  have hn5 : x.num + 5 * (x.den : ℤ) ≠ 0 := by
    intro h
    apply hxn5
    have h1 : (x.num : ℚ) = -(5 * (x.den : ℚ)) := by
      have : ((x.num + 5 * (x.den : ℤ) : ℤ) : ℚ) = 0 := by exact_mod_cast h
      push_cast at this
      linarith
    have h2 : (x.num : ℚ) / (x.den : ℚ) = x := Rat.num_div_den x
    rw [h1] at h2
    field_simp at h2
    linarith
  -- Now product of four nonzero factors is nonzero.
  intro hprod
  have h4 : (4 : ℤ) ≠ 0 := by decide
  rcases mul_eq_zero.mp hprod with hab | h3
  · rcases mul_eq_zero.mp hab with hac | h2
    · rcases mul_eq_zero.mp hac with ha | hb
      · rcases mul_eq_zero.mp ha with h4z | hnz
        · exact h4 h4z
        · exact hnum hnz
      · exact hden hb
    · exact h5 h2
  · exact hn5 h3

/-! ## §5 — the curve-specific 2-torsion lemma

On E_80b (short-form `y² = x³ − 25x`, `a₁ = a₃ = 0`),
`negY x y = -y - 0·x - 0 = -y`. So `y = negY x y ⟺ y = -y ⟺ y = 0`.
The curve equation at `y = 0` gives `0 = x³ − 25x = x·(x − 5)·(x + 5)`,
whose rational roots are exactly `{0, 5, -5}`.
-/

/-- `negY` on E_80b at `(x, y)` is `-y`. -/
theorem negY_E80b (x y : ℚ) : E_80b.toAffine.negY x y = -y := by
  simp [Affine.negY, E_80b]

/-- **Curve-specific 2-torsion lemma.** If `(x, y)` is a nonsingular
rational point of E_80b with `x ∉ {0, 5, -5}`, then `2 • Point.some h ≠ 0`. -/
theorem two_smul_ne_zero_of_x_not_torsion {x y : ℚ}
    (h : E_80b.toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) (hx5 : x ≠ 5) (hxn5 : x ≠ -5) :
    (2 : ℕ) • Point.some h ≠ 0 := by
  intro h2
  rw [two_nsmul] at h2
  by_cases hy : y = E_80b.toAffine.negY x y
  · -- y = -y ⟹ y = 0.
    rw [negY_E80b] at hy
    have hy0 : y = 0 := by linarith
    -- Plug y = 0 into the curve: 0 = x³ - 25x = x(x - 5)(x + 5).
    have hEq : E_80b.toAffine.Equation x y := h.left
    rw [WeierstrassCurve.Affine.equation_iff] at hEq
    simp [E_80b, hy0] at hEq
    -- hEq : -x³ + 25x = 0, i.e. x³ = 25x, so x(x - 5)(x + 5) = 0.
    have hfactor : x * (x - 5) * (x + 5) = 0 := by linarith
    rcases mul_eq_zero.mp hfactor with hab | hc
    · rcases mul_eq_zero.mp hab with ha | hb
      · exact hx0 ha
      · exact hx5 (by linarith)
    · exact hxn5 (by linarith)
  · rw [Point.add_self_of_Y_ne hy] at h2
    exact some_ne_zero _ h2

end E80b_RankOne20261111
end PrincipiaTractalis

#print axioms PrincipiaTractalis.E80b_RankOne20261111.b₂_eq
#print axioms PrincipiaTractalis.E80b_RankOne20261111.b₈_eq
#print axioms PrincipiaTractalis.E80b_RankOne20261111.hrel80b
#print axioms PrincipiaTractalis.E80b_RankOne20261111.hΔ80b
#print axioms PrincipiaTractalis.E80b_RankOne20261111.Psi_factorisation
#print axioms PrincipiaTractalis.E80b_RankOne20261111.Psi_ne_zero_at_not_torsion
#print axioms PrincipiaTractalis.E80b_RankOne20261111.negY_E80b
#print axioms PrincipiaTractalis.E80b_RankOne20261111.two_smul_ne_zero_of_x_not_torsion
