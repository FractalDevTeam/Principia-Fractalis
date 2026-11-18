import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
# E_37a1 Selmer rank-1, brick 5 — no rational root of the 3-division polynomial

## Context

For E_37a1 : `y² + y = x³ - x`, the 3-division polynomial is

    `ψ₃(x) = 3x⁴ + b₂ x³ + 3 b₄ x² + 3 b₆ x + b₈`
           `= 3x⁴ - 6 x² + 3 x - 1`

with b-invariants `(b₂, b₄, b₆, b₈) = (0, -2, 1, -1)`. Rational
3-torsion points of E_37a1 must have x-coordinate a rational root of
`ψ₃`. This file rules out every such root, so (modulo the standard
division-polynomial/torsion connection, which is Weierstrass
infrastructure) E_37a1 has no rational 3-torsion.

Chaining this with brick 4 (trivial 2^n-torsion) and the standard
Mazur-theorem classification would show the whole torsion subgroup
of E_37a1(ℚ) is trivial.

## Theorem

```
no_rational_root_3x4_minus_6x2_plus_3x_minus_1 :
    ∀ x : ℚ, 3 * x^4 - 6 * x^2 + 3 * x - 1 ≠ 0
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Proof

Clear denominators: writing `x = a/b` with `gcd(a, b) = 1`, `b > 0`,
the hypothesis becomes `3a⁴ - 6a²b² + 3ab³ - b⁴ = 0`. Mod-3 analysis:
`b⁴ = 3a⁴ - 6a²b² + 3ab³ = 3·(a⁴ - 2a²b² + ab³)`, so `3 ∣ b⁴`, hence
`3 ∣ b` (since `3` is prime). Write `b = 3c` and substitute:
`81c⁴ = 3a⁴ - 54a²c² + 81ac³`, divide by `3`: `27c⁴ = a⁴ - 18a²c² + 27ac³`,
so `a⁴ = 27c⁴ + 18a²c² - 27ac³ = 3·(9c⁴ + 6a²c² - 9ac³)`, hence `3 ∣ a⁴`,
and `3 ∣ a`. But `gcd(a, b) = 1` with `3 ∣ b` forces `3 ∤ a`.
Contradiction.
-/

namespace PrincipiaTractalis.E37a1Selmer_NoRationalRoot3Div_2026_11_18

/-- The integer `3` is prime. -/
private theorem three_prime : Prime (3 : ℤ) := Int.prime_three

/-- **Brick 5 of the E_37a1 Selmer rank-1 attack.**
The 3-division polynomial of E_37a1 has no rational root. -/
theorem no_rational_root_3x4_minus_6x2_plus_3x_minus_1 :
    ∀ x : ℚ, 3 * x ^ 4 - 6 * x ^ 2 + 3 * x - 1 ≠ 0 := by
  intro x hx
  set a : ℤ := x.num with ha_def
  set b : ℤ := (x.den : ℤ) with hb_def
  have hb_pos : 0 < b := by
    simp only [hb_def]
    exact_mod_cast x.pos
  have hb_ne : b ≠ 0 := hb_pos.ne'
  have hb_ne_cast : (b : ℚ) ≠ 0 := by exact_mod_cast hb_ne
  -- Integer form of the equation.
  have hab : 3 * a ^ 4 - 6 * a ^ 2 * b ^ 2 + 3 * a * b ^ 3 - b ^ 4 = 0 := by
    have hx_eq : (a : ℚ) = x * (b : ℚ) := by
      simp only [ha_def, hb_def]
      have h := Rat.num_div_den x
      field_simp at h
      push_cast
      linarith
    have hcast :
        3 * ((a : ℚ))^4 - 6 * (a : ℚ)^2 * (b : ℚ)^2 + 3 * (a : ℚ) * (b : ℚ)^3 - (b : ℚ)^4 = 0 := by
      calc 3 * ((a : ℚ))^4 - 6 * (a : ℚ)^2 * (b : ℚ)^2
              + 3 * (a : ℚ) * (b : ℚ)^3 - (b : ℚ)^4
          = (3 * x^4 - 6 * x^2 + 3 * x - 1) * (b : ℚ)^4 := by
            rw [hx_eq]; ring
        _ = 0 := by rw [hx]; ring
    exact_mod_cast hcast
  -- 3 ∣ b⁴.
  have h3_dvd_b4 : (3 : ℤ) ∣ b ^ 4 := by
    refine ⟨a^4 - 2 * a^2 * b^2 + a * b^3, ?_⟩
    linarith
  -- 3 ∣ b (from primality).
  have h3_dvd_b : (3 : ℤ) ∣ b := three_prime.dvd_of_dvd_pow h3_dvd_b4
  -- Write b = 3 c and substitute to derive an integer equation in a and c.
  obtain ⟨c, hbc⟩ := h3_dvd_b
  -- hab becomes 3·(...) - 81·c⁴ = 0, so a⁴ = 3·(…).
  have hac : a ^ 4 - 18 * a ^ 2 * c ^ 2 + 27 * a * c ^ 3 - 27 * c ^ 4 = 0 := by
    have hexp : 3 * a ^ 4 - 6 * a ^ 2 * (3 * c) ^ 2 + 3 * a * (3 * c) ^ 3 - (3 * c) ^ 4 = 0 := by
      rw [← hbc]; exact hab
    linarith [hexp]
  -- 3 ∣ a⁴.
  have h3_dvd_a4 : (3 : ℤ) ∣ a ^ 4 := by
    refine ⟨6 * a ^ 2 * c ^ 2 - 9 * a * c ^ 3 + 9 * c ^ 4, ?_⟩
    linarith [hac]
  -- 3 ∣ a.
  have h3_dvd_a : (3 : ℤ) ∣ a := three_prime.dvd_of_dvd_pow h3_dvd_a4
  -- But gcd(a, b) = 1 and 3 ∣ b, so 3 ∤ a. Contradiction.
  have hcop : Int.gcd a b = 1 := by
    simp only [ha_def, hb_def]
    exact x.reduced
  have h3_dvd_b_again : (3 : ℤ) ∣ b := ⟨c, hbc⟩
  have h3_dvd_gcd : (3 : ℕ) ∣ Int.gcd a b := Int.dvd_gcd h3_dvd_a h3_dvd_b_again
  rw [hcop] at h3_dvd_gcd
  norm_num at h3_dvd_gcd

#print axioms no_rational_root_3x4_minus_6x2_plus_3x_minus_1

end PrincipiaTractalis.E37a1Selmer_NoRationalRoot3Div_2026_11_18
