import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# E_43a1 Selmer rank-1, brick 13 (E_43a1 brick 5) — no rational root of ψ₃

## Context

For E_43a1 : `y² + y = x³ + x²`, the 3-division polynomial is

    `ψ₃(x) = 3x⁴ + b₂ x³ + 3 b₄ x² + 3 b₆ x + b₈`
           `= 3 x⁴ + 4 x³ + 3 x + 1`

with b-invariants `(b₂, b₄, b₆, b₈) = (4, 0, 1, 1)` for E_43a1.

## Theorem

```
no_rational_root_3x4_plus_4x3_plus_3x_plus_1 :
    ∀ x : ℚ, 3 * x^4 + 4 * x^3 + 3 * x + 1 ≠ 0
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Proof — mod-2 parity via ZMod 2

Clear denominators: writing `x = a/b` with `gcd(a, b) = 1`, the
hypothesis becomes `3 a⁴ + 4 a³ b + 3 a b³ + b⁴ = 0`.

Reduce modulo 2. In `ZMod 2`, `n⁴ = n` for every `n` (by `decide`,
since `ZMod 2` has only two elements), and `4 = 0`, so the equation
collapses to
    `a + a · b + b = 0  in  ZMod 2`.
By `decide`, this forces `a = 0` and `b = 0` in `ZMod 2` — i.e.
`2 ∣ a` and `2 ∣ b`. That contradicts `gcd(a, b) = 1`.
-/

namespace PrincipiaTractalis.E43a1Selmer_NoRationalRoot3Div_2026_11_18

/-- **Brick 13 (E_43a1 brick 5).** The 3-division polynomial of E_43a1
    has no rational root. -/
theorem no_rational_root_3x4_plus_4x3_plus_3x_plus_1 :
    ∀ x : ℚ, 3 * x ^ 4 + 4 * x ^ 3 + 3 * x + 1 ≠ 0 := by
  intro x hx
  -- Integer form of the equation.
  have hab : 3 * x.num ^ 4 + 4 * x.num ^ 3 * (x.den : ℤ)
             + 3 * x.num * (x.den : ℤ) ^ 3 + (x.den : ℤ) ^ 4 = 0 := by
    have hb_pos : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.pos
    have hb_ne : (x.den : ℚ) ≠ 0 := ne_of_gt hb_pos
    have hx_eq : (x.num : ℚ) = x * (x.den : ℚ) := by
      have := Rat.num_div_den x
      field_simp at this
      linarith
    have hpoly :
        3 * ((x.num : ℚ)) ^ 4 + 4 * (x.num : ℚ) ^ 3 * (x.den : ℚ)
          + 3 * (x.num : ℚ) * (x.den : ℚ) ^ 3 + (x.den : ℚ) ^ 4 = 0 := by
      calc 3 * ((x.num : ℚ)) ^ 4 + 4 * (x.num : ℚ) ^ 3 * (x.den : ℚ)
            + 3 * (x.num : ℚ) * (x.den : ℚ) ^ 3 + (x.den : ℚ) ^ 4
          = (3 * x ^ 4 + 4 * x ^ 3 + 3 * x + 1) * (x.den : ℚ) ^ 4 := by
            rw [hx_eq]; ring
        _ = 0 := by rw [hx]; ring
    exact_mod_cast hpoly
  -- Lift the equation to ZMod 2.
  have h_zmod : (x.num : ZMod 2) + (x.num : ZMod 2) * (x.den : ZMod 2)
                + (x.den : ZMod 2) = 0 := by
    have hab_zmod :
        ((3 * x.num ^ 4 + 4 * x.num ^ 3 * (x.den : ℤ)
          + 3 * x.num * (x.den : ℤ) ^ 3 + (x.den : ℤ) ^ 4 : ℤ) : ZMod 2) = 0 := by
      rw [hab]; simp
    have h_cube : ∀ (z : ZMod 2), z ^ 3 = z := by decide
    have h_quart : ∀ (z : ZMod 2), z ^ 4 = z := by decide
    push_cast at hab_zmod
    rw [h_quart, h_cube, h_cube, h_quart] at hab_zmod
    have h4 : (4 : ZMod 2) = 0 := by decide
    have h3 : (3 : ZMod 2) = 1 := by decide
    rw [h4, h3] at hab_zmod
    linear_combination hab_zmod
  -- `decide` on ZMod 2: only (0, 0) satisfies `a + a·b + b = 0`.
  have h_decide : ∀ (a b : ZMod 2), a + a * b + b = 0 → a = 0 ∧ b = 0 := by decide
  obtain ⟨ha_zmod, hb_zmod⟩ := h_decide _ _ h_zmod
  -- Translate back to divisibility.
  have h2a : (2 : ℤ) ∣ x.num := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha_zmod
  have h2b_nat : (2 : ℕ) ∣ x.den := by
    rwa [ZMod.natCast_zmod_eq_zero_iff_dvd] at hb_zmod
  have h2b : (2 : ℤ) ∣ (x.den : ℤ) := by exact_mod_cast h2b_nat
  have hcop : Int.gcd x.num (x.den : ℤ) = 1 := by
    have := x.reduced
    exact_mod_cast this
  have h2gcd : (2 : ℕ) ∣ Int.gcd x.num (x.den : ℤ) := Int.dvd_gcd h2a h2b
  rw [hcop] at h2gcd
  norm_num at h2gcd

#print axioms no_rational_root_3x4_plus_4x3_plus_3x_plus_1

end PrincipiaTractalis.E43a1Selmer_NoRationalRoot3Div_2026_11_18
