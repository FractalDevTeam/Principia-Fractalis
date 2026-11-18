import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
# E_43a1 Selmer rank-1, brick 1 — no rational root of `4x³ + 4x² + 1`

## Context

E_43a1 : `y² + y = x³ + x²` (long Weierstrass, conductor 43; the
second-smallest rank-1 elliptic curve after E_37a1). Rational 2-torsion
of E_43a1 requires `y = -1/2` (from `negY x y = -y - 1 = y`, the same
reduction as for E_37a1 since both have `(a₁, a₃) = (0, 1)`).
Substituting into the curve equation,
`(-1/2)² + (-1/2) = x³ + x²`, gives `4x³ + 4x² + 1 = 0`.

This file eliminates every rational `x` satisfying that polynomial,
so the arithmetic input to trivial rational 2-torsion for E_43a1 is
in place. Parallel to brick 1 of the E_37a1 attack
(`PF.E37a1Selmer_NoRationalRoot_2026_11_18`).

## Theorem

```
no_rational_root_4x3_plus_4x2_plus_1 :
    ∀ x : ℚ, 4 * x^3 + 4 * x^2 + 1 ≠ 0
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Proof

Clear denominators: writing `x = a/b` with `gcd(a, b) = 1`, `b > 0`, the
hypothesis becomes `4 a³ + 4 a² b + b³ = 0`. Parity analysis on `b`:
  * If `b` is odd, `b³` is odd while `4 a³ + 4 a² b` is even —
    their sum cannot be zero.
  * If `b` is even, write `b = 2c`. Divide the integer equation by 4:
    `a³ + 2 a² c + 2 c³ = 0`, so `a³ = -2 a² c - 2 c³ = 2·(-a² c - c³)`,
    hence `2 ∣ a³`. Since `(2k+1)³` is odd, `a` must be even. But
    `gcd(a, b) = 1` with `b` even forces `a` odd. Contradiction.
-/

namespace PrincipiaTractalis.E43a1Selmer_NoRationalRoot_2026_11_18

/-- **Brick 1 of the E_43a1 Selmer rank-1 attack.**
The polynomial `4x³ + 4x² + 1` has no rational root. -/
theorem no_rational_root_4x3_plus_4x2_plus_1 :
    ∀ x : ℚ, 4 * x ^ 3 + 4 * x ^ 2 + 1 ≠ 0 := by
  intro x hx
  -- Integer form of the equation.
  have hab : 4 * x.num ^ 3 + 4 * x.num ^ 2 * (x.den : ℤ)
             + (x.den : ℤ) ^ 3 = 0 := by
    have hb_pos : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.pos
    have hb_ne : (x.den : ℚ) ≠ 0 := ne_of_gt hb_pos
    have hx_eq : (x.num : ℚ) = x * (x.den : ℚ) := by
      have := Rat.num_div_den x
      field_simp at this
      linarith
    have hpoly :
        4 * ((x.num : ℚ)) ^ 3 + 4 * (x.num : ℚ) ^ 2 * (x.den : ℚ)
          + (x.den : ℚ) ^ 3 = 0 := by
      calc 4 * ((x.num : ℚ)) ^ 3 + 4 * (x.num : ℚ) ^ 2 * (x.den : ℚ)
            + (x.den : ℚ) ^ 3
          = (4 * x ^ 3 + 4 * x ^ 2 + 1) * (x.den : ℚ) ^ 3 := by rw [hx_eq]; ring
        _ = 0 := by rw [hx]; ring
    exact_mod_cast hpoly
  -- `b` must be even: otherwise `b³` is odd and the other terms are even.
  have h_b_even : Even (x.den : ℤ) := by
    by_contra h_b_odd
    rw [Int.not_even_iff_odd] at h_b_odd
    have h_b3_odd : Odd ((x.den : ℤ) ^ 3) := h_b_odd.pow
    have h_lhs_even :
        Even (4 * x.num ^ 3 + 4 * x.num ^ 2 * (x.den : ℤ)) := by
      refine Even.add ?_ ?_
      · exact ⟨2 * x.num ^ 3, by ring⟩
      · exact ⟨2 * x.num ^ 2 * (x.den : ℤ), by ring⟩
    have h_b3_eq :
        (x.den : ℤ) ^ 3 = -(4 * x.num ^ 3 + 4 * x.num ^ 2 * (x.den : ℤ)) := by
      linarith
    have h_b3_even : Even ((x.den : ℤ) ^ 3) := by
      rw [h_b3_eq]; exact h_lhs_even.neg
    exact (Int.not_even_iff_odd.mpr h_b3_odd) h_b3_even
  -- `gcd(a, b) = 1`.
  have hcop : Int.gcd x.num (x.den : ℤ) = 1 := by
    have := x.reduced
    exact_mod_cast this
  -- So `a` must be odd.
  have h_a_odd : Odd x.num := by
    by_contra h_a_even
    rw [Int.not_odd_iff_even] at h_a_even
    obtain ⟨k, hk⟩ := h_a_even
    obtain ⟨m, hm⟩ := h_b_even
    have h2a : (2 : ℤ) ∣ x.num := ⟨k, by linarith⟩
    have h2b : (2 : ℤ) ∣ (x.den : ℤ) := ⟨m, by linarith⟩
    have h2gcd : (2 : ℕ) ∣ Int.gcd x.num (x.den : ℤ) :=
      Int.dvd_gcd h2a h2b
    rw [hcop] at h2gcd
    norm_num at h2gcd
  -- Substitute `b = 2c` into `hab`; divide through by 4.
  obtain ⟨c, hbc⟩ := h_b_even
  have hbc' : (x.den : ℤ) = 2 * c := by rw [hbc]; ring
  have hac : x.num ^ 3 + 2 * x.num ^ 2 * c + 2 * c ^ 3 = 0 := by
    have h := hab
    rw [hbc'] at h
    linarith [h]
  -- `a³ = -2 a² c - 2 c³ = 2·(-a² c - c³)`, so `2 ∣ a³`.
  have h2_dvd_acube : (2 : ℤ) ∣ x.num ^ 3 := by
    refine ⟨-x.num ^ 2 * c - c ^ 3, ?_⟩
    linarith [hac]
  -- But `a` odd ⟹ `a³` odd. Contradiction.
  obtain ⟨k, hk⟩ := h_a_odd
  have h_acube : x.num ^ 3 = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by
    rw [hk]; ring
  rw [h_acube] at h2_dvd_acube
  obtain ⟨j, hj⟩ := h2_dvd_acube
  omega

#print axioms no_rational_root_4x3_plus_4x2_plus_1

end PrincipiaTractalis.E43a1Selmer_NoRationalRoot_2026_11_18
