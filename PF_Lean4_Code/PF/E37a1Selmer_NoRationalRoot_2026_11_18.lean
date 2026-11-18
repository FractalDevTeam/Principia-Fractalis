import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
# E_37a1 Selmer rank-1, brick 1 — no rational root of `4x³ - 4x + 1`

## Context

E_37a1 : `y² + y = x³ - x` (long Weierstrass, conductor 37, the smallest
rank-1 elliptic curve). Its 2-torsion is trivial: a point `(x, y)` is
2-torsion iff `-P = P`, which by `-(x, y) = (x, -y - a₁ x - a₃)` with
`(a₁, a₃) = (0, 1)` reduces to `2y + 1 = 0`, i.e. `y = -1/2`. Substituting
into the curve, `(-1/2)² + (-1/2) = x³ - x`, gives `4x³ - 4x + 1 = 0`.
No such rational `x` exists; that is what this file proves.

Once trivial rational 2-torsion is in hand, Mordell–Weil gives
`|E_37a1(ℚ) / 2·E_37a1(ℚ)| = 2^rank`. Combined with the corpus's
`E37a1_rank_ge_one` and any Selmer upper bound of 2, `rank = 1` would
follow exactly. This file lands the rational-root obstruction —
brick 1 of that attack.

## Proof

Clear denominators: writing `x = a/b` with `gcd(a, b) = 1`, `b > 0`, the
hypothesis becomes `4a³ - 4ab² + b³ = 0`. Parity forces `b` even: if
`b` were odd then `b³` would be odd, while `4a³ - 4ab²` is even,
contradicting the sum equalling zero. With `b = 2c`, substitute and
divide by the shared factor: `a³ - 4ac² + 2c³ = 0`, so
`a³ = 2 · (2ac² - c³)`, hence `2 ∣ a³`. Since `2` is prime (in ℤ),
`2 ∣ a`. But `b` is even and `gcd(a, b) = 1`, so `a` is odd. Contradiction.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`. No `sorry`,
no `native_decide`.
-/

namespace PrincipiaTractalis.E37a1Selmer_NoRationalRoot_2026_11_18

/-- **Brick 1 of the E_37a1 Selmer rank-1 attack.**
The polynomial `4x³ - 4x + 1` has no rational root. -/
theorem no_rational_root_4x3_minus_4x_plus_1 :
    ∀ x : ℚ, 4 * x ^ 3 - 4 * x + 1 ≠ 0 := by
  intro x hx
  -- Integer version of the equation.
  have hab : 4 * x.num ^ 3 - 4 * x.num * (x.den : ℤ) ^ 2 + (x.den : ℤ) ^ 3 = 0 := by
    have hb_pos : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.pos
    have hb_ne : (x.den : ℚ) ≠ 0 := ne_of_gt hb_pos
    have hx_eq : (x.num : ℚ) = x * (x.den : ℚ) := by
      have := Rat.num_div_den x
      field_simp at this
      linarith
    have hpoly : 4 * ((x.num : ℚ)) ^ 3 - 4 * (x.num : ℚ) * (x.den : ℚ) ^ 2 +
                 (x.den : ℚ) ^ 3 = 0 := by
      calc 4 * ((x.num : ℚ)) ^ 3 - 4 * (x.num : ℚ) * (x.den : ℚ) ^ 2 +
                 (x.den : ℚ) ^ 3
          = (4 * x ^ 3 - 4 * x + 1) * (x.den : ℚ) ^ 3 := by rw [hx_eq]; ring
        _ = 0 := by rw [hx]; ring
    exact_mod_cast hpoly
  -- `b` must be even: if `b` is odd then `b^3` is odd and `4a^3 - 4ab^2` is even.
  have h_b_even : Even (x.den : ℤ) := by
    by_contra h_b_odd
    rw [Int.not_even_iff_odd] at h_b_odd
    have h_b3_odd : Odd ((x.den : ℤ) ^ 3) := h_b_odd.pow
    -- `4a^3 - 4ab^2` is even
    have h_lhs_even : Even (4 * x.num ^ 3 - 4 * x.num * (x.den : ℤ) ^ 2) := by
      refine Even.sub ?_ ?_
      · exact ⟨2 * x.num ^ 3, by ring⟩
      · exact ⟨2 * x.num * (x.den : ℤ) ^ 2, by ring⟩
    -- From `hab`: `b^3 = -(4a^3 - 4ab^2)`, so `b^3` is even.
    have h_b3_eq : (x.den : ℤ) ^ 3 = -(4 * x.num ^ 3 - 4 * x.num * (x.den : ℤ) ^ 2) := by
      linarith
    have h_b3_even : Even ((x.den : ℤ) ^ 3) := by
      rw [h_b3_eq]; exact h_lhs_even.neg
    exact (Int.not_even_iff_odd.mpr h_b3_odd) h_b3_even
  -- `gcd(a, b) = 1`.
  have hcop : Int.gcd x.num (x.den : ℤ) = 1 := by
    have := x.reduced
    exact_mod_cast this
  -- So `a` is odd.
  have h_a_odd : Odd x.num := by
    by_contra h_a_even
    rw [Int.not_odd_iff_even] at h_a_even
    -- Both a, b even → 2 ∣ gcd, contradicting gcd = 1.
    obtain ⟨k, hk⟩ := h_a_even
    obtain ⟨m, hm⟩ := h_b_even
    have h2a : (2 : ℤ) ∣ x.num := ⟨k, by linarith⟩
    have h2b : (2 : ℤ) ∣ (x.den : ℤ) := ⟨m, by linarith⟩
    have h2gcd : (2 : ℕ) ∣ Int.gcd x.num (x.den : ℤ) :=
      Int.dvd_gcd h2a h2b
    rw [hcop] at h2gcd
    norm_num at h2gcd
  -- Substitute b = 2c; the equation `4a^3 - 4a·(2c)^2 + (2c)^3 = 0` simplifies to
  -- `4 · (a^3 - 4ac^2 + 2c^3) = 0`, so `a^3 - 4ac^2 + 2c^3 = 0`,
  -- hence `a^3 = 4ac^2 - 2c^3 = 2(2ac^2 - c^3)`, giving `2 ∣ a^3`, hence `2 ∣ a`.
  obtain ⟨c, hbc⟩ := h_b_even
  have hbc' : (x.den : ℤ) = 2 * c := by rw [hbc]; ring
  have hac : x.num ^ 3 - 4 * x.num * c ^ 2 + 2 * c ^ 3 = 0 := by
    have h := hab
    rw [hbc'] at h
    linarith [h]
  have h2_dvd_acube : (2 : ℤ) ∣ x.num ^ 3 := by
    refine ⟨2 * x.num * c ^ 2 - c ^ 3, ?_⟩
    linarith [hac]
  -- `a` odd contradicts `2 ∣ a^3`.
  obtain ⟨k, hk⟩ := h_a_odd
  have h_acube : x.num ^ 3 = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by
    rw [hk]; ring
  rw [h_acube] at h2_dvd_acube
  obtain ⟨j, hj⟩ := h2_dvd_acube
  omega

#print axioms no_rational_root_4x3_minus_4x_plus_1

end PrincipiaTractalis.E37a1Selmer_NoRationalRoot_2026_11_18
