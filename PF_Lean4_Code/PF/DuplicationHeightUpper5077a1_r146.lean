/-
# PF.DuplicationHeightUpper5077a1_r146

★★★ 2026-07-28 — W1 OF THE INDEPENDENCE ARC, 5077a1 SIDE ★★★

The upper duplication bound for the Buhler–Gross–Zagier rank-3 curve:

  `naiveHeight (f x / g x) ≤ 114 · naiveHeight x ^ 4`

With r144's lower bound this squeezes `h(x(2P))` into
`[H⁴/105754, 114·H⁴]` — the two-sided window for W3's canonical height
on 5077a1. Triangle inequality only: `|F| ≤ 114·H⁴` (coefficient sum of
`F = a⁴ + 14a²b² − 50ab³ + 49b⁴`), `|G3| ≤ 57·H³` so `|D| ≤ 57·H⁴`.

HONEST SCOPE. One inequality for one curve; no canonical height, no rank
statement.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.E5077a1RankOne_r144

namespace PrincipiaTractalis.DuplicationHeightUpper5077a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E5077a1RankOne

/-! ## §1 — monomial bounds -/

section Mono

private theorem mono40 (a b : ℤ) :
    a.natAbs ^ 4 ≤ (max a.natAbs b.natAbs) ^ 4 :=
  Nat.pow_le_pow_left (le_max_left _ _) 4

private theorem mono04 (a b : ℤ) :
    b.natAbs ^ 4 ≤ (max a.natAbs b.natAbs) ^ 4 :=
  Nat.pow_le_pow_left (le_max_right _ _) 4

private theorem mono22 (a b : ℤ) :
    a.natAbs ^ 2 * b.natAbs ^ 2 ≤ (max a.natAbs b.natAbs) ^ 4 := by
  calc a.natAbs ^ 2 * b.natAbs ^ 2
      ≤ (max a.natAbs b.natAbs) ^ 2 * (max a.natAbs b.natAbs) ^ 2 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) 2)
          (Nat.pow_le_pow_left (le_max_right _ _) 2)
    _ = (max a.natAbs b.natAbs) ^ 4 := by ring

private theorem mono13 (a b : ℤ) :
    a.natAbs * b.natAbs ^ 3 ≤ (max a.natAbs b.natAbs) ^ 4 := by
  calc a.natAbs * b.natAbs ^ 3
      ≤ max a.natAbs b.natAbs * (max a.natAbs b.natAbs) ^ 3 :=
        Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_left (le_max_right _ _) 3)
    _ = (max a.natAbs b.natAbs) ^ 4 := by ring

private theorem mono30 (a b : ℤ) :
    a.natAbs ^ 3 ≤ (max a.natAbs b.natAbs) ^ 3 :=
  Nat.pow_le_pow_left (le_max_left _ _) 3

private theorem mono03 (a b : ℤ) :
    b.natAbs ^ 3 ≤ (max a.natAbs b.natAbs) ^ 3 :=
  Nat.pow_le_pow_left (le_max_right _ _) 3

private theorem mono12 (a b : ℤ) :
    a.natAbs * b.natAbs ^ 2 ≤ (max a.natAbs b.natAbs) ^ 3 := by
  calc a.natAbs * b.natAbs ^ 2
      ≤ max a.natAbs b.natAbs * (max a.natAbs b.natAbs) ^ 2 :=
        Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_left (le_max_right _ _) 2)
    _ = (max a.natAbs b.natAbs) ^ 3 := by ring

end Mono

/-! ## §2 — the size upper bounds -/

/-- `|F(a,b)| ≤ 114·H⁴`  (`F = a⁴ + 14a²b² − 50ab³ + 49b⁴`). -/
theorem F_upper (a b : ℤ) :
    (F a b).natAbs ≤ 114 * (max a.natAbs b.natAbs) ^ 4 := by
  have h14 : ((14 : ℤ)).natAbs = 14 := rfl
  have h50 : ((50 : ℤ)).natAbs = 50 := rfl
  have h49 : ((49 : ℤ)).natAbs = 49 := rfl
  have e0 : (a ^ 4).natAbs = a.natAbs ^ 4 := Int.natAbs_pow a 4
  have e1 : ((14 : ℤ) * a ^ 2 * b ^ 2).natAbs
      = 14 * a.natAbs ^ 2 * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, h14]
  have e2 : ((50 : ℤ) * a * b ^ 3).natAbs = 50 * a.natAbs * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h50]
  have e3 : ((49 : ℤ) * b ^ 4).natAbs = 49 * b.natAbs ^ 4 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h49]
  calc (F a b).natAbs
      = (a ^ 4 + 14 * a ^ 2 * b ^ 2 - 50 * a * b ^ 3 + 49 * b ^ 4).natAbs := rfl
    _ ≤ (a ^ 4 + 14 * a ^ 2 * b ^ 2 - 50 * a * b ^ 3).natAbs
          + ((49 : ℤ) * b ^ 4).natAbs := Int.natAbs_add_le _ _
    _ ≤ ((a ^ 4 + 14 * a ^ 2 * b ^ 2).natAbs + ((50 : ℤ) * a * b ^ 3).natAbs)
          + ((49 : ℤ) * b ^ 4).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ ≤ (((a ^ 4).natAbs + ((14 : ℤ) * a ^ 2 * b ^ 2).natAbs)
            + ((50 : ℤ) * a * b ^ 3).natAbs)
          + ((49 : ℤ) * b ^ 4).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = a.natAbs ^ 4 + 14 * (a.natAbs ^ 2 * b.natAbs ^ 2)
          + 50 * (a.natAbs * b.natAbs ^ 3) + 49 * b.natAbs ^ 4 := by
        rw [e0, e1, e2, e3]; ring
    _ ≤ 114 * (max a.natAbs b.natAbs) ^ 4 := by
        have m1 := mono40 a b
        have m2 := mono22 a b
        have m3 := mono13 a b
        have m4 := mono04 a b
        linarith

/-- `|G3(a,b)| ≤ 57·H³`  (`G3 = 4a³ − 28ab² + 25b³`). -/
theorem G3_upper (a b : ℤ) :
    (G3 a b).natAbs ≤ 57 * (max a.natAbs b.natAbs) ^ 3 := by
  have h4 : ((4 : ℤ)).natAbs = 4 := rfl
  have h28 : ((28 : ℤ)).natAbs = 28 := rfl
  have h25 : ((25 : ℤ)).natAbs = 25 := rfl
  have e0 : ((4 : ℤ) * a ^ 3).natAbs = 4 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h4]
  have e1 : ((28 : ℤ) * a * b ^ 2).natAbs = 28 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h28]
  have e2 : ((25 : ℤ) * b ^ 3).natAbs = 25 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h25]
  calc (G3 a b).natAbs
      = (4 * a ^ 3 - 28 * a * b ^ 2 + 25 * b ^ 3).natAbs := rfl
    _ ≤ (4 * a ^ 3 - 28 * a * b ^ 2).natAbs + ((25 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ (((4 : ℤ) * a ^ 3).natAbs + ((28 : ℤ) * a * b ^ 2).natAbs)
          + ((25 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ = 4 * a.natAbs ^ 3 + 28 * (a.natAbs * b.natAbs ^ 2)
          + 25 * b.natAbs ^ 3 := by rw [e0, e1, e2]; ring
    _ ≤ 57 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono12 a b
        have m3 := mono03 a b
        linarith

/-- `|D(a,b)| ≤ 57·H⁴`. -/
theorem D_upper (a b : ℤ) :
    (D a b).natAbs ≤ 57 * (max a.natAbs b.natAbs) ^ 4 := by
  calc (D a b).natAbs = b.natAbs * (G3 a b).natAbs := Int.natAbs_mul _ _
    _ ≤ max a.natAbs b.natAbs * (57 * (max a.natAbs b.natAbs) ^ 3) :=
        Nat.mul_le_mul (le_max_right _ _) (G3_upper a b)
    _ = 57 * (max a.natAbs b.natAbs) ^ 4 := by ring

/-! ## §3 — division only shrinks -/

private theorem natAbs_ediv_gcd_le (x y : ℤ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    (x / (Int.gcd x y : ℤ)).natAbs ≤ x.natAbs := by
  have hd1 : 1 ≤ Int.gcd x y := by
    rcases hxy with hx | hy
    · exact Nat.one_le_iff_ne_zero.mpr fun h0 =>
        hx (Int.eq_zero_of_gcd_eq_zero_left h0)
    · exact Nat.one_le_iff_ne_zero.mpr fun h0 =>
        hy (Int.eq_zero_of_gcd_eq_zero_right h0)
  have hdvd : ((Int.gcd x y : ℕ) : ℤ) ∣ x := Int.gcd_dvd_left _ _
  have hx : (x / (Int.gcd x y : ℤ)).natAbs * Int.gcd x y = x.natAbs := by
    calc (x / (Int.gcd x y : ℤ)).natAbs * Int.gcd x y
        = (x / (Int.gcd x y : ℤ)).natAbs * ((Int.gcd x y : ℤ)).natAbs := by
          rw [Int.natAbs_natCast]
      _ = ((x / (Int.gcd x y : ℤ)) * (Int.gcd x y : ℤ)).natAbs :=
          (Int.natAbs_mul _ _).symm
      _ = x.natAbs := by rw [Int.ediv_mul_cancel hdvd]
  calc (x / (Int.gcd x y : ℤ)).natAbs
      ≤ (x / (Int.gcd x y : ℤ)).natAbs * Int.gcd x y :=
        Nat.le_mul_of_pos_right _ hd1
    _ = x.natAbs := hx

/-! ## §4 — the W1 capstone -/

/-- **The duplication height UPPER bound for 5077a1**:
`naiveHeight (f x / g x) ≤ 114 · naiveHeight x ^ 4`. -/
theorem duplication_height_upper (x : ℚ) :
    naiveHeight (f x / g x) ≤ 114 * naiveHeight x ^ 4 := by
  have hb : ((x.den : ℤ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hbQ : (((x.den : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : x = (x.num : ℚ) / (((x.den : ℤ)) : ℚ) := by
    rw [Int.cast_natCast]
    exact (Rat.num_div_den x).symm
  have hfval : ((F x.num (x.den : ℤ) : ℤ) : ℚ)
      = (((x.den : ℤ)) : ℚ) ^ 4 * f x := by
    have h : ((F x.num (x.den : ℤ) : ℤ) : ℚ)
        = (((x.den : ℤ)) : ℚ) ^ 4
          * f ((x.num : ℚ) / (((x.den : ℤ)) : ℚ)) := by
      simp only [F, f]
      push_cast
      field_simp
    rw [← hx] at h
    exact h
  have hDval : ((D x.num (x.den : ℤ) : ℤ) : ℚ)
      = (((x.den : ℤ)) : ℚ) ^ 4 * g x := by
    have h : ((D x.num (x.den : ℤ) : ℤ) : ℚ)
        = (((x.den : ℤ)) : ℚ) ^ 4
          * g ((x.num : ℚ) / (((x.den : ℤ)) : ℚ)) := by
      simp only [D, G3, g]
      push_cast
      field_simp
    rw [← hx] at h
    exact h
  have hgx : g x ≠ 0 := g_ne_zero x
  have hD : D x.num (x.den : ℤ) ≠ 0 := by
    intro h0
    apply mul_ne_zero (pow_ne_zero 4 hbQ) hgx
    rw [← hDval, h0, Int.cast_zero]
  have hfg : f x / g x
      = ((F x.num (x.den : ℤ) : ℤ) : ℚ) / ((D x.num (x.den : ℤ) : ℤ) : ℚ) := by
    rw [hfval, hDval, mul_div_mul_left _ _ (pow_ne_zero 4 hbQ)]
  set a := x.num
  set b := ((x.den : ℤ))
  have hred := DuplicationHeightBound37a1.naiveHeight_div_int (F a b) (D a b) hD
  have hFd : ((F a b) / (Int.gcd (F a b) (D a b) : ℤ)).natAbs
      ≤ (F a b).natAbs :=
    natAbs_ediv_gcd_le (F a b) (D a b) (Or.inr hD)
  have hDd' : ((D a b) / (Int.gcd (F a b) (D a b) : ℤ)).natAbs
      ≤ (D a b).natAbs := by
    have hcomm : Int.gcd (F a b) (D a b) = Int.gcd (D a b) (F a b) :=
      Nat.gcd_comm _ _
    rw [hcomm]
    exact natAbs_ediv_gcd_le (D a b) (F a b) (Or.inl hD)
  have hHx : max a.natAbs b.natAbs = naiveHeight x := by
    simp only [naiveHeight, a, b, Int.natAbs_natCast]
  calc naiveHeight (f x / g x)
      = naiveHeight ((F a b : ℚ) / (D a b : ℚ)) := by rw [hfg]
    _ = max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
            ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := hred
    _ ≤ max ((F a b).natAbs) ((D a b).natAbs) := max_le_max hFd hDd'
    _ ≤ max (114 * (max a.natAbs b.natAbs) ^ 4)
            (57 * (max a.natAbs b.natAbs) ^ 4) :=
        max_le_max (F_upper a b) (D_upper a b)
    _ = 114 * (max a.natAbs b.natAbs) ^ 4 := by
        rw [max_eq_left]
        exact Nat.mul_le_mul (by norm_num) le_rfl
    _ = 114 * naiveHeight x ^ 4 := by rw [hHx]

/-- **The two-sided window for 5077a1**:
`H⁴/105754 ≤ h(x(2P)) ≤ 114·H⁴`. -/
theorem duplication_two_sided (x : ℚ) :
    naiveHeight x ^ 4 ≤ 105754 * naiveHeight (f x / g x) ∧
    naiveHeight (f x / g x) ≤ 114 * naiveHeight x ^ 4 :=
  ⟨duplication_height_bound x, duplication_height_upper x⟩

end PrincipiaTractalis.DuplicationHeightUpper5077a1

#print axioms PrincipiaTractalis.DuplicationHeightUpper5077a1.F_upper
#print axioms PrincipiaTractalis.DuplicationHeightUpper5077a1.D_upper
#print axioms PrincipiaTractalis.DuplicationHeightUpper5077a1.duplication_height_upper
#print axioms PrincipiaTractalis.DuplicationHeightUpper5077a1.duplication_two_sided
