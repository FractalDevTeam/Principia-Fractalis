/-
# PF.DuplicationHeightUpper389a1_r145

★★★ 2026-07-28 — W1 OF THE INDEPENDENCE ARC: THE UPPER DUPLICATION BOUND ★★★

r143 (W0) gave the quartic LOWER bound for 389a1:
`naiveHeight x ^ 4 ≤ 1728 · naiveHeight (f x / g x)`.  This file adds the
UPPER bound

  `naiveHeight (f x / g x) ≤ 17 · naiveHeight x ^ 4`

so the duplication height is squeezed two-sidedly:
`H⁴/1728 ≤ h(x(2P)) ≤ 17·H⁴`.  This two-sided window is what makes
`h(2ⁿR)/4ⁿ` a Cauchy sequence with explicit modulus — the input to W3's
canonical height `ĥ(R) := lim h(2ⁿR)/4ⁿ`.

Mathematics: triangle inequality only.  `|F(a,b)| ≤ 10·H⁴` (coefficient
sum of `F = a⁴ + 4a²b² − 2ab³ + 3b⁴`), `|G3(a,b)| ≤ 17·H³`, so
`|D| = |b|·|G3| ≤ 17·H⁴`; dividing by the gcd only shrinks, and the
reduced max IS the naive height (r133's `naiveHeight_div_int`).

HONEST SCOPE.  One inequality for one curve.  No canonical height is
constructed here (that is W3); no rank statement is made.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.E389a1RankOne_r143

namespace PrincipiaTractalis.DuplicationHeightUpper389a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E389a1RankOne

/-! ## §1 — degree-4 monomial bounds -/

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

private theorem mono21 (a b : ℤ) :
    a.natAbs ^ 2 * b.natAbs ≤ (max a.natAbs b.natAbs) ^ 3 := by
  calc a.natAbs ^ 2 * b.natAbs
      ≤ (max a.natAbs b.natAbs) ^ 2 * max a.natAbs b.natAbs :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) 2) (le_max_right _ _)
    _ = (max a.natAbs b.natAbs) ^ 3 := by ring

private theorem mono12 (a b : ℤ) :
    a.natAbs * b.natAbs ^ 2 ≤ (max a.natAbs b.natAbs) ^ 3 := by
  calc a.natAbs * b.natAbs ^ 2
      ≤ max a.natAbs b.natAbs * (max a.natAbs b.natAbs) ^ 2 :=
        Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_left (le_max_right _ _) 2)
    _ = (max a.natAbs b.natAbs) ^ 3 := by ring

end Mono

/-! ## §2 — the size upper bounds -/

/-- `|F(a,b)| ≤ 10·H⁴`  (`F = a⁴ + 4a²b² − 2ab³ + 3b⁴`, coefficient sum 10). -/
theorem F_upper (a b : ℤ) :
    (F a b).natAbs ≤ 10 * (max a.natAbs b.natAbs) ^ 4 := by
  have h4 : ((4 : ℤ)).natAbs = 4 := rfl
  have h2 : ((2 : ℤ)).natAbs = 2 := rfl
  have h3 : ((3 : ℤ)).natAbs = 3 := rfl
  have e0 : (a ^ 4).natAbs = a.natAbs ^ 4 := Int.natAbs_pow a 4
  have e1 : ((4 : ℤ) * a ^ 2 * b ^ 2).natAbs
      = 4 * a.natAbs ^ 2 * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, h4]
  have e2 : ((2 : ℤ) * a * b ^ 3).natAbs = 2 * a.natAbs * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h2]
  have e3 : ((3 : ℤ) * b ^ 4).natAbs = 3 * b.natAbs ^ 4 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h3]
  calc (F a b).natAbs
      = (a ^ 4 + 4 * a ^ 2 * b ^ 2 - 2 * a * b ^ 3 + 3 * b ^ 4).natAbs := rfl
    _ ≤ (a ^ 4 + 4 * a ^ 2 * b ^ 2 - 2 * a * b ^ 3).natAbs
          + ((3 : ℤ) * b ^ 4).natAbs := Int.natAbs_add_le _ _
    _ ≤ ((a ^ 4 + 4 * a ^ 2 * b ^ 2).natAbs + ((2 : ℤ) * a * b ^ 3).natAbs)
          + ((3 : ℤ) * b ^ 4).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ ≤ (((a ^ 4).natAbs + ((4 : ℤ) * a ^ 2 * b ^ 2).natAbs)
            + ((2 : ℤ) * a * b ^ 3).natAbs)
          + ((3 : ℤ) * b ^ 4).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = a.natAbs ^ 4 + 4 * (a.natAbs ^ 2 * b.natAbs ^ 2)
          + 2 * (a.natAbs * b.natAbs ^ 3) + 3 * b.natAbs ^ 4 := by
        rw [e0, e1, e2, e3]; ring
    _ ≤ 10 * (max a.natAbs b.natAbs) ^ 4 := by
        have m1 := mono40 a b
        have m2 := mono22 a b
        have m3 := mono13 a b
        have m4 := mono04 a b
        linarith

/-- `|G3(a,b)| ≤ 17·H³`  (`G3 = 4a³ + 4a²b − 8ab² + b³`, coefficient sum 17). -/
theorem G3_upper (a b : ℤ) :
    (G3 a b).natAbs ≤ 17 * (max a.natAbs b.natAbs) ^ 3 := by
  have h4 : ((4 : ℤ)).natAbs = 4 := rfl
  have h8 : ((8 : ℤ)).natAbs = 8 := rfl
  have e0 : ((4 : ℤ) * a ^ 3).natAbs = 4 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h4]
  have e1 : ((4 : ℤ) * a ^ 2 * b).natAbs = 4 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h4]
  have e2 : ((8 : ℤ) * a * b ^ 2).natAbs = 8 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h8]
  have e3 : (b ^ 3).natAbs = b.natAbs ^ 3 := Int.natAbs_pow b 3
  calc (G3 a b).natAbs
      = (4 * a ^ 3 + 4 * a ^ 2 * b - 8 * a * b ^ 2 + b ^ 3).natAbs := rfl
    _ ≤ (4 * a ^ 3 + 4 * a ^ 2 * b - 8 * a * b ^ 2).natAbs
          + (b ^ 3).natAbs := Int.natAbs_add_le _ _
    _ ≤ ((4 * a ^ 3 + 4 * a ^ 2 * b).natAbs + ((8 : ℤ) * a * b ^ 2).natAbs)
          + (b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ ≤ ((((4 : ℤ) * a ^ 3).natAbs + ((4 : ℤ) * a ^ 2 * b).natAbs)
            + ((8 : ℤ) * a * b ^ 2).natAbs)
          + (b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = 4 * a.natAbs ^ 3 + 4 * (a.natAbs ^ 2 * b.natAbs)
          + 8 * (a.natAbs * b.natAbs ^ 2) + b.natAbs ^ 3 := by
        rw [e0, e1, e2, e3]; ring
    _ ≤ 17 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- `|D(a,b)| ≤ 17·H⁴`. -/
theorem D_upper (a b : ℤ) :
    (D a b).natAbs ≤ 17 * (max a.natAbs b.natAbs) ^ 4 := by
  calc (D a b).natAbs = b.natAbs * (G3 a b).natAbs := Int.natAbs_mul _ _
    _ ≤ max a.natAbs b.natAbs * (17 * (max a.natAbs b.natAbs) ^ 3) :=
        Nat.mul_le_mul (le_max_right _ _) (G3_upper a b)
    _ = 17 * (max a.natAbs b.natAbs) ^ 4 := by ring

/-! ## §3 — division only shrinks -/

/-- For `d = gcd(F, D) ≥ 1`: `|F/d| ≤ |F|` (and likewise for `D`). -/
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

/-- **The duplication height UPPER bound for 389a1.**  For every rational
`x`: `naiveHeight (f x / g x) ≤ 17 · naiveHeight x ^ 4`.  Together with
r143's lower bound this squeezes `h(x(2P))` into
`[h⁴/1728, 17·h⁴]` — the two-sided window W3's canonical-height limit
construction consumes. -/
theorem duplication_height_upper (x : ℚ) :
    naiveHeight (f x / g x) ≤ 17 * naiveHeight x ^ 4 := by
  -- reduced coordinates and the F/D representation (as in r143)
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
  -- the reduced height is the reduced max, which division only shrinks
  set a := x.num
  set b := ((x.den : ℤ))
  have hred := DuplicationHeightBound37a1.naiveHeight_div_int (F a b) (D a b) hD
  have hFd : ((F a b) / (Int.gcd (F a b) (D a b) : ℤ)).natAbs
      ≤ (F a b).natAbs :=
    natAbs_ediv_gcd_le (F a b) (D a b) (Or.inr hD)
  have hDd : ((D a b) / (Int.gcd (D a b) (F a b) : ℤ)).natAbs
      ≤ (D a b).natAbs := by
    have h := natAbs_ediv_gcd_le (D a b) (F a b) (Or.inl hD)
    exact h
  have hDd' : ((D a b) / (Int.gcd (F a b) (D a b) : ℤ)).natAbs
      ≤ (D a b).natAbs := by
    have hcomm : Int.gcd (F a b) (D a b) = Int.gcd (D a b) (F a b) :=
      Nat.gcd_comm _ _
    rw [hcomm]
    exact hDd
  -- assemble
  have hHx : max a.natAbs b.natAbs = naiveHeight x := by
    simp only [naiveHeight, a, b, Int.natAbs_natCast]
  calc naiveHeight (f x / g x)
      = naiveHeight ((F a b : ℚ) / (D a b : ℚ)) := by rw [hfg]
    _ = max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
            ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := hred
    _ ≤ max ((F a b).natAbs) ((D a b).natAbs) := max_le_max hFd hDd'
    _ ≤ max (10 * (max a.natAbs b.natAbs) ^ 4)
            (17 * (max a.natAbs b.natAbs) ^ 4) :=
        max_le_max (F_upper a b) (D_upper a b)
    _ = 17 * (max a.natAbs b.natAbs) ^ 4 := by
        rw [max_eq_right]
        exact Nat.mul_le_mul (by norm_num) le_rfl
    _ = 17 * naiveHeight x ^ 4 := by rw [hHx]

/-- **The two-sided window**, packaged: for every rational `x`,
`naiveHeight x ^ 4 ≤ 1728 · naiveHeight (f x / g x)` and
`naiveHeight (f x / g x) ≤ 17 · naiveHeight x ^ 4`. -/
theorem duplication_two_sided (x : ℚ) :
    naiveHeight x ^ 4 ≤ 1728 * naiveHeight (f x / g x) ∧
    naiveHeight (f x / g x) ≤ 17 * naiveHeight x ^ 4 :=
  ⟨duplication_height_bound x, duplication_height_upper x⟩

end PrincipiaTractalis.DuplicationHeightUpper389a1

#print axioms PrincipiaTractalis.DuplicationHeightUpper389a1.F_upper
#print axioms PrincipiaTractalis.DuplicationHeightUpper389a1.D_upper
#print axioms PrincipiaTractalis.DuplicationHeightUpper389a1.duplication_height_upper
#print axioms PrincipiaTractalis.DuplicationHeightUpper389a1.duplication_two_sided
