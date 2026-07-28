/-
# PF.E5077a1RankOne_r144

★★★ 2026-07-28 — W0 OF THE INDEPENDENCE ARC: THE 5077a1 SUBSTRATE ★★★

5077a1 (`y² + y = x³ − 7x + 6`) is the smallest-conductor rank-3 curve —
the Buhler–Gross–Zagier curve. This file is stone W0 of the independence
arc (`codex/RANK2_INDEPENDENCE_ARC_PLAN_2026-07-28.md`) for the rank-3
target: the per-curve duplication machine — `dbl_x`, the quartic height
LOWER bound (κ = 105754) — which stones W1–W5 (canonical height,
regulator, rank ≥ 3) consume. The rank ≥ 1 statement falls out as a
corollary via the r129/r130 engine:

  * `P_nonTorsion : ¬ IsOfFinAddOrder P5077` — `(−2, 3)` has infinite order;
  * `E5077a1_rank_ge_one : 1 ≤ Module.rank ℤ E5077a1.toAffine.Point`.

Data (sympy-verified, `cohort_data_pack.txt` §5077a1):
`f(x) = x⁴ + 14x² − 50x + 49`, `g(x) = 4x³ − 28x + 25` (no rational
roots), Bézout identities with conductor 5077, cofactor sums b-side
`496 + 827 = 1323`, a-side `38125 + 67629 = 105754` — hence
**κ = 105754**. Chain from `(−2, 3)`:
`−2 → 221/49 → 3009638454/1531704769`, heights
`2, 221, 3009638454 > 105754`.

HONEST SCOPE. Rank LOWER bound from one non-torsion point; the rank-3
statement is the independence arc's target, NOT proven here. No exact
rank, no L-functions, no BSD.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.NaiveHeightQ_r130
import PF.DuplicationHeightBound37a1_r133
import PF.MordellWeilRankLowerBound_r129
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.DivMod

namespace PrincipiaTractalis.E5077a1RankOne

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.MordellWeilRankLowerBound
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the Bézout layer (5077a1 data) -/

/-- Homogenized duplication numerator for 5077a1: `b⁴·f(a/b)`. -/
def F (a b : ℤ) : ℤ := a ^ 4 + 14 * a ^ 2 * b ^ 2 - 50 * a * b ^ 3 + 49 * b ^ 4

/-- Homogenized `g` before the extra factor of `b`: `b³·g(a/b)`. -/
def G3 (a b : ℤ) : ℤ := 4 * a ^ 3 - 28 * a * b ^ 2 + 25 * b ^ 3

/-- The duplication denominator form: `x(2P) = F a b / D a b` for `x = a/b`. -/
def D (a b : ℤ) : ℤ := b * G3 a b

/-- **Bézout identity, `b`-side**: eliminates `a` down to `5077·b⁶`. -/
theorem bezout_b (a b : ℤ) :
    (-48 * a ^ 2 + 448 * b ^ 2) * F a b
      + (12 * a ^ 3 + 140 * a * b ^ 2 - 675 * b ^ 3) * G3 a b
      = 5077 * b ^ 6 := by
  simp only [F, G3]; ring

/-- **Bézout identity, `a`-side**: eliminates `b` down to `5077·a⁷`, already in
the `D = b·G3` denominator form. -/
theorem bezout_a (a b : ℤ) :
    (5077 * a ^ 3 + 4900 * a ^ 2 * b - 18998 * a * b ^ 2 + 9150 * b ^ 3) * F a b
      + (-1225 * a ^ 3 - 13020 * a ^ 2 * b + 35450 * a * b ^ 2
          - 17934 * b ^ 3) * D a b
      = 5077 * a ^ 7 := by
  simp only [F, D, G3]; ring

/-- `bezout_b` multiplied through by `b`. -/
theorem bezout_b_D (a b : ℤ) :
    ((-48 * a ^ 2 + 448 * b ^ 2) * b) * F a b
      + (12 * a ^ 3 + 140 * a * b ^ 2 - 675 * b ^ 3) * D a b
      = 5077 * b ^ 7 := by
  simp only [F, D, G3]; ring

/-- **The gcd bound.** For coprime `a b : ℤ`, `gcd(F, D) ∣ 5077`. -/
theorem gcd_dvd_5077 {a b : ℤ} (h : IsCoprime a b) :
    (Int.gcd (F a b) (D a b) : ℤ) ∣ 5077 := by
  have hdF : (Int.gcd (F a b) (D a b) : ℤ) ∣ F a b := Int.gcd_dvd_left _ _
  have hdD : (Int.gcd (F a b) (D a b) : ℤ) ∣ D a b := Int.gcd_dvd_right _ _
  have hb7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 5077 * b ^ 7 := by
    rw [← bezout_b_D a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have ha7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 5077 * a ^ 7 := by
    rw [← bezout_a a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have h7 : IsCoprime (a ^ 7) (b ^ 7) := h.pow
  obtain ⟨u, v, huv⟩ := h7
  have key : (5077 : ℤ) = u * (5077 * a ^ 7) + v * (5077 * b ^ 7) := by
    linear_combination (-5077 : ℤ) * huv
  rw [key]
  exact dvd_add (ha7.mul_left u) (hb7.mul_left v)

/-- `gcd_dvd_5077` in `ℕ`-form. -/
theorem gcd_dvd_5077_nat {a b : ℤ} (h : IsCoprime a b) :
    Int.gcd (F a b) (D a b) ∣ 5077 := by
  exact_mod_cast gcd_dvd_5077 h

/-! ## §2 — the size lower bound: `5077·H⁷ ≤ 105754·H³·max |F| |D|` -/

section SizeBound

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

/-- `|(−48a² + 448b²)·b| ≤ 496·H³`. -/
private theorem c1_bound (a b : ℤ) :
    ((-48 * a ^ 2 + 448 * b ^ 2) * b).natAbs
      ≤ 496 * (max a.natAbs b.natAbs) ^ 3 := by
  have h48 : ((-48 : ℤ)).natAbs = 48 := rfl
  have h448 : ((448 : ℤ)).natAbs = 448 := rfl
  have e1 : ((-48 : ℤ) * a ^ 2).natAbs = 48 * a.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h48]
  have e2 : ((448 : ℤ) * b ^ 2).natAbs = 448 * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h448]
  calc ((-48 * a ^ 2 + 448 * b ^ 2) * b).natAbs
      = (-48 * a ^ 2 + 448 * b ^ 2).natAbs * b.natAbs :=
        Int.natAbs_mul _ _
    _ ≤ (((-48 : ℤ) * a ^ 2).natAbs + ((448 : ℤ) * b ^ 2).natAbs) * b.natAbs :=
        Nat.mul_le_mul (Int.natAbs_add_le _ _) le_rfl
    _ = (48 * a.natAbs ^ 2 + 448 * b.natAbs ^ 2) * b.natAbs := by rw [e1, e2]
    _ = 48 * (a.natAbs ^ 2 * b.natAbs) + 448 * b.natAbs ^ 3 := by ring
    _ ≤ 496 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono21 a b
        have m2 := mono03 a b
        linarith

/-- `|12a³ + 140ab² − 675b³| ≤ 827·H³`. -/
private theorem c2_bound (a b : ℤ) :
    (12 * a ^ 3 + 140 * a * b ^ 2 - 675 * b ^ 3).natAbs
      ≤ 827 * (max a.natAbs b.natAbs) ^ 3 := by
  have h12 : ((12 : ℤ)).natAbs = 12 := rfl
  have h140 : ((140 : ℤ)).natAbs = 140 := rfl
  have h675 : ((675 : ℤ)).natAbs = 675 := rfl
  have e1 : ((12 : ℤ) * a ^ 3).natAbs = 12 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  have e2 : ((140 : ℤ) * a * b ^ 2).natAbs = 140 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h140]
  have e3 : ((675 : ℤ) * b ^ 3).natAbs = 675 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h675]
  calc (12 * a ^ 3 + 140 * a * b ^ 2 - 675 * b ^ 3).natAbs
      ≤ (12 * a ^ 3 + 140 * a * b ^ 2).natAbs + ((675 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_sub_le _ _
    _ ≤ (((12 : ℤ) * a ^ 3).natAbs + ((140 : ℤ) * a * b ^ 2).natAbs)
          + ((675 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ = 12 * a.natAbs ^ 3 + 140 * a.natAbs * b.natAbs ^ 2
          + 675 * b.natAbs ^ 3 := by
        rw [e1, e2, e3]
    _ ≤ 827 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono12 a b
        have m3 := mono03 a b
        linarith

/-- `|5077a³ + 4900a²b − 18998ab² + 9150b³| ≤ 38125·H³`. -/
private theorem c3_bound (a b : ℤ) :
    (5077 * a ^ 3 + 4900 * a ^ 2 * b - 18998 * a * b ^ 2 + 9150 * b ^ 3).natAbs
      ≤ 38125 * (max a.natAbs b.natAbs) ^ 3 := by
  have h5077 : ((5077 : ℤ)).natAbs = 5077 := rfl
  have h4900 : ((4900 : ℤ)).natAbs = 4900 := rfl
  have h18998 : ((18998 : ℤ)).natAbs = 18998 := rfl
  have h9150 : ((9150 : ℤ)).natAbs = 9150 := rfl
  have e1 : ((5077 : ℤ) * a ^ 3).natAbs = 5077 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h5077]
  have e2 : ((4900 : ℤ) * a ^ 2 * b).natAbs = 4900 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h4900]
  have e3 : ((18998 : ℤ) * a * b ^ 2).natAbs
      = 18998 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h18998]
  have e4 : ((9150 : ℤ) * b ^ 3).natAbs = 9150 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h9150]
  calc (5077 * a ^ 3 + 4900 * a ^ 2 * b - 18998 * a * b ^ 2
          + 9150 * b ^ 3).natAbs
      ≤ (5077 * a ^ 3 + 4900 * a ^ 2 * b - 18998 * a * b ^ 2).natAbs
          + ((9150 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ ((5077 * a ^ 3 + 4900 * a ^ 2 * b).natAbs
            + ((18998 : ℤ) * a * b ^ 2).natAbs)
          + ((9150 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ ≤ ((((5077 : ℤ) * a ^ 3).natAbs + ((4900 : ℤ) * a ^ 2 * b).natAbs)
            + ((18998 : ℤ) * a * b ^ 2).natAbs)
          + ((9150 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = 5077 * a.natAbs ^ 3 + 4900 * a.natAbs ^ 2 * b.natAbs
          + 18998 * a.natAbs * b.natAbs ^ 2 + 9150 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 38125 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- `|−1225a³ − 13020a²b + 35450ab² − 17934b³| ≤ 67629·H³`. -/
private theorem c4_bound (a b : ℤ) :
    (-1225 * a ^ 3 - 13020 * a ^ 2 * b + 35450 * a * b ^ 2
        - 17934 * b ^ 3).natAbs
      ≤ 67629 * (max a.natAbs b.natAbs) ^ 3 := by
  have h1225 : ((-1225 : ℤ)).natAbs = 1225 := rfl
  have h13020 : ((13020 : ℤ)).natAbs = 13020 := rfl
  have h35450 : ((35450 : ℤ)).natAbs = 35450 := rfl
  have h17934 : ((17934 : ℤ)).natAbs = 17934 := rfl
  have e1 : ((-1225 : ℤ) * a ^ 3).natAbs = 1225 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h1225]
  have e2 : ((13020 : ℤ) * a ^ 2 * b).natAbs
      = 13020 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h13020]
  have e3 : ((35450 : ℤ) * a * b ^ 2).natAbs
      = 35450 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h35450]
  have e4 : ((17934 : ℤ) * b ^ 3).natAbs = 17934 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h17934]
  calc (-1225 * a ^ 3 - 13020 * a ^ 2 * b + 35450 * a * b ^ 2
          - 17934 * b ^ 3).natAbs
      ≤ (-1225 * a ^ 3 - 13020 * a ^ 2 * b + 35450 * a * b ^ 2).natAbs
          + ((17934 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_sub_le _ _
    _ ≤ ((-1225 * a ^ 3 - 13020 * a ^ 2 * b).natAbs
            + ((35450 : ℤ) * a * b ^ 2).natAbs)
          + ((17934 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((((-1225 : ℤ) * a ^ 3).natAbs + ((13020 : ℤ) * a ^ 2 * b).natAbs)
            + ((35450 : ℤ) * a * b ^ 2).natAbs)
          + ((17934 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
    _ = 1225 * a.natAbs ^ 3 + 13020 * a.natAbs ^ 2 * b.natAbs
          + 35450 * a.natAbs * b.natAbs ^ 2 + 17934 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 67629 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- The `b`-branch: `5077·|b|⁷ ≤ 105754·H³·max |F| |D|` (natural constant
`1323`, relaxed to `105754`). -/
theorem size_bound_b (a b : ℤ) :
    5077 * b.natAbs ^ 7
      ≤ 105754 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs := by
  have h5077 : ((5077 : ℤ)).natAbs = 5077 := rfl
  have h0 : ((5077 : ℤ) * b ^ 7).natAbs = 5077 * b.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h5077]
  have hterm1 : (((-48 * a ^ 2 + 448 * b ^ 2) * b) * F a b).natAbs
      ≤ 496 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c1_bound a b) (le_max_left _ _)
  have hterm2 : ((12 * a ^ 3 + 140 * a * b ^ 2 - 675 * b ^ 3) * D a b).natAbs
      ≤ 827 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c2_bound a b) (le_max_right _ _)
  calc 5077 * b.natAbs ^ 7 = ((5077 : ℤ) * b ^ 7).natAbs := h0.symm
    _ = (((-48 * a ^ 2 + 448 * b ^ 2) * b) * F a b
          + (12 * a ^ 3 + 140 * a * b ^ 2 - 675 * b ^ 3) * D a b).natAbs := by
        rw [bezout_b_D a b]
    _ ≤ (((-48 * a ^ 2 + 448 * b ^ 2) * b) * F a b).natAbs
          + ((12 * a ^ 3 + 140 * a * b ^ 2 - 675 * b ^ 3) * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 496 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 827 * (max a.natAbs b.natAbs) ^ 3
              * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 1323 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs := by
        ring
    _ ≤ 105754 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) le_rfl

/-- The `a`-branch: `5077·|a|⁷ ≤ 105754·H³·max |F| |D|`
(exact: `38125 + 67629`). -/
theorem size_bound_a (a b : ℤ) :
    5077 * a.natAbs ^ 7
      ≤ 105754 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs := by
  have h5077 : ((5077 : ℤ)).natAbs = 5077 := rfl
  have h0 : ((5077 : ℤ) * a ^ 7).natAbs = 5077 * a.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h5077]
  have hterm1 : ((5077 * a ^ 3 + 4900 * a ^ 2 * b - 18998 * a * b ^ 2
          + 9150 * b ^ 3) * F a b).natAbs
      ≤ 38125 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c3_bound a b) (le_max_left _ _)
  have hterm2 : ((-1225 * a ^ 3 - 13020 * a ^ 2 * b + 35450 * a * b ^ 2
          - 17934 * b ^ 3) * D a b).natAbs
      ≤ 67629 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c4_bound a b) (le_max_right _ _)
  calc 5077 * a.natAbs ^ 7 = ((5077 : ℤ) * a ^ 7).natAbs := h0.symm
    _ = ((5077 * a ^ 3 + 4900 * a ^ 2 * b - 18998 * a * b ^ 2
            + 9150 * b ^ 3) * F a b
          + (-1225 * a ^ 3 - 13020 * a ^ 2 * b + 35450 * a * b ^ 2
              - 17934 * b ^ 3) * D a b).natAbs := by
        rw [bezout_a a b]
    _ ≤ ((5077 * a ^ 3 + 4900 * a ^ 2 * b - 18998 * a * b ^ 2
            + 9150 * b ^ 3) * F a b).natAbs
          + ((-1225 * a ^ 3 - 13020 * a ^ 2 * b + 35450 * a * b ^ 2
              - 17934 * b ^ 3) * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 38125 * (max a.natAbs b.natAbs) ^ 3
            * max (F a b).natAbs (D a b).natAbs
          + 67629 * (max a.natAbs b.natAbs) ^ 3
              * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 105754 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs := by
        ring

/-- **The size lower bound**: `5077·H⁷ ≤ 105754·H³·max |F| |D|`. -/
theorem size_bound (a b : ℤ) :
    5077 * (max a.natAbs b.natAbs) ^ 7
      ≤ 105754 * (max a.natAbs b.natAbs) ^ 3
          * max (F a b).natAbs (D a b).natAbs := by
  rcases le_total a.natAbs b.natAbs with hab | hab
  · have h := size_bound_b a b
    rw [max_eq_right hab] at h ⊢
    exact h
  · have h := size_bound_a a b
    rw [max_eq_left hab] at h ⊢
    exact h

end SizeBound

/-! ## §3 — the division consequence -/

section Reduced

private theorem max_mul_nat (x y d : ℕ) : max (x * d) (y * d) = max x y * d := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (Nat.mul_le_mul hxy le_rfl)]
  · rw [max_eq_left hxy, max_eq_left (Nat.mul_le_mul hxy le_rfl)]

private theorem max_natAbs_split {x y : ℤ} {n : ℕ}
    (hx : (n : ℤ) ∣ x) (hy : (n : ℤ) ∣ y) :
    max x.natAbs y.natAbs
      = max ((x / (n : ℤ)).natAbs) ((y / (n : ℤ)).natAbs) * n := by
  have ex : (x / (n : ℤ)).natAbs * n = x.natAbs := by
    calc (x / (n : ℤ)).natAbs * n
        = (x / (n : ℤ)).natAbs * ((n : ℤ)).natAbs := by rw [Int.natAbs_natCast]
      _ = ((x / (n : ℤ)) * (n : ℤ)).natAbs := (Int.natAbs_mul _ _).symm
      _ = x.natAbs := by rw [Int.ediv_mul_cancel hx]
  have ey : (y / (n : ℤ)).natAbs * n = y.natAbs := by
    calc (y / (n : ℤ)).natAbs * n
        = (y / (n : ℤ)).natAbs * ((n : ℤ)).natAbs := by rw [Int.natAbs_natCast]
      _ = ((y / (n : ℤ)) * (n : ℤ)).natAbs := (Int.natAbs_mul _ _).symm
      _ = y.natAbs := by rw [Int.ediv_mul_cancel hy]
  rw [← ex, ← ey, max_mul_nat]

private theorem descend {H M d : ℕ} (hd : d ≤ 5077) (hH : 1 ≤ H)
    (hkey : 5077 * H ^ 7 ≤ 105754 * H ^ 3 * (M * d)) :
    5077 * H ^ 4 ≤ 105754 * 5077 * M := by
  have hH0 : 0 < H := hH
  have h2 : (5077 * H ^ 4) * H ^ 3 ≤ (105754 * 5077 * M) * H ^ 3 := by
    calc (5077 * H ^ 4) * H ^ 3 = 5077 * H ^ 7 := by ring
      _ ≤ 105754 * H ^ 3 * (M * d) := hkey
      _ ≤ 105754 * H ^ 3 * (M * 5077) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hd)
      _ = (105754 * 5077 * M) * H ^ 3 := by ring
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos hH0 3)

/-- **The reduced height bound.** -/
theorem reduced_height_bound {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (_hD : D a b ≠ 0) :
    5077 * (max a.natAbs b.natAbs) ^ 4
      ≤ 105754 * 5077 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have hd5077 : Int.gcd (F a b) (D a b) ≤ 5077 :=
    Nat.le_of_dvd (by norm_num) (gcd_dvd_5077_nat h)
  have hH1 : 1 ≤ max a.natAbs b.natAbs :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
      (le_max_right _ _)
  have hsplit :=
    max_natAbs_split (n := Int.gcd (F a b) (D a b))
      (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have key := size_bound a b
  rw [hsplit] at key
  exact descend hd5077 hH1 key

/-- The `5077`-cancelled form: `H⁴ ≤ 105754·max |F/g| |D/g|`. -/
theorem reduced_height_bound' {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 105754 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have key := reduced_height_bound h hb hD
  have key2 : 5077 * (max a.natAbs b.natAbs) ^ 4
      ≤ 5077 * (105754 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by
    calc 5077 * (max a.natAbs b.natAbs) ^ 4
        ≤ 105754 * 5077 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := key
      _ = 5077 * (105754 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by ring
  exact Nat.le_of_mul_le_mul_left key2 (by norm_num)

end Reduced

/-! ## §4 — the curve 5077a1 and the duplication formula -/

/-- **Curve 5077a1** (Buhler–Gross–Zagier): `y² + y = x³ − 7x + 6`. -/
def E5077a1 : WeierstrassCurve ℚ := ⟨0, 0, 1, -7, 6⟩

@[simp] lemma E5077a1_a₁ : E5077a1.a₁ = 0 := rfl
@[simp] lemma E5077a1_a₂ : E5077a1.a₂ = 0 := rfl
@[simp] lemma E5077a1_a₃ : E5077a1.a₃ = 1 := rfl
@[simp] lemma E5077a1_a₄ : E5077a1.a₄ = -7 := rfl
@[simp] lemma E5077a1_a₆ : E5077a1.a₆ = 6 := rfl

/-- The duplication numerator `f(x) = x⁴ + 14x² − 50x + 49` for 5077a1. -/
def f (x : ℚ) : ℚ := x ^ 4 + 14 * x ^ 2 - 50 * x + 49

/-- The duplication denominator `g(x) = 4x³ − 28x + 25` (= ψ₂²). -/
def g (x : ℚ) : ℚ := 4 * x ^ 3 - 28 * x + 25

/-- On 5077a1, `(2y + 1)² = g(x)`. -/
theorem two_y_add_one_sq {x y : ℚ} (h : E5077a1.toAffine.Equation x y) :
    (2 * y + 1) ^ 2 = g x := by
  rw [Affine.equation_iff] at h
  simp only [E5077a1_a₁, E5077a1_a₂, E5077a1_a₃, E5077a1_a₄, E5077a1_a₆] at h
  simp only [g]
  linear_combination 4 * h

/-- Integer core of the rational root theorem for `g`: no reduced fraction
`n/d` satisfies `4n³ − 28nd² + 25d³ = 0` (`n ∣ 25d³ ⟹ n ∣ 25`,
`d ∣ 4n³ ⟹ d ∣ 4`; the 24 candidates all fail). -/
lemma no_integer_root {n d : ℤ} (hd1 : 1 ≤ d) (hcop : IsCoprime n d)
    (key : 4 * n ^ 3 - 28 * n * d ^ 2 + 25 * d ^ 3 = 0) : False := by
  have hn_dvd : n ∣ 25 * d ^ 3 :=
    ⟨-4 * n ^ 2 + 28 * d ^ 2, by linear_combination key⟩
  have hn25 : n ∣ 25 :=
    (hcop.pow_right (n := 3)).dvd_of_dvd_mul_right hn_dvd
  have hd_dvd : d ∣ 4 * n ^ 3 :=
    ⟨28 * n * d - 25 * d ^ 2, by linear_combination key⟩
  have hd4 : d ∣ 4 :=
    (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right hd_dvd
  have hd_le : d ≤ 4 := Int.le_of_dvd (by norm_num) hd4
  have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  have hnabs : n.natAbs ∣ 25 := by
    have h := Int.natAbs_dvd_natAbs.mpr hn25
    simpa using h
  have h5 : n.natAbs ∣ 5 ^ 2 := by
    have h25 : (5 : ℕ) ^ 2 = 25 := by norm_num
    rw [h25]; exact hnabs
  have hn_cases : n = 1 ∨ n = -1 ∨ n = 5 ∨ n = -5 ∨ n = 25 ∨ n = -25 := by
    obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp h5
    interval_cases i <;> norm_num at hni <;> omega
  rcases hn_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hd_cases with rfl | rfl | rfl | rfl <;>
      norm_num at key

/-- **`g` has no rational roots.** -/
theorem g_ne_zero (x : ℚ) : g x ≠ 0 := by
  intro hg
  have hg' : 4 * x ^ 3 - 28 * x + 25 = 0 := by simpa [g] using hg
  have hden : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have h0 : 4 * (x.num : ℚ) ^ 3 - 28 * (x.num : ℚ) * (x.den : ℚ) ^ 2
      + 25 * (x.den : ℚ) ^ 3 = 0 := by
    have hxq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    rw [hxq] at hg'
    field_simp at hg'
    linear_combination hg'
  have key : 4 * x.num ^ 3 - 28 * x.num * (x.den : ℤ) ^ 2
      + 25 * (x.den : ℤ) ^ 3 = 0 := by
    exact_mod_cast h0
  have hd1 : (1 : ℤ) ≤ (x.den : ℤ) := by
    have := x.pos
    omega
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  exact no_integer_root hd1 hcop key

/-- On 5077a1, `2y + 1 ≠ 0` for every rational affine point. -/
theorem two_y_add_one_ne_zero {x y : ℚ} (h : E5077a1.toAffine.Equation x y) :
    2 * y + 1 ≠ 0 := by
  intro h0
  apply g_ne_zero x
  rw [← two_y_add_one_sq h, h0]
  norm_num

/-- `negY` on 5077a1 is `-y - 1`. -/
lemma negY_eq (x y : ℚ) : E5077a1.toAffine.negY x y = -y - 1 := by
  simp [Affine.negY]

/-- No rational affine point of 5077a1 is 2-torsion. -/
theorem y_ne_negY {x y : ℚ} (h : E5077a1.toAffine.Equation x y) :
    y ≠ E5077a1.toAffine.negY x y := by
  rw [negY_eq]
  intro hy
  exact two_y_add_one_ne_zero h (by linarith)

/-- The tangent slope at a rational affine point of 5077a1 is
`(3x² − 7)/(2y + 1)`. -/
theorem slope_eq {x y : ℚ} (h : E5077a1.toAffine.Nonsingular x y) :
    E5077a1.toAffine.slope x x y y = (3 * x ^ 2 - 7) / (2 * y + 1) := by
  rw [Affine.slope_of_Y_ne rfl (y_ne_negY h.left), negY_eq]
  have hnum : 3 * x ^ 2 + 2 * E5077a1.toAffine.a₂ * x + E5077a1.toAffine.a₄
      - E5077a1.toAffine.a₁ * y = 3 * x ^ 2 - 7 := by
    simp only [E5077a1_a₁, E5077a1_a₂, E5077a1_a₄]
    ring
  have hden : y - (-y - 1) = 2 * y + 1 := by ring
  rw [hnum, hden]

/-- **The duplication formula for 5077a1**: `x(P + P) = f(x)/g(x)`, via
`(3x² − 7)² − 2x·g(x) = f(x)` and `(2y + 1)² = g(x) ≠ 0`. -/
theorem dbl_x {x y : ℚ} (h : E5077a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E5077a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x := by
  have hy : y ≠ E5077a1.toAffine.negY x y := y_ne_negY h.left
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy, ?_⟩
  have hg : g x ≠ 0 := g_ne_zero x
  have h2y : 2 * y + 1 ≠ 0 := two_y_add_one_ne_zero h.left
  have hsq : (2 * y + 1) ^ 2 = g x := two_y_add_one_sq h.left
  rw [slope_eq h]
  simp only [Affine.addX, E5077a1_a₁, E5077a1_a₂]
  rw [div_pow, hsq]
  field_simp
  simp only [f, g]
  ring

/-! ## §5 — the height join -/

/-- `H⁴ ≤ 105754 · naiveHeight (F/D)`. -/
theorem height_bound_of_coprime {a b : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 105754 * naiveHeight ((F a b : ℚ) / (D a b : ℚ)) := by
  rw [DuplicationHeightBound37a1.naiveHeight_div_int (F a b) (D a b) hD]
  exact reduced_height_bound' hcop hb hD

section Cast

private theorem F_cast (a b : ℤ) (hb : (b : ℚ) ≠ 0) :
    ((F a b : ℤ) : ℚ) = (b : ℚ) ^ 4 * f ((a : ℚ) / (b : ℚ)) := by
  simp only [F, f]
  push_cast
  field_simp

private theorem D_cast (a b : ℤ) (hb : (b : ℚ) ≠ 0) :
    ((D a b : ℤ) : ℚ) = (b : ℚ) ^ 4 * g ((a : ℚ) / (b : ℚ)) := by
  simp only [D, G3, g]
  push_cast
  field_simp

end Cast

/-- **The duplication height inequality for 5077a1** (κ = 105754), for EVERY
rational `x`. -/
theorem duplication_height_bound (x : ℚ) :
    naiveHeight x ^ 4 ≤ 105754 * naiveHeight (f x / g x) := by
  have hb : ((x.den : ℤ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hbQ : (((x.den : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hcop : IsCoprime x.num ((x.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  have hx : x = (x.num : ℚ) / (((x.den : ℤ)) : ℚ) := by
    rw [Int.cast_natCast]
    exact (Rat.num_div_den x).symm
  have hfval : ((F x.num (x.den : ℤ) : ℤ) : ℚ)
      = (((x.den : ℤ)) : ℚ) ^ 4 * f x := by
    have h := F_cast x.num (x.den : ℤ) hbQ
    rw [← hx] at h
    exact h
  have hDval : ((D x.num (x.den : ℤ) : ℤ) : ℚ)
      = (((x.den : ℤ)) : ℚ) ^ 4 * g x := by
    have h := D_cast x.num (x.den : ℤ) hbQ
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
  have hHx : max x.num.natAbs ((x.den : ℤ)).natAbs = naiveHeight x := by
    simp only [naiveHeight, Int.natAbs_natCast]
  calc naiveHeight x ^ 4
      = (max x.num.natAbs ((x.den : ℤ)).natAbs) ^ 4 := by rw [hHx]
    _ ≤ 105754 * naiveHeight
          ((F x.num (x.den : ℤ) : ℚ) / (D x.num (x.den : ℤ) : ℚ)) :=
        height_bound_of_coprime hcop hb hD
    _ = 105754 * naiveHeight (f x / g x) := by rw [← hfg]

/-- **Duplication height step on the curve** (κ = 105754). -/
theorem dbl_height {x y : ℚ} (h : E5077a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E5077a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧
        naiveHeight x ^ 4 ≤ 105754 * naiveHeight x' := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
  refine ⟨x', y', h', hadd, ?_⟩
  rw [hx']
  exact duplication_height_bound x

/-! ## §6 — the base point `P = (−2, 3)` on 5077a1 -/

/-- `(−2, 3)` is a nonsingular rational point of 5077a1: the equation reads
`9 + 3 = −8 + 14 + 6`, and the Y-branch of nonsingularity holds because
`3 ≠ −3 − 0·(−2) − 1 = −4`. -/
theorem P5077_nonsingular : E5077a1.toAffine.Nonsingular (-2) 3 := by
  rw [Affine.nonsingular_iff]
  constructor
  · rw [Affine.equation_iff]
    simp only [E5077a1_a₁, E5077a1_a₂, E5077a1_a₃, E5077a1_a₄, E5077a1_a₆]
    norm_num
  · right
    simp only [E5077a1_a₁, E5077a1_a₃]
    norm_num

/-- **The base point** `P5077 = (−2, 3) ∈ E5077a1(ℚ)`. -/
noncomputable def P5077 : E5077a1.toAffine.Point := Point.some P5077_nonsingular

/-! ## §7 — the doubling chain -/

/-- The doubling chain from `(−2, 3)`. -/
noncomputable def chain : ℕ → Σ' (x y : ℚ), E5077a1.toAffine.Nonsingular x y :=
  Nat.rec (motive := fun _ => Σ' (x y : ℚ), E5077a1.toAffine.Nonsingular x y)
    ⟨-2, 3, P5077_nonsingular⟩
    fun _ c =>
      ⟨(dbl_height c.2.2).choose,
       (dbl_height c.2.2).choose_spec.choose,
       (dbl_height c.2.2).choose_spec.choose_spec.choose⟩

/-- The x-coordinate along the chain. -/
noncomputable def xs (n : ℕ) : ℚ := (chain n).1

/-- The chain as points of the group `E5077a1(ℚ)`. -/
noncomputable def pts (n : ℕ) : E5077a1.toAffine.Point := Point.some (chain n).2.2

@[simp] lemma xs_zero : xs 0 = -2 := rfl

lemma pts_zero : pts 0 = P5077 := rfl

lemma pts_succ (n : ℕ) : pts (n + 1) = pts n + pts n :=
  ((dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.1).symm

lemma height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ 105754 * naiveHeight (xs (n + 1)) :=
  (dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.2

lemma pts_eq_two_pow_smul (n : ℕ) : pts n = ((2 : ℤ) ^ n) • P5077 := by
  induction n with
  | zero => rw [pow_zero, one_zsmul, pts_zero]
  | succ k ih =>
      have h2 : ((2 : ℤ) ^ (k + 1)) = 2 ^ k + 2 ^ k := by ring
      rw [pts_succ, ih, h2, add_zsmul]

lemma xs_succ (n : ℕ) : xs (n + 1) = f (xs n) / g (xs n) := by
  obtain ⟨x', y', h', hadd, hx⟩ := dbl_x (chain n).2.2
  have hpt : Point.some (chain (n + 1)).2.2 = Point.some h' :=
    (pts_succ n).trans hadd
  have hxeq : (chain (n + 1)).1 = x' := (Point.some.inj hpt).left
  exact hxeq.trans hx

/-- `x(2P) = 221/49`. -/
lemma xs_one : xs 1 = 221 / 49 := by
  rw [xs_succ 0, xs_zero]; norm_num [f, g]

/-- `x(4P) = 3009638454/1531704769`. -/
lemma xs_two : xs 2 = 3009638454 / 1531704769 := by
  rw [xs_succ 1, xs_one]; norm_num [f, g]

/-- `naiveHeight (x(4P)) = 3009638454` — the fraction is reduced. -/
lemma naiveHeight_xs_two : naiveHeight (xs 2) = 3009638454 := by
  have h2 : xs 2 = ((3009638454 : ℤ) : ℚ) / ((1531704769 : ℤ) : ℚ) := by
    rw [xs_two]; norm_num
  have hg : Int.gcd 3009638454 1531704769 = 1 := by norm_num
  rw [h2, DuplicationHeightBound37a1.naiveHeight_div_int 3009638454 1531704769
    (by norm_num), hg]
  norm_num

/-- The threshold check: `x(4P)` clears `κ = 105754`. -/
lemma threshold : 105754 < naiveHeight (xs 2) := by
  rw [naiveHeight_xs_two]; norm_num

/-! ## §8 — firing the driver -/

theorem xs_shifted_infinite : (Set.range fun n => xs (n + 2)).Infinite :=
  infinite_of_duplication_step (κ := 105754) (fun n => xs (n + 2))
    (by norm_num) (fun n => height_step (n + 2)) threshold

/-! ## §9 — non-torsion -/

/-- The x-coordinate projection on the point group. -/
def X : E5077a1.toAffine.Point → ℚ
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

lemma X_pts (n : ℕ) : X (pts n) = xs n := rfl

/-- **CAPSTONE 1 — `P = (−2, 3)` is non-torsion on 5077a1.** -/
theorem P_nonTorsion : ¬ IsOfFinAddOrder P5077 := by
  intro hfin
  have hfinite := hfin.finite_zmultiples
  have hsub : (Set.range fun n => xs (n + 2))
      ⊆ X '' (AddSubgroup.zmultiples P5077 : Set _) := by
    rintro q ⟨n, rfl⟩
    refine ⟨pts (n + 2), ?_, X_pts (n + 2)⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨(2 : ℤ) ^ (n + 2), (pts_eq_two_pow_smul (n + 2)).symm⟩
  exact xs_shifted_infinite ((hfinite.image X).subset hsub)

/-! ## §10 — rank ≥ 1 (the W0 corollary; rank ≥ 3 is the arc's target) -/

/-- The r129 certificate, discharged. -/
theorem P5077_certificate : NonTorsionCertificate E5077a1.toAffine P5077 :=
  P_nonTorsion

/-- **CAPSTONE 2 — the Mordell–Weil rank of 5077a1 is at least 1.** -/
theorem E5077a1_rank_ge_one : 1 ≤ Module.rank ℤ E5077a1.toAffine.Point :=
  mordellWeil_rank_ge_one E5077a1.toAffine P5077 P_nonTorsion

end PrincipiaTractalis.E5077a1RankOne

#print axioms PrincipiaTractalis.E5077a1RankOne.bezout_b
#print axioms PrincipiaTractalis.E5077a1RankOne.bezout_a
#print axioms PrincipiaTractalis.E5077a1RankOne.gcd_dvd_5077
#print axioms PrincipiaTractalis.E5077a1RankOne.size_bound
#print axioms PrincipiaTractalis.E5077a1RankOne.reduced_height_bound'
#print axioms PrincipiaTractalis.E5077a1RankOne.dbl_x
#print axioms PrincipiaTractalis.E5077a1RankOne.duplication_height_bound
#print axioms PrincipiaTractalis.E5077a1RankOne.dbl_height
#print axioms PrincipiaTractalis.E5077a1RankOne.xs_two
#print axioms PrincipiaTractalis.E5077a1RankOne.naiveHeight_xs_two
#print axioms PrincipiaTractalis.E5077a1RankOne.P_nonTorsion
#print axioms PrincipiaTractalis.E5077a1RankOne.E5077a1_rank_ge_one
