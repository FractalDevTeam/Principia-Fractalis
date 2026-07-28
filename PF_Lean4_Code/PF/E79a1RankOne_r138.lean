/-
# PF.E79a1RankOne_r138

★★★ 2026-07-28 — THE FIVE-STONE PATTERN, REPLICATED FOR 79a1 ★★★

For the rank-1 curve **79a1** (`y² + xy + y = x³ + x² − 2x`) and its rational
point `P = (0, 0)`, this file proves — in ONE self-contained replica of the
37a1 arc (r131–r134) —

  * `P_nonTorsion : ¬ IsOfFinAddOrder P79` — the point `(0, 0)` has infinite
    order in `E79a1(ℚ)`;
  * `E79a1_rank_ge_one : 1 ≤ Module.rank ℤ E79a1.toAffine.Point` — the FLAG.

Construction (all five stones inlined, new data for 79a1):

  1. **B2 (duplication formula).** With `a₁ = 1` the on-curve square is
     `(2y + x + 1)² = g(x)`, `g(x) = 4x³ + 5x² − 6x + 1` (`= 4·E` certificate);
     `g` has no rational roots (rational root theorem: `4n³ + 5n²d − 6nd² + d³ = 0`
     forces `n = ±1`, `d ∣ 4` — eight candidates, all fail), so doubling stays
     affine; the tangent slope is `(3x² + 2x − 2 − y)/(2y + x + 1)` and
     `x(2P) = f(x)/g(x)` with `f(x) = x⁴ + 3x² − 2x + 1` via the certificate
     `N² + N·w − (1 + 2x)·w² − f = (−8x − 5)·E`.
  2. **B3 (Bézout/gcd/size).** Homogenized pair `F(a,b) = a⁴ + 3a²b² − 2ab³ + b⁴`,
     `D(a,b) = b·(4a³ + 5a²b − 6ab² + b³)`; explicit Bézout cofactors give
     `79·b⁶` and `79·a⁷`, hence `gcd(F, D) ∣ 79` for coprime inputs, and the
     cofactor coefficient sums give the size bound with
     `κ = 209 + 89 = 298` (`a`-branch `205 + 73 = 278 ≤ 298`).
  3. **B4 (height inequality).** `naiveHeight x ^ 4 ≤ 298 · naiveHeight (f x / g x)`
     for EVERY rational `x`, reusing r133's curve-generic `naiveHeight_div_int`.
  4. **B5 (the chain).** From `(0, 0)`: x-values `0 → 1 → 3/4 → 385/256`,
     heights `1, 1, 4, 385`; the driver (r130, `κ = 298`) fires at index 3
     since `naiveHeight (xs 3) = 385 > 298` (`gcd(385, 256) = 1`).
  5. r129's `mordellWeil_rank_ge_one` converts non-torsion into the rank bound.

HONEST SCOPE. This file certifies ONE point on ONE curve as non-torsion and
concludes `1 ≤ Module.rank ℤ E79a1(ℚ)` — a LOWER bound only.  It does not
compute the exact rank, says nothing about any other curve of the cohort,
and proves no statement about L-functions or BSD.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.NaiveHeightQ_r130
import PF.DuplicationHeightBound37a1_r133
import PF.MordellWeilRankLowerBound_r129
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.DivMod

namespace PrincipiaTractalis.E79a1RankOne

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.DuplicationHeightBound37a1 (naiveHeight_div_int)
open PrincipiaTractalis.MordellWeilRankLowerBound
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the curve 79a1 and the duplication polynomials -/

/-- **Curve 79a1**: `y² + xy + y = x³ + x² − 2x`, i.e.
`(a₁, a₂, a₃, a₄, a₆) = (1, 1, 1, −2, 0)`. -/
def E79a1 : WeierstrassCurve ℚ := ⟨1, 1, 1, -2, 0⟩

@[simp] lemma E79a1_a₁ : E79a1.a₁ = 1 := rfl
@[simp] lemma E79a1_a₂ : E79a1.a₂ = 1 := rfl
@[simp] lemma E79a1_a₃ : E79a1.a₃ = 1 := rfl
@[simp] lemma E79a1_a₄ : E79a1.a₄ = -2 := rfl
@[simp] lemma E79a1_a₆ : E79a1.a₆ = 0 := rfl

/-- The duplication numerator `f(x) = x⁴ + 3x² − 2x + 1`
(= `x⁴ − b₄x² − 2b₆x − b₈` for 79a1: `b₄ = −3`, `b₆ = 1`, `b₈ = −1`). -/
def f (x : ℚ) : ℚ := x ^ 4 + 3 * x ^ 2 - 2 * x + 1

/-- The duplication denominator `g(x) = 4x³ + 5x² − 6x + 1`
(= `ψ₂² = 4x³ + b₂x² + 2b₄x + b₆` for 79a1: `b₂ = 5`). -/
def g (x : ℚ) : ℚ := 4 * x ^ 3 + 5 * x ^ 2 - 6 * x + 1

/-- Homogenized duplication numerator for 79a1: `b⁴·f(a/b)`. -/
def F (a b : ℤ) : ℤ := a ^ 4 + 3 * a ^ 2 * b ^ 2 - 2 * a * b ^ 3 + b ^ 4

/-- Homogenized `g` before the extra factor of `b`: `b³·g(a/b)`. -/
def G3 (a b : ℤ) : ℤ := 4 * a ^ 3 + 5 * a ^ 2 * b - 6 * a * b ^ 2 + b ^ 3

/-- The duplication denominator form: `x(2P) = F a b / D a b` for `x = a/b`. -/
def D (a b : ℤ) : ℤ := b * G3 a b

/-! ## §2 — the two Bézout identities (resultant 79² at cofactor level) -/

/-- **Bézout identity, `b`-side**: eliminates `a` down to `79·b⁶`. -/
theorem bezout_b (a b : ℤ) :
    (-48 * a ^ 2 - 40 * a * b + 121 * b ^ 2) * F a b
      + (12 * a ^ 3 - 5 * a ^ 2 * b + 30 * a * b ^ 2 - 42 * b ^ 3) * G3 a b
      = 79 * b ^ 6 := by
  simp only [F, G3]; ring

/-- **Bézout identity, `a`-side**: eliminates `b` down to `79·a⁷`, already in
the `D = b·G3` denominator form. -/
theorem bezout_a (a b : ℤ) :
    (79 * a ^ 3 + 44 * a ^ 2 * b - 70 * a * b ^ 2 + 12 * b ^ 3) * F a b
      + (-11 * a ^ 3 - 28 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3) * D a b
      = 79 * a ^ 7 := by
  simp only [F, D, G3]; ring

/-- `bezout_b` multiplied through by `b`: the `b`-side identity in the
`D`-form that the gcd and size arguments consume. -/
theorem bezout_b_D (a b : ℤ) :
    ((-48 * a ^ 2 - 40 * a * b + 121 * b ^ 2) * b) * F a b
      + (12 * a ^ 3 - 5 * a ^ 2 * b + 30 * a * b ^ 2 - 42 * b ^ 3) * D a b
      = 79 * b ^ 7 := by
  simp only [F, D, G3]; ring

/-! ## §3 — the gcd bound: for coprime `(a, b)`, `gcd (F, D) ∣ 79` -/

/-- **The gcd bound.** For coprime `a b : ℤ`, the gcd of the duplication
numerator and denominator divides `79`: the gcd divides `79·a⁷` and `79·b⁷`,
and coprimality of `a⁷, b⁷` squeezes it into `79`. -/
theorem gcd_dvd_79 {a b : ℤ} (h : IsCoprime a b) :
    (Int.gcd (F a b) (D a b) : ℤ) ∣ 79 := by
  have hdF : (Int.gcd (F a b) (D a b) : ℤ) ∣ F a b := Int.gcd_dvd_left _ _
  have hdD : (Int.gcd (F a b) (D a b) : ℤ) ∣ D a b := Int.gcd_dvd_right _ _
  have hb7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 79 * b ^ 7 := by
    rw [← bezout_b_D a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have ha7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 79 * a ^ 7 := by
    rw [← bezout_a a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have h7 : IsCoprime (a ^ 7) (b ^ 7) := h.pow
  obtain ⟨u, v, huv⟩ := h7
  have key : (79 : ℤ) = u * (79 * a ^ 7) + v * (79 * b ^ 7) := by
    linear_combination (-79 : ℤ) * huv
  rw [key]
  exact dvd_add (ha7.mul_left u) (hb7.mul_left v)

/-- `gcd_dvd_79` in `ℕ`-form. -/
theorem gcd_dvd_79_nat {a b : ℤ} (h : IsCoprime a b) :
    Int.gcd (F a b) (D a b) ∣ 79 := by
  exact_mod_cast gcd_dvd_79 h

/-! ## §4 — the size lower bound

`79·H⁷ ≤ 298·H³·max |F| |D|` with `H = max |a| |b|`. Cofactor coefficient
sums: `b`-side `209 + 89 = 298`, `a`-side `205 + 73 = 278 ≤ 298`. -/

section SizeBound

/-- `|a|³ ≤ H³`. -/
private theorem mono30 (a b : ℤ) :
    a.natAbs ^ 3 ≤ (max a.natAbs b.natAbs) ^ 3 :=
  Nat.pow_le_pow_left (le_max_left _ _) 3

/-- `|b|³ ≤ H³`. -/
private theorem mono03 (a b : ℤ) :
    b.natAbs ^ 3 ≤ (max a.natAbs b.natAbs) ^ 3 :=
  Nat.pow_le_pow_left (le_max_right _ _) 3

/-- `|a|²·|b| ≤ H³`. -/
private theorem mono21 (a b : ℤ) :
    a.natAbs ^ 2 * b.natAbs ≤ (max a.natAbs b.natAbs) ^ 3 := by
  calc a.natAbs ^ 2 * b.natAbs
      ≤ (max a.natAbs b.natAbs) ^ 2 * max a.natAbs b.natAbs :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (le_max_left _ _) 2) (le_max_right _ _)
    _ = (max a.natAbs b.natAbs) ^ 3 := by ring

/-- `|a|·|b|² ≤ H³`. -/
private theorem mono12 (a b : ℤ) :
    a.natAbs * b.natAbs ^ 2 ≤ (max a.natAbs b.natAbs) ^ 3 := by
  calc a.natAbs * b.natAbs ^ 2
      ≤ max a.natAbs b.natAbs * (max a.natAbs b.natAbs) ^ 2 :=
        Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_left (le_max_right _ _) 2)
    _ = (max a.natAbs b.natAbs) ^ 3 := by ring

/-- Cofactor bound, `b`-side, first cofactor:
`|(−48a² − 40ab + 121b²)·b| ≤ 209·H³`. -/
private theorem c1_bound (a b : ℤ) :
    ((-48 * a ^ 2 - 40 * a * b + 121 * b ^ 2) * b).natAbs
      ≤ 209 * (max a.natAbs b.natAbs) ^ 3 := by
  have h48 : ((-48 : ℤ)).natAbs = 48 := rfl
  have h40 : ((40 : ℤ)).natAbs = 40 := rfl
  have h121 : ((121 : ℤ)).natAbs = 121 := rfl
  have e1 : ((-48 : ℤ) * a ^ 2).natAbs = 48 * a.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h48]
  have e2 : ((40 : ℤ) * a * b).natAbs = 40 * a.natAbs * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, h40]
  have e3 : ((121 : ℤ) * b ^ 2).natAbs = 121 * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h121]
  calc ((-48 * a ^ 2 - 40 * a * b + 121 * b ^ 2) * b).natAbs
      = (-48 * a ^ 2 - 40 * a * b + 121 * b ^ 2).natAbs * b.natAbs :=
        Int.natAbs_mul _ _
    _ ≤ ((-48 * a ^ 2 - 40 * a * b).natAbs + (121 * b ^ 2).natAbs) * b.natAbs :=
        Nat.mul_le_mul (Int.natAbs_add_le _ _) le_rfl
    _ ≤ ((((-48 : ℤ) * a ^ 2).natAbs + ((40 : ℤ) * a * b).natAbs)
          + ((121 : ℤ) * b ^ 2).natAbs) * b.natAbs :=
        Nat.mul_le_mul (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) le_rfl
    _ = (48 * a.natAbs ^ 2 + 40 * a.natAbs * b.natAbs + 121 * b.natAbs ^ 2)
          * b.natAbs := by rw [e1, e2, e3]
    _ = 48 * (a.natAbs ^ 2 * b.natAbs) + 40 * (a.natAbs * b.natAbs ^ 2)
          + 121 * b.natAbs ^ 3 := by ring
    _ ≤ 209 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono21 a b
        have m2 := mono12 a b
        have m3 := mono03 a b
        linarith

/-- Cofactor bound, `b`-side, second cofactor:
`|12a³ − 5a²b + 30ab² − 42b³| ≤ 89·H³`. -/
private theorem c2_bound (a b : ℤ) :
    (12 * a ^ 3 - 5 * a ^ 2 * b + 30 * a * b ^ 2 - 42 * b ^ 3).natAbs
      ≤ 89 * (max a.natAbs b.natAbs) ^ 3 := by
  have h12 : ((12 : ℤ)).natAbs = 12 := rfl
  have h5 : ((5 : ℤ)).natAbs = 5 := rfl
  have h30 : ((30 : ℤ)).natAbs = 30 := rfl
  have h42 : ((42 : ℤ)).natAbs = 42 := rfl
  have e1 : ((12 : ℤ) * a ^ 3).natAbs = 12 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  have e2 : ((5 : ℤ) * a ^ 2 * b).natAbs = 5 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h5]
  have e3 : ((30 : ℤ) * a * b ^ 2).natAbs = 30 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h30]
  have e4 : ((42 : ℤ) * b ^ 3).natAbs = 42 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h42]
  calc (12 * a ^ 3 - 5 * a ^ 2 * b + 30 * a * b ^ 2 - 42 * b ^ 3).natAbs
      ≤ (12 * a ^ 3 - 5 * a ^ 2 * b + 30 * a * b ^ 2).natAbs
          + (42 * b ^ 3).natAbs := Int.natAbs_sub_le _ _
    _ ≤ ((12 * a ^ 3 - 5 * a ^ 2 * b).natAbs + ((30 : ℤ) * a * b ^ 2).natAbs)
          + ((42 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((((12 : ℤ) * a ^ 3).natAbs + ((5 : ℤ) * a ^ 2 * b).natAbs)
            + ((30 : ℤ) * a * b ^ 2).natAbs)
          + ((42 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
    _ = 12 * a.natAbs ^ 3 + 5 * a.natAbs ^ 2 * b.natAbs
          + 30 * a.natAbs * b.natAbs ^ 2 + 42 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 89 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, first cofactor:
`|79a³ + 44a²b − 70ab² + 12b³| ≤ 205·H³`. -/
private theorem c3_bound (a b : ℤ) :
    (79 * a ^ 3 + 44 * a ^ 2 * b - 70 * a * b ^ 2 + 12 * b ^ 3).natAbs
      ≤ 205 * (max a.natAbs b.natAbs) ^ 3 := by
  have h79 : ((79 : ℤ)).natAbs = 79 := rfl
  have h44 : ((44 : ℤ)).natAbs = 44 := rfl
  have h70 : ((70 : ℤ)).natAbs = 70 := rfl
  have h12 : ((12 : ℤ)).natAbs = 12 := rfl
  have e1 : ((79 : ℤ) * a ^ 3).natAbs = 79 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h79]
  have e2 : ((44 : ℤ) * a ^ 2 * b).natAbs = 44 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h44]
  have e3 : ((70 : ℤ) * a * b ^ 2).natAbs = 70 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h70]
  have e4 : ((12 : ℤ) * b ^ 3).natAbs = 12 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  calc (79 * a ^ 3 + 44 * a ^ 2 * b - 70 * a * b ^ 2 + 12 * b ^ 3).natAbs
      ≤ (79 * a ^ 3 + 44 * a ^ 2 * b - 70 * a * b ^ 2).natAbs
          + (12 * b ^ 3).natAbs := Int.natAbs_add_le _ _
    _ ≤ ((79 * a ^ 3 + 44 * a ^ 2 * b).natAbs + ((70 : ℤ) * a * b ^ 2).natAbs)
          + ((12 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ ≤ ((((79 : ℤ) * a ^ 3).natAbs + ((44 : ℤ) * a ^ 2 * b).natAbs)
            + ((70 : ℤ) * a * b ^ 2).natAbs)
          + ((12 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = 79 * a.natAbs ^ 3 + 44 * a.natAbs ^ 2 * b.natAbs
          + 70 * a.natAbs * b.natAbs ^ 2 + 12 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 205 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, second cofactor:
`|−11a³ − 28a²b + 22ab² − 12b³| ≤ 73·H³`. -/
private theorem c4_bound (a b : ℤ) :
    (-11 * a ^ 3 - 28 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3).natAbs
      ≤ 73 * (max a.natAbs b.natAbs) ^ 3 := by
  have h11 : ((-11 : ℤ)).natAbs = 11 := rfl
  have h28 : ((28 : ℤ)).natAbs = 28 := rfl
  have h22 : ((22 : ℤ)).natAbs = 22 := rfl
  have h12 : ((12 : ℤ)).natAbs = 12 := rfl
  have e1 : ((-11 : ℤ) * a ^ 3).natAbs = 11 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h11]
  have e2 : ((28 : ℤ) * a ^ 2 * b).natAbs = 28 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h28]
  have e3 : ((22 : ℤ) * a * b ^ 2).natAbs = 22 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h22]
  have e4 : ((12 : ℤ) * b ^ 3).natAbs = 12 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  calc (-11 * a ^ 3 - 28 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3).natAbs
      ≤ (-11 * a ^ 3 - 28 * a ^ 2 * b + 22 * a * b ^ 2).natAbs
          + (12 * b ^ 3).natAbs := Int.natAbs_sub_le _ _
    _ ≤ ((-11 * a ^ 3 - 28 * a ^ 2 * b).natAbs + ((22 : ℤ) * a * b ^ 2).natAbs)
          + ((12 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((((-11 : ℤ) * a ^ 3).natAbs + ((28 : ℤ) * a ^ 2 * b).natAbs)
            + ((22 : ℤ) * a * b ^ 2).natAbs)
          + ((12 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
    _ = 11 * a.natAbs ^ 3 + 28 * a.natAbs ^ 2 * b.natAbs
          + 22 * a.natAbs * b.natAbs ^ 2 + 12 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 73 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- The `b`-branch of the size bound: `79·|b|⁷ ≤ 298·H³·max |F| |D|`. -/
theorem size_bound_b (a b : ℤ) :
    79 * b.natAbs ^ 7
      ≤ 298 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h79 : ((79 : ℤ)).natAbs = 79 := rfl
  have h0 : ((79 : ℤ) * b ^ 7).natAbs = 79 * b.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h79]
  have hterm1 : (((-48 * a ^ 2 - 40 * a * b + 121 * b ^ 2) * b) * F a b).natAbs
      ≤ 209 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c1_bound a b) (le_max_left _ _)
  have hterm2 : ((12 * a ^ 3 - 5 * a ^ 2 * b + 30 * a * b ^ 2 - 42 * b ^ 3)
        * D a b).natAbs
      ≤ 89 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c2_bound a b) (le_max_right _ _)
  calc 79 * b.natAbs ^ 7 = ((79 : ℤ) * b ^ 7).natAbs := h0.symm
    _ = (((-48 * a ^ 2 - 40 * a * b + 121 * b ^ 2) * b) * F a b
          + (12 * a ^ 3 - 5 * a ^ 2 * b + 30 * a * b ^ 2 - 42 * b ^ 3)
              * D a b).natAbs := by
        rw [bezout_b_D a b]
    _ ≤ (((-48 * a ^ 2 - 40 * a * b + 121 * b ^ 2) * b) * F a b).natAbs
          + ((12 * a ^ 3 - 5 * a ^ 2 * b + 30 * a * b ^ 2 - 42 * b ^ 3)
              * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 209 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 89 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 298 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring

/-- The `a`-branch of the size bound: `79·|a|⁷ ≤ 298·H³·max |F| |D|`
(the natural constant is `278`; we relax to `298` to share one constant). -/
theorem size_bound_a (a b : ℤ) :
    79 * a.natAbs ^ 7
      ≤ 298 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h79 : ((79 : ℤ)).natAbs = 79 := rfl
  have h0 : ((79 : ℤ) * a ^ 7).natAbs = 79 * a.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h79]
  have hterm1 : ((79 * a ^ 3 + 44 * a ^ 2 * b - 70 * a * b ^ 2 + 12 * b ^ 3)
        * F a b).natAbs
      ≤ 205 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c3_bound a b) (le_max_left _ _)
  have hterm2 : ((-11 * a ^ 3 - 28 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3)
        * D a b).natAbs
      ≤ 73 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c4_bound a b) (le_max_right _ _)
  calc 79 * a.natAbs ^ 7 = ((79 : ℤ) * a ^ 7).natAbs := h0.symm
    _ = ((79 * a ^ 3 + 44 * a ^ 2 * b - 70 * a * b ^ 2 + 12 * b ^ 3) * F a b
          + (-11 * a ^ 3 - 28 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3)
              * D a b).natAbs := by
        rw [bezout_a a b]
    _ ≤ ((79 * a ^ 3 + 44 * a ^ 2 * b - 70 * a * b ^ 2 + 12 * b ^ 3) * F a b).natAbs
          + ((-11 * a ^ 3 - 28 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3)
              * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 205 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 73 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 278 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring
    _ ≤ 298 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) le_rfl

/-- **The size lower bound.** For all `a b : ℤ`, with `H = max |a| |b|`:
`79·H⁷ ≤ 298·H³·max |F(a,b)| |D(a,b)|`. -/
theorem size_bound (a b : ℤ) :
    79 * (max a.natAbs b.natAbs) ^ 7
      ≤ 298 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  rcases le_total a.natAbs b.natAbs with hab | hab
  · have h := size_bound_b a b
    rw [max_eq_right hab] at h ⊢
    exact h
  · have h := size_bound_a a b
    rw [max_eq_left hab] at h ⊢
    exact h

end SizeBound

/-! ## §5 — the division consequence: height survives gcd cancellation -/

section Reduced

/-- `max` distributes over a common right factor in `ℕ`. -/
private theorem max_mul_nat (x y d : ℕ) : max (x * d) (y * d) = max x y * d := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (Nat.mul_le_mul hxy le_rfl)]
  · rw [max_eq_left hxy, max_eq_left (Nat.mul_le_mul hxy le_rfl)]

/-- Splitting `max |x| |y|` along a common divisor `n`:
`max |x| |y| = max |x/n| |y/n| · n`. -/
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

/-- Pure-`ℕ` descent arithmetic: from `79·H⁷ ≤ 298·H³·(M·d)` with `d ≤ 79`
and `1 ≤ H`, cancel `H³` to get `79·H⁴ ≤ 298·79·M`. -/
private theorem descend {H M d : ℕ} (hd : d ≤ 79) (hH : 1 ≤ H)
    (hkey : 79 * H ^ 7 ≤ 298 * H ^ 3 * (M * d)) : 79 * H ^ 4 ≤ 298 * 79 * M := by
  have hH0 : 0 < H := hH
  have h2 : (79 * H ^ 4) * H ^ 3 ≤ (298 * 79 * M) * H ^ 3 := by
    calc (79 * H ^ 4) * H ^ 3 = 79 * H ^ 7 := by ring
      _ ≤ 298 * H ^ 3 * (M * d) := hkey
      _ ≤ 298 * H ^ 3 * (M * 79) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hd)
      _ = (298 * 79 * M) * H ^ 3 := by ring
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos hH0 3)

/-- **The reduced height bound.** For coprime `a b` with `b ≠ 0`, after
dividing the duplication pair `(F, D)` by `gcd(F, D)` (which divides `79`),
the reduced max still dominates the fourth power of the input height. -/
theorem reduced_height_bound {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (_hD : D a b ≠ 0) :
    79 * (max a.natAbs b.natAbs) ^ 4
      ≤ 298 * 79 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have hd79 : Int.gcd (F a b) (D a b) ≤ 79 :=
    Nat.le_of_dvd (by norm_num) (gcd_dvd_79_nat h)
  have hH1 : 1 ≤ max a.natAbs b.natAbs :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
      (le_max_right _ _)
  have hsplit :=
    max_natAbs_split (n := Int.gcd (F a b) (D a b))
      (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have key := size_bound a b
  rw [hsplit] at key
  exact descend hd79 hH1 key

/-- `reduced_height_bound` with the common factor `79` cancelled:
`H⁴ ≤ 298·max |F/g| |D/g|`. -/
theorem reduced_height_bound' {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 298 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have key := reduced_height_bound h hb hD
  have key2 : 79 * (max a.natAbs b.natAbs) ^ 4
      ≤ 79 * (298 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by
    calc 79 * (max a.natAbs b.natAbs) ^ 4
        ≤ 298 * 79 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := key
      _ = 79 * (298 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by ring
  exact Nat.le_of_mul_le_mul_left key2 (by norm_num)

end Reduced

/-! ## §6 — the duplication formula on the curve (B2 for 79a1, `a₁ = 1`)

The on-curve square is `w² = g(x)` for `w = 2y + x + 1` (`= 2y + a₁x + a₃`). -/

/-- On 79a1, `(2y + x + 1)² = g(x)`: four times the Weierstrass equation. -/
theorem w_sq {x y : ℚ} (h : E79a1.toAffine.Equation x y) :
    (2 * y + x + 1) ^ 2 = g x := by
  rw [Affine.equation_iff] at h
  simp only [E79a1_a₁, E79a1_a₂, E79a1_a₃, E79a1_a₄, E79a1_a₆] at h
  simp only [g]
  linear_combination 4 * h

/-- Integer core of the rational root theorem for `g`: no reduced fraction
`n/d` (`d ≥ 1`, `gcd(n, d) = 1`) satisfies `4n³ + 5n²d − 6nd² + d³ = 0`.
From the equation, `n ∣ d³` forces `n = ±1` and `d ∣ 4n³` forces `d ∣ 4`;
the eight candidates `±1, ±1/2, ±1/3, ±1/4` all fail. -/
lemma no_integer_root {n d : ℤ} (hd1 : 1 ≤ d) (hcop : IsCoprime n d)
    (key : 4 * n ^ 3 + 5 * n ^ 2 * d - 6 * n * d ^ 2 + d ^ 3 = 0) : False := by
  -- n ∣ d³ since d³ = n · (−4n² − 5nd + 6d²)
  have hn_dvd : n ∣ d ^ 3 :=
    ⟨-4 * n ^ 2 - 5 * n * d + 6 * d ^ 2, by linear_combination key⟩
  have hn_unit : IsUnit n :=
    (hcop.pow_right (n := 3)).isUnit_of_dvd' dvd_rfl hn_dvd
  -- d ∣ 4n³ since 4n³ = d · (−5n² + 6nd − d²)
  have hd_dvd : d ∣ 4 * n ^ 3 :=
    ⟨-5 * n ^ 2 + 6 * n * d - d ^ 2, by linear_combination key⟩
  have hd4 : d ∣ 4 :=
    (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right hd_dvd
  have hd_le : d ≤ 4 := Int.le_of_dvd (by norm_num) hd4
  have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases Int.isUnit_iff.mp hn_unit with rfl | rfl <;>
    rcases hd_cases with rfl | rfl | rfl | rfl <;>
      norm_num at key

/-- **`g` has no rational roots.**  In particular no rational affine point of
79a1 is 2-torsion, so doubling never leaves the affine chart. -/
theorem g_ne_zero (x : ℚ) : g x ≠ 0 := by
  intro hg
  have hg' : 4 * x ^ 3 + 5 * x ^ 2 - 6 * x + 1 = 0 := by simpa [g] using hg
  have hden : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  -- clear denominators: 4n³ + 5n²d − 6nd² + d³ = 0 over ℚ, then over ℤ
  have h0 : 4 * (x.num : ℚ) ^ 3 + 5 * (x.num : ℚ) ^ 2 * (x.den : ℚ)
      - 6 * (x.num : ℚ) * (x.den : ℚ) ^ 2 + (x.den : ℚ) ^ 3 = 0 := by
    have hxq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    rw [hxq] at hg'
    field_simp at hg'
    linear_combination hg'
  have key : 4 * x.num ^ 3 + 5 * x.num ^ 2 * (x.den : ℤ)
      - 6 * x.num * (x.den : ℤ) ^ 2 + (x.den : ℤ) ^ 3 = 0 := by
    exact_mod_cast h0
  have hd1 : (1 : ℤ) ≤ (x.den : ℤ) := by
    have := x.pos
    omega
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  exact no_integer_root hd1 hcop key

/-- On 79a1, `2y + x + 1 ≠ 0` for every rational affine point: otherwise
`g(x) = (2y + x + 1)² = 0`, contradicting `g_ne_zero`. -/
theorem w_ne_zero {x y : ℚ} (h : E79a1.toAffine.Equation x y) :
    2 * y + x + 1 ≠ 0 := by
  intro h0
  apply g_ne_zero x
  rw [← w_sq h, h0]
  norm_num

/-- `negY` on 79a1 is `-y - x - 1`. -/
lemma negY_eq (x y : ℚ) : E79a1.toAffine.negY x y = -y - x - 1 := by
  simp only [Affine.negY, E79a1_a₁, E79a1_a₃]
  ring

/-- No rational affine point of 79a1 is 2-torsion: `y ≠ negY x y`. -/
theorem y_ne_negY {x y : ℚ} (h : E79a1.toAffine.Equation x y) :
    y ≠ E79a1.toAffine.negY x y := by
  rw [negY_eq]
  intro hy
  exact w_ne_zero h (by linarith)

/-- The tangent slope at a rational affine point of 79a1 is
`(3x² + 2x − 2 − y)/(2y + x + 1)`. -/
theorem slope_eq {x y : ℚ} (h : E79a1.toAffine.Nonsingular x y) :
    E79a1.toAffine.slope x x y y
      = (3 * x ^ 2 + 2 * x - 2 - y) / (2 * y + x + 1) := by
  rw [Affine.slope_of_Y_ne rfl (y_ne_negY h.left), negY_eq]
  have hnum : 3 * x ^ 2 + 2 * E79a1.toAffine.a₂ * x + E79a1.toAffine.a₄
      - E79a1.toAffine.a₁ * y = 3 * x ^ 2 + 2 * x - 2 - y := by
    simp only [E79a1_a₁, E79a1_a₂, E79a1_a₄]
    ring
  have hden : y - (-y - x - 1) = 2 * y + x + 1 := by ring
  rw [hnum, hden]

/-- **The duplication formula for 79a1.**  For any rational affine point
`P = some h` at `(x, y)`, the double `P + P` is again an affine point
`some h'`, and its x-coordinate is exactly `f(x)/g(x)`.  The x-coordinate
identity is the certificate
`N² + N·w − (1 + 2x)·w² − f = (−8x − 5)·E` (`E` the curve equation)
combined with `w² = g(x) ≠ 0`. -/
theorem dbl_x {x y : ℚ} (h : E79a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E79a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x := by
  have hy : y ≠ E79a1.toAffine.negY x y := y_ne_negY h.left
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy, ?_⟩
  -- goal: addX x x (slope x x y y) = f x / g x
  have hw : 2 * y + x + 1 ≠ 0 := w_ne_zero h.left
  have hsq : (2 * y + x + 1) ^ 2 = g x := w_sq h.left
  have hEq := h.left
  rw [Affine.equation_iff] at hEq
  simp only [E79a1_a₁, E79a1_a₂, E79a1_a₃, E79a1_a₄, E79a1_a₆] at hEq
  -- the duplication certificate: M_raw = f on-curve
  have hM : (3 * x ^ 2 + 2 * x - 2 - y) ^ 2
      + (3 * x ^ 2 + 2 * x - 2 - y) * (2 * y + x + 1)
      - (1 + 2 * x) * (2 * y + x + 1) ^ 2 = f x := by
    simp only [f]
    linear_combination (-8 * x - 5) * hEq
  rw [slope_eq h]
  simp only [Affine.addX, E79a1_a₁, E79a1_a₂]
  rw [← hM, ← hsq]
  field_simp
  ring

/-! ## §7 — the duplication height inequality on 79a1 (B4, κ = 298) -/

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

/-- The B3 bound transported to `naiveHeight`:
`H⁴ ≤ 298 · naiveHeight (F/D)` for `H = max |a| |b|`. -/
theorem height_bound_of_coprime {a b : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 298 * naiveHeight ((F a b : ℚ) / (D a b : ℚ)) := by
  rw [naiveHeight_div_int (F a b) (D a b) hD]
  exact reduced_height_bound' hcop hb hD

/-- **The duplication height inequality for 79a1.**  For every rational `x`
(no on-curve hypothesis: `g` never vanishes on ℚ):
`naiveHeight x ^ 4 ≤ 298 * naiveHeight (f x / g x)`. -/
theorem duplication_height_bound (x : ℚ) :
    naiveHeight x ^ 4 ≤ 298 * naiveHeight (f x / g x) := by
  -- the reduced coordinates of x
  have hb : ((x.den : ℤ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hbQ : (((x.den : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hcop : IsCoprime x.num ((x.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  have hx : x = (x.num : ℚ) / (((x.den : ℤ)) : ℚ) := by
    rw [Int.cast_natCast]
    exact (Rat.num_div_den x).symm
  -- dehomogenize F and D against f and g
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
  -- the homogeneous denominator never vanishes (g has no rational roots)
  have hgx : g x ≠ 0 := g_ne_zero x
  have hD : D x.num (x.den : ℤ) ≠ 0 := by
    intro h0
    apply mul_ne_zero (pow_ne_zero 4 hbQ) hgx
    rw [← hDval, h0, Int.cast_zero]
  -- the fraction identity
  have hfg : f x / g x
      = ((F x.num (x.den : ℤ) : ℤ) : ℚ) / ((D x.num (x.den : ℤ) : ℤ) : ℚ) := by
    rw [hfval, hDval, mul_div_mul_left _ _ (pow_ne_zero 4 hbQ)]
  -- naiveHeight x in homogenized form
  have hHx : max x.num.natAbs ((x.den : ℤ)).natAbs = naiveHeight x := by
    simp only [naiveHeight, Int.natAbs_natCast]
  calc naiveHeight x ^ 4
      = (max x.num.natAbs ((x.den : ℤ)).natAbs) ^ 4 := by rw [hHx]
    _ ≤ 298 * naiveHeight
          ((F x.num (x.den : ℤ) : ℚ) / (D x.num (x.den : ℤ) : ℚ)) :=
        height_bound_of_coprime hcop hb hD
    _ = 298 * naiveHeight (f x / g x) := by rw [← hfg]

/-- **Duplication height step on the curve.** For any rational affine point
`P = some h` of 79a1 at `(x, y)`: `P + P` is an affine point `some h'` at
some `(x', y')` with `naiveHeight x ^ 4 ≤ 298 * naiveHeight x'`. -/
theorem dbl_height {x y : ℚ} (h : E79a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E79a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧
        naiveHeight x ^ 4 ≤ 298 * naiveHeight x' := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
  refine ⟨x', y', h', hadd, ?_⟩
  rw [hx']
  exact duplication_height_bound x

/-! ## §8 — the base point `P = (0, 0)` on 79a1 -/

/-- `(0, 0)` is a nonsingular rational point of 79a1: `a₆ = 0`, and the
Y-partial there is `a₃ = 1 ≠ 0`. -/
theorem P79_nonsingular : E79a1.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  refine ⟨rfl, Or.inl ?_⟩
  show (1 : ℚ) ≠ 0
  norm_num

/-- **The base point** `P79 = (0, 0) ∈ E79a1(ℚ)`. -/
noncomputable def P79 : E79a1.toAffine.Point := Point.some P79_nonsingular

/-! ## §9 — the doubling chain -/

/-- The doubling chain: `chain 0 = (0, 0, proof)`, and `chain (n+1)` is the
affine data of `chain n + chain n` chosen from `dbl_height`. -/
noncomputable def chain : ℕ → Σ' (x y : ℚ), E79a1.toAffine.Nonsingular x y :=
  Nat.rec (motive := fun _ => Σ' (x y : ℚ), E79a1.toAffine.Nonsingular x y)
    ⟨0, 0, P79_nonsingular⟩
    fun _ c =>
      ⟨(dbl_height c.2.2).choose,
       (dbl_height c.2.2).choose_spec.choose,
       (dbl_height c.2.2).choose_spec.choose_spec.choose⟩

/-- The x-coordinate along the chain. -/
noncomputable def xs (n : ℕ) : ℚ := (chain n).1

/-- The chain as points of the group `E79a1(ℚ)`. -/
noncomputable def pts (n : ℕ) : E79a1.toAffine.Point := Point.some (chain n).2.2

@[simp] lemma xs_zero : xs 0 = 0 := rfl

lemma pts_zero : pts 0 = P79 := rfl

/-- Each chain step doubles the point (from `dbl_height`'s `choose_spec`). -/
lemma pts_succ (n : ℕ) : pts (n + 1) = pts n + pts n :=
  ((dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.1).symm

/-- Each chain step satisfies the quartic height inequality (κ = 298). -/
lemma height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ 298 * naiveHeight (xs (n + 1)) :=
  (dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.2

/-- The chain is the `2ⁿ`-multiples of the base point: `pts n = 2ⁿ • P79`. -/
lemma pts_eq_two_pow_smul (n : ℕ) : pts n = ((2 : ℤ) ^ n) • P79 := by
  induction n with
  | zero => rw [pow_zero, one_zsmul, pts_zero]
  | succ k ih =>
      have h2 : ((2 : ℤ) ^ (k + 1)) = 2 ^ k + 2 ^ k := by ring
      rw [pts_succ, ih, h2, add_zsmul]

/-- The chain's x-coordinate recursion, made explicit via `dbl_x` and
`Point.some`-injectivity. -/
lemma xs_succ (n : ℕ) : xs (n + 1) = f (xs n) / g (xs n) := by
  obtain ⟨x', y', h', hadd, hx⟩ := dbl_x (chain n).2.2
  have hpt : Point.some (chain (n + 1)).2.2 = Point.some h' :=
    (pts_succ n).trans hadd
  have hxeq : (chain (n + 1)).1 = x' := (Point.some.inj hpt).left
  exact hxeq.trans hx

/-- `x(2P) = 1`. -/
lemma xs_one : xs 1 = 1 := by
  rw [xs_succ 0, xs_zero]; norm_num [f, g]

/-- `x(4P) = 3/4`. -/
lemma xs_two : xs 2 = 3 / 4 := by
  rw [xs_succ 1, xs_one]; norm_num [f, g]

/-- `x(8P) = 385/256`. -/
lemma xs_three : xs 3 = 385 / 256 := by
  rw [xs_succ 2, xs_two]; norm_num [f, g]

/-- `naiveHeight (x(8P)) = 385` — the fraction is already reduced:
`gcd(385, 256) = 1` (`385 = 5·7·11` is odd, `256 = 2⁸`). -/
lemma naiveHeight_xs_three : naiveHeight (xs 3) = 385 := by
  have h3 : xs 3 = ((385 : ℤ) : ℚ) / ((256 : ℤ) : ℚ) := by
    rw [xs_three]; norm_num
  have hg : Int.gcd 385 256 = 1 := by norm_num
  rw [h3, naiveHeight_div_int 385 256 (by norm_num), hg]
  norm_num

/-- The threshold check: `x(8P)` clears the curve constant `κ = 298`. -/
lemma threshold : 298 < naiveHeight (xs 3) := by
  rw [naiveHeight_xs_three]; norm_num

/-! ## §10 — firing the driver: infinitely many x-coordinates -/

/-- **The chain from `8P` on has infinite x-coordinate range**: the quartic
step starts above the threshold, so r130's growth engine applies. -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 3)).Infinite :=
  infinite_of_duplication_step (κ := 298) (fun n => xs (n + 3))
    (by norm_num) (fun n => height_step (n + 3)) threshold

/-! ## §11 — non-torsion: a finite orbit cannot contain an infinite image -/

/-- The x-coordinate projection on the point group (`0` at the identity). -/
def X : E79a1.toAffine.Point → ℚ
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

lemma X_pts (n : ℕ) : X (pts n) = xs n := rfl

/-- **CAPSTONE 1 — `P = (0, 0)` is non-torsion on 79a1.** If `P79` had
finite order, `AddSubgroup.zmultiples P79` would be a finite set; its image
under `X` would be finite, yet it contains the infinite range of §10 (every
`pts (n+3) = 2^(n+3) • P79` is a `ℤ`-multiple of `P79`). -/
theorem P_nonTorsion : ¬ IsOfFinAddOrder P79 := by
  intro hfin
  have hfinite := hfin.finite_zmultiples
  have hsub : (Set.range fun n => xs (n + 3))
      ⊆ X '' (AddSubgroup.zmultiples P79 : Set _) := by
    rintro q ⟨n, rfl⟩
    refine ⟨pts (n + 3), ?_, X_pts (n + 3)⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨(2 : ℤ) ^ (n + 3), (pts_eq_two_pow_smul (n + 3)).symm⟩
  exact xs_shifted_infinite ((hfinite.image X).subset hsub)

/-! ## §12 — THE FLAG: rank ≥ 1 for 79a1 -/

/-- The r129 certificate, discharged: `P79` has infinite order in
`E79a1(ℚ)`. -/
theorem P79_certificate : NonTorsionCertificate E79a1.toAffine P79 :=
  P_nonTorsion

/-- **CAPSTONE 2 — the Mordell–Weil rank of 79a1 is at least 1.** -/
theorem E79a1_rank_ge_one : 1 ≤ Module.rank ℤ E79a1.toAffine.Point :=
  mordellWeil_rank_ge_one E79a1.toAffine P79 P_nonTorsion

end PrincipiaTractalis.E79a1RankOne

#print axioms PrincipiaTractalis.E79a1RankOne.bezout_b
#print axioms PrincipiaTractalis.E79a1RankOne.bezout_a
#print axioms PrincipiaTractalis.E79a1RankOne.gcd_dvd_79
#print axioms PrincipiaTractalis.E79a1RankOne.dbl_x
#print axioms PrincipiaTractalis.E79a1RankOne.duplication_height_bound
#print axioms PrincipiaTractalis.E79a1RankOne.dbl_height
#print axioms PrincipiaTractalis.E79a1RankOne.xs_three
#print axioms PrincipiaTractalis.E79a1RankOne.naiveHeight_xs_three
#print axioms PrincipiaTractalis.E79a1RankOne.xs_shifted_infinite
#print axioms PrincipiaTractalis.E79a1RankOne.P_nonTorsion
#print axioms PrincipiaTractalis.E79a1RankOne.P79_certificate
#print axioms PrincipiaTractalis.E79a1RankOne.E79a1_rank_ge_one
