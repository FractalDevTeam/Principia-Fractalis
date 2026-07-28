/-
# PF.E53a1RankOne_r136

★★★ 2026-07-28 — THE FIVE-STONE PATTERN REPLICATED FOR 53a1 ★★★

The non-torsion arc (B1–B5, first closed for 37a1 in r131–r134) replayed in
ONE self-contained file for the rank-1 curve **53a1**:

  `y² + xy + y = x³ − x²`,  i.e. `(a₁, a₂, a₃, a₄, a₆) = (1, −1, 1, 0, 0)`,

with generator `P = (0, 0)`.  This is the first curve of the cohort with
`a₁ ≠ 0`, so the tangent-line quantities change shape: the square unit is
`w = 2y + x + 1` (not `2y + 1`), the slope numerator is `3x² − 2x − y`
(the `−a₁y` term survives), and the duplication x-identity needs an on-curve
certificate with a `y`-dependent cofactor (`3 − 8x`).

Capstones:

  * `P_nonTorsion : ¬ IsOfFinAddOrder P53` — `(0, 0)` has infinite order;
  * `E53a1_rank_ge_one : 1 ≤ Module.rank ℤ E53a1.toAffine.Point`.

Construction (cloning r131 → r132 → r133 → r134 with 53a1 data):

  §A  Pure-ℤ Bézout/gcd/size stone (r131 pattern):
      `F(a,b) = a⁴ − a²b² − 2ab³ + b⁴`, `D(a,b) = b·(4a³ − 3a²b + 2ab² + b³)`,
      Bézout cofactors certify `Res = 53²` at cofactor level;
      coprime ⟹ `gcd(F, D) ∣ 53`; size bound with κ = 172
      (`b`-side 95 + 55 = 150 ≤ 172, `a`-side 119 + 53 = 172).
  §B  Duplication formula stone (r132 pattern):
      `(2y + x + 1)² = g(x)` on-curve, `g(x) = 4x³ − 3x² + 2x + 1` has no
      rational roots (integer-core candidates `±1, ±1/2, ±1/4, ±1/3`), the
      tangent slope is `(3x² − 2x − y)/(2y + x + 1)`, and
      `x(P + P) = f(x)/g(x)` with `f(x) = x⁴ − x² − 2x + 1`, certified by
      `(N² + Nw + (1−2x)w²)·g − f·w² = ((3−8x)·g − 4f)·E`.
  §C  Height stone (r133 pattern, REUSING r133's curve-generic
      `naiveHeight_div_int`): `naiveHeight x ⁴ ≤ 172 · naiveHeight (f x/g x)`,
      then `dbl_height` through the group law.
  §D  The chain stone (r134 pattern): `xs : 0 → 1 → −1/4 → 369/64` with
      heights `1, 1, 4, 369`; `369/64` is reduced (`gcd(369, 64) = 1`) and
      `369 > 172 = κ`, so r130's driver fires from index 3; a finite orbit
      cannot contain the infinite x-range, hence non-torsion, hence rank ≥ 1
      by r129's conversion lemma.

HONEST SCOPE. This file certifies ONE point on ONE curve as non-torsion and
concludes `1 ≤ Module.rank ℤ E53a1(ℚ)` — a LOWER bound only.  It does not
compute the exact rank, says nothing about any other curve, and proves no
statement about L-functions or BSD.

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

namespace PrincipiaTractalis.E53a1RankOne

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.MordellWeilRankLowerBound
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §A0 — the curve 53a1 and the duplication polynomials -/

/-- **Curve 53a1**: `y² + xy + y = x³ − x²`,
i.e. `(a₁, a₂, a₃, a₄, a₆) = (1, −1, 1, 0, 0)`. -/
def E53a1 : WeierstrassCurve ℚ := ⟨1, -1, 1, 0, 0⟩

@[simp] lemma E53a1_a₁ : E53a1.a₁ = 1 := rfl
@[simp] lemma E53a1_a₂ : E53a1.a₂ = -1 := rfl
@[simp] lemma E53a1_a₃ : E53a1.a₃ = 1 := rfl
@[simp] lemma E53a1_a₄ : E53a1.a₄ = 0 := rfl
@[simp] lemma E53a1_a₆ : E53a1.a₆ = 0 := rfl

/-- The duplication numerator `f(x) = x⁴ − x² − 2x + 1`
(= `x⁴ − b₄x² − 2b₆x − b₈` for 53a1: `b₄ = 1, b₆ = 1, b₈ = −1`). -/
def f (x : ℚ) : ℚ := x ^ 4 - x ^ 2 - 2 * x + 1

/-- The duplication denominator `g(x) = 4x³ − 3x² + 2x + 1`
(= `ψ₂² = 4x³ + b₂x² + 2b₄x + b₆` for 53a1: `b₂ = −3`). -/
def g (x : ℚ) : ℚ := 4 * x ^ 3 - 3 * x ^ 2 + 2 * x + 1

/-! ## §A1 — the homogenized duplication pair (r131 pattern)

Substituting `x = a/b` and clearing denominators: `x(2P) = F a b / D a b`. -/

/-- Homogenized duplication numerator for 53a1: `b⁴·f(a/b)`. -/
def F (a b : ℤ) : ℤ := a ^ 4 - a ^ 2 * b ^ 2 - 2 * a * b ^ 3 + b ^ 4

/-- Homogenized `g` before the extra factor of `b`: `b³·g(a/b)`. -/
def G3 (a b : ℤ) : ℤ := 4 * a ^ 3 - 3 * a ^ 2 * b + 2 * a * b ^ 2 + b ^ 3

/-- The duplication denominator form: `x(2P) = F a b / D a b` for `x = a/b`. -/
def D (a b : ℤ) : ℤ := b * G3 a b

/-! ## §A2 — the two Bézout identities (resultant 53² at cofactor level) -/

/-- **Bézout identity, `b`-side**: eliminates `a` down to `53·b⁶`. -/
theorem bezout_b (a b : ℤ) :
    (48 * a ^ 2 - 24 * a * b + 23 * b ^ 2) * F a b
      + (-12 * a ^ 3 - 3 * a ^ 2 * b + 10 * a * b ^ 2 + 30 * b ^ 3) * G3 a b
      = 53 * b ^ 6 := by
  simp only [F, G3]; ring

/-- **Bézout identity, `a`-side**: eliminates `b` down to `53·a⁷`, already in
the `D = b·G3` denominator form. -/
theorem bezout_a (a b : ℤ) :
    (53 * a ^ 3 - 28 * a ^ 2 * b + 26 * a * b ^ 2 + 12 * b ^ 3) * F a b
      + (7 * a ^ 3 + 12 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3) * D a b
      = 53 * a ^ 7 := by
  simp only [F, D, G3]; ring

/-- `bezout_b` multiplied through by `b` (first cofactor expanded): the
`b`-side identity in the `D`-form that the gcd and size arguments consume. -/
theorem bezout_b_D (a b : ℤ) :
    (48 * a ^ 2 * b - 24 * a * b ^ 2 + 23 * b ^ 3) * F a b
      + (-12 * a ^ 3 - 3 * a ^ 2 * b + 10 * a * b ^ 2 + 30 * b ^ 3) * D a b
      = 53 * b ^ 7 := by
  simp only [F, D, G3]; ring

/-! ## §A3 — the gcd bound: for coprime `(a, b)`, `gcd (F, D) ∣ 53` -/

/-- **The gcd bound.** For coprime `a b : ℤ`, the gcd of the duplication
numerator and denominator divides `53`. -/
theorem gcd_dvd_53 {a b : ℤ} (h : IsCoprime a b) :
    (Int.gcd (F a b) (D a b) : ℤ) ∣ 53 := by
  have hdF : (Int.gcd (F a b) (D a b) : ℤ) ∣ F a b := Int.gcd_dvd_left _ _
  have hdD : (Int.gcd (F a b) (D a b) : ℤ) ∣ D a b := Int.gcd_dvd_right _ _
  have hb7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 53 * b ^ 7 := by
    rw [← bezout_b_D a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have ha7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 53 * a ^ 7 := by
    rw [← bezout_a a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have h7 : IsCoprime (a ^ 7) (b ^ 7) := h.pow
  obtain ⟨u, v, huv⟩ := h7
  have key : (53 : ℤ) = u * (53 * a ^ 7) + v * (53 * b ^ 7) := by
    linear_combination (-53 : ℤ) * huv
  rw [key]
  exact dvd_add (ha7.mul_left u) (hb7.mul_left v)

/-- `gcd_dvd_53` in `ℕ`-form. -/
theorem gcd_dvd_53_nat {a b : ℤ} (h : IsCoprime a b) :
    Int.gcd (F a b) (D a b) ∣ 53 := by
  exact_mod_cast gcd_dvd_53 h

/-! ## §A4 — the size lower bound

`53·H⁷ ≤ 172·H³·max |F| |D|` with `H = max |a| |b|`; cofactor coefficient
sums are `b`-side `95 + 55 = 150 ≤ 172`, `a`-side `119 + 53 = 172`. -/

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
`|48a²b − 24ab² + 23b³| ≤ 95·H³`. -/
private theorem c1_bound (a b : ℤ) :
    (48 * a ^ 2 * b - 24 * a * b ^ 2 + 23 * b ^ 3).natAbs
      ≤ 95 * (max a.natAbs b.natAbs) ^ 3 := by
  have h48 : ((48 : ℤ)).natAbs = 48 := rfl
  have h24 : ((24 : ℤ)).natAbs = 24 := rfl
  have h23 : ((23 : ℤ)).natAbs = 23 := rfl
  have e1 : ((48 : ℤ) * a ^ 2 * b).natAbs = 48 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h48]
  have e2 : ((24 : ℤ) * a * b ^ 2).natAbs = 24 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h24]
  have e3 : ((23 : ℤ) * b ^ 3).natAbs = 23 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h23]
  calc (48 * a ^ 2 * b - 24 * a * b ^ 2 + 23 * b ^ 3).natAbs
      ≤ (48 * a ^ 2 * b - 24 * a * b ^ 2).natAbs + (23 * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ (((48 : ℤ) * a ^ 2 * b).natAbs + ((24 : ℤ) * a * b ^ 2).natAbs)
          + ((23 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ = 48 * a.natAbs ^ 2 * b.natAbs + 24 * a.natAbs * b.natAbs ^ 2
          + 23 * b.natAbs ^ 3 := by
        rw [e1, e2, e3]
    _ ≤ 95 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono21 a b
        have m2 := mono12 a b
        have m3 := mono03 a b
        linarith

/-- Cofactor bound, `b`-side, second cofactor:
`|−12a³ − 3a²b + 10ab² + 30b³| ≤ 55·H³`. -/
private theorem c2_bound (a b : ℤ) :
    (-12 * a ^ 3 - 3 * a ^ 2 * b + 10 * a * b ^ 2 + 30 * b ^ 3).natAbs
      ≤ 55 * (max a.natAbs b.natAbs) ^ 3 := by
  have h12 : ((-12 : ℤ)).natAbs = 12 := rfl
  have h3 : ((3 : ℤ)).natAbs = 3 := rfl
  have h10 : ((10 : ℤ)).natAbs = 10 := rfl
  have h30 : ((30 : ℤ)).natAbs = 30 := rfl
  have e1 : ((-12 : ℤ) * a ^ 3).natAbs = 12 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  have e2 : ((3 : ℤ) * a ^ 2 * b).natAbs = 3 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h3]
  have e3 : ((10 : ℤ) * a * b ^ 2).natAbs = 10 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h10]
  have e4 : ((30 : ℤ) * b ^ 3).natAbs = 30 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h30]
  calc (-12 * a ^ 3 - 3 * a ^ 2 * b + 10 * a * b ^ 2 + 30 * b ^ 3).natAbs
      ≤ (-12 * a ^ 3 - 3 * a ^ 2 * b + 10 * a * b ^ 2).natAbs
          + (30 * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ ((-12 * a ^ 3 - 3 * a ^ 2 * b).natAbs + ((10 : ℤ) * a * b ^ 2).natAbs)
          + ((30 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((((-12 : ℤ) * a ^ 3).natAbs + ((3 : ℤ) * a ^ 2 * b).natAbs)
            + ((10 : ℤ) * a * b ^ 2).natAbs)
          + ((30 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
    _ = 12 * a.natAbs ^ 3 + 3 * a.natAbs ^ 2 * b.natAbs
          + 10 * a.natAbs * b.natAbs ^ 2 + 30 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 55 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, first cofactor:
`|53a³ − 28a²b + 26ab² + 12b³| ≤ 119·H³`. -/
private theorem c3_bound (a b : ℤ) :
    (53 * a ^ 3 - 28 * a ^ 2 * b + 26 * a * b ^ 2 + 12 * b ^ 3).natAbs
      ≤ 119 * (max a.natAbs b.natAbs) ^ 3 := by
  have h53 : ((53 : ℤ)).natAbs = 53 := rfl
  have h28 : ((28 : ℤ)).natAbs = 28 := rfl
  have h26 : ((26 : ℤ)).natAbs = 26 := rfl
  have h12 : ((12 : ℤ)).natAbs = 12 := rfl
  have e1 : ((53 : ℤ) * a ^ 3).natAbs = 53 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h53]
  have e2 : ((28 : ℤ) * a ^ 2 * b).natAbs = 28 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h28]
  have e3 : ((26 : ℤ) * a * b ^ 2).natAbs = 26 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h26]
  have e4 : ((12 : ℤ) * b ^ 3).natAbs = 12 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  calc (53 * a ^ 3 - 28 * a ^ 2 * b + 26 * a * b ^ 2 + 12 * b ^ 3).natAbs
      ≤ (53 * a ^ 3 - 28 * a ^ 2 * b + 26 * a * b ^ 2).natAbs
          + (12 * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ ((53 * a ^ 3 - 28 * a ^ 2 * b).natAbs + ((26 : ℤ) * a * b ^ 2).natAbs)
          + ((12 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((((53 : ℤ) * a ^ 3).natAbs + ((28 : ℤ) * a ^ 2 * b).natAbs)
            + ((26 : ℤ) * a * b ^ 2).natAbs)
          + ((12 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
    _ = 53 * a.natAbs ^ 3 + 28 * a.natAbs ^ 2 * b.natAbs
          + 26 * a.natAbs * b.natAbs ^ 2 + 12 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 119 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, second cofactor:
`|7a³ + 12a²b + 22ab² − 12b³| ≤ 53·H³`. -/
private theorem c4_bound (a b : ℤ) :
    (7 * a ^ 3 + 12 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3).natAbs
      ≤ 53 * (max a.natAbs b.natAbs) ^ 3 := by
  have h7 : ((7 : ℤ)).natAbs = 7 := rfl
  have h12 : ((12 : ℤ)).natAbs = 12 := rfl
  have h22 : ((22 : ℤ)).natAbs = 22 := rfl
  have e1 : ((7 : ℤ) * a ^ 3).natAbs = 7 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h7]
  have e2 : ((12 : ℤ) * a ^ 2 * b).natAbs = 12 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h12]
  have e3 : ((22 : ℤ) * a * b ^ 2).natAbs = 22 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h22]
  have e4 : ((12 : ℤ) * b ^ 3).natAbs = 12 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  calc (7 * a ^ 3 + 12 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3).natAbs
      ≤ (7 * a ^ 3 + 12 * a ^ 2 * b + 22 * a * b ^ 2).natAbs
          + (12 * b ^ 3).natAbs :=
        Int.natAbs_sub_le _ _
    _ ≤ ((7 * a ^ 3 + 12 * a ^ 2 * b).natAbs + ((22 : ℤ) * a * b ^ 2).natAbs)
          + ((12 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((((7 : ℤ) * a ^ 3).natAbs + ((12 : ℤ) * a ^ 2 * b).natAbs)
            + ((22 : ℤ) * a * b ^ 2).natAbs)
          + ((12 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = 7 * a.natAbs ^ 3 + 12 * a.natAbs ^ 2 * b.natAbs
          + 22 * a.natAbs * b.natAbs ^ 2 + 12 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 53 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- The `b`-branch of the size bound: `53·|b|⁷ ≤ 172·H³·max |F| |D|`
(the natural constant is `150`; we relax to `172` to share one constant). -/
theorem size_bound_b (a b : ℤ) :
    53 * b.natAbs ^ 7
      ≤ 172 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h53 : ((53 : ℤ)).natAbs = 53 := rfl
  have h0 : ((53 : ℤ) * b ^ 7).natAbs = 53 * b.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h53]
  have hterm1 : ((48 * a ^ 2 * b - 24 * a * b ^ 2 + 23 * b ^ 3) * F a b).natAbs
      ≤ 95 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c1_bound a b) (le_max_left _ _)
  have hterm2 : ((-12 * a ^ 3 - 3 * a ^ 2 * b + 10 * a * b ^ 2 + 30 * b ^ 3)
        * D a b).natAbs
      ≤ 55 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c2_bound a b) (le_max_right _ _)
  calc 53 * b.natAbs ^ 7 = ((53 : ℤ) * b ^ 7).natAbs := h0.symm
    _ = ((48 * a ^ 2 * b - 24 * a * b ^ 2 + 23 * b ^ 3) * F a b
          + (-12 * a ^ 3 - 3 * a ^ 2 * b + 10 * a * b ^ 2 + 30 * b ^ 3)
              * D a b).natAbs := by
        rw [bezout_b_D a b]
    _ ≤ ((48 * a ^ 2 * b - 24 * a * b ^ 2 + 23 * b ^ 3) * F a b).natAbs
          + ((-12 * a ^ 3 - 3 * a ^ 2 * b + 10 * a * b ^ 2 + 30 * b ^ 3)
              * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 95 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 55 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 150 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring
    _ ≤ 172 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) le_rfl

/-- The `a`-branch of the size bound: `53·|a|⁷ ≤ 172·H³·max |F| |D|`. -/
theorem size_bound_a (a b : ℤ) :
    53 * a.natAbs ^ 7
      ≤ 172 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h53 : ((53 : ℤ)).natAbs = 53 := rfl
  have h0 : ((53 : ℤ) * a ^ 7).natAbs = 53 * a.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h53]
  have hterm1 : ((53 * a ^ 3 - 28 * a ^ 2 * b + 26 * a * b ^ 2 + 12 * b ^ 3)
        * F a b).natAbs
      ≤ 119 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c3_bound a b) (le_max_left _ _)
  have hterm2 : ((7 * a ^ 3 + 12 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3)
        * D a b).natAbs
      ≤ 53 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c4_bound a b) (le_max_right _ _)
  calc 53 * a.natAbs ^ 7 = ((53 : ℤ) * a ^ 7).natAbs := h0.symm
    _ = ((53 * a ^ 3 - 28 * a ^ 2 * b + 26 * a * b ^ 2 + 12 * b ^ 3) * F a b
          + (7 * a ^ 3 + 12 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3)
              * D a b).natAbs := by
        rw [bezout_a a b]
    _ ≤ ((53 * a ^ 3 - 28 * a ^ 2 * b + 26 * a * b ^ 2 + 12 * b ^ 3) * F a b).natAbs
          + ((7 * a ^ 3 + 12 * a ^ 2 * b + 22 * a * b ^ 2 - 12 * b ^ 3)
              * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 119 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 53 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 172 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring

/-- **The size lower bound.** For all `a b : ℤ`, with `H = max |a| |b|`:
`53·H⁷ ≤ 172·H³·max |F(a,b)| |D(a,b)|`. -/
theorem size_bound (a b : ℤ) :
    53 * (max a.natAbs b.natAbs) ^ 7
      ≤ 172 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  rcases le_total a.natAbs b.natAbs with hab | hab
  · have h := size_bound_b a b
    rw [max_eq_right hab] at h ⊢
    exact h
  · have h := size_bound_a a b
    rw [max_eq_left hab] at h ⊢
    exact h

end SizeBound

/-! ## §A5 — the division consequence: height survives gcd cancellation -/

section Reduced

/-- `max` distributes over a common right factor in `ℕ`. -/
private theorem max_mul_nat (x y d : ℕ) : max (x * d) (y * d) = max x y * d := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (Nat.mul_le_mul hxy le_rfl)]
  · rw [max_eq_left hxy, max_eq_left (Nat.mul_le_mul hxy le_rfl)]

/-- Splitting `max |x| |y|` along a common divisor `n`. -/
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

/-- Pure-`ℕ` descent arithmetic: from `53·H⁷ ≤ 172·H³·(M·d)` with `d ≤ 53`
and `1 ≤ H`, cancel `H³` to get `53·H⁴ ≤ 172·53·M`. -/
private theorem descend {H M d : ℕ} (hd : d ≤ 53) (hH : 1 ≤ H)
    (hkey : 53 * H ^ 7 ≤ 172 * H ^ 3 * (M * d)) : 53 * H ^ 4 ≤ 172 * 53 * M := by
  have hH0 : 0 < H := hH
  have h2 : (53 * H ^ 4) * H ^ 3 ≤ (172 * 53 * M) * H ^ 3 := by
    calc (53 * H ^ 4) * H ^ 3 = 53 * H ^ 7 := by ring
      _ ≤ 172 * H ^ 3 * (M * d) := hkey
      _ ≤ 172 * H ^ 3 * (M * 53) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hd)
      _ = (172 * 53 * M) * H ^ 3 := by ring
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos hH0 3)

/-- **The reduced height bound.** For coprime `a b` with `b ≠ 0`, after
dividing the duplication pair `(F, D)` by `gcd(F, D)` (which divides `53`):
`53·H⁴ ≤ 172·53·max |F/g| |D/g|`. -/
theorem reduced_height_bound {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (_hD : D a b ≠ 0) :
    53 * (max a.natAbs b.natAbs) ^ 4
      ≤ 172 * 53 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have hd53 : Int.gcd (F a b) (D a b) ≤ 53 :=
    Nat.le_of_dvd (by norm_num) (gcd_dvd_53_nat h)
  have hH1 : 1 ≤ max a.natAbs b.natAbs :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
      (le_max_right _ _)
  have hsplit :=
    max_natAbs_split (n := Int.gcd (F a b) (D a b))
      (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have key := size_bound a b
  rw [hsplit] at key
  exact descend hd53 hH1 key

/-- `reduced_height_bound` with the common factor `53` cancelled:
`H⁴ ≤ 172·max |F/g| |D/g|`. -/
theorem reduced_height_bound' {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 172 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have key := reduced_height_bound h hb hD
  have key2 : 53 * (max a.natAbs b.natAbs) ^ 4
      ≤ 53 * (172 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by
    calc 53 * (max a.natAbs b.natAbs) ^ 4
        ≤ 172 * 53 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := key
      _ = 53 * (172 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by ring
  exact Nat.le_of_mul_le_mul_left key2 (by norm_num)

end Reduced

/-! ## §B — the duplication formula for 53a1 (r132 pattern)

`a₁ = 1` here, so the square unit is `w = 2y + x + 1 = y − negY x y` and the
slope numerator keeps its `−a₁y` term. -/

/-- On 53a1, `(2y + x + 1)² = g(x)`: four times the Weierstrass equation. -/
theorem w_sq {x y : ℚ} (h : E53a1.toAffine.Equation x y) :
    (2 * y + x + 1) ^ 2 = g x := by
  rw [Affine.equation_iff] at h
  simp only [E53a1_a₁, E53a1_a₂, E53a1_a₃, E53a1_a₄, E53a1_a₆] at h
  simp only [g]
  linear_combination 4 * h

/-- The Weierstrass equation of 53a1 in simplified form. -/
theorem on_curve {x y : ℚ} (h : E53a1.toAffine.Equation x y) :
    y ^ 2 + x * y + y = x ^ 3 - x ^ 2 := by
  rw [Affine.equation_iff] at h
  simp only [E53a1_a₁, E53a1_a₂, E53a1_a₃, E53a1_a₄, E53a1_a₆] at h
  linear_combination h

/-- Integer core of the rational root theorem for `g`: no reduced fraction
`n/d` (`d ≥ 1`, `gcd(n, d) = 1`) satisfies `4n³ − 3n²d + 2nd² + d³ = 0`.
From the equation, `n ∣ d³` forces `n = ±1` and `d ∣ 4n³` forces `d ∣ 4`;
all candidates fail. -/
lemma no_integer_root {n d : ℤ} (hd1 : 1 ≤ d) (hcop : IsCoprime n d)
    (key : 4 * n ^ 3 - 3 * n ^ 2 * d + 2 * n * d ^ 2 + d ^ 3 = 0) : False := by
  -- n ∣ d³ since d³ = n · (−(4n² − 3nd + 2d²))
  have hn_dvd : n ∣ d ^ 3 :=
    ⟨-(4 * n ^ 2 - 3 * n * d + 2 * d ^ 2), by linear_combination key⟩
  have hn_unit : IsUnit n :=
    (hcop.pow_right (n := 3)).isUnit_of_dvd' dvd_rfl hn_dvd
  -- d ∣ 4n³ since 4n³ = d · (3n² − 2nd − d²)
  have hd_dvd : d ∣ 4 * n ^ 3 := ⟨3 * n ^ 2 - 2 * n * d - d ^ 2, by linear_combination key⟩
  have hd4 : d ∣ 4 :=
    (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right hd_dvd
  have hd_le : d ≤ 4 := Int.le_of_dvd (by norm_num) hd4
  have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases Int.isUnit_iff.mp hn_unit with rfl | rfl <;>
    rcases hd_cases with rfl | rfl | rfl | rfl <;>
      norm_num at key

/-- **`g` has no rational roots.** In particular no rational affine point of
53a1 is 2-torsion, so doubling never leaves the affine chart. -/
theorem g_ne_zero (x : ℚ) : g x ≠ 0 := by
  intro hg
  have hg' : 4 * x ^ 3 - 3 * x ^ 2 + 2 * x + 1 = 0 := by simpa [g] using hg
  have hden : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  -- clear denominators: 4n³ − 3n²d + 2nd² + d³ = 0 over ℚ, then over ℤ
  have h0 : 4 * (x.num : ℚ) ^ 3 - 3 * (x.num : ℚ) ^ 2 * (x.den : ℚ)
      + 2 * (x.num : ℚ) * (x.den : ℚ) ^ 2 + (x.den : ℚ) ^ 3 = 0 := by
    have hxq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    rw [hxq] at hg'
    field_simp at hg'
    linear_combination hg'
  have key : 4 * x.num ^ 3 - 3 * x.num ^ 2 * (x.den : ℤ)
      + 2 * x.num * (x.den : ℤ) ^ 2 + (x.den : ℤ) ^ 3 = 0 := by
    exact_mod_cast h0
  have hd1 : (1 : ℤ) ≤ (x.den : ℤ) := by
    have := x.pos
    omega
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  exact no_integer_root hd1 hcop key

/-- On 53a1, `2y + x + 1 ≠ 0` for every rational affine point: otherwise
`g(x) = (2y + x + 1)² = 0`. -/
theorem w_ne_zero {x y : ℚ} (h : E53a1.toAffine.Equation x y) :
    2 * y + x + 1 ≠ 0 := by
  intro h0
  apply g_ne_zero x
  rw [← w_sq h, h0]
  norm_num

/-- `negY` on 53a1 is `−y − x − 1` (`a₁ = 1`, `a₃ = 1`). -/
lemma negY_eq (x y : ℚ) : E53a1.toAffine.negY x y = -y - x - 1 := by
  simp only [Affine.negY, E53a1_a₁, E53a1_a₃]
  ring

/-- No rational affine point of 53a1 is 2-torsion: `y ≠ negY x y`. -/
theorem y_ne_negY {x y : ℚ} (h : E53a1.toAffine.Equation x y) :
    y ≠ E53a1.toAffine.negY x y := by
  rw [negY_eq]
  intro hy
  exact w_ne_zero h (by linarith)

/-- The tangent slope at a rational affine point of 53a1 is
`(3x² − 2x − y)/(2y + x + 1)` (the `−a₁y` term survives, `a₁ = 1`). -/
theorem slope_eq {x y : ℚ} (h : E53a1.toAffine.Nonsingular x y) :
    E53a1.toAffine.slope x x y y = (3 * x ^ 2 - 2 * x - y) / (2 * y + x + 1) := by
  rw [Affine.slope_of_Y_ne rfl (y_ne_negY h.left), negY_eq]
  have hnum : 3 * x ^ 2 + 2 * E53a1.toAffine.a₂ * x + E53a1.toAffine.a₄
      - E53a1.toAffine.a₁ * y = 3 * x ^ 2 - 2 * x - y := by
    simp only [E53a1_a₁, E53a1_a₂, E53a1_a₄]
    ring
  have hden : y - (-y - x - 1) = 2 * y + x + 1 := by ring
  rw [hnum, hden]

/-- **The duplication formula for 53a1.** For any rational affine point
`P = some h` at `(x, y)`, the double `P + P` is again an affine point
`some h'` whose x-coordinate is exactly `f(x)/g(x)`. The on-curve certificate
is `(N² + Nw + (1−2x)w²)·g − f·w² = ((3−8x)·g − 4f)·E` with
`N = 3x² − 2x − y`, `w = 2y + x + 1`, `E = y² + xy + y − x³ + x²`. -/
theorem dbl_x {x y : ℚ} (h : E53a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E53a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x := by
  have hy : y ≠ E53a1.toAffine.negY x y := y_ne_negY h.left
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy, ?_⟩
  -- goal: addX x x (slope x x y y) = f x / g x
  have hg : g x ≠ 0 := g_ne_zero x
  have hw : 2 * y + x + 1 ≠ 0 := w_ne_zero h.left
  have hEq : y ^ 2 + x * y + y = x ^ 3 - x ^ 2 := on_curve h.left
  rw [slope_eq h]
  simp only [Affine.addX, E53a1_a₁, E53a1_a₂]
  field_simp
  simp only [f, g]
  linear_combination ((3 - 8 * x) * (4 * x ^ 3 - 3 * x ^ 2 + 2 * x + 1)
      - 4 * (x ^ 4 - x ^ 2 - 2 * x + 1)) * hEq

/-! ## §C — the duplication height inequality (r133 pattern, κ = 172)

Reuses r133's curve-generic `naiveHeight_div_int` for the reduction
bookkeeping; only the curve-specific casts and the 172-bound are new. -/

/-- The §A bound transported to `naiveHeight`:
`H⁴ ≤ 172 · naiveHeight (F/D)` for `H = max |a| |b|`. -/
theorem height_bound_of_coprime {a b : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 172 * naiveHeight ((F a b : ℚ) / (D a b : ℚ)) := by
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

/-- **The duplication height inequality for 53a1.** For every rational `x`
(no on-curve hypothesis: `g` never vanishes on ℚ):
`naiveHeight x ^ 4 ≤ 172 * naiveHeight (f x / g x)`. -/
theorem duplication_height_bound (x : ℚ) :
    naiveHeight x ^ 4 ≤ 172 * naiveHeight (f x / g x) := by
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
    _ ≤ 172 * naiveHeight
          ((F x.num (x.den : ℤ) : ℚ) / (D x.num (x.den : ℤ) : ℚ)) :=
        height_bound_of_coprime hcop hb hD
    _ = 172 * naiveHeight (f x / g x) := by rw [← hfg]

/-- **Duplication height step on the curve.** For any rational affine point
`P = some h` of 53a1 at `(x, y)`: `P + P` is an affine point `some h'` at
some `(x', y')` with `naiveHeight x ^ 4 ≤ 172 * naiveHeight x'`. -/
theorem dbl_height {x y : ℚ} (h : E53a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E53a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧
        naiveHeight x ^ 4 ≤ 172 * naiveHeight x' := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
  refine ⟨x', y', h', hadd, ?_⟩
  rw [hx']
  exact duplication_height_bound x

/-! ## §D1 — the base point `P = (0, 0)` on 53a1 -/

/-- `(0, 0)` is a nonsingular rational point of 53a1: the equation reads
`0 = 0` (`a₆ = 0`), and the Y-partial there is `a₃ = 1 ≠ 0`. -/
theorem P53_nonsingular : E53a1.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  refine ⟨rfl, Or.inl ?_⟩
  show (1 : ℚ) ≠ 0
  norm_num

/-- **The base point** `P53 = (0, 0) ∈ E53a1(ℚ)`. -/
noncomputable def P53 : E53a1.toAffine.Point := Point.some P53_nonsingular

/-! ## §D2 — the doubling chain -/

/-- The doubling chain: `chain 0 = (0, 0, proof)`, and `chain (n+1)` is the
affine data of `chain n + chain n` chosen from `dbl_height`. -/
noncomputable def chain : ℕ → Σ' (x y : ℚ), E53a1.toAffine.Nonsingular x y :=
  Nat.rec (motive := fun _ => Σ' (x y : ℚ), E53a1.toAffine.Nonsingular x y)
    ⟨0, 0, P53_nonsingular⟩
    fun _ c =>
      ⟨(dbl_height c.2.2).choose,
       (dbl_height c.2.2).choose_spec.choose,
       (dbl_height c.2.2).choose_spec.choose_spec.choose⟩

/-- The x-coordinate along the chain. -/
noncomputable def xs (n : ℕ) : ℚ := (chain n).1

/-- The chain as points of the group `E53a1(ℚ)`. -/
noncomputable def pts (n : ℕ) : E53a1.toAffine.Point := Point.some (chain n).2.2

@[simp] lemma xs_zero : xs 0 = 0 := rfl

lemma pts_zero : pts 0 = P53 := rfl

/-- Each chain step doubles the point. -/
lemma pts_succ (n : ℕ) : pts (n + 1) = pts n + pts n :=
  ((dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.1).symm

/-- Each chain step satisfies the quartic height inequality (κ = 172). -/
lemma height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ 172 * naiveHeight (xs (n + 1)) :=
  (dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.2

/-- The chain is the `2ⁿ`-multiples of the base point: `pts n = 2ⁿ • P53`. -/
lemma pts_eq_two_pow_smul (n : ℕ) : pts n = ((2 : ℤ) ^ n) • P53 := by
  induction n with
  | zero => rw [pow_zero, one_zsmul, pts_zero]
  | succ k ih =>
      have h2 : ((2 : ℤ) ^ (k + 1)) = 2 ^ k + 2 ^ k := by ring
      rw [pts_succ, ih, h2, add_zsmul]

/-! ## §D3 — the x-coordinates pinned exactly: `xs (n+1) = f (xs n) / g (xs n)` -/

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

/-- `x(4P) = −1/4`. -/
lemma xs_two : xs 2 = -1 / 4 := by
  rw [xs_succ 1, xs_one]; norm_num [f, g]

/-- `x(8P) = 369/64`. -/
lemma xs_three : xs 3 = 369 / 64 := by
  rw [xs_succ 2, xs_two]; norm_num [f, g]

/-- `naiveHeight (x(8P)) = 369` — the fraction is already reduced:
`gcd(369, 64) = 1` (`369 = 9·41` is odd, `64 = 2⁶`). -/
lemma naiveHeight_xs_three : naiveHeight (xs 3) = 369 := by
  have h3 : xs 3 = ((369 : ℤ) : ℚ) / ((64 : ℤ) : ℚ) := by
    rw [xs_three]; norm_num
  have hg : Int.gcd 369 64 = 1 := by norm_num
  rw [h3, DuplicationHeightBound37a1.naiveHeight_div_int 369 64 (by norm_num), hg]
  norm_num

/-- The threshold check: `x(8P)` clears the curve constant `κ = 172`. -/
lemma threshold : 172 < naiveHeight (xs 3) := by
  rw [naiveHeight_xs_three]; norm_num

/-! ## §D4 — firing the driver: infinitely many x-coordinates -/

/-- **The chain from `8P` on has infinite x-coordinate range**: the quartic
step starts above the threshold, so r130's growth engine applies. -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 3)).Infinite :=
  infinite_of_duplication_step (κ := 172) (fun n => xs (n + 3))
    (by norm_num) (fun n => height_step (n + 3)) threshold

/-! ## §D5 — non-torsion: a finite orbit cannot contain an infinite image -/

/-- The x-coordinate projection on the point group (`0` at the identity). -/
def X : E53a1.toAffine.Point → ℚ
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

lemma X_pts (n : ℕ) : X (pts n) = xs n := rfl

/-- **CAPSTONE 1 — `P = (0, 0)` is non-torsion on 53a1.** If `P53` had
finite order, `AddSubgroup.zmultiples P53` would be a finite set; its image
under `X` would be finite, yet it contains the infinite range of §D4. -/
theorem P_nonTorsion : ¬ IsOfFinAddOrder P53 := by
  intro hfin
  have hfinite := hfin.finite_zmultiples
  have hsub : (Set.range fun n => xs (n + 3))
      ⊆ X '' (AddSubgroup.zmultiples P53 : Set _) := by
    rintro q ⟨n, rfl⟩
    refine ⟨pts (n + 3), ?_, X_pts (n + 3)⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨(2 : ℤ) ^ (n + 3), (pts_eq_two_pow_smul (n + 3)).symm⟩
  exact xs_shifted_infinite ((hfinite.image X).subset hsub)

/-! ## §D6 — THE FLAG: rank ≥ 1 for 53a1 -/

/-- The r129 certificate, discharged: `P53` has infinite order in
`E53a1(ℚ)`. -/
theorem P53_certificate : NonTorsionCertificate E53a1.toAffine P53 :=
  P_nonTorsion

/-- **CAPSTONE 2 — the Mordell–Weil rank of 53a1 is at least 1.** -/
theorem E53a1_rank_ge_one : 1 ≤ Module.rank ℤ E53a1.toAffine.Point :=
  mordellWeil_rank_ge_one E53a1.toAffine P53 P_nonTorsion

end PrincipiaTractalis.E53a1RankOne

#print axioms PrincipiaTractalis.E53a1RankOne.bezout_b
#print axioms PrincipiaTractalis.E53a1RankOne.bezout_a
#print axioms PrincipiaTractalis.E53a1RankOne.gcd_dvd_53
#print axioms PrincipiaTractalis.E53a1RankOne.size_bound
#print axioms PrincipiaTractalis.E53a1RankOne.reduced_height_bound'
#print axioms PrincipiaTractalis.E53a1RankOne.dbl_x
#print axioms PrincipiaTractalis.E53a1RankOne.duplication_height_bound
#print axioms PrincipiaTractalis.E53a1RankOne.dbl_height
#print axioms PrincipiaTractalis.E53a1RankOne.naiveHeight_xs_three
#print axioms PrincipiaTractalis.E53a1RankOne.P_nonTorsion
#print axioms PrincipiaTractalis.E53a1RankOne.P53_certificate
#print axioms PrincipiaTractalis.E53a1RankOne.E53a1_rank_ge_one
