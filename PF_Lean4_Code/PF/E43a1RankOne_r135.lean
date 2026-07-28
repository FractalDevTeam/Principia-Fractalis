/-
# PF.E43a1RankOne_r135

★★★ 2026-07-28 — THE SECOND CURVE OF THE NON-TORSION COHORT ★★★

Replicates the completed five-stone 37a1 arc (r130–r134) for the rank-1
curve **43a1** (`y² + y = x³ + x²`) and its rational point `P = (0, 0)`,
as ONE self-contained file (the curve-generic lemmas
`exists_common_factor` / `naiveHeight_div_int` are REUSED from r133 by
import; everything curve-specific is re-derived here):

  * `P_nonTorsion : ¬ IsOfFinAddOrder P43` — the point `(0, 0)` has
    infinite order in `E43a1(ℚ)`;
  * `E43a1_rank_ge_one : 1 ≤ Module.rank ℤ E43a1.toAffine.Point` — the FLAG.

Construction (the 37a1 pattern, new data):

  1. Bézout layer (r131-clone): for `F(a,b) = a⁴ − 2ab³ − b⁴` and
     `D(a,b) = b·(4a³ + 4a²b + b³)` (so `x(2P) = F/D` for `x = a/b`),
     explicit `ring`-checked identities
       `(48a² + 32ab − 16b²)·F + (−12a³ + 4a²b + 27b³)·G3 = 43·b⁶`
       `(43a³ + 20a²b + 4ab² + 6b³)·F + (−5a³ + 4a²b + 16ab² + 6b³)·D = 43·a⁷`
     give `gcd(F, D) ∣ 43` for coprime `(a, b)` and the size bound
     `43·H⁷ ≤ 139·H³·max |F| |D|` (cofactor sums: b-side `96 + 43 = 139`,
     a-side `73 + 31 = 104 ≤ 139`) — hence **κ = 139**.
  2. Curve layer (r132-clone): on 43a1, `(2y + 1)² = g(x)` with
     `g(x) = 4x³ + 4x² + 1`; `g` has no rational roots (integer core
     `4n³ + 4n²d + d³ = 0` is impossible for coprime `(n, d)`), so no
     rational affine point is 2-torsion; the tangent slope is
     `(3x² + 2x)/(2y + 1)` and `x(P + P) = f(x)/g(x)` with
     `f(x) = x⁴ − 2x − 1`, via `(3x² + 2x)² − (1 + 2x)·g(x) = f(x)`.
  3. Height join (r133-clone, generic parts imported):
     `naiveHeight x ^ 4 ≤ 139 · naiveHeight (f x / g x)` for EVERY
     rational `x`, transported through the group law as `dbl_height`.
  4. Chain + driver + flag (r134-clone): the doubling chain from `(0, 0)`
     has x-values `0 → −1 → 2 → 11/49 → −8338438/7187761`, heights
     `1, 1, 2, 49, 8338438`; `gcd(8338438, 7187761) = 1` so
     `naiveHeight (xs 4) = 8338438 > 139` and r130's
     `infinite_of_duplication_step` fires; a finite torsion orbit cannot
     contain the infinite x-range, so `P_nonTorsion`, and r129's
     `mordellWeil_rank_ge_one` concludes.

HONEST SCOPE. This file certifies ONE point on ONE curve as non-torsion
and concludes `1 ≤ Module.rank ℤ E43a1(ℚ)` — a LOWER bound only.  It does
not compute the exact rank, says nothing about any other curve of the
cohort, and proves no statement about L-functions or BSD.

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

namespace PrincipiaTractalis.E43a1RankOne

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.MordellWeilRankLowerBound
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the Bézout layer (r131-clone with 43a1 data)

For 43a1 (`y² + y = x³ + x²`): `x(2P) = f(x)/g(x)` with
`f(x) = x⁴ − 2x − 1`, `g(x) = 4x³ + 4x² + 1`. Substituting `x = a/b` and
clearing denominators gives the homogenized pair below. -/

/-- Homogenized duplication numerator for 43a1: `b⁴·f(a/b)`. -/
def F (a b : ℤ) : ℤ := a ^ 4 - 2 * a * b ^ 3 - b ^ 4

/-- Homogenized `g` before the extra factor of `b`: `b³·g(a/b)`. -/
def G3 (a b : ℤ) : ℤ := 4 * a ^ 3 + 4 * a ^ 2 * b + b ^ 3

/-- The duplication denominator form: `x(2P) = F a b / D a b` for `x = a/b`. -/
def D (a b : ℤ) : ℤ := b * G3 a b

/-- **Bézout identity, `b`-side**: eliminates `a` down to `43·b⁶`. -/
theorem bezout_b (a b : ℤ) :
    (48 * a ^ 2 + 32 * a * b - 16 * b ^ 2) * F a b
      + (-12 * a ^ 3 + 4 * a ^ 2 * b + 27 * b ^ 3) * G3 a b = 43 * b ^ 6 := by
  simp only [F, G3]; ring

/-- **Bézout identity, `a`-side**: eliminates `b` down to `43·a⁷`, already in
the `D = b·G3` denominator form. -/
theorem bezout_a (a b : ℤ) :
    (43 * a ^ 3 + 20 * a ^ 2 * b + 4 * a * b ^ 2 + 6 * b ^ 3) * F a b
      + (-5 * a ^ 3 + 4 * a ^ 2 * b + 16 * a * b ^ 2 + 6 * b ^ 3) * D a b
      = 43 * a ^ 7 := by
  simp only [F, D, G3]; ring

/-- `bezout_b` multiplied through by `b`: the `b`-side identity in the
`D`-form that the gcd and size arguments consume. -/
theorem bezout_b_D (a b : ℤ) :
    ((48 * a ^ 2 + 32 * a * b - 16 * b ^ 2) * b) * F a b
      + (-12 * a ^ 3 + 4 * a ^ 2 * b + 27 * b ^ 3) * D a b = 43 * b ^ 7 := by
  simp only [F, D, G3]; ring

/-- **The gcd bound.** For coprime `a b : ℤ`, the gcd of the duplication
numerator and denominator divides `43`: the gcd divides `43·a⁷` and `43·b⁷`,
and coprimality of `a⁷, b⁷` squeezes it into `43`. -/
theorem gcd_dvd_43 {a b : ℤ} (h : IsCoprime a b) :
    (Int.gcd (F a b) (D a b) : ℤ) ∣ 43 := by
  have hdF : (Int.gcd (F a b) (D a b) : ℤ) ∣ F a b := Int.gcd_dvd_left _ _
  have hdD : (Int.gcd (F a b) (D a b) : ℤ) ∣ D a b := Int.gcd_dvd_right _ _
  have hb7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 43 * b ^ 7 := by
    rw [← bezout_b_D a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have ha7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 43 * a ^ 7 := by
    rw [← bezout_a a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have h7 : IsCoprime (a ^ 7) (b ^ 7) := h.pow
  obtain ⟨u, v, huv⟩ := h7
  have key : (43 : ℤ) = u * (43 * a ^ 7) + v * (43 * b ^ 7) := by
    linear_combination (-43 : ℤ) * huv
  rw [key]
  exact dvd_add (ha7.mul_left u) (hb7.mul_left v)

/-- `gcd_dvd_43` in `ℕ`-form. -/
theorem gcd_dvd_43_nat {a b : ℤ} (h : IsCoprime a b) :
    Int.gcd (F a b) (D a b) ∣ 43 := by
  exact_mod_cast gcd_dvd_43 h

/-! ## §2 — the size lower bound

`43·H⁷ ≤ 139·H³·max |F| |D|` with `H = max |a| |b|`. Cofactor coefficient
sums: `b`-side `96 + 43 = 139`, `a`-side `73 + 31 = 104 ≤ 139`. -/

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
`|(48a² + 32ab − 16b²)·b| ≤ 96·H³`. -/
private theorem c1_bound (a b : ℤ) :
    ((48 * a ^ 2 + 32 * a * b - 16 * b ^ 2) * b).natAbs
      ≤ 96 * (max a.natAbs b.natAbs) ^ 3 := by
  have h48 : ((48 : ℤ)).natAbs = 48 := rfl
  have h32 : ((32 : ℤ)).natAbs = 32 := rfl
  have h16 : ((16 : ℤ)).natAbs = 16 := rfl
  have e1 : ((48 : ℤ) * a ^ 2).natAbs = 48 * a.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h48]
  have e2 : ((32 : ℤ) * a * b).natAbs = 32 * a.natAbs * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, h32]
  have e3 : ((16 : ℤ) * b ^ 2).natAbs = 16 * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h16]
  calc ((48 * a ^ 2 + 32 * a * b - 16 * b ^ 2) * b).natAbs
      = (48 * a ^ 2 + 32 * a * b - 16 * b ^ 2).natAbs * b.natAbs :=
        Int.natAbs_mul _ _
    _ ≤ ((48 * a ^ 2 + 32 * a * b).natAbs + (16 * b ^ 2).natAbs) * b.natAbs :=
        Nat.mul_le_mul (Int.natAbs_sub_le _ _) le_rfl
    _ ≤ ((((48 : ℤ) * a ^ 2).natAbs + ((32 : ℤ) * a * b).natAbs)
          + ((16 : ℤ) * b ^ 2).natAbs) * b.natAbs :=
        Nat.mul_le_mul (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) le_rfl
    _ = (48 * a.natAbs ^ 2 + 32 * a.natAbs * b.natAbs + 16 * b.natAbs ^ 2)
          * b.natAbs := by rw [e1, e2, e3]
    _ = 48 * (a.natAbs ^ 2 * b.natAbs) + 32 * (a.natAbs * b.natAbs ^ 2)
          + 16 * b.natAbs ^ 3 := by ring
    _ ≤ 96 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono21 a b
        have m2 := mono12 a b
        have m3 := mono03 a b
        linarith

/-- Cofactor bound, `b`-side, second cofactor:
`|−12a³ + 4a²b + 27b³| ≤ 43·H³`. -/
private theorem c2_bound (a b : ℤ) :
    (-12 * a ^ 3 + 4 * a ^ 2 * b + 27 * b ^ 3).natAbs
      ≤ 43 * (max a.natAbs b.natAbs) ^ 3 := by
  have h12 : ((-12 : ℤ)).natAbs = 12 := rfl
  have h4 : ((4 : ℤ)).natAbs = 4 := rfl
  have h27 : ((27 : ℤ)).natAbs = 27 := rfl
  have e1 : ((-12 : ℤ) * a ^ 3).natAbs = 12 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  have e2 : ((4 : ℤ) * a ^ 2 * b).natAbs = 4 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h4]
  have e3 : ((27 : ℤ) * b ^ 3).natAbs = 27 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h27]
  calc (-12 * a ^ 3 + 4 * a ^ 2 * b + 27 * b ^ 3).natAbs
      ≤ (-12 * a ^ 3 + 4 * a ^ 2 * b).natAbs + ((27 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ (((-12 : ℤ) * a ^ 3).natAbs + ((4 : ℤ) * a ^ 2 * b).natAbs)
          + ((27 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ = 12 * a.natAbs ^ 3 + 4 * a.natAbs ^ 2 * b.natAbs
          + 27 * b.natAbs ^ 3 := by rw [e1, e2, e3]
    _ ≤ 43 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, first cofactor:
`|43a³ + 20a²b + 4ab² + 6b³| ≤ 73·H³`. -/
private theorem c3_bound (a b : ℤ) :
    (43 * a ^ 3 + 20 * a ^ 2 * b + 4 * a * b ^ 2 + 6 * b ^ 3).natAbs
      ≤ 73 * (max a.natAbs b.natAbs) ^ 3 := by
  have h43 : ((43 : ℤ)).natAbs = 43 := rfl
  have h20 : ((20 : ℤ)).natAbs = 20 := rfl
  have h4 : ((4 : ℤ)).natAbs = 4 := rfl
  have h6 : ((6 : ℤ)).natAbs = 6 := rfl
  have e1 : ((43 : ℤ) * a ^ 3).natAbs = 43 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h43]
  have e2 : ((20 : ℤ) * a ^ 2 * b).natAbs = 20 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h20]
  have e3 : ((4 : ℤ) * a * b ^ 2).natAbs = 4 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h4]
  have e4 : ((6 : ℤ) * b ^ 3).natAbs = 6 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h6]
  calc (43 * a ^ 3 + 20 * a ^ 2 * b + 4 * a * b ^ 2 + 6 * b ^ 3).natAbs
      ≤ (43 * a ^ 3 + 20 * a ^ 2 * b + 4 * a * b ^ 2).natAbs
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ ((43 * a ^ 3 + 20 * a ^ 2 * b).natAbs + ((4 : ℤ) * a * b ^ 2).natAbs)
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((((43 : ℤ) * a ^ 3).natAbs + ((20 : ℤ) * a ^ 2 * b).natAbs)
            + ((4 : ℤ) * a * b ^ 2).natAbs)
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = 43 * a.natAbs ^ 3 + 20 * a.natAbs ^ 2 * b.natAbs
          + 4 * a.natAbs * b.natAbs ^ 2 + 6 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 73 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, second cofactor:
`|−5a³ + 4a²b + 16ab² + 6b³| ≤ 31·H³`. -/
private theorem c4_bound (a b : ℤ) :
    (-5 * a ^ 3 + 4 * a ^ 2 * b + 16 * a * b ^ 2 + 6 * b ^ 3).natAbs
      ≤ 31 * (max a.natAbs b.natAbs) ^ 3 := by
  have h5 : ((-5 : ℤ)).natAbs = 5 := rfl
  have h4 : ((4 : ℤ)).natAbs = 4 := rfl
  have h16 : ((16 : ℤ)).natAbs = 16 := rfl
  have h6 : ((6 : ℤ)).natAbs = 6 := rfl
  have e1 : ((-5 : ℤ) * a ^ 3).natAbs = 5 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h5]
  have e2 : ((4 : ℤ) * a ^ 2 * b).natAbs = 4 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h4]
  have e3 : ((16 : ℤ) * a * b ^ 2).natAbs = 16 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h16]
  have e4 : ((6 : ℤ) * b ^ 3).natAbs = 6 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h6]
  calc (-5 * a ^ 3 + 4 * a ^ 2 * b + 16 * a * b ^ 2 + 6 * b ^ 3).natAbs
      ≤ (-5 * a ^ 3 + 4 * a ^ 2 * b + 16 * a * b ^ 2).natAbs
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ ((-5 * a ^ 3 + 4 * a ^ 2 * b).natAbs + ((16 : ℤ) * a * b ^ 2).natAbs)
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((((-5 : ℤ) * a ^ 3).natAbs + ((4 : ℤ) * a ^ 2 * b).natAbs)
            + ((16 : ℤ) * a * b ^ 2).natAbs)
          + ((6 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = 5 * a.natAbs ^ 3 + 4 * a.natAbs ^ 2 * b.natAbs
          + 16 * a.natAbs * b.natAbs ^ 2 + 6 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 31 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- The `b`-branch of the size bound: `43·|b|⁷ ≤ 139·H³·max |F| |D|`. -/
theorem size_bound_b (a b : ℤ) :
    43 * b.natAbs ^ 7
      ≤ 139 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h43 : ((43 : ℤ)).natAbs = 43 := rfl
  have h0 : ((43 : ℤ) * b ^ 7).natAbs = 43 * b.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h43]
  have hterm1 : (((48 * a ^ 2 + 32 * a * b - 16 * b ^ 2) * b) * F a b).natAbs
      ≤ 96 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c1_bound a b) (le_max_left _ _)
  have hterm2 : ((-12 * a ^ 3 + 4 * a ^ 2 * b + 27 * b ^ 3) * D a b).natAbs
      ≤ 43 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c2_bound a b) (le_max_right _ _)
  calc 43 * b.natAbs ^ 7 = ((43 : ℤ) * b ^ 7).natAbs := h0.symm
    _ = (((48 * a ^ 2 + 32 * a * b - 16 * b ^ 2) * b) * F a b
          + (-12 * a ^ 3 + 4 * a ^ 2 * b + 27 * b ^ 3) * D a b).natAbs := by
        rw [bezout_b_D a b]
    _ ≤ (((48 * a ^ 2 + 32 * a * b - 16 * b ^ 2) * b) * F a b).natAbs
          + ((-12 * a ^ 3 + 4 * a ^ 2 * b + 27 * b ^ 3) * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 96 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 43 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 139 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring

/-- The `a`-branch of the size bound: `43·|a|⁷ ≤ 139·H³·max |F| |D|`
(the natural constant is `104`; we relax to `139` to share one constant). -/
theorem size_bound_a (a b : ℤ) :
    43 * a.natAbs ^ 7
      ≤ 139 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h43 : ((43 : ℤ)).natAbs = 43 := rfl
  have h0 : ((43 : ℤ) * a ^ 7).natAbs = 43 * a.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h43]
  have hterm1 : ((43 * a ^ 3 + 20 * a ^ 2 * b + 4 * a * b ^ 2 + 6 * b ^ 3)
        * F a b).natAbs
      ≤ 73 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c3_bound a b) (le_max_left _ _)
  have hterm2 : ((-5 * a ^ 3 + 4 * a ^ 2 * b + 16 * a * b ^ 2 + 6 * b ^ 3)
        * D a b).natAbs
      ≤ 31 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c4_bound a b) (le_max_right _ _)
  calc 43 * a.natAbs ^ 7 = ((43 : ℤ) * a ^ 7).natAbs := h0.symm
    _ = ((43 * a ^ 3 + 20 * a ^ 2 * b + 4 * a * b ^ 2 + 6 * b ^ 3) * F a b
          + (-5 * a ^ 3 + 4 * a ^ 2 * b + 16 * a * b ^ 2 + 6 * b ^ 3)
              * D a b).natAbs := by
        rw [bezout_a a b]
    _ ≤ ((43 * a ^ 3 + 20 * a ^ 2 * b + 4 * a * b ^ 2 + 6 * b ^ 3) * F a b).natAbs
          + ((-5 * a ^ 3 + 4 * a ^ 2 * b + 16 * a * b ^ 2 + 6 * b ^ 3)
              * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 73 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 31 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 104 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring
    _ ≤ 139 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) le_rfl

/-- **The size lower bound.** For all `a b : ℤ`, with `H = max |a| |b|`:
`43·H⁷ ≤ 139·H³·max |F(a,b)| |D(a,b)|`. -/
theorem size_bound (a b : ℤ) :
    43 * (max a.natAbs b.natAbs) ^ 7
      ≤ 139 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  rcases le_total a.natAbs b.natAbs with hab | hab
  · have h := size_bound_b a b
    rw [max_eq_right hab] at h ⊢
    exact h
  · have h := size_bound_a a b
    rw [max_eq_left hab] at h ⊢
    exact h

end SizeBound

/-! ## §3 — the division consequence: height survives gcd cancellation -/

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

/-- Pure-`ℕ` descent arithmetic: from `43·H⁷ ≤ 139·H³·(M·d)` with `d ≤ 43`
and `1 ≤ H`, cancel `H³` to get `43·H⁴ ≤ 139·43·M`. -/
private theorem descend {H M d : ℕ} (hd : d ≤ 43) (hH : 1 ≤ H)
    (hkey : 43 * H ^ 7 ≤ 139 * H ^ 3 * (M * d)) : 43 * H ^ 4 ≤ 139 * 43 * M := by
  have hH0 : 0 < H := hH
  have h2 : (43 * H ^ 4) * H ^ 3 ≤ (139 * 43 * M) * H ^ 3 := by
    calc (43 * H ^ 4) * H ^ 3 = 43 * H ^ 7 := by ring
      _ ≤ 139 * H ^ 3 * (M * d) := hkey
      _ ≤ 139 * H ^ 3 * (M * 43) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hd)
      _ = (139 * 43 * M) * H ^ 3 := by ring
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos hH0 3)

/-- **The reduced height bound.** For coprime `a b` with `b ≠ 0`, after
dividing the duplication pair `(F, D)` by `gcd(F, D)` (which divides `43`),
the reduced max still dominates the fourth power of the input height. -/
theorem reduced_height_bound {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (_hD : D a b ≠ 0) :
    43 * (max a.natAbs b.natAbs) ^ 4
      ≤ 139 * 43 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have hd43 : Int.gcd (F a b) (D a b) ≤ 43 :=
    Nat.le_of_dvd (by norm_num) (gcd_dvd_43_nat h)
  have hH1 : 1 ≤ max a.natAbs b.natAbs :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
      (le_max_right _ _)
  have hsplit :=
    max_natAbs_split (n := Int.gcd (F a b) (D a b))
      (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have key := size_bound a b
  rw [hsplit] at key
  exact descend hd43 hH1 key

/-- `reduced_height_bound` with the common factor `43` cancelled:
`H⁴ ≤ 139·max |F/g| |D/g|`. Cleanest form for the height join. -/
theorem reduced_height_bound' {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 139 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have key := reduced_height_bound h hb hD
  have key2 : 43 * (max a.natAbs b.natAbs) ^ 4
      ≤ 43 * (139 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by
    calc 43 * (max a.natAbs b.natAbs) ^ 4
        ≤ 139 * 43 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := key
      _ = 43 * (139 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by ring
  exact Nat.le_of_mul_le_mul_left key2 (by norm_num)

end Reduced

/-! ## §4 — the curve 43a1 and the duplication formula (r132-clone) -/

/-- **Curve 43a1**: `y² + y = x³ + x²`, i.e.
`(a₁, a₂, a₃, a₄, a₆) = (0, 1, 1, 0, 0)`. -/
def E43a1 : WeierstrassCurve ℚ := ⟨0, 1, 1, 0, 0⟩

@[simp] lemma E43a1_a₁ : E43a1.a₁ = 0 := rfl
@[simp] lemma E43a1_a₂ : E43a1.a₂ = 1 := rfl
@[simp] lemma E43a1_a₃ : E43a1.a₃ = 1 := rfl
@[simp] lemma E43a1_a₄ : E43a1.a₄ = 0 := rfl
@[simp] lemma E43a1_a₆ : E43a1.a₆ = 0 := rfl

/-- The duplication numerator `f(x) = x⁴ − 2x − 1` for 43a1. -/
def f (x : ℚ) : ℚ := x ^ 4 - 2 * x - 1

/-- The duplication denominator `g(x) = 4x³ + 4x² + 1` (= ψ₂²) for 43a1. -/
def g (x : ℚ) : ℚ := 4 * x ^ 3 + 4 * x ^ 2 + 1

/-- On 43a1, `(2y + 1)² = g(x)`: four times the Weierstrass equation
`y² + y = x³ + x²` plus one. -/
theorem two_y_add_one_sq {x y : ℚ} (h : E43a1.toAffine.Equation x y) :
    (2 * y + 1) ^ 2 = g x := by
  rw [Affine.equation_iff] at h
  simp only [E43a1_a₁, E43a1_a₂, E43a1_a₃, E43a1_a₄, E43a1_a₆] at h
  simp only [g]
  linear_combination 4 * h

/-- Integer core of the rational root theorem for `g`: no reduced fraction
`n/d` (`d ≥ 1`, `gcd(n, d) = 1`) satisfies `4n³ + 4n²d + d³ = 0`.
From the equation, `n ∣ d³` forces `n = ±1` and `d ∣ 4n³` forces `d ∣ 4`;
the candidates `±1, ±1/2, ±1/4` all fail. -/
lemma no_integer_root {n d : ℤ} (hd1 : 1 ≤ d) (hcop : IsCoprime n d)
    (key : 4 * n ^ 3 + 4 * n ^ 2 * d + d ^ 3 = 0) : False := by
  -- n ∣ d³ since d³ = n · (−4n² − 4nd)
  have hn_dvd : n ∣ d ^ 3 := ⟨-4 * n ^ 2 - 4 * n * d, by linear_combination key⟩
  have hn_unit : IsUnit n :=
    (hcop.pow_right (n := 3)).isUnit_of_dvd' dvd_rfl hn_dvd
  -- d ∣ 4n³ since 4n³ = d · (−4n² − d²)
  have hd_dvd : d ∣ 4 * n ^ 3 := ⟨-4 * n ^ 2 - d ^ 2, by linear_combination key⟩
  have hd4 : d ∣ 4 :=
    (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right hd_dvd
  have hd_le : d ≤ 4 := Int.le_of_dvd (by norm_num) hd4
  have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases Int.isUnit_iff.mp hn_unit with rfl | rfl <;>
    rcases hd_cases with rfl | rfl | rfl | rfl <;>
      norm_num at key

/-- **`g` has no rational roots.**  In particular no rational affine point of
43a1 is 2-torsion, so doubling never leaves the affine chart. -/
theorem g_ne_zero (x : ℚ) : g x ≠ 0 := by
  intro hg
  have hg' : 4 * x ^ 3 + 4 * x ^ 2 + 1 = 0 := by simpa [g] using hg
  have hden : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  -- clear denominators: 4n³ + 4n²d + d³ = 0 over ℚ, then over ℤ
  have h0 : 4 * (x.num : ℚ) ^ 3 + 4 * (x.num : ℚ) ^ 2 * (x.den : ℚ)
      + (x.den : ℚ) ^ 3 = 0 := by
    have hxq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    rw [hxq] at hg'
    field_simp at hg'
    linear_combination hg'
  have key : 4 * x.num ^ 3 + 4 * x.num ^ 2 * (x.den : ℤ) + (x.den : ℤ) ^ 3 = 0 := by
    exact_mod_cast h0
  have hd1 : (1 : ℤ) ≤ (x.den : ℤ) := by
    have := x.pos
    omega
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  exact no_integer_root hd1 hcop key

/-- On 43a1, `2y + 1 ≠ 0` for every rational affine point: otherwise
`g(x) = (2y + 1)² = 0`, contradicting `g_ne_zero`. -/
theorem two_y_add_one_ne_zero {x y : ℚ} (h : E43a1.toAffine.Equation x y) :
    2 * y + 1 ≠ 0 := by
  intro h0
  apply g_ne_zero x
  rw [← two_y_add_one_sq h, h0]
  norm_num

/-- `negY` on 43a1 is `-y - 1` (since `a₁ = 0`, `a₃ = 1`). -/
lemma negY_eq (x y : ℚ) : E43a1.toAffine.negY x y = -y - 1 := by
  simp [Affine.negY]

/-- No rational affine point of 43a1 is 2-torsion: `y ≠ negY x y`. -/
theorem y_ne_negY {x y : ℚ} (h : E43a1.toAffine.Equation x y) :
    y ≠ E43a1.toAffine.negY x y := by
  rw [negY_eq]
  intro hy
  exact two_y_add_one_ne_zero h (by linarith)

/-- The tangent slope at a rational affine point of 43a1 is
`(3x² + 2x)/(2y + 1)`. -/
theorem slope_eq {x y : ℚ} (h : E43a1.toAffine.Nonsingular x y) :
    E43a1.toAffine.slope x x y y = (3 * x ^ 2 + 2 * x) / (2 * y + 1) := by
  rw [Affine.slope_of_Y_ne rfl (y_ne_negY h.left), negY_eq]
  have hnum : 3 * x ^ 2 + 2 * E43a1.toAffine.a₂ * x + E43a1.toAffine.a₄
      - E43a1.toAffine.a₁ * y = 3 * x ^ 2 + 2 * x := by
    simp only [E43a1_a₁, E43a1_a₂, E43a1_a₄]
    ring
  have hden : y - (-y - 1) = 2 * y + 1 := by ring
  rw [hnum, hden]

/-- **The duplication formula for 43a1.**  For any rational affine point
`P = some h` at `(x, y)`, the double `P + P` is again an affine point
`some h'`, and its x-coordinate is exactly `f(x)/g(x)`.
The x-coordinate identity is `(3x² + 2x)² − (1 + 2x)·g(x) = f(x)` combined
with `(2y + 1)² = g(x) ≠ 0`. -/
theorem dbl_x {x y : ℚ} (h : E43a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E43a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x := by
  have hy : y ≠ E43a1.toAffine.negY x y := y_ne_negY h.left
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy, ?_⟩
  -- goal: addX x x (slope x x y y) = f x / g x
  have hg : g x ≠ 0 := g_ne_zero x
  have h2y : 2 * y + 1 ≠ 0 := two_y_add_one_ne_zero h.left
  have hsq : (2 * y + 1) ^ 2 = g x := two_y_add_one_sq h.left
  rw [slope_eq h]
  simp only [Affine.addX, E43a1_a₁, E43a1_a₂]
  rw [div_pow, hsq]
  field_simp
  simp only [f, g]
  ring

/-! ## §5 — the height join (r133-clone; generic lemmas imported from r133) -/

/-- The Bézout bound transported to `naiveHeight`:
`H⁴ ≤ 139 · naiveHeight (F/D)` for `H = max |a| |b|`. -/
theorem height_bound_of_coprime {a b : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 139 * naiveHeight ((F a b : ℚ) / (D a b : ℚ)) := by
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

/-- **The duplication height inequality for 43a1.** For every rational `x`
(no on-curve hypothesis: `g` never vanishes on ℚ):
`naiveHeight x ^ 4 ≤ 139 · naiveHeight (f x / g x)`. -/
theorem duplication_height_bound (x : ℚ) :
    naiveHeight x ^ 4 ≤ 139 * naiveHeight (f x / g x) := by
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
    _ ≤ 139 * naiveHeight
          ((F x.num (x.den : ℤ) : ℚ) / (D x.num (x.den : ℤ) : ℚ)) :=
        height_bound_of_coprime hcop hb hD
    _ = 139 * naiveHeight (f x / g x) := by rw [← hfg]

/-- **Duplication height step on the curve.** For any rational affine point
`P = some h` of 43a1 at `(x, y)`: `P + P` is an affine point `some h'` at
some `(x', y')` with `naiveHeight x ^ 4 ≤ 139 * naiveHeight x'`. -/
theorem dbl_height {x y : ℚ} (h : E43a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E43a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧
        naiveHeight x ^ 4 ≤ 139 * naiveHeight x' := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
  refine ⟨x', y', h', hadd, ?_⟩
  rw [hx']
  exact duplication_height_bound x

/-! ## §6 — the base point `P = (0, 0)` on 43a1 (r134-clone) -/

/-- `(0, 0)` is a nonsingular rational point of 43a1: the equation reads
`0 + 0 = 0 + 0` (i.e. `a₆ = 0`), and the Y-partial there is `a₃ = 1 ≠ 0`. -/
theorem P43_nonsingular : E43a1.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  refine ⟨rfl, Or.inl ?_⟩
  show (1 : ℚ) ≠ 0
  norm_num

/-- **The base point** `P43 = (0, 0) ∈ E43a1(ℚ)`. -/
noncomputable def P43 : E43a1.toAffine.Point := Point.some P43_nonsingular

/-! ## §7 — the doubling chain -/

/-- The doubling chain: `chain 0 = (0, 0, proof)`, and `chain (n+1)` is the
affine data of `chain n + chain n` chosen from `dbl_height`. -/
noncomputable def chain : ℕ → Σ' (x y : ℚ), E43a1.toAffine.Nonsingular x y :=
  Nat.rec (motive := fun _ => Σ' (x y : ℚ), E43a1.toAffine.Nonsingular x y)
    ⟨0, 0, P43_nonsingular⟩
    fun _ c =>
      ⟨(dbl_height c.2.2).choose,
       (dbl_height c.2.2).choose_spec.choose,
       (dbl_height c.2.2).choose_spec.choose_spec.choose⟩

/-- The x-coordinate along the chain. -/
noncomputable def xs (n : ℕ) : ℚ := (chain n).1

/-- The chain as points of the group `E43a1(ℚ)`. -/
noncomputable def pts (n : ℕ) : E43a1.toAffine.Point := Point.some (chain n).2.2

@[simp] lemma xs_zero : xs 0 = 0 := rfl

lemma pts_zero : pts 0 = P43 := rfl

/-- Each chain step doubles the point (from `dbl_height`'s `choose_spec`). -/
lemma pts_succ (n : ℕ) : pts (n + 1) = pts n + pts n :=
  ((dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.1).symm

/-- Each chain step satisfies the quartic height inequality (κ = 139). -/
lemma height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ 139 * naiveHeight (xs (n + 1)) :=
  (dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.2

/-- The chain is the `2ⁿ`-multiples of the base point: `pts n = 2ⁿ • P43`. -/
lemma pts_eq_two_pow_smul (n : ℕ) : pts n = ((2 : ℤ) ^ n) • P43 := by
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

/-- `x(2P) = −1`. -/
lemma xs_one : xs 1 = -1 := by
  rw [xs_succ 0, xs_zero]; norm_num [f, g]

/-- `x(4P) = 2`. -/
lemma xs_two : xs 2 = 2 := by
  rw [xs_succ 1, xs_one]; norm_num [f, g]

/-- `x(8P) = 11/49`. -/
lemma xs_three : xs 3 = 11 / 49 := by
  rw [xs_succ 2, xs_two]; norm_num [f, g]

/-- `x(16P) = −8338438/7187761`. -/
lemma xs_four : xs 4 = -8338438 / 7187761 := by
  rw [xs_succ 3, xs_three]; norm_num [f, g]

/-- `naiveHeight (x(16P)) = 8338438` — the fraction is already reduced:
`gcd(8338438, 7187761) = 1` (`7187761 = 7²·383²` and `8338438` is even and
divisible by neither 7 nor 383; certified by `norm_num`'s gcd extension). -/
lemma naiveHeight_xs_four : naiveHeight (xs 4) = 8338438 := by
  have h4 : xs 4 = ((-8338438 : ℤ) : ℚ) / ((7187761 : ℤ) : ℚ) := by
    rw [xs_four]; norm_num
  have hg : Int.gcd (-8338438) 7187761 = 1 := by norm_num
  rw [h4, DuplicationHeightBound37a1.naiveHeight_div_int (-8338438) 7187761
    (by norm_num), hg]
  norm_num

/-- The threshold check: `x(16P)` clears the curve constant `κ = 139`. -/
lemma threshold : 139 < naiveHeight (xs 4) := by
  rw [naiveHeight_xs_four]; norm_num

/-! ## §8 — firing the driver: infinitely many x-coordinates -/

/-- **The chain from `16P` on has infinite x-coordinate range**: the quartic
step starts above the threshold, so r130's growth engine applies. -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 4)).Infinite :=
  infinite_of_duplication_step (κ := 139) (fun n => xs (n + 4))
    (by norm_num) (fun n => height_step (n + 4)) threshold

/-! ## §9 — non-torsion: a finite orbit cannot contain an infinite image -/

/-- The x-coordinate projection on the point group (`0` at the identity). -/
def X : E43a1.toAffine.Point → ℚ
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

lemma X_pts (n : ℕ) : X (pts n) = xs n := rfl

/-- **CAPSTONE 1 — `P = (0, 0)` is non-torsion on 43a1.** If `P43` had
finite order, `AddSubgroup.zmultiples P43` would be a finite set; its image
under `X` would be finite, yet it contains the infinite range of §8 (every
`pts (n+4) = 2^(n+4) • P43` is a `ℤ`-multiple of `P43`). -/
theorem P_nonTorsion : ¬ IsOfFinAddOrder P43 := by
  intro hfin
  have hfinite := hfin.finite_zmultiples
  have hsub : (Set.range fun n => xs (n + 4))
      ⊆ X '' (AddSubgroup.zmultiples P43 : Set _) := by
    rintro q ⟨n, rfl⟩
    refine ⟨pts (n + 4), ?_, X_pts (n + 4)⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨(2 : ℤ) ^ (n + 4), (pts_eq_two_pow_smul (n + 4)).symm⟩
  exact xs_shifted_infinite ((hfinite.image X).subset hsub)

/-! ## §10 — THE FLAG: rank ≥ 1 for 43a1 -/

/-- The r129 certificate, discharged: `P43` has infinite order in
`E43a1(ℚ)`. -/
theorem P43_certificate : NonTorsionCertificate E43a1.toAffine P43 :=
  P_nonTorsion

/-- **CAPSTONE 2 — the Mordell–Weil rank of 43a1 is at least 1.** -/
theorem E43a1_rank_ge_one : 1 ≤ Module.rank ℤ E43a1.toAffine.Point :=
  mordellWeil_rank_ge_one E43a1.toAffine P43 P_nonTorsion

end PrincipiaTractalis.E43a1RankOne

#print axioms PrincipiaTractalis.E43a1RankOne.bezout_b
#print axioms PrincipiaTractalis.E43a1RankOne.bezout_a
#print axioms PrincipiaTractalis.E43a1RankOne.gcd_dvd_43
#print axioms PrincipiaTractalis.E43a1RankOne.size_bound
#print axioms PrincipiaTractalis.E43a1RankOne.reduced_height_bound'
#print axioms PrincipiaTractalis.E43a1RankOne.dbl_x
#print axioms PrincipiaTractalis.E43a1RankOne.duplication_height_bound
#print axioms PrincipiaTractalis.E43a1RankOne.dbl_height
#print axioms PrincipiaTractalis.E43a1RankOne.xs_four
#print axioms PrincipiaTractalis.E43a1RankOne.naiveHeight_xs_four
#print axioms PrincipiaTractalis.E43a1RankOne.P_nonTorsion
#print axioms PrincipiaTractalis.E43a1RankOne.P43_certificate
#print axioms PrincipiaTractalis.E43a1RankOne.E43a1_rank_ge_one
