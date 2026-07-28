/-
# PF.E101a1RankOne_r141

★★★ 2026-07-28 — THE 101a1 STONE OF THE NON-TORSION COHORT ★★★

Replicates the completed five-stone 37a1 arc (r130–r134) for the rank-1
curve **101a1** (`y² + y = x³ + x² − x − 1`) and its rational point
`P = (−1, 0)`, as ONE self-contained file (the curve-generic lemmas
`exists_common_factor` / `naiveHeight_div_int` are REUSED from r133 by
import; everything curve-specific is re-derived here):

  * `P_nonTorsion : ¬ IsOfFinAddOrder P101` — the point `(−1, 0)` has
    infinite order in `E101a1(ℚ)`;
  * `E101a1_rank_ge_one : 1 ≤ Module.rank ℤ E101a1.toAffine.Point` — the FLAG.

Construction (the 37a1/43a1 pattern, new data):

  1. Bézout layer: for `F(a,b) = a⁴ + 2a²b² + 6ab³ + 4b⁴` and
     `D(a,b) = b·(4a³ + 4a²b − 4ab² − 3b³)` (so `x(2P) = F/D` for `x = a/b`),
     explicit `ring`-checked identities
       `(−48a² − 32ab + 80b²)·F + (12a³ − 4a²b + 20ab² + 73b³)·G3 = 101·b⁶`
       `(101a³ − 64a²b − 42ab² + 18b³)·F + (16a³ − 56a²b − 52ab² + 24b³)·D = 101·a⁷`
     give `gcd(F, D) ∣ 101` for coprime `(a, b)` and the size bound
     `101·H⁷ ≤ 373·H³·max |F| |D|` (cofactor sums: b-side `160 + 109 = 269`,
     a-side `225 + 148 = 373`) — hence **κ = 373**.
  2. Curve layer: on 101a1, `(2y + 1)² = g(x)` with
     `g(x) = 4x³ + 4x² − 4x − 3`; `g` has no rational roots (integer core
     `4n³ + 4n²d − 4nd² − 3d³ = 0` is impossible for coprime `(n, d)`:
     `n ∣ 3`, `d ∣ 4`, all 16 candidates fail), so no rational affine point
     is 2-torsion; the tangent slope is `(3x² + 2x − 1)/(2y + 1)` and
     `x(P + P) = f(x)/g(x)` with `f(x) = x⁴ + 2x² + 6x + 4`, via
     `(3x² + 2x − 1)² − (1 + 2x)·g(x) = f(x)`.
  3. Height join (generic parts imported from r133):
     `naiveHeight x ^ 4 ≤ 373 · naiveHeight (f x / g x)` for EVERY
     rational `x`, transported through the group law as `dbl_height`.
  4. Chain + driver + flag: the doubling chain from `(−1, 0)` has x-values
     `−1 → 1 → 13 → 28981/9409`, heights `1, 1, 13, 28981`;
     `gcd(28981, 9409) = 1` (`9409 = 97²`) so
     `naiveHeight (xs 3) = 28981 > 373` and r130's
     `infinite_of_duplication_step` fires; a finite torsion orbit cannot
     contain the infinite x-range, so `P_nonTorsion`, and r129's
     `mordellWeil_rank_ge_one` concludes.

HONEST SCOPE. This file certifies ONE point on ONE curve as non-torsion
and concludes `1 ≤ Module.rank ℤ E101a1(ℚ)` — a LOWER bound only.  It does
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

namespace PrincipiaTractalis.E101a1RankOne

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.MordellWeilRankLowerBound
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the Bézout layer (101a1 data) -/

/-- Homogenized duplication numerator for 101a1: `b⁴·f(a/b)`. -/
def F (a b : ℤ) : ℤ := a ^ 4 + 2 * a ^ 2 * b ^ 2 + 6 * a * b ^ 3 + 4 * b ^ 4

/-- Homogenized `g` before the extra factor of `b`: `b³·g(a/b)`. -/
def G3 (a b : ℤ) : ℤ := 4 * a ^ 3 + 4 * a ^ 2 * b - 4 * a * b ^ 2 - 3 * b ^ 3

/-- The duplication denominator form: `x(2P) = F a b / D a b` for `x = a/b`. -/
def D (a b : ℤ) : ℤ := b * G3 a b

/-- **Bézout identity, `b`-side**: eliminates `a` down to `101·b⁶`. -/
theorem bezout_b (a b : ℤ) :
    (-48 * a ^ 2 - 32 * a * b + 80 * b ^ 2) * F a b
      + (12 * a ^ 3 - 4 * a ^ 2 * b + 20 * a * b ^ 2 + 73 * b ^ 3) * G3 a b
      = 101 * b ^ 6 := by
  simp only [F, G3]; ring

/-- **Bézout identity, `a`-side**: eliminates `b` down to `101·a⁷`, already in
the `D = b·G3` denominator form. -/
theorem bezout_a (a b : ℤ) :
    (101 * a ^ 3 - 64 * a ^ 2 * b - 42 * a * b ^ 2 + 18 * b ^ 3) * F a b
      + (16 * a ^ 3 - 56 * a ^ 2 * b - 52 * a * b ^ 2 + 24 * b ^ 3) * D a b
      = 101 * a ^ 7 := by
  simp only [F, D, G3]; ring

/-- `bezout_b` multiplied through by `b`: the `b`-side identity in the
`D`-form that the gcd and size arguments consume. -/
theorem bezout_b_D (a b : ℤ) :
    ((-48 * a ^ 2 - 32 * a * b + 80 * b ^ 2) * b) * F a b
      + (12 * a ^ 3 - 4 * a ^ 2 * b + 20 * a * b ^ 2 + 73 * b ^ 3) * D a b
      = 101 * b ^ 7 := by
  simp only [F, D, G3]; ring

/-- **The gcd bound.** For coprime `a b : ℤ`, the gcd of the duplication
numerator and denominator divides `101`. -/
theorem gcd_dvd_101 {a b : ℤ} (h : IsCoprime a b) :
    (Int.gcd (F a b) (D a b) : ℤ) ∣ 101 := by
  have hdF : (Int.gcd (F a b) (D a b) : ℤ) ∣ F a b := Int.gcd_dvd_left _ _
  have hdD : (Int.gcd (F a b) (D a b) : ℤ) ∣ D a b := Int.gcd_dvd_right _ _
  have hb7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 101 * b ^ 7 := by
    rw [← bezout_b_D a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have ha7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 101 * a ^ 7 := by
    rw [← bezout_a a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have h7 : IsCoprime (a ^ 7) (b ^ 7) := h.pow
  obtain ⟨u, v, huv⟩ := h7
  have key : (101 : ℤ) = u * (101 * a ^ 7) + v * (101 * b ^ 7) := by
    linear_combination (-101 : ℤ) * huv
  rw [key]
  exact dvd_add (ha7.mul_left u) (hb7.mul_left v)

/-- `gcd_dvd_101` in `ℕ`-form. -/
theorem gcd_dvd_101_nat {a b : ℤ} (h : IsCoprime a b) :
    Int.gcd (F a b) (D a b) ∣ 101 := by
  exact_mod_cast gcd_dvd_101 h

/-! ## §2 — the size lower bound

`101·H⁷ ≤ 373·H³·max |F| |D|` with `H = max |a| |b|`. Cofactor coefficient
sums: `b`-side `160 + 109 = 269 ≤ 373`, `a`-side `225 + 148 = 373`. -/

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
`|(−48a² − 32ab + 80b²)·b| ≤ 160·H³`. -/
private theorem c1_bound (a b : ℤ) :
    ((-48 * a ^ 2 - 32 * a * b + 80 * b ^ 2) * b).natAbs
      ≤ 160 * (max a.natAbs b.natAbs) ^ 3 := by
  have h48 : ((-48 : ℤ)).natAbs = 48 := rfl
  have h32 : ((32 : ℤ)).natAbs = 32 := rfl
  have h80 : ((80 : ℤ)).natAbs = 80 := rfl
  have e1 : ((-48 : ℤ) * a ^ 2).natAbs = 48 * a.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h48]
  have e2 : ((32 : ℤ) * a * b).natAbs = 32 * a.natAbs * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, h32]
  have e3 : ((80 : ℤ) * b ^ 2).natAbs = 80 * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h80]
  calc ((-48 * a ^ 2 - 32 * a * b + 80 * b ^ 2) * b).natAbs
      = (-48 * a ^ 2 - 32 * a * b + 80 * b ^ 2).natAbs * b.natAbs :=
        Int.natAbs_mul _ _
    _ ≤ ((-48 * a ^ 2 - 32 * a * b).natAbs + ((80 : ℤ) * b ^ 2).natAbs)
          * b.natAbs :=
        Nat.mul_le_mul (Int.natAbs_add_le _ _) le_rfl
    _ ≤ ((((-48 : ℤ) * a ^ 2).natAbs + ((32 : ℤ) * a * b).natAbs)
          + ((80 : ℤ) * b ^ 2).natAbs) * b.natAbs :=
        Nat.mul_le_mul (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) le_rfl
    _ = (48 * a.natAbs ^ 2 + 32 * a.natAbs * b.natAbs + 80 * b.natAbs ^ 2)
          * b.natAbs := by rw [e1, e2, e3]
    _ = 48 * (a.natAbs ^ 2 * b.natAbs) + 32 * (a.natAbs * b.natAbs ^ 2)
          + 80 * b.natAbs ^ 3 := by ring
    _ ≤ 160 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono21 a b
        have m2 := mono12 a b
        have m3 := mono03 a b
        linarith

/-- Cofactor bound, `b`-side, second cofactor:
`|12a³ − 4a²b + 20ab² + 73b³| ≤ 109·H³`. -/
private theorem c2_bound (a b : ℤ) :
    (12 * a ^ 3 - 4 * a ^ 2 * b + 20 * a * b ^ 2 + 73 * b ^ 3).natAbs
      ≤ 109 * (max a.natAbs b.natAbs) ^ 3 := by
  have h12 : ((12 : ℤ)).natAbs = 12 := rfl
  have h4 : ((4 : ℤ)).natAbs = 4 := rfl
  have h20 : ((20 : ℤ)).natAbs = 20 := rfl
  have h73 : ((73 : ℤ)).natAbs = 73 := rfl
  have e1 : ((12 : ℤ) * a ^ 3).natAbs = 12 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h12]
  have e2 : ((4 : ℤ) * a ^ 2 * b).natAbs = 4 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h4]
  have e3 : ((20 : ℤ) * a * b ^ 2).natAbs = 20 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h20]
  have e4 : ((73 : ℤ) * b ^ 3).natAbs = 73 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h73]
  calc (12 * a ^ 3 - 4 * a ^ 2 * b + 20 * a * b ^ 2 + 73 * b ^ 3).natAbs
      ≤ (12 * a ^ 3 - 4 * a ^ 2 * b + 20 * a * b ^ 2).natAbs
          + ((73 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ ((12 * a ^ 3 - 4 * a ^ 2 * b).natAbs + ((20 : ℤ) * a * b ^ 2).natAbs)
          + ((73 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((((12 : ℤ) * a ^ 3).natAbs + ((4 : ℤ) * a ^ 2 * b).natAbs)
            + ((20 : ℤ) * a * b ^ 2).natAbs)
          + ((73 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
    _ = 12 * a.natAbs ^ 3 + 4 * a.natAbs ^ 2 * b.natAbs
          + 20 * a.natAbs * b.natAbs ^ 2 + 73 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 109 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, first cofactor:
`|101a³ − 64a²b − 42ab² + 18b³| ≤ 225·H³`. -/
private theorem c3_bound (a b : ℤ) :
    (101 * a ^ 3 - 64 * a ^ 2 * b - 42 * a * b ^ 2 + 18 * b ^ 3).natAbs
      ≤ 225 * (max a.natAbs b.natAbs) ^ 3 := by
  have h101 : ((101 : ℤ)).natAbs = 101 := rfl
  have h64 : ((64 : ℤ)).natAbs = 64 := rfl
  have h42 : ((42 : ℤ)).natAbs = 42 := rfl
  have h18 : ((18 : ℤ)).natAbs = 18 := rfl
  have e1 : ((101 : ℤ) * a ^ 3).natAbs = 101 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h101]
  have e2 : ((64 : ℤ) * a ^ 2 * b).natAbs = 64 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h64]
  have e3 : ((42 : ℤ) * a * b ^ 2).natAbs = 42 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h42]
  have e4 : ((18 : ℤ) * b ^ 3).natAbs = 18 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h18]
  calc (101 * a ^ 3 - 64 * a ^ 2 * b - 42 * a * b ^ 2 + 18 * b ^ 3).natAbs
      ≤ (101 * a ^ 3 - 64 * a ^ 2 * b - 42 * a * b ^ 2).natAbs
          + ((18 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ ((101 * a ^ 3 - 64 * a ^ 2 * b).natAbs + ((42 : ℤ) * a * b ^ 2).natAbs)
          + ((18 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ ≤ ((((101 : ℤ) * a ^ 3).natAbs + ((64 : ℤ) * a ^ 2 * b).natAbs)
            + ((42 : ℤ) * a * b ^ 2).natAbs)
          + ((18 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
    _ = 101 * a.natAbs ^ 3 + 64 * a.natAbs ^ 2 * b.natAbs
          + 42 * a.natAbs * b.natAbs ^ 2 + 18 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 225 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- Cofactor bound, `a`-side, second cofactor:
`|16a³ − 56a²b − 52ab² + 24b³| ≤ 148·H³`. -/
private theorem c4_bound (a b : ℤ) :
    (16 * a ^ 3 - 56 * a ^ 2 * b - 52 * a * b ^ 2 + 24 * b ^ 3).natAbs
      ≤ 148 * (max a.natAbs b.natAbs) ^ 3 := by
  have h16 : ((16 : ℤ)).natAbs = 16 := rfl
  have h56 : ((56 : ℤ)).natAbs = 56 := rfl
  have h52 : ((52 : ℤ)).natAbs = 52 := rfl
  have h24 : ((24 : ℤ)).natAbs = 24 := rfl
  have e1 : ((16 : ℤ) * a ^ 3).natAbs = 16 * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h16]
  have e2 : ((56 : ℤ) * a ^ 2 * b).natAbs = 56 * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h56]
  have e3 : ((52 : ℤ) * a * b ^ 2).natAbs = 52 * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, h52]
  have e4 : ((24 : ℤ) * b ^ 3).natAbs = 24 * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h24]
  calc (16 * a ^ 3 - 56 * a ^ 2 * b - 52 * a * b ^ 2 + 24 * b ^ 3).natAbs
      ≤ (16 * a ^ 3 - 56 * a ^ 2 * b - 52 * a * b ^ 2).natAbs
          + ((24 : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ ((16 * a ^ 3 - 56 * a ^ 2 * b).natAbs + ((52 : ℤ) * a * b ^ 2).natAbs)
          + ((24 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
    _ ≤ ((((16 : ℤ) * a ^ 3).natAbs + ((56 : ℤ) * a ^ 2 * b).natAbs)
            + ((52 : ℤ) * a * b ^ 2).natAbs)
          + ((24 : ℤ) * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _) _
    _ = 16 * a.natAbs ^ 3 + 56 * a.natAbs ^ 2 * b.natAbs
          + 52 * a.natAbs * b.natAbs ^ 2 + 24 * b.natAbs ^ 3 := by
        rw [e1, e2, e3, e4]
    _ ≤ 148 * (max a.natAbs b.natAbs) ^ 3 := by
        have m1 := mono30 a b
        have m2 := mono21 a b
        have m3 := mono12 a b
        have m4 := mono03 a b
        linarith

/-- The `b`-branch of the size bound: `101·|b|⁷ ≤ 373·H³·max |F| |D|`
(the natural constant is `269`; we relax to `373` to share one constant). -/
theorem size_bound_b (a b : ℤ) :
    101 * b.natAbs ^ 7
      ≤ 373 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h101 : ((101 : ℤ)).natAbs = 101 := rfl
  have h0 : ((101 : ℤ) * b ^ 7).natAbs = 101 * b.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h101]
  have hterm1 : (((-48 * a ^ 2 - 32 * a * b + 80 * b ^ 2) * b) * F a b).natAbs
      ≤ 160 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c1_bound a b) (le_max_left _ _)
  have hterm2 : ((12 * a ^ 3 - 4 * a ^ 2 * b + 20 * a * b ^ 2 + 73 * b ^ 3)
        * D a b).natAbs
      ≤ 109 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c2_bound a b) (le_max_right _ _)
  calc 101 * b.natAbs ^ 7 = ((101 : ℤ) * b ^ 7).natAbs := h0.symm
    _ = (((-48 * a ^ 2 - 32 * a * b + 80 * b ^ 2) * b) * F a b
          + (12 * a ^ 3 - 4 * a ^ 2 * b + 20 * a * b ^ 2 + 73 * b ^ 3)
              * D a b).natAbs := by
        rw [bezout_b_D a b]
    _ ≤ (((-48 * a ^ 2 - 32 * a * b + 80 * b ^ 2) * b) * F a b).natAbs
          + ((12 * a ^ 3 - 4 * a ^ 2 * b + 20 * a * b ^ 2 + 73 * b ^ 3)
              * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 160 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 109 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 269 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring
    _ ≤ 373 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) le_rfl

/-- The `a`-branch of the size bound: `101·|a|⁷ ≤ 373·H³·max |F| |D|`. -/
theorem size_bound_a (a b : ℤ) :
    101 * a.natAbs ^ 7
      ≤ 373 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h101 : ((101 : ℤ)).natAbs = 101 := rfl
  have h0 : ((101 : ℤ) * a ^ 7).natAbs = 101 * a.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h101]
  have hterm1 : ((101 * a ^ 3 - 64 * a ^ 2 * b - 42 * a * b ^ 2 + 18 * b ^ 3)
        * F a b).natAbs
      ≤ 225 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c3_bound a b) (le_max_left _ _)
  have hterm2 : ((16 * a ^ 3 - 56 * a ^ 2 * b - 52 * a * b ^ 2 + 24 * b ^ 3)
        * D a b).natAbs
      ≤ 148 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c4_bound a b) (le_max_right _ _)
  calc 101 * a.natAbs ^ 7 = ((101 : ℤ) * a ^ 7).natAbs := h0.symm
    _ = ((101 * a ^ 3 - 64 * a ^ 2 * b - 42 * a * b ^ 2 + 18 * b ^ 3) * F a b
          + (16 * a ^ 3 - 56 * a ^ 2 * b - 52 * a * b ^ 2 + 24 * b ^ 3)
              * D a b).natAbs := by
        rw [bezout_a a b]
    _ ≤ ((101 * a ^ 3 - 64 * a ^ 2 * b - 42 * a * b ^ 2 + 18 * b ^ 3)
            * F a b).natAbs
          + ((16 * a ^ 3 - 56 * a ^ 2 * b - 52 * a * b ^ 2 + 24 * b ^ 3)
              * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 225 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 148 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 373 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring

/-- **The size lower bound.** For all `a b : ℤ`, with `H = max |a| |b|`:
`101·H⁷ ≤ 373·H³·max |F(a,b)| |D(a,b)|`. -/
theorem size_bound (a b : ℤ) :
    101 * (max a.natAbs b.natAbs) ^ 7
      ≤ 373 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
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

/-- Pure-`ℕ` descent arithmetic: from `101·H⁷ ≤ 373·H³·(M·d)` with `d ≤ 101`
and `1 ≤ H`, cancel `H³` to get `101·H⁴ ≤ 373·101·M`. -/
private theorem descend {H M d : ℕ} (hd : d ≤ 101) (hH : 1 ≤ H)
    (hkey : 101 * H ^ 7 ≤ 373 * H ^ 3 * (M * d)) :
    101 * H ^ 4 ≤ 373 * 101 * M := by
  have hH0 : 0 < H := hH
  have h2 : (101 * H ^ 4) * H ^ 3 ≤ (373 * 101 * M) * H ^ 3 := by
    calc (101 * H ^ 4) * H ^ 3 = 101 * H ^ 7 := by ring
      _ ≤ 373 * H ^ 3 * (M * d) := hkey
      _ ≤ 373 * H ^ 3 * (M * 101) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hd)
      _ = (373 * 101 * M) * H ^ 3 := by ring
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos hH0 3)

/-- **The reduced height bound.** For coprime `a b` with `b ≠ 0`, after
dividing the duplication pair `(F, D)` by `gcd(F, D)` (which divides `101`),
the reduced max still dominates the fourth power of the input height. -/
theorem reduced_height_bound {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (_hD : D a b ≠ 0) :
    101 * (max a.natAbs b.natAbs) ^ 4
      ≤ 373 * 101 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have hd101 : Int.gcd (F a b) (D a b) ≤ 101 :=
    Nat.le_of_dvd (by norm_num) (gcd_dvd_101_nat h)
  have hH1 : 1 ≤ max a.natAbs b.natAbs :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
      (le_max_right _ _)
  have hsplit :=
    max_natAbs_split (n := Int.gcd (F a b) (D a b))
      (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have key := size_bound a b
  rw [hsplit] at key
  exact descend hd101 hH1 key

/-- `reduced_height_bound` with the common factor `101` cancelled:
`H⁴ ≤ 373·max |F/g| |D/g|`. Cleanest form for the height join. -/
theorem reduced_height_bound' {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 373 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have key := reduced_height_bound h hb hD
  have key2 : 101 * (max a.natAbs b.natAbs) ^ 4
      ≤ 101 * (373 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by
    calc 101 * (max a.natAbs b.natAbs) ^ 4
        ≤ 373 * 101 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := key
      _ = 101 * (373 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by ring
  exact Nat.le_of_mul_le_mul_left key2 (by norm_num)

end Reduced

/-! ## §4 — the curve 101a1 and the duplication formula -/

/-- **Curve 101a1**: `y² + y = x³ + x² − x − 1`, i.e.
`(a₁, a₂, a₃, a₄, a₆) = (0, 1, 1, −1, −1)`. -/
def E101a1 : WeierstrassCurve ℚ := ⟨0, 1, 1, -1, -1⟩

@[simp] lemma E101a1_a₁ : E101a1.a₁ = 0 := rfl
@[simp] lemma E101a1_a₂ : E101a1.a₂ = 1 := rfl
@[simp] lemma E101a1_a₃ : E101a1.a₃ = 1 := rfl
@[simp] lemma E101a1_a₄ : E101a1.a₄ = -1 := rfl
@[simp] lemma E101a1_a₆ : E101a1.a₆ = -1 := rfl

/-- The duplication numerator `f(x) = x⁴ + 2x² + 6x + 4` for 101a1. -/
def f (x : ℚ) : ℚ := x ^ 4 + 2 * x ^ 2 + 6 * x + 4

/-- The duplication denominator `g(x) = 4x³ + 4x² − 4x − 3` (= ψ₂²). -/
def g (x : ℚ) : ℚ := 4 * x ^ 3 + 4 * x ^ 2 - 4 * x - 3

/-- On 101a1, `(2y + 1)² = g(x)`. -/
theorem two_y_add_one_sq {x y : ℚ} (h : E101a1.toAffine.Equation x y) :
    (2 * y + 1) ^ 2 = g x := by
  rw [Affine.equation_iff] at h
  simp only [E101a1_a₁, E101a1_a₂, E101a1_a₃, E101a1_a₄, E101a1_a₆] at h
  simp only [g]
  linear_combination 4 * h

/-- Integer core of the rational root theorem for `g`: no reduced fraction
`n/d` (`d ≥ 1`, `gcd(n, d) = 1`) satisfies `4n³ + 4n²d − 4nd² − 3d³ = 0`.
From the equation, `n ∣ 3d³` forces `n ∣ 3` and `d ∣ 4n³` forces `d ∣ 4`;
all 16 candidates fail. -/
lemma no_integer_root {n d : ℤ} (hd1 : 1 ≤ d) (hcop : IsCoprime n d)
    (key : 4 * n ^ 3 + 4 * n ^ 2 * d - 4 * n * d ^ 2 - 3 * d ^ 3 = 0) :
    False := by
  -- n ∣ 3d³ since 3d³ = n · (4n² + 4nd − 4d²)
  have hn_dvd : n ∣ 3 * d ^ 3 :=
    ⟨4 * n ^ 2 + 4 * n * d - 4 * d ^ 2, by linear_combination (-1 : ℤ) * key⟩
  have hn3 : n ∣ 3 :=
    (hcop.pow_right (n := 3)).dvd_of_dvd_mul_right hn_dvd
  -- d ∣ 4n³ since 4n³ = d · (−4n² + 4nd + 3d²)
  have hd_dvd : d ∣ 4 * n ^ 3 :=
    ⟨-4 * n ^ 2 + 4 * n * d + 3 * d ^ 2, by linear_combination key⟩
  have hd4 : d ∣ 4 :=
    (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right hd_dvd
  have hd_le : d ≤ 4 := Int.le_of_dvd (by norm_num) hd4
  have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  -- n ∣ 3 forces |n| ∈ {1, 3}
  have hnabs : n.natAbs ∣ 3 := by
    have := Int.natAbs_dvd_natAbs.mpr hn3
    simpa using this
  have hn_cases : n = 1 ∨ n = -1 ∨ n = 3 ∨ n = -3 := by
    have h13 : n.natAbs = 1 ∨ n.natAbs = 3 :=
      (Nat.prime_three).eq_one_or_self_of_dvd _ hnabs
    rcases h13 with h | h <;> omega
  rcases hn_cases with rfl | rfl | rfl | rfl <;>
    rcases hd_cases with rfl | rfl | rfl | rfl <;>
      norm_num at key

/-- **`g` has no rational roots.**  In particular no rational affine point of
101a1 is 2-torsion, so doubling never leaves the affine chart. -/
theorem g_ne_zero (x : ℚ) : g x ≠ 0 := by
  intro hg
  have hg' : 4 * x ^ 3 + 4 * x ^ 2 - 4 * x - 3 = 0 := by simpa [g] using hg
  have hden : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have h0 : 4 * (x.num : ℚ) ^ 3 + 4 * (x.num : ℚ) ^ 2 * (x.den : ℚ)
      - 4 * (x.num : ℚ) * (x.den : ℚ) ^ 2 - 3 * (x.den : ℚ) ^ 3 = 0 := by
    have hxq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    rw [hxq] at hg'
    field_simp at hg'
    linear_combination hg'
  have key : 4 * x.num ^ 3 + 4 * x.num ^ 2 * (x.den : ℤ)
      - 4 * x.num * (x.den : ℤ) ^ 2 - 3 * (x.den : ℤ) ^ 3 = 0 := by
    exact_mod_cast h0
  have hd1 : (1 : ℤ) ≤ (x.den : ℤ) := by
    have := x.pos
    omega
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  exact no_integer_root hd1 hcop key

/-- On 101a1, `2y + 1 ≠ 0` for every rational affine point. -/
theorem two_y_add_one_ne_zero {x y : ℚ} (h : E101a1.toAffine.Equation x y) :
    2 * y + 1 ≠ 0 := by
  intro h0
  apply g_ne_zero x
  rw [← two_y_add_one_sq h, h0]
  norm_num

/-- `negY` on 101a1 is `-y - 1` (since `a₁ = 0`, `a₃ = 1`). -/
lemma negY_eq (x y : ℚ) : E101a1.toAffine.negY x y = -y - 1 := by
  simp [Affine.negY]

/-- No rational affine point of 101a1 is 2-torsion: `y ≠ negY x y`. -/
theorem y_ne_negY {x y : ℚ} (h : E101a1.toAffine.Equation x y) :
    y ≠ E101a1.toAffine.negY x y := by
  rw [negY_eq]
  intro hy
  exact two_y_add_one_ne_zero h (by linarith)

/-- The tangent slope at a rational affine point of 101a1 is
`(3x² + 2x − 1)/(2y + 1)`. -/
theorem slope_eq {x y : ℚ} (h : E101a1.toAffine.Nonsingular x y) :
    E101a1.toAffine.slope x x y y = (3 * x ^ 2 + 2 * x - 1) / (2 * y + 1) := by
  rw [Affine.slope_of_Y_ne rfl (y_ne_negY h.left), negY_eq]
  have hnum : 3 * x ^ 2 + 2 * E101a1.toAffine.a₂ * x + E101a1.toAffine.a₄
      - E101a1.toAffine.a₁ * y = 3 * x ^ 2 + 2 * x - 1 := by
    simp only [E101a1_a₁, E101a1_a₂, E101a1_a₄]
    ring
  have hden : y - (-y - 1) = 2 * y + 1 := by ring
  rw [hnum, hden]

/-- **The duplication formula for 101a1.**  For any rational affine point
`P = some h` at `(x, y)`, the double `P + P` is again an affine point
`some h'`, and its x-coordinate is exactly `f(x)/g(x)`.
The x-coordinate identity is `(3x² + 2x − 1)² − (1 + 2x)·g(x) = f(x)`
combined with `(2y + 1)² = g(x) ≠ 0`. -/
theorem dbl_x {x y : ℚ} (h : E101a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E101a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x := by
  have hy : y ≠ E101a1.toAffine.negY x y := y_ne_negY h.left
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy, ?_⟩
  have hg : g x ≠ 0 := g_ne_zero x
  have h2y : 2 * y + 1 ≠ 0 := two_y_add_one_ne_zero h.left
  have hsq : (2 * y + 1) ^ 2 = g x := two_y_add_one_sq h.left
  rw [slope_eq h]
  simp only [Affine.addX, E101a1_a₁, E101a1_a₂]
  rw [div_pow, hsq]
  field_simp
  simp only [f, g]
  ring

/-! ## §5 — the height join (generic lemmas imported from r133) -/

/-- The Bézout bound transported to `naiveHeight`:
`H⁴ ≤ 373 · naiveHeight (F/D)` for `H = max |a| |b|`. -/
theorem height_bound_of_coprime {a b : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 373 * naiveHeight ((F a b : ℚ) / (D a b : ℚ)) := by
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

/-- **The duplication height inequality for 101a1.** For every rational `x`
(no on-curve hypothesis: `g` never vanishes on ℚ):
`naiveHeight x ^ 4 ≤ 373 · naiveHeight (f x / g x)`. -/
theorem duplication_height_bound (x : ℚ) :
    naiveHeight x ^ 4 ≤ 373 * naiveHeight (f x / g x) := by
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
    _ ≤ 373 * naiveHeight
          ((F x.num (x.den : ℤ) : ℚ) / (D x.num (x.den : ℤ) : ℚ)) :=
        height_bound_of_coprime hcop hb hD
    _ = 373 * naiveHeight (f x / g x) := by rw [← hfg]

/-- **Duplication height step on the curve.** For any rational affine point
`P = some h` of 101a1 at `(x, y)`: `P + P` is an affine point `some h'` at
some `(x', y')` with `naiveHeight x ^ 4 ≤ 373 * naiveHeight x'`. -/
theorem dbl_height {x y : ℚ} (h : E101a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E101a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧
        naiveHeight x ^ 4 ≤ 373 * naiveHeight x' := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
  refine ⟨x', y', h', hadd, ?_⟩
  rw [hx']
  exact duplication_height_bound x

/-! ## §6 — the base point `P = (−1, 0)` on 101a1 -/

/-- `(−1, 0)` is a nonsingular rational point of 101a1: the equation reads
`0 = −1 + 1 + 1 − 1`, and the Y-branch of nonsingularity holds because
`0 ≠ −0 − 0·(−1) − 1 = −1`. -/
theorem P101_nonsingular : E101a1.toAffine.Nonsingular (-1) 0 := by
  rw [Affine.nonsingular_iff]
  constructor
  · rw [Affine.equation_iff]
    simp only [E101a1_a₁, E101a1_a₂, E101a1_a₃, E101a1_a₄, E101a1_a₆]
    norm_num
  · right
    simp only [E101a1_a₁, E101a1_a₃]
    norm_num

/-- **The base point** `P101 = (−1, 0) ∈ E101a1(ℚ)`. -/
noncomputable def P101 : E101a1.toAffine.Point := Point.some P101_nonsingular

/-! ## §7 — the doubling chain -/

/-- The doubling chain: `chain 0 = (−1, 0, proof)`, and `chain (n+1)` is the
affine data of `chain n + chain n` chosen from `dbl_height`. -/
noncomputable def chain : ℕ → Σ' (x y : ℚ), E101a1.toAffine.Nonsingular x y :=
  Nat.rec (motive := fun _ => Σ' (x y : ℚ), E101a1.toAffine.Nonsingular x y)
    ⟨-1, 0, P101_nonsingular⟩
    fun _ c =>
      ⟨(dbl_height c.2.2).choose,
       (dbl_height c.2.2).choose_spec.choose,
       (dbl_height c.2.2).choose_spec.choose_spec.choose⟩

/-- The x-coordinate along the chain. -/
noncomputable def xs (n : ℕ) : ℚ := (chain n).1

/-- The chain as points of the group `E101a1(ℚ)`. -/
noncomputable def pts (n : ℕ) : E101a1.toAffine.Point := Point.some (chain n).2.2

@[simp] lemma xs_zero : xs 0 = -1 := rfl

lemma pts_zero : pts 0 = P101 := rfl

/-- Each chain step doubles the point. -/
lemma pts_succ (n : ℕ) : pts (n + 1) = pts n + pts n :=
  ((dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.1).symm

/-- Each chain step satisfies the quartic height inequality (κ = 373). -/
lemma height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ 373 * naiveHeight (xs (n + 1)) :=
  (dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.2

/-- The chain is the `2ⁿ`-multiples of the base point: `pts n = 2ⁿ • P101`. -/
lemma pts_eq_two_pow_smul (n : ℕ) : pts n = ((2 : ℤ) ^ n) • P101 := by
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

/-- `x(4P) = 13`. -/
lemma xs_two : xs 2 = 13 := by
  rw [xs_succ 1, xs_one]; norm_num [f, g]

/-- `x(8P) = 28981/9409`. -/
lemma xs_three : xs 3 = 28981 / 9409 := by
  rw [xs_succ 2, xs_two]; norm_num [f, g]

/-- `naiveHeight (x(8P)) = 28981` — the fraction is already reduced:
`gcd(28981, 9409) = 1` (`9409 = 97²` and `97 ∤ 28981`). -/
lemma naiveHeight_xs_three : naiveHeight (xs 3) = 28981 := by
  have h3 : xs 3 = ((28981 : ℤ) : ℚ) / ((9409 : ℤ) : ℚ) := by
    rw [xs_three]; norm_num
  have hg : Int.gcd 28981 9409 = 1 := by norm_num
  rw [h3, DuplicationHeightBound37a1.naiveHeight_div_int 28981 9409
    (by norm_num), hg]
  norm_num

/-- The threshold check: `x(8P)` clears the curve constant `κ = 373`. -/
lemma threshold : 373 < naiveHeight (xs 3) := by
  rw [naiveHeight_xs_three]; norm_num

/-! ## §8 — firing the driver: infinitely many x-coordinates -/

/-- **The chain from `8P` on has infinite x-coordinate range**: the quartic
step starts above the threshold, so r130's growth engine applies. -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 3)).Infinite :=
  infinite_of_duplication_step (κ := 373) (fun n => xs (n + 3))
    (by norm_num) (fun n => height_step (n + 3)) threshold

/-! ## §9 — non-torsion: a finite orbit cannot contain an infinite image -/

/-- The x-coordinate projection on the point group (`0` at the identity). -/
def X : E101a1.toAffine.Point → ℚ
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

lemma X_pts (n : ℕ) : X (pts n) = xs n := rfl

/-- **CAPSTONE 1 — `P = (−1, 0)` is non-torsion on 101a1.** If `P101` had
finite order, `AddSubgroup.zmultiples P101` would be a finite set; its image
under `X` would be finite, yet it contains the infinite range of §8. -/
theorem P_nonTorsion : ¬ IsOfFinAddOrder P101 := by
  intro hfin
  have hfinite := hfin.finite_zmultiples
  have hsub : (Set.range fun n => xs (n + 3))
      ⊆ X '' (AddSubgroup.zmultiples P101 : Set _) := by
    rintro q ⟨n, rfl⟩
    refine ⟨pts (n + 3), ?_, X_pts (n + 3)⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨(2 : ℤ) ^ (n + 3), (pts_eq_two_pow_smul (n + 3)).symm⟩
  exact xs_shifted_infinite ((hfinite.image X).subset hsub)

/-! ## §10 — THE FLAG: rank ≥ 1 for 101a1 -/

/-- The r129 certificate, discharged: `P101` has infinite order in
`E101a1(ℚ)`. -/
theorem P101_certificate : NonTorsionCertificate E101a1.toAffine P101 :=
  P_nonTorsion

/-- **CAPSTONE 2 — the Mordell–Weil rank of 101a1 is at least 1.** -/
theorem E101a1_rank_ge_one : 1 ≤ Module.rank ℤ E101a1.toAffine.Point :=
  mordellWeil_rank_ge_one E101a1.toAffine P101 P_nonTorsion

end PrincipiaTractalis.E101a1RankOne

#print axioms PrincipiaTractalis.E101a1RankOne.bezout_b
#print axioms PrincipiaTractalis.E101a1RankOne.bezout_a
#print axioms PrincipiaTractalis.E101a1RankOne.gcd_dvd_101
#print axioms PrincipiaTractalis.E101a1RankOne.size_bound
#print axioms PrincipiaTractalis.E101a1RankOne.reduced_height_bound'
#print axioms PrincipiaTractalis.E101a1RankOne.dbl_x
#print axioms PrincipiaTractalis.E101a1RankOne.duplication_height_bound
#print axioms PrincipiaTractalis.E101a1RankOne.dbl_height
#print axioms PrincipiaTractalis.E101a1RankOne.xs_three
#print axioms PrincipiaTractalis.E101a1RankOne.naiveHeight_xs_three
#print axioms PrincipiaTractalis.E101a1RankOne.P_nonTorsion
#print axioms PrincipiaTractalis.E101a1RankOne.P101_certificate
#print axioms PrincipiaTractalis.E101a1RankOne.E101a1_rank_ge_one
