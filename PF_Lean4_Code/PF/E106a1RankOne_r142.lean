/-
# PF.E106a1RankOne_r142

★★★ 2026-07-28 — THE FIVE-STONE PATTERN, REPLICATED FOR 106a1 ★★★

The completed non-torsion arc of 37a1 (r131–r134), cloned in one
self-contained file for the rank-1 curve **106a1** of COMPOSITE conductor
`106 = 2·53` (`y² + xy = x³ + x² − 7x + 5`) and its generator `P = (2, 1)`:

  * `P_nonTorsion : ¬ IsOfFinAddOrder P106` — the point `(2, 1)` has infinite
    order in `E106a1(ℚ)`;
  * `E106a1_rank_ge_one : 1 ≤ Module.rank ℤ E106a1.toAffine.Point` — the FLAG.

The five stones, all in this file (curve-generic pieces reused by import):

  1. **B2 (duplication formula)** — for 106a1 the doubling unit is
     `w = 2y + x` with `w² = g(x)` on-curve, `g(x) = 4x³ + 5x² − 28x + 20`;
     `g` has no rational roots (rational root theorem by hand: `n ∣ 20`,
     `d ∣ 4`, all candidate pairs fail), so no rational affine point is
     2-torsion and `x(2P) = f(x)/g(x)` with `f(x) = x⁴ + 14x² − 40x + 24`,
     via the certificate
     `N² + N·w − (1 + 2x)·w² − f(x) = (−8x − 5)·(y² + xy − x³ − x² + 7x − 5)`
     for the slope numerator `N = 3x² + 2x − 7 − y`.
  2. **B3 (Bézout/resultant)** — for the homogenized pair
     `F(a,b) = a⁴ + 14a²b² − 40ab³ + 24b⁴`, `D(a,b) = b·(4a³ + 5a²b − 28ab² + 20b³)`:
     explicit Bézout identities to `848·b⁶` and `848·a⁷` (the conductor is
     composite; the Bézout level is `Lc = 848 = 2⁴·53` on BOTH sides), hence
     `gcd(F, D) ∣ 848` for coprime `(a, b)`, and the size bound
     `848·H⁷ ≤ 38896·H³·max |F| |D|` (cofactor sums: `b`-side
     `561 + 767 = 1328`, `a`-side `16720 + 22176 = 38896`; κ = 38896).
  3. **B4 (height inequality)** — `naiveHeight x ⁴ ≤ 38896·naiveHeight (f x / g x)`
     for every rational `x`, through the curve-generic
     `naiveHeight_div_int` (imported from r133).
  4. **B1 (driver)** — r130's `infinite_of_duplication_step` with κ = 38896.
  5. **B5 (chain)** — the doubling chain from `(2, 1)`:
     `xs = 2, 1, −1, 79/49, 15319439/26615281`, heights
     `2, 1, 1, 79, 26615281` (the DENOMINATOR dominates at index 4);
     `naiveHeight (xs 4) = 26615281 > 38896`
     (`gcd(15319439, 26615281) = 1`, `26615281 = 5159² = 7²·11²·67²`), so the
     shifted sequence has infinite x-coordinate range, `P106` is non-torsion,
     and r129's `mordellWeil_rank_ge_one` fires.

HONEST SCOPE. This file certifies ONE point on ONE curve as non-torsion and
concludes `1 ≤ Module.rank ℤ E106a1(ℚ)` — a LOWER bound only.  It does not
compute the exact rank, says nothing about any other curve of the cohort,
and proves no statement about L-functions or BSD.

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
import Mathlib.Tactic.IntervalCases

namespace PrincipiaTractalis.E106a1RankOne

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.MordellWeilRankLowerBound
open PrincipiaTractalis.DuplicationHeightBound37a1 (naiveHeight_div_int)
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the curve 106a1 and the duplication polynomials -/

/-- **Curve 106a1**: `y² + xy = x³ + x² − 7x + 5`, i.e.
`(a₁, a₂, a₃, a₄, a₆) = (1, 1, 0, −7, 5)`. -/
def E106a1 : WeierstrassCurve ℚ := ⟨1, 1, 0, -7, 5⟩

@[simp] lemma E106a1_a₁ : E106a1.a₁ = 1 := rfl
@[simp] lemma E106a1_a₂ : E106a1.a₂ = 1 := rfl
@[simp] lemma E106a1_a₃ : E106a1.a₃ = 0 := rfl
@[simp] lemma E106a1_a₄ : E106a1.a₄ = -7 := rfl
@[simp] lemma E106a1_a₆ : E106a1.a₆ = 5 := rfl

/-- The duplication numerator `f(x) = x⁴ + 14x² − 40x + 24`. -/
def f (x : ℚ) : ℚ := x ^ 4 + 14 * x ^ 2 - 40 * x + 24

/-- The duplication denominator `g(x) = 4x³ + 5x² − 28x + 20` (= ψ₂² for 106a1). -/
def g (x : ℚ) : ℚ := 4 * x ^ 3 + 5 * x ^ 2 - 28 * x + 20

/-! ## §2 — the on-curve square identity `(2y + x)² = g(x)` -/

/-- On 106a1, `(2y + x)² = g(x)`: four times the Weierstrass equation
`y² + xy = x³ + x² − 7x + 5` plus `x²`. -/
theorem w_sq {x y : ℚ} (h : E106a1.toAffine.Equation x y) :
    (2 * y + x) ^ 2 = g x := by
  rw [Affine.equation_iff] at h
  simp only [E106a1_a₁, E106a1_a₂, E106a1_a₃, E106a1_a₄, E106a1_a₆] at h
  simp only [g]
  linear_combination 4 * h

/-! ## §3 — `g` has no rational roots (rational root theorem, by hand) -/

/-- Integer core of the rational root theorem for `g`: no reduced fraction
`n/d` (`d ≥ 1`, `gcd(n, d) = 1`) satisfies `4n³ + 5n²d − 28nd² + 20d³ = 0`.
From the equation, `n ∣ 20d³` forces `n ∣ 20` and `d ∣ 4n³` forces `d ∣ 4`;
all candidate pairs `n ∈ [−20, 20]`, `d ∈ [1, 4]` fail numerically. -/
lemma no_integer_root {n d : ℤ} (hd1 : 1 ≤ d) (hcop : IsCoprime n d)
    (key : 4 * n ^ 3 + 5 * n ^ 2 * d - 28 * n * d ^ 2 + 20 * d ^ 3 = 0) : False := by
  -- n ∣ 20d³ since 20d³ = n · (−4n² − 5nd + 28d²)
  have hn_dvd : n ∣ 20 * d ^ 3 :=
    ⟨-4 * n ^ 2 - 5 * n * d + 28 * d ^ 2, by linear_combination key⟩
  have hn20 : n ∣ 20 :=
    (hcop.pow_right (n := 3)).dvd_of_dvd_mul_right hn_dvd
  -- d ∣ 4n³ since 4n³ = d · (−5n² + 28nd − 20d²)
  have hd_dvd : d ∣ 4 * n ^ 3 :=
    ⟨-5 * n ^ 2 + 28 * n * d - 20 * d ^ 2, by linear_combination key⟩
  have hd4 : d ∣ 4 :=
    (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right hd_dvd
  have hd_le : d ≤ 4 := Int.le_of_dvd (by norm_num) hd4
  have hn_abs : n.natAbs ∣ 20 := by
    have h := Int.natAbs_dvd_natAbs.mpr hn20
    simpa using h
  have hn_le : n.natAbs ≤ 20 := Nat.le_of_dvd (by norm_num) hn_abs
  have hn_lo : -20 ≤ n := by omega
  have hn_hi : n ≤ 20 := by omega
  interval_cases n <;> interval_cases d <;> norm_num at key

/-- **`g` has no rational roots.**  In particular (via §2) no rational affine
point of 106a1 is 2-torsion, so doubling never leaves the affine chart. -/
theorem g_ne_zero (x : ℚ) : g x ≠ 0 := by
  intro hg
  have hg' : 4 * x ^ 3 + 5 * x ^ 2 - 28 * x + 20 = 0 := by simpa [g] using hg
  have hden : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  -- clear denominators: 4n³ + 5n²d − 28nd² + 20d³ = 0 over ℚ, then over ℤ
  have h0 : 4 * (x.num : ℚ) ^ 3 + 5 * (x.num : ℚ) ^ 2 * (x.den : ℚ)
      - 28 * (x.num : ℚ) * (x.den : ℚ) ^ 2 + 20 * (x.den : ℚ) ^ 3 = 0 := by
    have hxq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    rw [hxq] at hg'
    field_simp at hg'
    linear_combination hg'
  have key : 4 * x.num ^ 3 + 5 * x.num ^ 2 * (x.den : ℤ)
      - 28 * x.num * (x.den : ℤ) ^ 2 + 20 * (x.den : ℤ) ^ 3 = 0 := by
    exact_mod_cast h0
  have hd1 : (1 : ℤ) ≤ (x.den : ℤ) := by
    have := x.pos
    omega
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  exact no_integer_root hd1 hcop key

/-! ## §4 — no rational affine 2-torsion: `2y + x ≠ 0` on-curve -/

/-- On 106a1, `2y + x ≠ 0` for every rational affine point: otherwise
`g(x) = (2y + x)² = 0`, contradicting §3. -/
theorem w_ne_zero {x y : ℚ} (h : E106a1.toAffine.Equation x y) :
    2 * y + x ≠ 0 := by
  intro h0
  apply g_ne_zero x
  rw [← w_sq h, h0]
  norm_num

/-- `negY` on 106a1 is `-y - x`. -/
lemma negY_eq (x y : ℚ) : E106a1.toAffine.negY x y = -y - x := by
  simp only [Affine.negY, E106a1_a₁, E106a1_a₃]
  ring

/-- No rational affine point of 106a1 is 2-torsion: `y ≠ negY x y`. -/
theorem y_ne_negY {x y : ℚ} (h : E106a1.toAffine.Equation x y) :
    y ≠ E106a1.toAffine.negY x y := by
  rw [negY_eq]
  intro hy
  exact w_ne_zero h (by linarith)

/-! ## §5 — the tangent slope -/

/-- The tangent slope at a rational affine point of 106a1 is
`(3x² + 2x − 7 − y)/(2y + x)`. -/
theorem slope_eq {x y : ℚ} (h : E106a1.toAffine.Nonsingular x y) :
    E106a1.toAffine.slope x x y y
      = (3 * x ^ 2 + 2 * x - 7 - y) / (2 * y + x) := by
  rw [Affine.slope_of_Y_ne rfl (y_ne_negY h.left), negY_eq]
  have hnum : 3 * x ^ 2 + 2 * E106a1.toAffine.a₂ * x + E106a1.toAffine.a₄
      - E106a1.toAffine.a₁ * y = 3 * x ^ 2 + 2 * x - 7 - y := by
    simp only [E106a1_a₁, E106a1_a₂, E106a1_a₄]
    ring
  have hden : y - (-y - x) = 2 * y + x := by ring
  rw [hnum, hden]

/-! ## §6 — B2 CAPSTONE: `x(P + P) = f(x)/g(x)` -/

/-- **The duplication formula for 106a1.**  For any rational affine point
`P = some h` at `(x, y)`, the double `P + P` is again an affine point
`some h'` (never `0`, by §4), and its x-coordinate is exactly `f(x)/g(x)`.
The numerator identity is the `linear_combination` certificate
`N² + N·w − (1 + 2x)·w² − f(x) = (−8x − 5)·(y² + xy − x³ − x² + 7x − 5)`
combined with `w² = g(x) ≠ 0`. -/
theorem dbl_x {x y : ℚ} (h : E106a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E106a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x := by
  have hy : y ≠ E106a1.toAffine.negY x y := y_ne_negY h.left
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy, ?_⟩
  -- goal: addX x x (slope x x y y) = f x / g x
  have hw : 2 * y + x ≠ 0 := w_ne_zero h.left
  have hsq : (2 * y + x) ^ 2 = g x := w_sq h.left
  have hEq : y ^ 2 + x * y = x ^ 3 + x ^ 2 - 7 * x + 5 := by
    have h' := h.left
    rw [Affine.equation_iff] at h'
    simp only [E106a1_a₁, E106a1_a₂, E106a1_a₃, E106a1_a₄, E106a1_a₆] at h'
    linear_combination h'
  -- the duplication certificate: M_raw = f on-curve
  have hM : (3 * x ^ 2 + 2 * x - 7 - y) ^ 2
      + (3 * x ^ 2 + 2 * x - 7 - y) * (2 * y + x)
      - (1 + 2 * x) * (2 * y + x) ^ 2 = f x := by
    simp only [f]
    linear_combination (-8 * x - 5) * hEq
  rw [slope_eq h]
  simp only [Affine.addX, E106a1_a₁, E106a1_a₂]
  rw [← hM, ← hsq]
  field_simp
  ring

/-! ## §7 — B3: the Bézout/resultant stone (pure integer arithmetic)

Homogenize `x = a/b`: `F(a,b) = b⁴·f(a/b)`, `G3(a,b) = b³·g(a/b)`,
`D = b·G3` (so `x(2P) = F/D`). The conductor `106 = 2·53` is composite; the
normalized Bézout level is `Lc = 848 = 2⁴·53` on both sides. -/

/-- Homogenized duplication numerator for 106a1: `b⁴·f(a/b)`. -/
def F (a b : ℤ) : ℤ := a ^ 4 + 14 * a ^ 2 * b ^ 2 - 40 * a * b ^ 3 + 24 * b ^ 4

/-- Homogenized `g` before the extra factor of `b`: `b³·g(a/b)`. -/
def G3 (a b : ℤ) : ℤ := 4 * a ^ 3 + 5 * a ^ 2 * b - 28 * a * b ^ 2 + 20 * b ^ 3

/-- The duplication denominator form: `x(2P) = F a b / D a b` for `x = a/b`. -/
def D (a b : ℤ) : ℤ := b * G3 a b

/-- **Bézout identity, `b`-side**: eliminates `a` down to `848·b⁶`. -/
theorem bezout_b (a b : ℤ) :
    (48 * a ^ 2 + 40 * a * b - 473 * b ^ 2) * F a b
      + (-12 * a ^ 3 + 5 * a ^ 2 * b - 140 * a * b ^ 2 + 610 * b ^ 3) * G3 a b
      = 848 * b ^ 6 := by
  simp only [F, G3]; ring

/-- **Bézout identity, `a`-side**: eliminates `b` down to `848·a⁷`, already in
the `D = b·G3` denominator form. -/
theorem bezout_a (a b : ℤ) :
    (848 * a ^ 3 - 640 * a ^ 2 * b - 7552 * a * b ^ 2 + 7680 * b ^ 3) * F a b
      + (160 * a ^ 3 - 1280 * a ^ 2 * b + 11520 * a * b ^ 2 - 9216 * b ^ 3) * D a b
      = 848 * a ^ 7 := by
  simp only [F, D, G3]; ring

/-- `bezout_b` multiplied through by `b`: the `b`-side identity in the
`D`-form that the gcd and size arguments consume. -/
theorem bezout_b_D (a b : ℤ) :
    ((48 * a ^ 2 + 40 * a * b - 473 * b ^ 2) * b) * F a b
      + (-12 * a ^ 3 + 5 * a ^ 2 * b - 140 * a * b ^ 2 + 610 * b ^ 3) * D a b
      = 848 * b ^ 7 := by
  simp only [F, D, G3]; ring

/-- **The gcd bound.** For coprime `a b : ℤ`, the gcd of the duplication
numerator and denominator divides `848`. -/
theorem gcd_dvd_848 {a b : ℤ} (h : IsCoprime a b) :
    (Int.gcd (F a b) (D a b) : ℤ) ∣ 848 := by
  have hdF : (Int.gcd (F a b) (D a b) : ℤ) ∣ F a b := Int.gcd_dvd_left _ _
  have hdD : (Int.gcd (F a b) (D a b) : ℤ) ∣ D a b := Int.gcd_dvd_right _ _
  have hb7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 848 * b ^ 7 := by
    rw [← bezout_b_D a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have ha7 : (Int.gcd (F a b) (D a b) : ℤ) ∣ 848 * a ^ 7 := by
    rw [← bezout_a a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have h7 : IsCoprime (a ^ 7) (b ^ 7) := h.pow
  obtain ⟨u, v, huv⟩ := h7
  have key : (848 : ℤ) = u * (848 * a ^ 7) + v * (848 * b ^ 7) := by
    linear_combination (-848 : ℤ) * huv
  rw [key]
  exact dvd_add (ha7.mul_left u) (hb7.mul_left v)

/-- `gcd_dvd_848` in `ℕ`-form. -/
theorem gcd_dvd_848_nat {a b : ℤ} (h : IsCoprime a b) :
    Int.gcd (F a b) (D a b) ∣ 848 := by
  exact_mod_cast gcd_dvd_848 h

/-! ## §8 — the size lower bound: `848·H⁷ ≤ 38896·H³·max |F| |D|`

Cofactor coefficient sums: `b`-side `561 + 767 = 1328 ≤ 38896`, `a`-side
`16720 + 22176 = 38896`; κ = 38896. All cofactors are cubic forms in
`(a, b)`, bounded uniformly by `cubic_natAbs_bound`. -/

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

/-- **Uniform cubic-form bound**: any integer cubic form in `(a, b)` is
bounded by its coefficient `natAbs`-sum times `H³`. -/
private theorem cubic_natAbs_bound (c30 c21 c12 c03 a b : ℤ) :
    (c30 * a ^ 3 + c21 * a ^ 2 * b + c12 * a * b ^ 2 + c03 * b ^ 3).natAbs
      ≤ (c30.natAbs + c21.natAbs + c12.natAbs + c03.natAbs)
          * (max a.natAbs b.natAbs) ^ 3 := by
  have e1 : (c30 * a ^ 3).natAbs = c30.natAbs * a.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
  have e2 : (c21 * a ^ 2 * b).natAbs = c21.natAbs * a.natAbs ^ 2 * b.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
  have e3 : (c12 * a * b ^ 2).natAbs = c12.natAbs * a.natAbs * b.natAbs ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
  have e4 : (c03 * b ^ 3).natAbs = c03.natAbs * b.natAbs ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
  calc (c30 * a ^ 3 + c21 * a ^ 2 * b + c12 * a * b ^ 2 + c03 * b ^ 3).natAbs
      ≤ (c30 * a ^ 3 + c21 * a ^ 2 * b + c12 * a * b ^ 2).natAbs
          + (c03 * b ^ 3).natAbs := Int.natAbs_add_le _ _
    _ ≤ ((c30 * a ^ 3 + c21 * a ^ 2 * b).natAbs + (c12 * a * b ^ 2).natAbs)
          + (c03 * b ^ 3).natAbs :=
        Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ (((c30 * a ^ 3).natAbs + (c21 * a ^ 2 * b).natAbs)
            + (c12 * a * b ^ 2).natAbs) + (c03 * b ^ 3).natAbs :=
        Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ = c30.natAbs * (a.natAbs ^ 3) + c21.natAbs * (a.natAbs ^ 2 * b.natAbs)
          + c12.natAbs * (a.natAbs * b.natAbs ^ 2)
          + c03.natAbs * (b.natAbs ^ 3) := by
        rw [e1, e2, e3, e4]; ring
    _ ≤ c30.natAbs * (max a.natAbs b.natAbs) ^ 3
          + c21.natAbs * (max a.natAbs b.natAbs) ^ 3
          + c12.natAbs * (max a.natAbs b.natAbs) ^ 3
          + c03.natAbs * (max a.natAbs b.natAbs) ^ 3 :=
        Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add (Nat.mul_le_mul le_rfl (mono30 a b))
              (Nat.mul_le_mul le_rfl (mono21 a b)))
            (Nat.mul_le_mul le_rfl (mono12 a b)))
          (Nat.mul_le_mul le_rfl (mono03 a b))
    _ = (c30.natAbs + c21.natAbs + c12.natAbs + c03.natAbs)
          * (max a.natAbs b.natAbs) ^ 3 := by ring

/-- Cofactor bound, `b`-side, first cofactor:
`|(48a² + 40ab − 473b²)·b| ≤ 561·H³`. -/
private theorem c1_bound (a b : ℤ) :
    ((48 * a ^ 2 + 40 * a * b - 473 * b ^ 2) * b).natAbs
      ≤ 561 * (max a.natAbs b.natAbs) ^ 3 := by
  have h : (48 * a ^ 2 + 40 * a * b - 473 * b ^ 2) * b
      = 0 * a ^ 3 + 48 * a ^ 2 * b + 40 * a * b ^ 2 + (-473) * b ^ 3 := by ring
  have hs : (0 : ℤ).natAbs + (48 : ℤ).natAbs + (40 : ℤ).natAbs
      + ((-473 : ℤ)).natAbs = 561 := rfl
  calc ((48 * a ^ 2 + 40 * a * b - 473 * b ^ 2) * b).natAbs
      = (0 * a ^ 3 + 48 * a ^ 2 * b + 40 * a * b ^ 2 + (-473) * b ^ 3).natAbs := by
        rw [h]
    _ ≤ ((0 : ℤ).natAbs + (48 : ℤ).natAbs + (40 : ℤ).natAbs + ((-473 : ℤ)).natAbs)
          * (max a.natAbs b.natAbs) ^ 3 := cubic_natAbs_bound 0 48 40 (-473) a b
    _ = 561 * (max a.natAbs b.natAbs) ^ 3 := by rw [hs]

/-- Cofactor bound, `b`-side, second cofactor:
`|−12a³ + 5a²b − 140ab² + 610b³| ≤ 767·H³`. -/
private theorem c2_bound (a b : ℤ) :
    (-12 * a ^ 3 + 5 * a ^ 2 * b - 140 * a * b ^ 2 + 610 * b ^ 3).natAbs
      ≤ 767 * (max a.natAbs b.natAbs) ^ 3 := by
  have h : -12 * a ^ 3 + 5 * a ^ 2 * b - 140 * a * b ^ 2 + 610 * b ^ 3
      = (-12) * a ^ 3 + 5 * a ^ 2 * b + (-140) * a * b ^ 2 + 610 * b ^ 3 := by ring
  have hs : ((-12 : ℤ)).natAbs + (5 : ℤ).natAbs + ((-140 : ℤ)).natAbs
      + (610 : ℤ).natAbs = 767 := rfl
  calc (-12 * a ^ 3 + 5 * a ^ 2 * b - 140 * a * b ^ 2 + 610 * b ^ 3).natAbs
      = ((-12) * a ^ 3 + 5 * a ^ 2 * b + (-140) * a * b ^ 2 + 610 * b ^ 3).natAbs := by
        rw [h]
    _ ≤ (((-12 : ℤ)).natAbs + (5 : ℤ).natAbs + ((-140 : ℤ)).natAbs + (610 : ℤ).natAbs)
          * (max a.natAbs b.natAbs) ^ 3 := cubic_natAbs_bound (-12) 5 (-140) 610 a b
    _ = 767 * (max a.natAbs b.natAbs) ^ 3 := by rw [hs]

/-- Cofactor bound, `a`-side, first cofactor:
`|848a³ − 640a²b − 7552ab² + 7680b³| ≤ 16720·H³`. -/
private theorem c3_bound (a b : ℤ) :
    (848 * a ^ 3 - 640 * a ^ 2 * b - 7552 * a * b ^ 2 + 7680 * b ^ 3).natAbs
      ≤ 16720 * (max a.natAbs b.natAbs) ^ 3 := by
  have h : 848 * a ^ 3 - 640 * a ^ 2 * b - 7552 * a * b ^ 2 + 7680 * b ^ 3
      = 848 * a ^ 3 + (-640) * a ^ 2 * b + (-7552) * a * b ^ 2 + 7680 * b ^ 3 := by
    ring
  have hs : (848 : ℤ).natAbs + ((-640 : ℤ)).natAbs + ((-7552 : ℤ)).natAbs
      + (7680 : ℤ).natAbs = 16720 := rfl
  calc (848 * a ^ 3 - 640 * a ^ 2 * b - 7552 * a * b ^ 2 + 7680 * b ^ 3).natAbs
      = (848 * a ^ 3 + (-640) * a ^ 2 * b + (-7552) * a * b ^ 2
          + 7680 * b ^ 3).natAbs := by
        rw [h]
    _ ≤ ((848 : ℤ).natAbs + ((-640 : ℤ)).natAbs + ((-7552 : ℤ)).natAbs
          + (7680 : ℤ).natAbs)
          * (max a.natAbs b.natAbs) ^ 3 :=
        cubic_natAbs_bound 848 (-640) (-7552) 7680 a b
    _ = 16720 * (max a.natAbs b.natAbs) ^ 3 := by rw [hs]

/-- Cofactor bound, `a`-side, second cofactor:
`|160a³ − 1280a²b + 11520ab² − 9216b³| ≤ 22176·H³`. -/
private theorem c4_bound (a b : ℤ) :
    (160 * a ^ 3 - 1280 * a ^ 2 * b + 11520 * a * b ^ 2 - 9216 * b ^ 3).natAbs
      ≤ 22176 * (max a.natAbs b.natAbs) ^ 3 := by
  have h : 160 * a ^ 3 - 1280 * a ^ 2 * b + 11520 * a * b ^ 2 - 9216 * b ^ 3
      = 160 * a ^ 3 + (-1280) * a ^ 2 * b + 11520 * a * b ^ 2
          + (-9216) * b ^ 3 := by
    ring
  have hs : (160 : ℤ).natAbs + ((-1280 : ℤ)).natAbs + (11520 : ℤ).natAbs
      + ((-9216 : ℤ)).natAbs = 22176 := rfl
  calc (160 * a ^ 3 - 1280 * a ^ 2 * b + 11520 * a * b ^ 2 - 9216 * b ^ 3).natAbs
      = (160 * a ^ 3 + (-1280) * a ^ 2 * b + 11520 * a * b ^ 2
          + (-9216) * b ^ 3).natAbs := by
        rw [h]
    _ ≤ ((160 : ℤ).natAbs + ((-1280 : ℤ)).natAbs + (11520 : ℤ).natAbs
          + ((-9216 : ℤ)).natAbs)
          * (max a.natAbs b.natAbs) ^ 3 :=
        cubic_natAbs_bound 160 (-1280) 11520 (-9216) a b
    _ = 22176 * (max a.natAbs b.natAbs) ^ 3 := by rw [hs]

/-- The `b`-branch of the size bound: `848·|b|⁷ ≤ 38896·H³·max |F| |D|`
(the natural constant is `1328`; we relax to `38896` to share one constant). -/
theorem size_bound_b (a b : ℤ) :
    848 * b.natAbs ^ 7
      ≤ 38896 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h848 : ((848 : ℤ)).natAbs = 848 := rfl
  have h0 : ((848 : ℤ) * b ^ 7).natAbs = 848 * b.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h848]
  have hterm1 : (((48 * a ^ 2 + 40 * a * b - 473 * b ^ 2) * b) * F a b).natAbs
      ≤ 561 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c1_bound a b) (le_max_left _ _)
  have hterm2 : ((-12 * a ^ 3 + 5 * a ^ 2 * b - 140 * a * b ^ 2 + 610 * b ^ 3)
        * D a b).natAbs
      ≤ 767 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c2_bound a b) (le_max_right _ _)
  calc 848 * b.natAbs ^ 7 = ((848 : ℤ) * b ^ 7).natAbs := h0.symm
    _ = (((48 * a ^ 2 + 40 * a * b - 473 * b ^ 2) * b) * F a b
          + (-12 * a ^ 3 + 5 * a ^ 2 * b - 140 * a * b ^ 2 + 610 * b ^ 3)
              * D a b).natAbs := by
        rw [bezout_b_D a b]
    _ ≤ (((48 * a ^ 2 + 40 * a * b - 473 * b ^ 2) * b) * F a b).natAbs
          + ((-12 * a ^ 3 + 5 * a ^ 2 * b - 140 * a * b ^ 2 + 610 * b ^ 3)
              * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 561 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 767 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 1328 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring
    _ ≤ 38896 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) le_rfl

/-- The `a`-branch of the size bound: `848·|a|⁷ ≤ 38896·H³·max |F| |D|`
(cofactor sums `16720 + 22176 = 38896` — this branch fixes κ). -/
theorem size_bound_a (a b : ℤ) :
    848 * a.natAbs ^ 7
      ≤ 38896 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  have h848 : ((848 : ℤ)).natAbs = 848 := rfl
  have h0 : ((848 : ℤ) * a ^ 7).natAbs = 848 * a.natAbs ^ 7 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, h848]
  have hterm1 : ((848 * a ^ 3 - 640 * a ^ 2 * b - 7552 * a * b ^ 2 + 7680 * b ^ 3)
        * F a b).natAbs
      ≤ 16720 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c3_bound a b) (le_max_left _ _)
  have hterm2 : ((160 * a ^ 3 - 1280 * a ^ 2 * b + 11520 * a * b ^ 2 - 9216 * b ^ 3)
        * D a b).natAbs
      ≤ 22176 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (c4_bound a b) (le_max_right _ _)
  calc 848 * a.natAbs ^ 7 = ((848 : ℤ) * a ^ 7).natAbs := h0.symm
    _ = ((848 * a ^ 3 - 640 * a ^ 2 * b - 7552 * a * b ^ 2 + 7680 * b ^ 3) * F a b
          + (160 * a ^ 3 - 1280 * a ^ 2 * b + 11520 * a * b ^ 2 - 9216 * b ^ 3)
              * D a b).natAbs := by
        rw [bezout_a a b]
    _ ≤ ((848 * a ^ 3 - 640 * a ^ 2 * b - 7552 * a * b ^ 2 + 7680 * b ^ 3)
            * F a b).natAbs
          + ((160 * a ^ 3 - 1280 * a ^ 2 * b + 11520 * a * b ^ 2 - 9216 * b ^ 3)
              * D a b).natAbs :=
        Int.natAbs_add_le _ _
    _ ≤ 16720 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs
          + 22176 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs :=
        Nat.add_le_add hterm1 hterm2
    _ = 38896 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
        ring

/-- **The size lower bound.** For all `a b : ℤ`, with `H = max |a| |b|`:
`848·H⁷ ≤ 38896·H³·max |F(a,b)| |D(a,b)|`. -/
theorem size_bound (a b : ℤ) :
    848 * (max a.natAbs b.natAbs) ^ 7
      ≤ 38896 * (max a.natAbs b.natAbs) ^ 3 * max (F a b).natAbs (D a b).natAbs := by
  rcases le_total a.natAbs b.natAbs with hab | hab
  · have h := size_bound_b a b
    rw [max_eq_right hab] at h ⊢
    exact h
  · have h := size_bound_a a b
    rw [max_eq_left hab] at h ⊢
    exact h

end SizeBound

/-! ## §9 — the division consequence: height survives gcd cancellation -/

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

/-- Pure-`ℕ` descent arithmetic: from `848·H⁷ ≤ 38896·H³·(M·d)` with
`d ≤ 848` and `1 ≤ H`, cancel `H³` to get `848·H⁴ ≤ 38896·848·M`. -/
private theorem descend {H M d : ℕ} (hd : d ≤ 848) (hH : 1 ≤ H)
    (hkey : 848 * H ^ 7 ≤ 38896 * H ^ 3 * (M * d)) :
    848 * H ^ 4 ≤ 38896 * 848 * M := by
  have hH0 : 0 < H := hH
  have h2 : (848 * H ^ 4) * H ^ 3 ≤ (38896 * 848 * M) * H ^ 3 := by
    calc (848 * H ^ 4) * H ^ 3 = 848 * H ^ 7 := by ring
      _ ≤ 38896 * H ^ 3 * (M * d) := hkey
      _ ≤ 38896 * H ^ 3 * (M * 848) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hd)
      _ = (38896 * 848 * M) * H ^ 3 := by ring
  exact Nat.le_of_mul_le_mul_right h2 (pow_pos hH0 3)

/-- **The reduced height bound.** For coprime `a b` with `b ≠ 0`, after
dividing the duplication pair `(F, D)` by `gcd(F, D)` (which divides `848`),
the reduced max still dominates the fourth power of the input height. -/
theorem reduced_height_bound {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (_hD : D a b ≠ 0) :
    848 * (max a.natAbs b.natAbs) ^ 4
      ≤ 38896 * 848 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have hd848 : Int.gcd (F a b) (D a b) ≤ 848 :=
    Nat.le_of_dvd (by norm_num) (gcd_dvd_848_nat h)
  have hH1 : 1 ≤ max a.natAbs b.natAbs :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
      (le_max_right _ _)
  have hsplit :=
    max_natAbs_split (n := Int.gcd (F a b) (D a b))
      (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have key := size_bound a b
  rw [hsplit] at key
  exact descend hd848 hH1 key

/-- `reduced_height_bound` with the common factor `848` cancelled:
`H⁴ ≤ 38896·max |F/g| |D/g|`. -/
theorem reduced_height_bound' {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 38896 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := by
  have key := reduced_height_bound h hb hD
  have key2 : 848 * (max a.natAbs b.natAbs) ^ 4
      ≤ 848 * (38896 *
          max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
              ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by
    calc 848 * (max a.natAbs b.natAbs) ^ 4
        ≤ 38896 * 848 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs) := key
      _ = 848 * (38896 *
            max ((F a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)
                ((D a b / (Int.gcd (F a b) (D a b) : ℤ)).natAbs)) := by ring
  exact Nat.le_of_mul_le_mul_left key2 (by norm_num)

end Reduced

/-! ## §10 — B4: the duplication height inequality on 106a1 (κ = 38896) -/

/-- The B3 bound transported to `naiveHeight`:
`H⁴ ≤ 38896 · naiveHeight (F/D)` for `H = max |a| |b|`. -/
theorem height_bound_of_coprime {a b : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 38896 * naiveHeight ((F a b : ℚ) / (D a b : ℚ)) := by
  rw [naiveHeight_div_int (F a b) (D a b) hD]
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

/-- **The duplication height inequality for 106a1.**  For every rational `x`
(no on-curve hypothesis: `g` never vanishes on ℚ):
`naiveHeight x ^ 4 ≤ 38896 * naiveHeight (f x / g x)`. -/
theorem duplication_height_bound (x : ℚ) :
    naiveHeight x ^ 4 ≤ 38896 * naiveHeight (f x / g x) := by
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
    _ ≤ 38896 * naiveHeight
          ((F x.num (x.den : ℤ) : ℚ) / (D x.num (x.den : ℤ) : ℚ)) :=
        height_bound_of_coprime hcop hb hD
    _ = 38896 * naiveHeight (f x / g x) := by rw [← hfg]

/-- **Duplication height step on the curve.** For any rational affine point
`P = some h` of 106a1 at `(x, y)`: `P + P` is an affine point `some h'` at
some `(x', y')` with `naiveHeight x ^ 4 ≤ 38896 * naiveHeight x'`. -/
theorem dbl_height {x y : ℚ} (h : E106a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E106a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧
        naiveHeight x ^ 4 ≤ 38896 * naiveHeight x' := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
  refine ⟨x', y', h', hadd, ?_⟩
  rw [hx']
  exact duplication_height_bound x

/-! ## §11 — B5: the base point `P = (2, 1)` on 106a1 -/

/-- `(2, 1)` is a nonsingular rational point of 106a1: the equation reads
`1 + 2 = 8 + 4 − 14 + 5`, and the Y-partial there is
`2y + a₁x + a₃ = 4 ≠ 0`. -/
theorem P106_nonsingular : E106a1.toAffine.Nonsingular 2 1 := by
  rw [Affine.nonsingular_iff]
  refine ⟨?_, Or.inr ?_⟩
  · rw [Affine.equation_iff]
    simp only [E106a1_a₁, E106a1_a₂, E106a1_a₃, E106a1_a₄, E106a1_a₆]
    norm_num
  · simp only [E106a1_a₁, E106a1_a₃]
    norm_num

/-- **The base point** `P106 = (2, 1) ∈ E106a1(ℚ)`. -/
noncomputable def P106 : E106a1.toAffine.Point := Point.some P106_nonsingular

/-! ## §12 — the doubling chain -/

/-- The doubling chain: `chain 0 = (2, 1, proof)`, and `chain (n+1)` is the
affine data of `chain n + chain n` chosen from `dbl_height`. -/
noncomputable def chain : ℕ → Σ' (x y : ℚ), E106a1.toAffine.Nonsingular x y :=
  Nat.rec (motive := fun _ => Σ' (x y : ℚ), E106a1.toAffine.Nonsingular x y)
    ⟨2, 1, P106_nonsingular⟩
    fun _ c =>
      ⟨(dbl_height c.2.2).choose,
       (dbl_height c.2.2).choose_spec.choose,
       (dbl_height c.2.2).choose_spec.choose_spec.choose⟩

/-- The x-coordinate along the chain. -/
noncomputable def xs (n : ℕ) : ℚ := (chain n).1

/-- The chain as points of the group `E106a1(ℚ)`. -/
noncomputable def pts (n : ℕ) : E106a1.toAffine.Point := Point.some (chain n).2.2

@[simp] lemma xs_zero : xs 0 = 2 := rfl

lemma pts_zero : pts 0 = P106 := rfl

/-- Each chain step doubles the point (from `dbl_height`'s `choose_spec`). -/
lemma pts_succ (n : ℕ) : pts (n + 1) = pts n + pts n :=
  ((dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.1).symm

/-- Each chain step satisfies the quartic height inequality (κ = 38896). -/
lemma height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ 38896 * naiveHeight (xs (n + 1)) :=
  (dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.2

/-- The chain is the `2ⁿ`-multiples of the base point: `pts n = 2ⁿ • P106`. -/
lemma pts_eq_two_pow_smul (n : ℕ) : pts n = ((2 : ℤ) ^ n) • P106 := by
  induction n with
  | zero => rw [pow_zero, one_zsmul, pts_zero]
  | succ k ih =>
      have h2 : ((2 : ℤ) ^ (k + 1)) = 2 ^ k + 2 ^ k := by ring
      rw [pts_succ, ih, h2, add_zsmul]

/-! ## §13 — the x-coordinates are pinned exactly -/

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

/-- `x(4P) = −1`. -/
lemma xs_two : xs 2 = -1 := by
  rw [xs_succ 1, xs_one]; norm_num [f, g]

/-- `x(8P) = 79/49`. -/
lemma xs_three : xs 3 = 79 / 49 := by
  rw [xs_succ 2, xs_two]; norm_num [f, g]

/-- `x(16P) = 15319439/26615281`. -/
lemma xs_four : xs 4 = 15319439 / 26615281 := by
  rw [xs_succ 3, xs_three]; norm_num [f, g]

/-- `naiveHeight (x(16P)) = 26615281` — the DENOMINATOR dominates:
the fraction is already reduced, `gcd(15319439, 26615281) = 1`
(`26615281 = 5159² = 7²·11²·67²` and `15319439` shares no factor), and
`max(15319439, 26615281) = 26615281`. -/
lemma naiveHeight_xs_four : naiveHeight (xs 4) = 26615281 := by
  have h4 : xs 4 = ((15319439 : ℤ) : ℚ) / ((26615281 : ℤ) : ℚ) := by
    rw [xs_four]; norm_num
  have hg : Int.gcd 15319439 26615281 = 1 := by norm_num
  rw [h4, naiveHeight_div_int 15319439 26615281 (by norm_num), hg]
  norm_num

/-- The B5 threshold check: `x(16P)` clears the curve constant `κ = 38896`. -/
lemma threshold : 38896 < naiveHeight (xs 4) := by
  rw [naiveHeight_xs_four]; norm_num

/-! ## §14 — firing B1's driver: infinitely many x-coordinates -/

/-- **The chain from `16P` on has infinite x-coordinate range**: the quartic
step (§12) starts above the threshold (§13), so r130's growth engine applies. -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 4)).Infinite :=
  infinite_of_duplication_step (κ := 38896) (fun n => xs (n + 4))
    (by norm_num) (fun n => height_step (n + 4)) threshold

/-! ## §15 — non-torsion: a finite orbit cannot contain an infinite image -/

/-- The x-coordinate projection on the point group (`0` at the identity). -/
def X : E106a1.toAffine.Point → ℚ
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

lemma X_pts (n : ℕ) : X (pts n) = xs n := rfl

/-- **CAPSTONE 1 — `P = (2, 1)` is non-torsion on 106a1.** If `P106` had
finite order, `AddSubgroup.zmultiples P106` would be a finite set; its image
under `X` would be finite, yet it contains the infinite range of §14. -/
theorem P_nonTorsion : ¬ IsOfFinAddOrder P106 := by
  intro hfin
  have hfinite := hfin.finite_zmultiples
  have hsub : (Set.range fun n => xs (n + 4))
      ⊆ X '' (AddSubgroup.zmultiples P106 : Set _) := by
    rintro q ⟨n, rfl⟩
    refine ⟨pts (n + 4), ?_, X_pts (n + 4)⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨(2 : ℤ) ^ (n + 4), (pts_eq_two_pow_smul (n + 4)).symm⟩
  exact xs_shifted_infinite ((hfinite.image X).subset hsub)

/-! ## §16 — THE FLAG: rank ≥ 1 for 106a1 -/

/-- The r129 certificate, discharged: `P106` has infinite order in
`E106a1(ℚ)`. -/
theorem P106_certificate : NonTorsionCertificate E106a1.toAffine P106 :=
  P_nonTorsion

/-- **CAPSTONE 2 — the Mordell–Weil rank of 106a1 is at least 1.** -/
theorem E106a1_rank_ge_one : 1 ≤ Module.rank ℤ E106a1.toAffine.Point :=
  mordellWeil_rank_ge_one E106a1.toAffine P106 P_nonTorsion

end PrincipiaTractalis.E106a1RankOne

#print axioms PrincipiaTractalis.E106a1RankOne.bezout_b
#print axioms PrincipiaTractalis.E106a1RankOne.bezout_a
#print axioms PrincipiaTractalis.E106a1RankOne.gcd_dvd_848
#print axioms PrincipiaTractalis.E106a1RankOne.dbl_x
#print axioms PrincipiaTractalis.E106a1RankOne.duplication_height_bound
#print axioms PrincipiaTractalis.E106a1RankOne.dbl_height
#print axioms PrincipiaTractalis.E106a1RankOne.P106_nonsingular
#print axioms PrincipiaTractalis.E106a1RankOne.xs_four
#print axioms PrincipiaTractalis.E106a1RankOne.naiveHeight_xs_four
#print axioms PrincipiaTractalis.E106a1RankOne.xs_shifted_infinite
#print axioms PrincipiaTractalis.E106a1RankOne.P_nonTorsion
#print axioms PrincipiaTractalis.E106a1RankOne.P106_certificate
#print axioms PrincipiaTractalis.E106a1RankOne.E106a1_rank_ge_one
