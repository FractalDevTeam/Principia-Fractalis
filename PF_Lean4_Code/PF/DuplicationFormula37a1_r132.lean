/-
# PF.DuplicationFormula37a1_r132

★ 2026-07-27 — STONE B2 OF THE NON-TORSION ARC (BSD axis) ★

The duplication formula for the rank-1 curve **37a1**: `y² + y = x³ − x`,
as a kernel-verified statement about mathlib's affine group law.

For an affine rational point `P = (x, y)` on 37a1:

  * `(2y + 1)² = g(x)` on-curve, where `g(x) = 4x³ − 4x + 1` (= ψ₂²);
  * `g` has **no rational roots** (rational root theorem, 6 candidates) —
    hence no rational affine point of 37a1 is 2-torsion, and doubling never
    leaves the affine chart;
  * the tangent slope at `P` is `(3x² − 1)/(2y + 1)`;
  * **the capstone**: `P + P` is again an affine point `some h'` whose
    x-coordinate is exactly `f(x)/g(x)` with `f(x) = x⁴ + 2x² − 2x + 1`,
    via the on-curve identity `(3x² − 1)² − 2x·g(x) = f(x)`;
  * `(2 : ℤ) • P = P + P`, so the arc's B5 stone can phrase iterated
    doubling as `2^n • Q`.

This is the mathlib-facing half of the single-curve height machine
(wall map: codex/BSD_NONTORSION_ARC_PLAN_2026-07-27.md).  Stone B3
(`DuplicationBezout37a1_r131`) handles the pure-ℤ resultant/gcd bounds;
B4 joins the two into the duplication height inequality.

HONEST SCOPE. This file proves the duplication formula for the ONE curve
37a1 over ℚ, nothing more.  It does not bound heights (B3/B4), does not
certify any point as non-torsion (B5), and does not touch `Module.rank`
(that is r129's conversion lemma).  All statements are unconditional
theorems about `WeierstrassCurve.Affine.Point` addition on the pin
(mathlib eed770a4, Lean v4.24.0-rc1).

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-27.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace PrincipiaTractalis.DuplicationFormula37a1

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the curve 37a1 and the duplication polynomials -/

/-- **Curve 37a1**: `y² + y = x³ − x`, i.e. `(a₁, a₂, a₃, a₄, a₆) = (0, 0, 1, −1, 0)`.
Defined locally to keep this file self-contained (the corpus's
`BSDGaloisPairConcordance.E_rank_one` is the same literal). -/
def E37a1 : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

@[simp] lemma E37a1_a₁ : E37a1.a₁ = 0 := rfl
@[simp] lemma E37a1_a₂ : E37a1.a₂ = 0 := rfl
@[simp] lemma E37a1_a₃ : E37a1.a₃ = 1 := rfl
@[simp] lemma E37a1_a₄ : E37a1.a₄ = -1 := rfl
@[simp] lemma E37a1_a₆ : E37a1.a₆ = 0 := rfl

/-- The duplication numerator `f(x) = x⁴ + 2x² − 2x + 1`
(= `x⁴ − b₄x² − 2b₆x − b₈` for 37a1). -/
def f (x : ℚ) : ℚ := x ^ 4 + 2 * x ^ 2 - 2 * x + 1

/-- The duplication denominator `g(x) = 4x³ − 4x + 1`
(= `ψ₂² = 4x³ + b₂x² + 2b₄x + b₆` for 37a1). -/
def g (x : ℚ) : ℚ := 4 * x ^ 3 - 4 * x + 1

/-! ## §2 — the on-curve square identity `(2y + 1)² = g(x)` -/

/-- On 37a1, `(2y + 1)² = g(x)`: four times the Weierstrass equation
`y² + y = x³ − x` plus one. -/
theorem two_y_add_one_sq {x y : ℚ} (h : E37a1.toAffine.Equation x y) :
    (2 * y + 1) ^ 2 = g x := by
  rw [Affine.equation_iff] at h
  simp only [E37a1_a₁, E37a1_a₂, E37a1_a₃, E37a1_a₄, E37a1_a₆] at h
  simp only [g]
  linear_combination 4 * h

/-! ## §3 — `g` has no rational roots (rational root theorem, by hand) -/

/-- Integer core of the rational root theorem for `g`: no reduced fraction
`n/d` (`d ≥ 1`, `gcd(n, d) = 1`) satisfies `4n³ − 4nd² + d³ = 0`.
From the equation, `n ∣ d³` forces `n = ±1` and `d ∣ 4n³` forces `d ∣ 4`;
the six candidates `±1, ±1/2, ±1/4` all fail. -/
lemma no_integer_root {n d : ℤ} (hd1 : 1 ≤ d) (hcop : IsCoprime n d)
    (key : 4 * n ^ 3 - 4 * n * d ^ 2 + d ^ 3 = 0) : False := by
  -- n ∣ d³ since d³ = n · 4(d² − n²)
  have hn_dvd : n ∣ d ^ 3 := ⟨4 * (d ^ 2 - n ^ 2), by linear_combination key⟩
  have hn_unit : IsUnit n :=
    (hcop.pow_right (n := 3)).isUnit_of_dvd' dvd_rfl hn_dvd
  -- d ∣ 4n³ since 4n³ = d · (4nd − d²)
  have hd_dvd : d ∣ 4 * n ^ 3 := ⟨4 * n * d - d ^ 2, by linear_combination key⟩
  have hd4 : d ∣ 4 :=
    (hcop.symm.pow_right (n := 3)).dvd_of_dvd_mul_right hd_dvd
  have hd_le : d ≤ 4 := Int.le_of_dvd (by norm_num) hd4
  have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases Int.isUnit_iff.mp hn_unit with rfl | rfl <;>
    rcases hd_cases with rfl | rfl | rfl | rfl <;>
      norm_num at key

/-- **`g` has no rational roots.**  In particular (via §2) no rational affine
point of 37a1 is 2-torsion, so doubling never leaves the affine chart. -/
theorem g_ne_zero (x : ℚ) : g x ≠ 0 := by
  intro hg
  have hg' : 4 * x ^ 3 - 4 * x + 1 = 0 := by simpa [g] using hg
  have hden : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  -- clear denominators: 4n³ − 4nd² + d³ = 0 over ℚ, then over ℤ
  have h0 : 4 * (x.num : ℚ) ^ 3 - 4 * (x.num : ℚ) * (x.den : ℚ) ^ 2
      + (x.den : ℚ) ^ 3 = 0 := by
    have hxq : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    rw [hxq] at hg'
    field_simp at hg'
    linear_combination hg'
  have key : 4 * x.num ^ 3 - 4 * x.num * (x.den : ℤ) ^ 2 + (x.den : ℤ) ^ 3 = 0 := by
    exact_mod_cast h0
  have hd1 : (1 : ℤ) ≤ (x.den : ℤ) := by
    have := x.pos
    omega
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  exact no_integer_root hd1 hcop key

/-! ## §4 — no rational affine 2-torsion: `2y + 1 ≠ 0` on-curve -/

/-- On 37a1, `2y + 1 ≠ 0` for every rational affine point: otherwise
`g(x) = (2y + 1)² = 0`, contradicting §3. -/
theorem two_y_add_one_ne_zero {x y : ℚ} (h : E37a1.toAffine.Equation x y) :
    2 * y + 1 ≠ 0 := by
  intro h0
  apply g_ne_zero x
  rw [← two_y_add_one_sq h, h0]
  norm_num

/-- `negY` on 37a1 is `-y - 1`. -/
lemma negY_eq (x y : ℚ) : E37a1.toAffine.negY x y = -y - 1 := by
  simp [Affine.negY]

/-- No rational affine point of 37a1 is 2-torsion: `y ≠ negY x y`.
This is the hypothesis that lands doubling in the `some` branch of the
group law. -/
theorem y_ne_negY {x y : ℚ} (h : E37a1.toAffine.Equation x y) :
    y ≠ E37a1.toAffine.negY x y := by
  rw [negY_eq]
  intro hy
  exact two_y_add_one_ne_zero h (by linarith)

/-! ## §5 — the tangent slope -/

/-- The tangent slope at a rational affine point of 37a1 is
`(3x² − 1)/(2y + 1)`. -/
theorem slope_eq {x y : ℚ} (h : E37a1.toAffine.Nonsingular x y) :
    E37a1.toAffine.slope x x y y = (3 * x ^ 2 - 1) / (2 * y + 1) := by
  rw [Affine.slope_of_Y_ne rfl (y_ne_negY h.left), negY_eq]
  have hnum : 3 * x ^ 2 + 2 * E37a1.toAffine.a₂ * x + E37a1.toAffine.a₄
      - E37a1.toAffine.a₁ * y = 3 * x ^ 2 - 1 := by
    simp only [E37a1_a₁, E37a1_a₂, E37a1_a₄]
    ring
  have hden : y - (-y - 1) = 2 * y + 1 := by ring
  rw [hnum, hden]

/-! ## §6 — THE CAPSTONE: `x(P + P) = f(x)/g(x)` -/

/-- **The duplication formula for 37a1.**  For any rational affine point
`P = some h` at `(x, y)`, the double `P + P` is again an affine point
`some h'` (never `0`, by §4), and its x-coordinate is exactly `f(x)/g(x)`.
The x-coordinate identity is `(3x² − 1)² − 2x·g(x) = f(x)` combined with
`(2y + 1)² = g(x) ≠ 0`. -/
theorem dbl_x {x y : ℚ} (h : E37a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E37a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x := by
  have hy : y ≠ E37a1.toAffine.negY x y := y_ne_negY h.left
  refine ⟨_, _, _, Point.add_self_of_Y_ne hy, ?_⟩
  -- goal: addX x x (slope x x y y) = f x / g x
  have hg : g x ≠ 0 := g_ne_zero x
  have h2y : 2 * y + 1 ≠ 0 := two_y_add_one_ne_zero h.left
  have hsq : (2 * y + 1) ^ 2 = g x := two_y_add_one_sq h.left
  rw [slope_eq h]
  simp only [Affine.addX, E37a1_a₁, E37a1_a₂]
  rw [div_pow, hsq]
  field_simp
  simp only [f, g]
  ring

/-! ## §7 — `2 • P = P + P` (interface for B5's `2^n • Q` chain) -/

/-- `(2 : ℤ) • P = P + P` in the point group of 37a1 — lets stone B5 phrase
the doubling chain as `2^n • Q`. -/
theorem two_zsmul_eq_add {x y : ℚ} (h : E37a1.toAffine.Nonsingular x y) :
    (2 : ℤ) • (Point.some h) = Point.some h + Point.some h :=
  two_zsmul _

/-- The `ℕ`-scalar version. -/
theorem two_nsmul_eq_add {x y : ℚ} (h : E37a1.toAffine.Nonsingular x y) :
    (2 : ℕ) • (Point.some h) = Point.some h + Point.some h :=
  two_nsmul _

end PrincipiaTractalis.DuplicationFormula37a1

#print axioms PrincipiaTractalis.DuplicationFormula37a1.two_y_add_one_sq
#print axioms PrincipiaTractalis.DuplicationFormula37a1.g_ne_zero
#print axioms PrincipiaTractalis.DuplicationFormula37a1.two_y_add_one_ne_zero
#print axioms PrincipiaTractalis.DuplicationFormula37a1.slope_eq
#print axioms PrincipiaTractalis.DuplicationFormula37a1.dbl_x
#print axioms PrincipiaTractalis.DuplicationFormula37a1.two_zsmul_eq_add
