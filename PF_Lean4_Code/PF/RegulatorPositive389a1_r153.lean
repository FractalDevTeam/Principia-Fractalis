/-
# PF.RegulatorPositive389a1_r153

★★★ 2026-07-28 — r153: THE INTERVAL MACHINE FOR CANONICAL HEIGHTS ★★★

r152 reduced `rank ≥ 2` for 389a1 to one numerical fact: `regDet P Q ≠ 0`
for the LMFDB generators `P = (0,0)`, `Q = (1,0)`.  This file builds the
certified machinery that produces explicit rational intervals for canonical
heights, from which that fact (and the four non-torsion side conditions)
follow by interval arithmetic in r154.

Three ingredients, all exact:

1. **The shifted window** (`canheight_window_shift`).  r147 gives
   `|ĥ(R) − lognh R| ≤ log 1728 / 3` and `ĥ(2ⁿR) = 4ⁿ·ĥ(R)`; applying the
   former at `2ⁿR` and dividing by `4ⁿ` sharpens it to
       `|ĥ(R) − hseq R n| ≤ log 1728 / (3·4ⁿ)`,
   which at `n = 3` is below `7.625/192 < 0.0398`.
2. **The dyadic log bracket** (`log_bracket_rat`).  For an explicit natural
   `H` with `2ʲ ≤ H < 2ʲ⁺¹`, `log H` is pinned between `j·log 2` and
   `(j+1)·log 2`, and mathlib's `Real.log_two_gt_d9 / lt_d9` turn those into
   rationals.  One bit costs only `log 2 / 64 ≈ 0.0108` at `n = 3`.
3. **The dyadic chain in `X`-form** (`X_eight_smul`).  For an affine point,
   `X(8·R)` is the third iterate of `x ↦ f x / g x` (r143's `dbl_x`, r148g's
   `add_self_ne_zero`), so it is computable by `norm_num`.

Composing them, `canheight_bracket` turns "the level-3 chain value of `R`
has naive height between `2ʲ` and `2ʲ⁺¹`" into a rational two-sided bound on
`ĥ(R)`.

Reconnaissance for 389a1 (exact, sympy-verified; the Lean instantiations are
r154):

| point | `x(8·)` naive height | bracket | resulting `ĥ` interval |
|---|---|---|---|
| `P = (0,0)`     | `1169154495`              | `2³⁰…2³¹` | `[0.2851, 0.3755]` |
| `Q = (1,0)`     | `11776563836346`          | `2⁴³…2⁴⁴` | `[0.4259, 0.5163]` |
| `P+Q = (−2,−1)` | `30157844295583882647192303` | `2⁸⁴…2⁸⁵` | `[0.8700, 0.9603]` |
| `P−Q = (−1,−2)` | `7960116832793145801`     | `2⁶²…2⁶³` | `[0.6317, 0.7221]` |

All four lower bounds are positive, so all four points are non-torsion; and
`ĥP·ĥQ ≥ 0.1214` while `⟨P,Q⟩² ≤ 0.0156`, giving `regDet ≥ 0.1059 > 0`.

HONEST SCOPE.  This file provides the machinery and proves nothing about
389a1's generators; the instantiation and the flag are r154.  Nothing here
asserts a value for any canonical height.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.RegulatorIndependence389a1_r152
import Mathlib.Analysis.Complex.ExponentialBounds

namespace PrincipiaTractalis.RegulatorPositive389a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E389a1RankOne
open PrincipiaTractalis.CanonicalHeight389a1
open PrincipiaTractalis.QuasiParallelogramLower389a1
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the shifted window -/

/-- **The sharpened window.**  `|ĥ(R) − hseq R n| ≤ log 1728 / (3·4ⁿ)`. -/
theorem canheight_window_shift (R : E389a1.toAffine.Point) (n : ℕ) :
    |canheight R - hseq R n| ≤ Real.log 1728 / 3 / 4 ^ n := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hw := canheight_window (((2 : ℤ) ^ n) • R)
  rw [canheight_two_pow R n] at hw
  have hkey : 4 ^ n * |canheight R - hseq R n| ≤ Real.log 1728 / 3 := by
    have e : (4 : ℝ) ^ n * (canheight R - hseq R n)
        = 4 ^ n * canheight R - lognh (((2 : ℤ) ^ n) • R) := by
      simp only [hseq]
      field_simp
    calc 4 ^ n * |canheight R - hseq R n|
        = |(4 : ℝ) ^ n * (canheight R - hseq R n)| := by
          rw [abs_mul, abs_of_pos h4]
      _ = |4 ^ n * canheight R - lognh (((2 : ℤ) ^ n) • R)| := by rw [e]
      _ ≤ Real.log 1728 / 3 := hw
  rw [le_div_iff₀ h4]
  calc |canheight R - hseq R n| * 4 ^ n
      = 4 ^ n * |canheight R - hseq R n| := by ring
    _ ≤ Real.log 1728 / 3 := hkey

/-! ## §2 — the dyadic log bracket -/

/-- `log N` is bracketed by consecutive multiples of `log 2` when
`2ʲ ≤ N < 2ʲ⁺¹`. -/
theorem log_bracket {N j : ℕ} (hlo : 2 ^ j ≤ N) (hhi : N < 2 ^ (j + 1)) :
    (j : ℝ) * Real.log 2 ≤ Real.log N ∧
      Real.log N ≤ ((j : ℝ) + 1) * Real.log 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := lt_of_lt_of_le (pow_pos (by norm_num : (0:ℕ) < 2) j) hlo
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · have hle : ((2 : ℝ) ^ j) ≤ (N : ℝ) := by exact_mod_cast hlo
    calc (j : ℝ) * Real.log 2 = Real.log (2 ^ j) := by rw [Real.log_pow]
      _ ≤ Real.log N := Real.log_le_log (by positivity) hle
  · have hle : (N : ℝ) ≤ ((2 : ℝ) ^ (j + 1)) := by
      have h : (N : ℝ) < ((2 : ℝ) ^ (j + 1)) := by exact_mod_cast hhi
      linarith [h]
    calc Real.log N ≤ Real.log (2 ^ (j + 1)) := Real.log_le_log hNpos hle
      _ = ((j : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring

/-- The bracket with `log 2` replaced by mathlib's nine-decimal bounds. -/
theorem log_bracket_rat {N j : ℕ} (hlo : 2 ^ j ≤ N) (hhi : N < 2 ^ (j + 1)) :
    (j : ℝ) * 0.6931471803 ≤ Real.log N ∧
      Real.log N ≤ ((j : ℝ) + 1) * 0.6931471808 := by
  obtain ⟨h1, h2⟩ := log_bracket hlo hhi
  have hgt := Real.log_two_gt_d9
  have hlt := Real.log_two_lt_d9
  refine ⟨?_, ?_⟩
  · have hstep : (j : ℝ) * 0.6931471803 ≤ (j : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (le_of_lt hgt) (Nat.cast_nonneg j)
    linarith [hstep, h1]
  · have hstep : ((j : ℝ) + 1) * Real.log 2 ≤ ((j : ℝ) + 1) * 0.6931471808 :=
      mul_le_mul_of_nonneg_left (le_of_lt hlt) (by positivity)
    linarith [hstep, h2]

/-- `log 1728 < 7.625`, via `2¹⁰ ≤ 1728 < 2¹¹` and the `log 2` bound. -/
theorem log_1728_lt : Real.log 1728 < 7.625 := by
  have hlo : (2 : ℕ) ^ 10 ≤ 1728 := by norm_num
  have hhi : (1728 : ℕ) < 2 ^ (10 + 1) := by norm_num
  obtain ⟨_, h2⟩ := log_bracket_rat hlo hhi
  have hcast : ((1728 : ℕ) : ℝ) = (1728 : ℝ) := by norm_num
  rw [hcast] at h2
  norm_num at h2
  linarith [h2]

/-! ## §3 — the dyadic chain in `X`-form -/

/-- `(2 : ℤ) • R = R + R`. -/
theorem two_zsmul_eq (R : E389a1.toAffine.Point) : (2 : ℤ) • R = R + R := by
  rw [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]

/-- **One doubling step, in affine form.**  For an affine point with
x-coordinate `x`, the double is affine with x-coordinate `f x / g x`. -/
theorem dbl_step {x y : ℚ} (h : E389a1.toAffine.Nonsingular x y) :
    ∃ x' y', ∃ h' : E389a1.toAffine.Nonsingular x' y',
      Point.some h + Point.some h = Point.some h' ∧ x' = f x / g x := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
  exact ⟨x', y', h', hadd, hx'⟩

/-- **`X(8·R)` is the third iterate of `x ↦ f x / g x`.**  Three applications
of `dbl_step`, with `8 = 2·2·2` handled by `smul_smul`. -/
theorem X_eight_smul {x₀ y₀ : ℚ} (h₀ : E389a1.toAffine.Nonsingular x₀ y₀) :
    X ((((2 : ℤ)) ^ 3) • Point.some h₀)
      = f (f (f x₀ / g x₀) / g (f x₀ / g x₀))
          / g (f (f x₀ / g x₀) / g (f x₀ / g x₀)) := by
  obtain ⟨x₁, y₁, h₁, e₁, hx₁⟩ := dbl_step h₀
  obtain ⟨x₂, y₂, h₂, e₂, hx₂⟩ := dbl_step h₁
  obtain ⟨x₃, y₃, h₃, e₃, hx₃⟩ := dbl_step h₂
  -- 8•R = 2•(2•(2•R))
  have h8 : (((2 : ℤ)) ^ 3) • Point.some h₀
      = (2 : ℤ) • ((2 : ℤ) • ((2 : ℤ) • Point.some h₀)) := by
    rw [smul_smul, smul_smul]
    norm_num
  have s₁ : (2 : ℤ) • Point.some h₀ = Point.some h₁ := by
    rw [two_zsmul_eq]; exact e₁
  have s₂ : (2 : ℤ) • Point.some h₁ = Point.some h₂ := by
    rw [two_zsmul_eq]; exact e₂
  have s₃ : (2 : ℤ) • Point.some h₂ = Point.some h₃ := by
    rw [two_zsmul_eq]; exact e₃
  rw [h8, s₁, s₂, s₃]
  show x₃ = _
  rw [hx₃, hx₂, hx₁]

/-! ## §4 — THE INTERVAL MACHINE -/

/-- **★★★ r153 — THE CANONICAL-HEIGHT BRACKET ★★★**

If the level-3 dyadic chain value of `R` has naive height `H` with
`2ʲ ≤ H < 2ʲ⁺¹`, then `ĥ(R)` lies in an explicit rational interval:

    `j·0.6931471803/64 − 7.625/192 ≤ ĥ(R) ≤ (j+1)·0.6931471808/64 + 7.625/192`.

The left term comes from the dyadic bracket, the right from the shifted
window at `n = 3`. -/
theorem canheight_bracket {R : E389a1.toAffine.Point} {H j : ℕ}
    (hH : naiveHeight (X ((((2 : ℤ)) ^ 3) • R)) = H)
    (hlo : 2 ^ j ≤ H) (hhi : H < 2 ^ (j + 1)) :
    (j : ℝ) * 0.6931471803 / 64 - 7.625 / 192 ≤ canheight R ∧
      canheight R ≤ ((j : ℝ) + 1) * 0.6931471808 / 64 + 7.625 / 192 := by
  -- the level-3 sequence value is log H / 64
  have hh3 : hseq R 3 = Real.log H / 64 := by
    simp only [hseq, lognh, hH]
    norm_num
  -- the shifted window at n = 3
  have hwin := canheight_window_shift R 3
  have hwin' : |canheight R - hseq R 3| ≤ 7.625 / 192 := by
    have h1728 := log_1728_lt
    have : Real.log 1728 / 3 / 4 ^ 3 < 7.625 / 192 := by
      norm_num
      linarith [h1728]
    linarith [hwin, this]
  rw [hh3] at hwin'
  rw [abs_le] at hwin'
  obtain ⟨hw1, hw2⟩ := hwin'
  -- the dyadic bracket on log H
  obtain ⟨hb1, hb2⟩ := log_bracket_rat hlo hhi
  refine ⟨?_, ?_⟩
  · have : (j : ℝ) * 0.6931471803 / 64 ≤ Real.log H / 64 := by
      linarith [hb1]
    linarith [hw1, this]
  · have : Real.log H / 64 ≤ ((j : ℝ) + 1) * 0.6931471808 / 64 := by
      linarith [hb2]
    linarith [hw2, this]

/-- A positive lower bracket certifies non-torsion (r147's
`canheight_eq_zero_iff_torsion`). -/
theorem nonTorsion_of_bracket {R : E389a1.toAffine.Point} {H j : ℕ}
    (hH : naiveHeight (X ((((2 : ℤ)) ^ 3) • R)) = H)
    (hlo : 2 ^ j ≤ H) (hhi : H < 2 ^ (j + 1))
    (hpos : 0 < (j : ℝ) * 0.6931471803 / 64 - 7.625 / 192) :
    ¬ IsOfFinAddOrder R := by
  intro hfin
  have h0 : canheight R = 0 := canheight_of_torsion hfin
  obtain ⟨hb1, _⟩ := canheight_bracket hH hlo hhi
  rw [h0] at hb1
  linarith [hpos, hb1]

end PrincipiaTractalis.RegulatorPositive389a1

#print axioms PrincipiaTractalis.RegulatorPositive389a1.canheight_window_shift
#print axioms PrincipiaTractalis.RegulatorPositive389a1.log_bracket_rat
#print axioms PrincipiaTractalis.RegulatorPositive389a1.X_eight_smul
#print axioms PrincipiaTractalis.RegulatorPositive389a1.canheight_bracket
#print axioms PrincipiaTractalis.RegulatorPositive389a1.nonTorsion_of_bracket
