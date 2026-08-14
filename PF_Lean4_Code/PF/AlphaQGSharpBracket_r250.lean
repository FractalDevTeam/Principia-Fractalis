/-
# r250: SHARP α_QG UPPER BRACKET — σ(α_QG) < log₃(49/50).

★ 2026-08-13 r250 — the SEVENTH sharp bracket landing, completing 6/6
coverage of the irrational corpus pillars. `σ(α_QG = √(2π)) < log₃(49/50)
= -log₃(50/49) ≈ -0.0184`. Near-critical value σ_QG ≈ -0.0387 requires
r248's Level-4 sin lower bound plus high-precision π (`Real.pi_gt_d6`,
`Real.pi_lt_d6`). ★

## Numerical setup

`π · √(2π) ≈ 7.87481`. Subtract 2π ≈ 6.28319 to land at
`z := π · √(2π) − 2π ≈ 1.59162`, which is `π/2 + h` with
`h ≈ 0.02083`. Then `cos(π · √(2π)) = cos(π/2 + h) = −sin(h) ≈ −0.02083`.
So `1 + 2·cos(π · √(2π)) ≈ 0.9583`, giving `σ_QG ≈ log₃(0.9583) ≈ -0.0387`.

Bracket target: prove `σ_QG < log₃(49/50)`, i.e., `1 + 2·cos < 49/50`,
i.e., `cos(π · √(2π)) < −1/100`.

Sufficient: prove `sin(h) > 1/100` where `h = π · √(2π) − 5π/2`.

By r248's `sin_ge_x_sub_cube_div_six`: `sin(h) ≥ h − h³/6`.
If `h ≥ 1/50`, then `h − h³/6 ≥ 1/50 − (1/50)³/6 > 1/50 − 1/750000 > 1/100`. ✓

The technical crux: prove `h = π · (√(2π) − 5/2) > 1/50`.

Chain (with `π > 3.141592`):

    √(2π) > 2.5065 ⟺ (2.5065)² < 2π ⟺ 6.28253 < 2π.
    From π > 3.141592: 2π > 6.283184 > 6.28253 ✓.

    Then π · (√(2π) − 5/2) > 3.141592 · (2.5065 − 2.5) = 3.141592 · 0.0065
        = 0.020420 > 1/50 = 0.02 ✓.

## The completed sharp-bracket coverage

Together with r243–r248 (bundled in r249), every irrational corpus pillar
now has a kernel-clean sharp algebraic (or Taylor) bracket:

| pillar         | bracket                     | landing |
|----------------|-----------------------------|---------|
| α_Hodge = φ   | σ < 1/2                    | r248 (Taylor) |
| α_NP = φ+1/4  | σ > 2·log₃ φ                | r247 |
| α_BSD = 3π/4  | σ < log 2/log 3             | r245 |
| α_P = √2      | σ < -log 2/log 3            | r244 |
| α_QG = √(2π)  | **σ < log₃(49/50)**        | **r250 (this file)** |
| α_NS = 3π/2   | σ < -log 2/log 3            | r246 |

## Contents

§1 High-precision √(2π) bounds.
§2 `h = π · √(2π) − 5π/2 > 1/50`.
§3 sin(h) > 1/100 via r248 Level-4 `sin_ge_x_sub_cube_div_six`.
§4 `cos(π · √(2π)) < -1/100` via cos(π/2 + h) = -sin(h) + `cos_add_two_pi`.
§5 Positivity: `1 + 2·cos(π · √(2π)) > 0`.
§6 `sigma_alphaQG_lt_logb_three_49_over_50` — the sharp bracket.
§7 `SO_αQG_sigma_lt_logb_three_49_over_50` — r223 elevation.
§8 Axiom check.

## Scope

* NOT novel — pure algebra + r248 Level 4 + high-precision `Real.pi_gt_d6`.
* NOT the tightest possible (σ_QG ≈ -0.039 vs the -0.018 bracket).
* NOT a Millennium discharge.
* IS the seventh sharp substrate bracket, closing 6/6 irrational corpus
  pillar sharp-bracket coverage.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaQGSigmaNegative_r230
import PF.AlphaHodgeTighterHalfBracket_r248

open scoped Real

namespace PrincipiaTractalis.AlphaQGSharpBracket

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 High-precision `√(2π)` lower bound. -/

/-- **`sqrt_two_pi_gt_25065_over_10000`** — `√(2π) > 2.5065`. -/
lemma sqrt_two_pi_gt_25065_over_10000 :
    (25065 : ℝ) / 10000 < Real.sqrt (2 * π) := by
  have hpi : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have h2pi_gt : (2.5065 : ℝ)^2 < 2 * π := by nlinarith [hpi]
  have hnn : (0 : ℝ) ≤ 2.5065 := by norm_num
  have hlt : Real.sqrt ((2.5065 : ℝ)^2) < Real.sqrt (2 * π) :=
    Real.sqrt_lt_sqrt (by positivity) h2pi_gt
  rw [Real.sqrt_sq hnn] at hlt
  have h_eq : (25065 : ℝ) / 10000 = 2.5065 := by norm_num
  rw [h_eq]; exact hlt

/-! ## §2 `h := π · √(2π) − 5π/2 > 1/50`. -/

/-- **`h_gt_one_fiftieth`** — `π · √(2π) − 5π/2 > 1/50`.

Chain: `√(2π) > 2.5065` (§1); `π > 3.141592`; product bound. -/
lemma h_gt_one_fiftieth :
    (1 : ℝ) / 50 < π * Real.sqrt (2 * π) - 5 * π / 2 := by
  have hpi : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hs := sqrt_two_pi_gt_25065_over_10000
  -- π · √(2π) - 5π/2 = π · (√(2π) - 5/2) > 3.141592 · (25065/10000 - 5/2)
  --                = 3.141592 · (65/10000) = 20.42.../1000000 > 1/50.
  nlinarith [hpi, hs, hpi_pos, mul_pos hpi_pos (by linarith : (0:ℝ) < Real.sqrt (2 * π) - 5/2)]

/-! ## §3 `sin(h) > 1/100`. -/

/-- **`sin_h_gt_one_hundredth`** — `sin(π · √(2π) − 5π/2) > 1/100`.

Via r248's Level-4 `sin_ge_x_sub_cube_div_six`: `sin(h) ≥ h − h³/6`.
With `h > 1/50` (§2), `h − h³/6 > 1/50 − (1/50)³/6 > 1/100`. -/
lemma sin_h_gt_one_hundredth :
    (1 : ℝ) / 100 < Real.sin (π * Real.sqrt (2 * π) - 5 * π / 2) := by
  set h := π * Real.sqrt (2 * π) - 5 * π / 2 with hh_def
  have hh_gt : (1 : ℝ) / 50 < h := h_gt_one_fiftieth
  have hh_pos : (0 : ℝ) < h := by linarith
  have hh_pos_le : (0 : ℝ) ≤ h := le_of_lt hh_pos
  have htay : h - h^3 / 6 ≤ Real.sin h :=
    AlphaHodgeTighterHalfBracket.sin_ge_x_sub_cube_div_six hh_pos_le
  -- h > 1/50 → h³ small → h - h³/6 > 1/50 - (1/50)³/6 > 1/100. But we need explicit
  -- h upper bound to bound h³.
  have hh_lt_one : h < 1 := by
    -- h ≈ 0.021; use loose bounds.
    have hpi_lt : π < (3.141593 : ℝ) := Real.pi_lt_d6
    have hs_lt : Real.sqrt (2 * π) < 2.51 := by
      have h1 : (2.51 : ℝ)^2 > 2 * π := by nlinarith [hpi_lt]
      have hnn : (0 : ℝ) ≤ 2.51 := by norm_num
      have h2 : Real.sqrt (2 * π) < Real.sqrt ((2.51 : ℝ)^2) :=
        Real.sqrt_lt_sqrt (by positivity) h1
      rwa [Real.sqrt_sq hnn] at h2
    have hpi_pos : (0:ℝ) < π := Real.pi_pos
    nlinarith [hs_lt, hpi_lt, hpi_pos]
  -- We have h > 1/50 and h < 1, so h³ < h.
  -- Then h - h³/6 > h - h/6 = 5h/6 > 5·(1/50)/6 = 1/60 > 1/100.
  have hkey : h - h^3 / 6 > 1 / 100 := by
    have hh3_lt : h^3 < h := by
      have hsq_lt : h^2 < 1 := by nlinarith [hh_lt_one, hh_pos_le]
      have h_eq : h^3 = h * h^2 := by ring
      rw [h_eq]
      nlinarith [hh_pos, hsq_lt, mul_pos hh_pos hh_pos]
    nlinarith [hh_pos, hh3_lt, hh_gt]
  linarith

/-! ## §4 `cos(π · √(2π)) < -1/100`. -/

/-- Local `cos_add_two_pi` (matches r230's). -/
private lemma cos_add_two_pi_local (x : ℝ) : Real.cos (x + 2 * π) = Real.cos x := by
  have h : x + 2 * π = (x + π) + π := by ring
  rw [h, Real.cos_add_pi, Real.cos_add_pi]
  ring

/-- **`cos_pi_mul_alphaQG_lt_neg_one_hundredth`** — `cos(π · √(2π)) < -1/100`.

Chain: `π · √(2π) = 2π + (π · √(2π) − 2π) = 2π + (π/2 + h)` with
`h = π · √(2π) − 5π/2`. So `cos(π · √(2π)) = cos(2π + π/2 + h) = cos(π/2 + h)
= -sin(h) < -1/100` by §3. -/
lemma cos_pi_mul_alphaQG_lt_neg_one_hundredth :
    Real.cos (π * Real.sqrt (2 * π)) < -(1 : ℝ) / 100 := by
  set h : ℝ := π * Real.sqrt (2 * π) - 5 * π / 2 with hh_def
  have hsin := sin_h_gt_one_hundredth
  -- Rewrite: π · √(2π) = π/2 + h + 2π.
  have heq : π * Real.sqrt (2 * π) = (π / 2 + h) + 2 * π := by
    rw [hh_def]; ring
  rw [heq, cos_add_two_pi_local]
  -- cos(π/2 + h) = -sin(h).
  rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  linarith

/-! ## §5 Positivity: `1 + 2·cos(π · √(2π)) > 0`. -/

/-- **`one_add_two_cos_pi_mul_alphaQG_pos`** — `0 < 1 + 2·cos(π · √(2π))`.

Since `cos(π · √(2π)) > -1/2`. From r230's chain: `-1 < cos < 0`, but we
need the stronger `> -1/2`. Reprove directly: `h < π/2` (numerically
h ≈ 0.021 << π/2 ≈ 1.571), so cos(π/2 + h) = -sin(h) > -1 easily. In fact
`sin(h) < 1` (trivial from `sin_lt` for h > 0), so cos > -1 > -1/2 fails —
need tighter. Use: sin(h) < h (mathlib `Real.sin_lt`), and h < π/2, so
sin(h) < π/2 < 2, but need sin(h) < 1/2. Trivial: h < 1/2 will do
(numerically h ≈ 0.021 << 0.5). -/
lemma one_add_two_cos_pi_mul_alphaQG_pos :
    0 < 1 + 2 * Real.cos (π * Real.sqrt (2 * π)) := by
  set h : ℝ := π * Real.sqrt (2 * π) - 5 * π / 2 with hh_def
  -- h ≈ 0.021 < 1/2, so sin(h) < h < 1/2 (from Real.sin_lt), so cos(...) = -sin(h) > -1/2.
  have hh_gt : (1 : ℝ) / 50 < h := h_gt_one_fiftieth
  have hh_pos : (0 : ℝ) < h := by linarith
  -- Upper bound on h: h < 1/2. Uses √(2π) < 2.51 and π < 3.141593.
  have hh_lt_half : h < 1 / 2 := by
    have hpi_lt : π < (3.141593 : ℝ) := Real.pi_lt_d6
    have hs_lt : Real.sqrt (2 * π) < 2.51 := by
      have h1 : (2.51 : ℝ)^2 > 2 * π := by nlinarith [hpi_lt]
      have hnn : (0 : ℝ) ≤ 2.51 := by norm_num
      have h2 : Real.sqrt (2 * π) < Real.sqrt ((2.51 : ℝ)^2) :=
        Real.sqrt_lt_sqrt (by positivity) h1
      rwa [Real.sqrt_sq hnn] at h2
    have hpi_pos : (0:ℝ) < π := Real.pi_pos
    nlinarith [hs_lt, hpi_lt, hpi_pos]
  -- sin(h) < h (Real.sin_lt for h > 0).
  have hsin_lt : Real.sin h < h := Real.sin_lt hh_pos
  have hsin_lt_half : Real.sin h < 1 / 2 := lt_trans hsin_lt hh_lt_half
  -- cos(π · √(2π)) = -sin(h).
  have heq : π * Real.sqrt (2 * π) = (π / 2 + h) + 2 * π := by
    rw [hh_def]; ring
  have hcos_eq : Real.cos (π * Real.sqrt (2 * π)) = -Real.sin h := by
    rw [heq, cos_add_two_pi_local, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [hcos_eq]
  linarith

/-! ## §6 The sharp bracket. -/

/-- **`sigma_alphaQG_lt_logb_three_49_over_50`** — the sharp α_QG upper bracket.

`σ(α_QG = √(2π)) < log₃(49/50) = -log₃(50/49) ≈ -0.018`. Completes the
6/6 sharp-bracket coverage of the irrational corpus pillars. -/
theorem sigma_alphaQG_lt_logb_three_49_over_50 :
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) < Real.logb 3 (49 / 50) := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos_lt := cos_pi_mul_alphaQG_lt_neg_one_hundredth
  have hval_pos := one_add_two_cos_pi_mul_alphaQG_pos
  have hval_lt : 1 + 2 * Real.cos (π * Real.sqrt (2 * π)) < 49 / 50 := by linarith
  rw [abs_of_pos hval_pos]
  exact Real.logb_lt_logb (by norm_num : (1:ℝ) < 3) hval_pos hval_lt

/-! ## §7 r223 elevation. -/

/-- **`SO_αQG_sigma_lt_logb_three_49_over_50`** — universal over data-fit. -/
theorem SO_αQG_sigma_lt_logb_three_49_over_50 (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αQG A φ₀ hA).sigma < Real.logb 3 (49 / 50) := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) < Real.logb 3 (49 / 50)
  exact sigma_alphaQG_lt_logb_three_49_over_50

/-! ## §8 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaQGSharpBracket.sqrt_two_pi_gt_25065_over_10000
#print axioms PrincipiaTractalis.AlphaQGSharpBracket.h_gt_one_fiftieth
#print axioms PrincipiaTractalis.AlphaQGSharpBracket.sin_h_gt_one_hundredth
#print axioms PrincipiaTractalis.AlphaQGSharpBracket.cos_pi_mul_alphaQG_lt_neg_one_hundredth
#print axioms PrincipiaTractalis.AlphaQGSharpBracket.sigma_alphaQG_lt_logb_three_49_over_50

end PrincipiaTractalis.AlphaQGSharpBracket
