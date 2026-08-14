/-
# r254: σ_QG TWO-SIDED SHARP BRACKET.

★ 2026-08-13 r254 — companion lower bound to r250's upper. Gives the
two-sided σ_QG bracket `log₃(19/20) < σ(α_QG) < log₃(49/50)`. Numerical
σ_QG ≈ −0.0387 sits between −0.0466 and −0.0184. Uses `Real.sin_le`
(the 1st-order Taylor upper on sin) instead of r248's Level 4 (which was
a lower bound). ★

## The lower bracket

**Lower end**: `log₃(19/20) < σ(α_QG = √(2π))`.

Because:
1. `√(2π) < 2.5073` via `(2.5073)² > 2π` from `Real.pi_lt_d6` (π < 3.141593).
2. `h := π · √(2π) − 5π/2 < 1/40` via step 1 and `π < 3.141593`.
3. `sin(h) < h < 1/40` via `Real.sin_lt` (for h > 0).
4. `cos(π · √(2π)) = cos(π/2 + h + 2π) = -sin(h) > -1/40`.
5. `1 + 2·cos(π · √(2π)) > 1 − 2/40 = 19/20`.
6. `σ_QG = log₃|1 + 2·cos| > log₃(19/20)` since `|·| > 0` (r250 positivity).

## Contents

§1 High-precision `√(2π)` upper bound: `√(2π) < 25073/10000`.
§2 `h < 1/40`.
§3 `sin(h) < 1/40` via `Real.sin_lt`.
§4 `cos(π · √(2π)) > -1/40`.
§5 `sigma_alphaQG_gt_logb_three_19_over_20` — the lower bracket.
§6 `sigma_alphaQG_two_sided_bracket` — two-sided capstone combining
    r250 upper + §5 lower.
§7 Axiom check.

## Scope

* NOT novel — pure algebra + `Real.sin_lt` + high-precision `Real.pi_lt_d6`.
* NOT the tightest possible (σ_QG ≈ -0.0387 vs the (-0.0466, -0.0184)
  bracket).
* NOT a Millennium discharge.
* IS the two-sided sharp bracket for σ_QG, complementing r250's one-sided.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaQGSharpBracket_r250

open scoped Real

namespace PrincipiaTractalis.AlphaQGTwoSidedBracket

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 High-precision `√(2π)` upper bound. -/

/-- **`sqrt_two_pi_lt_25073_over_10000`** — `√(2π) < 2.5073`.

`2.5073² = 6.286557 > 6.283186 > 2π` (using `π < 3.141593`). -/
lemma sqrt_two_pi_lt_25073_over_10000 :
    Real.sqrt (2 * π) < 25073 / 10000 := by
  have hpi : π < (3.141593 : ℝ) := Real.pi_lt_d6
  have h2pi_lt : 2 * π < (2.5073 : ℝ)^2 := by nlinarith [hpi]
  have hnn : (0 : ℝ) ≤ 2.5073 := by norm_num
  have hlt : Real.sqrt (2 * π) < Real.sqrt ((2.5073 : ℝ)^2) :=
    Real.sqrt_lt_sqrt (by positivity) h2pi_lt
  rw [Real.sqrt_sq hnn] at hlt
  have h_eq : (2.5073 : ℝ) = 25073 / 10000 := by norm_num
  rw [h_eq] at hlt
  exact hlt

/-! ## §2 `h := π · √(2π) − 5π/2 < 1/40`. -/

/-- **`h_lt_one_fortieth`** — `π · √(2π) − 5π/2 < 1/40`. -/
lemma h_lt_one_fortieth :
    π * Real.sqrt (2 * π) - 5 * π / 2 < (1 : ℝ) / 40 := by
  have hpi : π < (3.141593 : ℝ) := Real.pi_lt_d6
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hs := sqrt_two_pi_lt_25073_over_10000
  -- π · √(2π) - 5π/2 = π · (√(2π) - 5/2) < 3.141593 · 0.0073 < 0.02293 < 1/40.
  -- Need √(2π) - 5/2 > 0 for the multiplication direction; but we're proving upper
  -- bound so we don't need it strictly.
  -- Product bound: π · (√(2π) - 5/2) < π_upper · (sqrt_upper - 5/2).
  -- But sqrt_upper - 5/2 might be negative if we picked a bad upper. Here it's positive.
  have h_diff_pos : (0 : ℝ) < 25073 / 10000 - 5 / 2 := by norm_num
  nlinarith [hpi, hs, hpi_pos, h_diff_pos]

/-! ## §3 `sin(h) < 1/40`. -/

/-- **`sin_h_lt_one_fortieth`** — `sin(π · √(2π) − 5π/2) < 1/40`.

Via `Real.sin_lt` for `h > 0` (from r250 chain). -/
lemma sin_h_lt_one_fortieth :
    Real.sin (π * Real.sqrt (2 * π) - 5 * π / 2) < (1 : ℝ) / 40 := by
  set h : ℝ := π * Real.sqrt (2 * π) - 5 * π / 2 with hh_def
  have hh_gt : (1 : ℝ) / 50 < h := AlphaQGSharpBracket.h_gt_one_fiftieth
  have hh_pos : (0 : ℝ) < h := by linarith
  have hsin_lt_h : Real.sin h < h := Real.sin_lt hh_pos
  have hh_lt : h < (1 : ℝ) / 40 := h_lt_one_fortieth
  linarith

/-! ## §4 `cos(π · √(2π)) > -1/40`. -/

/-- Local `cos_add_two_pi` (matches r250's). -/
private lemma cos_add_two_pi_local (x : ℝ) : Real.cos (x + 2 * π) = Real.cos x := by
  have h : x + 2 * π = (x + π) + π := by ring
  rw [h, Real.cos_add_pi, Real.cos_add_pi]
  ring

/-- **`cos_pi_mul_alphaQG_gt_neg_one_fortieth`** — `cos(π · √(2π)) > -1/40`.

Via `cos(π · √(2π)) = cos(π/2 + h + 2π) = -sin(h) > -1/40` from §3. -/
lemma cos_pi_mul_alphaQG_gt_neg_one_fortieth :
    -(1 : ℝ) / 40 < Real.cos (π * Real.sqrt (2 * π)) := by
  set h : ℝ := π * Real.sqrt (2 * π) - 5 * π / 2 with hh_def
  have hsin := sin_h_lt_one_fortieth
  have heq : π * Real.sqrt (2 * π) = (π / 2 + h) + 2 * π := by
    rw [hh_def]; ring
  rw [heq, cos_add_two_pi_local]
  rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  linarith

/-! ## §5 The lower bracket. -/

/-- **`sigma_alphaQG_gt_logb_three_19_over_20`** — `σ(α_QG) > log₃(19/20)`.

Chain: `cos > -1/40` (§4) → `1 + 2·cos > 1 − 2/40 = 19/20`. Combined with
r250's positivity, `|·| = 1 + 2·cos ∈ (19/20, ...)`. Then `log₃` monotone
strictly gives `σ > log₃(19/20)`. -/
theorem sigma_alphaQG_gt_logb_three_19_over_20 :
    Real.logb 3 (19 / 20) < PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos_gt := cos_pi_mul_alphaQG_gt_neg_one_fortieth
  have hval_pos := AlphaQGSharpBracket.one_add_two_cos_pi_mul_alphaQG_pos
  have hval_gt : (19 : ℝ) / 20 < 1 + 2 * Real.cos (π * Real.sqrt (2 * π)) := by linarith
  rw [abs_of_pos hval_pos]
  have h_1920_pos : (0 : ℝ) < 19 / 20 := by norm_num
  exact Real.logb_lt_logb (by norm_num : (1:ℝ) < 3) h_1920_pos hval_gt

/-! ## §6 Two-sided bracket capstone. -/

/-- **`sigma_alphaQG_two_sided_bracket`** — the two-sided σ_QG bracket.

`log₃(19/20) < σ(α_QG = √(2π)) < log₃(49/50)`. Numerically the interval
is approximately `(-0.0466, -0.0184)`, containing `σ_QG ≈ -0.0387`. -/
theorem sigma_alphaQG_two_sided_bracket :
    Real.logb 3 (19 / 20) < PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) ∧
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) < Real.logb 3 (49 / 50) :=
  ⟨sigma_alphaQG_gt_logb_three_19_over_20,
   AlphaQGSharpBracket.sigma_alphaQG_lt_logb_three_49_over_50⟩

/-! ## §7 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaQGTwoSidedBracket.sqrt_two_pi_lt_25073_over_10000
#print axioms PrincipiaTractalis.AlphaQGTwoSidedBracket.h_lt_one_fortieth
#print axioms PrincipiaTractalis.AlphaQGTwoSidedBracket.sin_h_lt_one_fortieth
#print axioms PrincipiaTractalis.AlphaQGTwoSidedBracket.cos_pi_mul_alphaQG_gt_neg_one_fortieth
#print axioms PrincipiaTractalis.AlphaQGTwoSidedBracket.sigma_alphaQG_gt_logb_three_19_over_20
#print axioms PrincipiaTractalis.AlphaQGTwoSidedBracket.sigma_alphaQG_two_sided_bracket

end PrincipiaTractalis.AlphaQGTwoSidedBracket
