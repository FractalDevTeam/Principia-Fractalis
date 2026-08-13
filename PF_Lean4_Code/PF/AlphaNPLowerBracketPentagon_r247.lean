/-
# r247: SHARP α_NP LOWER BRACKET — σ(α_NP) > 2·log₃ φ = σ(1/5).

★ 2026-08-13 r247 — the FIFTH sharp bracket landing. `σ(α_NP = φ+1/4) >
2·log₃ φ = σ(1/5)`. Ties NP pillar strictly ABOVE r237's pentagon-golden
substrate value σ(1/5). Analogous algebraic route to r243/r245 but on the
LOWER side. ★

## The bracket

**Lower end**: `σ(α_NP = φ+1/4) > 2·log₃ φ = log₃(φ²)`.

Because:
1. `φ < 31/20` FAILS numerically (φ ≈ 1.618, 31/20 = 1.55). We need `φ > 31/20`.
   `φ > 31/20 ⟺ √5 > 21/10 ⟺ 5 > 441/100 = 4.41` ✓.
2. `φ < 7/4` (companion upper bound so `y > 0`):
   `φ < 7/4 ⟺ √5 < 5/2 ⟺ 5 < 25/4 = 6.25` ✓.
3. Set `y := 2π − π · (φ+1/4) = π(7/4 − φ)`.
4. `y > 0` from `φ < 7/4`.
5. `y < π/5` from `φ > 31/20`.
6. `y ∈ (0, π/5) ⊂ [0, π]`, `Real.strictAntiOn_cos` gives
   `cos(y) > cos(π/5) = (1+√5)/4 = φ/2`.
7. `cos(π · α_NP) = cos(-y + 2π) = cos(-y) = cos(y)` via `cos_add_two_pi`
   and `cos_neg`.
8. `1 + 2·cos(π · α_NP) > 1 + 2·(φ/2) = 1 + φ = φ²`
   (via `Real.goldenRatio_sq`).
9. Positivity: `φ² > 0`, so `1 + 2·cos > 0`, so `|·| = 1 + 2·cos > φ²`.
10. `σ(α_NP) = log₃|·| > log₃(φ²) = 2·log₃ φ`.

## Substrate significance

r237 established `σ(1/5) = 2·log₃ φ` — the pentagon-golden closed-form
substrate value at rational α = 1/5. r247 now ties the α_NP pillar STRICTLY
ABOVE that value:

    σ(1/5) = 2·log₃ φ  <  σ(α_NP = φ+1/4).

The α_NP pillar sits above the pentagon-golden value in the substrate σ
spectrum. Together with r243–r246, we now have five of the six irrational
corpus pillars sharp-bracketed against exact substrate values:

- σ(α_Hodge)  ∈ (0, log 2/log 3)         [r226, r243]
- σ(α_NP)     ∈ (2·log₃ φ, ??)           [r247, r241/r242]  ← NEW
- σ(α_BSD)    ∈ (0, log 2/log 3)         [r228, r245]
- σ(α_P)      ∈ (-log 2/log 3, ??)       ... wait: σ_P < -log 2/log 3 (r244)
  So σ(α_P)   ∈ (?, -log 2/log 3)         [r225, r244]
- σ(α_NS)     ∈ (?, -log 2/log 3)         [r229, r246]
- σ(α_QG)     — remaining, near-critical

## Contents

§1 `sqrt_five_gt_twenty_one_tenths` — `√5 > 21/10`.
§2 `sqrt_five_lt_five_halves` — `√5 < 5/2`.
§3 `goldenRatio_gt_thirty_one_twentieths` — `φ > 31/20`.
§4 `goldenRatio_lt_seven_fourths` — `φ < 7/4`.
§5 `two_pi_sub_pi_mul_alphaNP_pos` — `2π − π · α_NP > 0`.
§6 `two_pi_sub_pi_mul_alphaNP_lt_pi_div_five` — `2π − π · α_NP < π/5`.
§7 `cos_pi_mul_alphaNP_gt_half_goldenRatio` — the cos bound.
§8 `sigma_alphaNP_gt_two_logb_three_goldenRatio` — the sharp bracket.
§9 `sigma_alphaNP_gt_sigma_one_fifth` — the r237 tie form.
§10 `SO_αNP_sigma_gt_two_logb_three_goldenRatio` — r223 elevation.
§11 Axiom check.

## Scope

* NOT novel — pure algebra + `Real.strictAntiOn_cos` + `Real.cos_pi_div_five`
  + `Real.goldenRatio_sq`.
* NOT the tightest possible (σ_NP ≈ 0.947 vs the 0.877 bracket).
* NOT a Millennium discharge.
* IS the fifth sharp substrate bracket, tying NP above the r237 pentagon-
  golden value.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaNPSigmaPositive_r227
import PF.AlphaNSUpperBracketNegCantor_r246

open scoped Real

namespace PrincipiaTractalis.AlphaNPLowerBracketPentagon

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.AlphaHodgeSigmaPositive
open PrincipiaTractalis

/-! ## §1–§4 Algebraic tightenings on `√5` and `φ`. -/

/-- **`sqrt_five_gt_twenty_one_tenths`** — `√5 > 21/10`. -/
lemma sqrt_five_gt_twenty_one_tenths : (21 : ℝ) / 10 < Real.sqrt 5 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [Real.sqrt_nonneg 5, h]

/-- **`sqrt_five_lt_five_halves`** — `√5 < 5/2`. -/
lemma sqrt_five_lt_five_halves : Real.sqrt 5 < 5 / 2 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [Real.sqrt_nonneg 5, h]

/-- **`goldenRatio_gt_thirty_one_twentieths`** — `φ > 31/20`. -/
lemma goldenRatio_gt_thirty_one_twentieths :
    (31 : ℝ) / 20 < Real.goldenRatio := by
  unfold Real.goldenRatio
  have := sqrt_five_gt_twenty_one_tenths
  linarith

/-- **`goldenRatio_lt_seven_fourths`** — `φ < 7/4`. -/
lemma goldenRatio_lt_seven_fourths : Real.goldenRatio < 7 / 4 := by
  unfold Real.goldenRatio
  have := sqrt_five_lt_five_halves
  linarith

/-! ## §5–§6 The angle-y bounds. -/

/-- **`two_pi_sub_pi_mul_alphaNP_pos`** — `2π − π·(φ+1/4) > 0` via `φ < 7/4`. -/
lemma two_pi_sub_pi_mul_alphaNP_pos :
    0 < 2 * π - π * (Real.goldenRatio + 1 / 4) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := goldenRatio_lt_seven_fourths
  nlinarith

/-- **`two_pi_sub_pi_mul_alphaNP_lt_pi_div_five`** — `2π − π·(φ+1/4) < π/5`
via `φ > 31/20`. -/
lemma two_pi_sub_pi_mul_alphaNP_lt_pi_div_five :
    2 * π - π * (Real.goldenRatio + 1 / 4) < π / 5 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := goldenRatio_gt_thirty_one_twentieths
  nlinarith

/-! ## §7 `cos(π · α_NP) > φ/2`. -/

/-- **`cos_pi_mul_alphaNP_gt_half_goldenRatio`** — `cos(π·(φ+1/4)) > φ/2`.

Route: set `y := 2π − π·(φ+1/4) ∈ (0, π/5) ⊂ [0, π]`; `Real.strictAntiOn_cos`
gives `cos(y) > cos(π/5) = (1+√5)/4 = φ/2` via mathlib `cos_pi_div_five`.
Then `cos(π · α_NP) = cos(-y + 2π) = cos(-y) = cos(y)`. -/
lemma cos_pi_mul_alphaNP_gt_half_goldenRatio :
    Real.goldenRatio / 2 < Real.cos (π * (Real.goldenRatio + 1 / 4)) := by
  set y := 2 * π - π * (Real.goldenRatio + 1 / 4) with hy_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hy_pos : 0 < y := two_pi_sub_pi_mul_alphaNP_pos
  have hy_lt : y < π / 5 := two_pi_sub_pi_mul_alphaNP_lt_pi_div_five
  have hpi5_mem : π / 5 ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩; linarith
  have hy_mem : y ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨le_of_lt hy_pos, ?_⟩; linarith
  have hcos_gt : Real.cos (π / 5) < Real.cos y :=
    Real.strictAntiOn_cos hy_mem hpi5_mem hy_lt
  rw [Real.cos_pi_div_five] at hcos_gt
  -- (1 + √5)/4 = φ/2 by definition of φ = (1 + √5)/2.
  have hphi2 : (1 + Real.sqrt 5) / 4 = Real.goldenRatio / 2 := by
    unfold Real.goldenRatio; ring
  rw [hphi2] at hcos_gt
  have heq : π * (Real.goldenRatio + 1 / 4) = -y + 2 * π := by
    rw [hy_def]; ring
  rw [heq, cos_add_two_pi, Real.cos_neg]
  exact hcos_gt

/-! ## §8 The sharp bracket. -/

/-- **`sigma_alphaNP_gt_two_logb_three_goldenRatio`** — the sharp α_NP lower bracket.

`σ(α_NP = φ+1/4) > 2·log₃ φ`.

Chain:
- `cos(π · α_NP) > φ/2` from §7.
- `1 + 2·cos(π · α_NP) > 1 + φ = φ²` (via `Real.goldenRatio_sq`).
- `φ² > 0`, so `1 + 2·cos > 0`, so `|·| = 1 + 2·cos > φ²`.
- `σ = log₃|·| > log₃(φ²) = 2·log₃ φ` via `Real.logb_lt_logb` + `Real.logb_pow`. -/
theorem sigma_alphaNP_gt_two_logb_three_goldenRatio :
    2 * Real.logb 3 Real.goldenRatio <
      PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1 / 4) := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos_gt := cos_pi_mul_alphaNP_gt_half_goldenRatio
  have hphi_pos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hphi_sq_pos : (0 : ℝ) < Real.goldenRatio ^ 2 := by positivity
  have hval_gt : Real.goldenRatio ^ 2 < 1 + 2 * Real.cos (π * (Real.goldenRatio + 1 / 4)) := by
    have hphi_sq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
    linarith
  have hval_pos : 0 < 1 + 2 * Real.cos (π * (Real.goldenRatio + 1 / 4)) := by
    linarith
  rw [abs_of_pos hval_pos]
  have hstep : Real.logb 3 (Real.goldenRatio ^ 2) <
      Real.logb 3 (1 + 2 * Real.cos (π * (Real.goldenRatio + 1 / 4))) :=
    Real.logb_lt_logb (by norm_num : (1:ℝ) < 3) hphi_sq_pos hval_gt
  have hlog_pow : Real.logb 3 (Real.goldenRatio ^ 2) = 2 * Real.logb 3 Real.goldenRatio := by
    rw [Real.logb_pow]; ring
  linarith [hlog_pow ▸ hstep]

/-! ## §9 The r237 pentagon-golden tie form. -/

/-- **`sigma_alphaNP_gt_sigma_one_fifth`** — the r237 substrate-value tie.

`σ(α_NP = φ+1/4) > σ(1/5) = 2·log₃ φ`. The α_NP pillar sits strictly above
the r237 pentagon-golden substrate value in the σ spectrum. -/
theorem sigma_alphaNP_gt_sigma_one_fifth :
    PrincipiaTractalis.SigmaAbscissa.sigma (1/5 : ℝ) <
      PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1 / 4) := by
  have h_sig_one_fifth :
      PrincipiaTractalis.SigmaAbscissa.sigma (1/5 : ℝ) = 2 * Real.logb 3 Real.goldenRatio :=
    PrincipiaTractalis.ValidationSigmaPentagonGolden.sigma_one_fifth_eq_two_logb_three_goldenRatio
  rw [h_sig_one_fifth]
  exact sigma_alphaNP_gt_two_logb_three_goldenRatio

/-! ## §10 r223 elevation. -/

/-- **`SO_αNP_sigma_gt_two_logb_three_goldenRatio`** — universal over data-fit. -/
theorem SO_αNP_sigma_gt_two_logb_three_goldenRatio (A φ₀ : ℝ) (hA : A ≠ 0) :
    2 * Real.logb 3 Real.goldenRatio < (SO_αNP A φ₀ hA).sigma := by
  show 2 * Real.logb 3 Real.goldenRatio <
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1 / 4)
  exact sigma_alphaNP_gt_two_logb_three_goldenRatio

/-! ## §11 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaNPLowerBracketPentagon.sqrt_five_gt_twenty_one_tenths
#print axioms PrincipiaTractalis.AlphaNPLowerBracketPentagon.goldenRatio_gt_thirty_one_twentieths
#print axioms PrincipiaTractalis.AlphaNPLowerBracketPentagon.cos_pi_mul_alphaNP_gt_half_goldenRatio
#print axioms PrincipiaTractalis.AlphaNPLowerBracketPentagon.sigma_alphaNP_gt_two_logb_three_goldenRatio
#print axioms PrincipiaTractalis.AlphaNPLowerBracketPentagon.sigma_alphaNP_gt_sigma_one_fifth

end PrincipiaTractalis.AlphaNPLowerBracketPentagon
