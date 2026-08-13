/-
# r246: SHARP α_NS UPPER BRACKET — σ(α_NS) < -log 2 / log 3 = -Cantor Hausdorff dim.

★ 2026-08-13 r246 — the FOURTH sharp bracket landing. `σ(α_NS = 3π/2) <
-log 2 / log 3 = -log₃ 2 = -σ(1/3) = -Cantor Hausdorff dim`. Together with
r244 (`σ_P < -log 2 / log 3`), TWO of the three σ < 0 corpus pillars are
now proved strictly below -Cantor dim. Same pi-bounds pattern as r245. ★

## The bracket

**Upper end**: `σ(α_NS = 3π/2) < -log 2 / log 3 = -log₃ 2`.

Because:
1. `α_NS = 3π/2`, so `π · α_NS = 3π²/2`.
2. Set `z := π · α_NS − 4π = π(3π − 8)/2`. Then `3π²/2 = 4π + z`.
3. `z > 2π/3`: needs `π(3π − 8)/2 > 2π/3`, i.e., `9π > 28`.
   Since `π > 3.14`, `9π > 28.26 > 28` ✓.
4. `z < 3π/4`: needs `π(3π − 8)/2 < 3π/4`, i.e., `6π < 19`.
   Since `π < 3.15`, `6π < 18.9 < 19` ✓.
5. Hence `z ∈ (2π/3, 3π/4) ⊂ [0, π]`, and `Real.strictAntiOn_cos` gives
   `cos(z) ∈ (cos(3π/4), cos(2π/3)) = (-√2/2, -1/2)`.
6. `cos(π · α_NS) = cos(4π + z) = cos(z)` via `cos_add_two_pi` twice.
7. `1 + 2·cos(π · α_NS) ∈ (1 − √2, 0)`.
8. `|1 + 2·cos(π · α_NS)| ∈ (0, √2 − 1)`.
9. `√2 − 1 < 1/2` (from `√2 < 3/2`, r225's `sqrt_two_lt_three_halves`).
10. So `|·| < 1/2`, hence `σ(α_NS) = log₃|·| < log₃(1/2) = -log₃ 2`.

## The completed Cantor-value straddle

Together with r243/r244/r245:

- σ(α_Hodge = φ)   < log 2 / log 3    (r243)
- σ(α_BSD = 3π/4)  < log 2 / log 3    (r245)
- σ(α_P = √2)      < -log 2 / log 3   (r244)
- σ(α_NS = 3π/2)   < -log 2 / log 3   (r246)

Four of the six irrational corpus pillars are now bracketed against the
Cantor value. Remaining: α_NP (positive side; ≈ 0.947 > Cantor) and α_QG
(near-critical; ≈ -0.039 not bounded by -Cantor).

## Contents

§1 `nine_pi_gt_twenty_eight` — `9π > 28` (mirrors r245).
§2 `six_pi_lt_nineteen` — `6π < 19`.
§3 `pi_mul_alphaNS_sub_four_pi_gt_two_pi_div_three` — `3π²/2 − 4π > 2π/3`.
§4 `pi_mul_alphaNS_sub_four_pi_lt_three_pi_div_four` — `3π²/2 − 4π < 3π/4`.
§5 `cos_pi_mul_alphaNS_lt_neg_half` — `cos(π · 3π/2) < -1/2`.
§6 `cos_pi_mul_alphaNS_gt_neg_sqrt_two_div_two` — `cos(π · 3π/2) > -√2/2`.
§7 `abs_one_add_two_cos_pi_mul_alphaNS_lt_half` — `|·| < 1/2` via §5, §6, `√2 < 3/2`.
§8 `sigma_alphaNS_lt_neg_logb_three_two` — the sharp bracket.
§9 `sigma_alphaNS_lt_neg_cantor_hausdorff_dim` — the Cantor-tie form.
§10 `SO_αNS_sigma_lt_neg_logb_three_two` — r223 elevation.
§11 Axiom check.

## Scope

* NOT novel — pure algebra + `Real.strictAntiOn_cos` + mathlib pi bounds.
* NOT the tightest possible (σ_NS ≈ -1.308 vs the -0.631 bracket).
* NOT a Millennium discharge.
* IS the fourth sharp substrate bracket, completing the negative-side
  Cantor-value bounding pattern started by r244.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaNSSigmaNegative_r229
import PF.AlphaBSDUpperBracketCantor_r245

open scoped Real

namespace PrincipiaTractalis.AlphaNSUpperBracketNegCantor

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.AlphaPSigmaNegative
open PrincipiaTractalis

/-! ## §1–§2 The pi-bound derivations. -/

/-- **`nine_pi_gt_twenty_eight_r246`** — `9π > 28` via `Real.pi_gt_d2`. -/
lemma nine_pi_gt_twenty_eight_r246 : (28 : ℝ) < 9 * π := by
  have := Real.pi_gt_d2
  linarith

/-- **`six_pi_lt_nineteen`** — `6π < 19` via `Real.pi_lt_d2`. -/
lemma six_pi_lt_nineteen : 6 * π < 19 := by
  have := Real.pi_lt_d2
  linarith

/-! ## §3 `3π²/2 − 4π > 2π/3`. -/

/-- **`pi_mul_alphaNS_sub_four_pi_gt_two_pi_div_three`** — via §1. -/
lemma pi_mul_alphaNS_sub_four_pi_gt_two_pi_div_three :
    2 * π / 3 < π * (3 * π / 2) - 4 * π := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h9 := nine_pi_gt_twenty_eight_r246
  nlinarith [h9, hpi]

/-! ## §4 `3π²/2 − 4π < 3π/4`. -/

/-- **`pi_mul_alphaNS_sub_four_pi_lt_three_pi_div_four`** — via §2. -/
lemma pi_mul_alphaNS_sub_four_pi_lt_three_pi_div_four :
    π * (3 * π / 2) - 4 * π < 3 * π / 4 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h6 := six_pi_lt_nineteen
  nlinarith [h6, hpi]

/-! ## §5 & §6 `cos(π · α_NS)` bracket via strictAntiOn_cos. -/

/-- **`cos_add_four_pi_local`** — `cos(x + 4π) = cos(x)` locally. -/
private lemma cos_add_four_pi_local (x : ℝ) : Real.cos (x + 4 * π) = Real.cos x := by
  have h : x + 4 * π = (x + 2 * π) + 2 * π := by ring
  rw [h, Real.cos_add_two_pi, Real.cos_add_two_pi]

/-- **`cos_pi_mul_alphaNS_lt_neg_half`** — `cos(π · 3π/2) < -1/2`.

Set `z := π · (3π/2) − 4π`. §3 gives `z > 2π/3`; §4 gives `z < 3π/4 < π`.
Both endpoints in `[0, π]`, `Real.strictAntiOn_cos` gives
`cos(z) < cos(2π/3) = -1/2`. `cos(π · 3π/2) = cos(4π + z) = cos(z)`. -/
lemma cos_pi_mul_alphaNS_lt_neg_half :
    Real.cos (π * (3 * π / 2)) < -(1 : ℝ) / 2 := by
  set z := π * (3 * π / 2) - 4 * π with hz_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hz_gt : 2 * π / 3 < z := pi_mul_alphaNS_sub_four_pi_gt_two_pi_div_three
  have hz_lt : z < 3 * π / 4 :=
    pi_mul_alphaNS_sub_four_pi_lt_three_pi_div_four
  have h2pi3_mem : 2 * π / 3 ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩; linarith
  have hz_mem : z ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨?_, ?_⟩ <;> [linarith; linarith]
  have hcos_lt : Real.cos z < Real.cos (2 * π / 3) :=
    Real.strictAntiOn_cos h2pi3_mem hz_mem hz_gt
  have hcos_two_pi_three : Real.cos (2 * π / 3) = -(1 / 2) := by
    have h : (2 : ℝ) * π / 3 = π - π / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [hcos_two_pi_three] at hcos_lt
  have heq : π * (3 * π / 2) = z + 4 * π := by rw [hz_def]; ring
  rw [heq, cos_add_four_pi_local]
  linarith

/-- **`cos_pi_mul_alphaNS_gt_neg_sqrt_two_div_two`** — `cos(π · 3π/2) > -√2/2`.

Symmetric to §5: `z < 3π/4` gives `cos(z) > cos(3π/4) = -√2/2`. -/
lemma cos_pi_mul_alphaNS_gt_neg_sqrt_two_div_two :
    -(Real.sqrt 2 / 2) < Real.cos (π * (3 * π / 2)) := by
  set z := π * (3 * π / 2) - 4 * π with hz_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hz_gt : 2 * π / 3 < z := pi_mul_alphaNS_sub_four_pi_gt_two_pi_div_three
  have hz_lt : z < 3 * π / 4 :=
    pi_mul_alphaNS_sub_four_pi_lt_three_pi_div_four
  have h3pi4_mem : 3 * π / 4 ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩; linarith
  have hz_mem : z ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨?_, ?_⟩ <;> [linarith; linarith]
  have hcos_gt : Real.cos (3 * π / 4) < Real.cos z :=
    Real.strictAntiOn_cos hz_mem h3pi4_mem hz_lt
  have hcos_three_pi_four : Real.cos (3 * π / 4) = -(Real.sqrt 2 / 2) := by
    have h : (3 : ℝ) * π / 4 = π - π / 4 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_four]
  rw [hcos_three_pi_four] at hcos_gt
  have heq : π * (3 * π / 2) = z + 4 * π := by rw [hz_def]; ring
  rw [heq, cos_add_four_pi_local]
  linarith

/-! ## §7 `|1 + 2·cos(π · 3π/2)| < 1/2`. -/

/-- **`abs_one_add_two_cos_pi_mul_alphaNS_lt_half`** — `|1 + 2·cos(π · 3π/2)| < 1/2`.

From §5: `1 + 2·cos < 0`. From §6: `1 + 2·cos > 1 − √2`. So `|·| < √2 − 1`.
Since `√2 < 3/2` (r225's `sqrt_two_lt_three_halves`), `√2 − 1 < 1/2`,
giving `|·| < 1/2`. -/
lemma abs_one_add_two_cos_pi_mul_alphaNS_lt_half :
    |1 + 2 * Real.cos (π * (3 * π / 2))| < 1 / 2 := by
  have hupper := cos_pi_mul_alphaNS_lt_neg_half
  have hlower := cos_pi_mul_alphaNS_gt_neg_sqrt_two_div_two
  have hs2 := AlphaPSigmaNegative.sqrt_two_lt_three_halves
  have hs2_pos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hval_neg : 1 + 2 * Real.cos (π * (3 * π / 2)) < 0 := by linarith
  have hval_gt : 1 - Real.sqrt 2 < 1 + 2 * Real.cos (π * (3 * π / 2)) := by
    have : 2 * (-(Real.sqrt 2 / 2)) = -Real.sqrt 2 := by ring
    linarith
  rw [abs_of_neg hval_neg]
  linarith

/-! ## §8 The sharp bracket. -/

/-- **`sigma_alphaNS_lt_neg_logb_three_two`** — the sharp α_NS upper bracket.

`σ(α_NS = 3π/2) < -log₃ 2 = -log 2 / log 3`. -/
theorem sigma_alphaNS_lt_neg_logb_three_two :
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) < -Real.logb 3 2 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have habs_lt := abs_one_add_two_cos_pi_mul_alphaNS_lt_half
  have habs_pos : 0 < |1 + 2 * Real.cos (π * (3 * π / 2))| :=
    AlphaNSSigmaNegative.abs_one_add_two_cos_pi_mul_alphaNS_pos
  have hstep : Real.logb 3 |1 + 2 * Real.cos (π * (3 * π / 2))| <
      Real.logb 3 (1 / 2) :=
    Real.logb_lt_logb (by norm_num : (1:ℝ) < 3) habs_pos habs_lt
  have h_half : Real.logb 3 (1 / 2 : ℝ) = -Real.logb 3 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv]
  linarith [h_half ▸ hstep]

/-! ## §9 The Cantor-tie form. -/

/-- **`sigma_alphaNS_lt_neg_cantor_hausdorff_dim`** — the Cantor-tie form. -/
theorem sigma_alphaNS_lt_neg_cantor_hausdorff_dim :
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) < -(Real.log 2 / Real.log 3) := by
  have h := sigma_alphaNS_lt_neg_logb_three_two
  unfold Real.logb at h
  linarith

/-! ## §10 r223 elevation. -/

/-- **`SO_αNS_sigma_lt_neg_logb_three_two`** — universal over data-fit. -/
theorem SO_αNS_sigma_lt_neg_logb_three_two (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αNS A φ₀ hA).sigma < -Real.logb 3 2 := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 2) < -Real.logb 3 2
  exact sigma_alphaNS_lt_neg_logb_three_two

/-! ## §11 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaNSUpperBracketNegCantor.nine_pi_gt_twenty_eight_r246
#print axioms PrincipiaTractalis.AlphaNSUpperBracketNegCantor.six_pi_lt_nineteen
#print axioms PrincipiaTractalis.AlphaNSUpperBracketNegCantor.cos_pi_mul_alphaNS_lt_neg_half
#print axioms PrincipiaTractalis.AlphaNSUpperBracketNegCantor.cos_pi_mul_alphaNS_gt_neg_sqrt_two_div_two
#print axioms PrincipiaTractalis.AlphaNSUpperBracketNegCantor.abs_one_add_two_cos_pi_mul_alphaNS_lt_half
#print axioms PrincipiaTractalis.AlphaNSUpperBracketNegCantor.sigma_alphaNS_lt_neg_logb_three_two
#print axioms PrincipiaTractalis.AlphaNSUpperBracketNegCantor.sigma_alphaNS_lt_neg_cantor_hausdorff_dim

end PrincipiaTractalis.AlphaNSUpperBracketNegCantor
