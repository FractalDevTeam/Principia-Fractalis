/-
# r244: SHARP α_P UPPER BRACKET — σ(α_P) < -log 2 / log 3 = -Cantor Hausdorff dim.

★ 2026-08-13 r244 — the SECOND sharp bracket landing, companion to r243.
`σ(α_P = √2) < -log 2 / log 3 = -log₃ 2 = -σ(1/3) = -Cantor Hausdorff dim`.
Together with r243 (`σ_Hodge < +log₃ 2`), the Cantor dim value bounds BOTH
the Hodge pillar from above (positive side) and the P pillar from below
(negative side). ★

## The bracket

**Upper end**: `σ(α_P = √2) < -log 2 / log 3 = -log₃ 2`.

Because:
1. `√2 < 17/12` — algebraic, via `(17/12)² = 289/144 > 288/144 = 2`.
2. `π · √2 − π < 5π/12`, hence `y := π(√2 − 1) ∈ (0, 5π/12)`.
3. `cos(5π/12) = (√6 − √2)/4` — derived via `cos_add` on `π/4 + π/6`
   with mathlib's `cos_pi_div_four`, `cos_pi_div_six`, `sin_pi_div_four`,
   `sin_pi_div_six`.
4. `cos(y) > (√6 − √2)/4` via `Real.strictAntiOn_cos` on `[0, π]` and
   `y < 5π/12`.
5. `cos(π · √2) = -cos(y)` (via `cos_add_pi` since `π · √2 = y + π`).
6. `cos(π · √2) < -(√6 − √2)/4`.
7. `1 + 2 · cos(π · √2) < 1 − (√6 − √2)/2 = (2 − √6 + √2)/2 < 1/2`.
   The `< 1/2` step uses `√6 > 1 + √2` (algebra via `1 + 2√2 + 2 < 6`).
8. Positivity of `1 + 2 · cos(π · √2)`: `√2 > 4/3` gives `y > π/3`,
   giving `cos(y) < cos(π/3) = 1/2`, giving `cos(π · √2) > -1/2`, giving
   `1 + 2 · cos(π · √2) > 0`.
9. So `|1 + 2 · cos(π · √2)| = 1 + 2 · cos(π · √2) < 1/2`.
10. `σ(α_P) = log₃|·| < log₃(1/2) = -log₃ 2`.

## The r243 companion

r243 landed `σ(α_Hodge = φ) < +log₃ 2` via the same style algebra
(`√5 < 7/3`, cos strictAntiOn, `cos(π/3) = 1/2`).

r244 lands `σ(α_P = √2) < -log₃ 2` via the same style algebra
(`√2 < 17/12`, cos strictAntiOn, `cos(5π/12) = (√6 − √2)/4`).

Together:

    -log₃ 2 < σ(α_P) < 0 < σ(α_Hodge) < log₃ 2

with the middle inequalities from r225 and r226, and the outer strict
inequalities being the new r243/r244 contributions. **The Cantor Hausdorff
value log 2 / log 3 STRADDLES the σ = 0 origin, bounding the Hodge pillar
from above and the P pillar from below.** Framework-first substrate result.

## Contents

§1 `sqrt_two_lt_seventeen_twelfths` — the tightening `√2 < 17/12`.
§2 `sqrt_two_gt_four_thirds` — the lower tightening `√2 > 4/3`.
§3 `cos_five_pi_div_twelve` — `cos(5π/12) = (√6 − √2)/4`.
§4 `sqrt_six_gt_one_add_sqrt_two` — `√6 > 1 + √2` for the threshold step.
§5 `cos_pi_mul_sqrt_two_lt_neg_sqrt_six_sub_sqrt_two_div_four` — the
   key upper bound on `cos(π · √2)`.
§6 `cos_pi_mul_sqrt_two_gt_neg_half` — the positivity lower bound.
§7 `sigma_alphaP_lt_neg_logb_three_two` — the σ_P bracket.
§8 `sigma_alphaP_lt_neg_cantor_hausdorff_dim` — the Cantor-tie form.
§9 `SO_αP_sigma_lt_neg_logb_three_two` — r223 elevation.
§10 Axiom check.

## Scope

* NOT novel — pure algebra + `Real.strictAntiOn_cos`.
* NOT the tightest possible (σ_P ≈ -0.692 vs the -0.631 bracket).
* NOT a Millennium discharge.
* IS the companion sharp substrate bracket to r243, giving the Cantor
  Hausdorff value a two-sided bounding role in the σ spectrum.

Second sharp bracket landing.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaPSigmaNegative_r225
import PF.AlphaHodgeUpperBracketCantor_r243

open scoped Real

namespace PrincipiaTractalis.AlphaPUpperBracketNegCantor

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.AlphaPSigmaNegative
open PrincipiaTractalis

/-! ## §1 `√2 < 17/12` — the algebraic tightening. -/

/-- **`sqrt_two_lt_seventeen_twelfths`** — `√2 < 17/12`.

Via nlinarith on `(17/12)² = 289/144 > 288/144 = 2`. Tighter than r225's
`sqrt_two_lt_three_halves`. -/
lemma sqrt_two_lt_seventeen_twelfths : Real.sqrt 2 < 17 / 12 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg 2, h]

/-! ## §2 `√2 > 4/3` — the algebraic lower tightening. -/

/-- **`sqrt_two_gt_four_thirds`** — `4/3 < √2`.

Via nlinarith on `(4/3)² = 16/9 < 18/9 = 2`. Tighter than `1 < √2`. -/
lemma sqrt_two_gt_four_thirds : (4 : ℝ) / 3 < Real.sqrt 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg 2, h]

/-! ## §3 `cos(5π/12) = (√6 − √2)/4`. -/

/-- **`cos_five_pi_div_twelve`** — `cos(5π/12) = (√6 − √2)/4`.

Via `cos_add π/4 π/6` with mathlib's exact values for `cos(π/4)`, `cos(π/6)`,
`sin(π/4)`, `sin(π/6)`.

`5π/12 = π/4 + π/6`; `cos(a+b) = cos(a)cos(b) − sin(a)sin(b)`;
`(√2/2)(√3/2) − (√2/2)(1/2) = (√6 − √2)/4`. -/
lemma cos_five_pi_div_twelve :
    Real.cos (5 * π / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
  have hsum : (5 : ℝ) * π / 12 = π / 4 + π / 6 := by ring
  rw [hsum, Real.cos_add, Real.cos_pi_div_four, Real.cos_pi_div_six,
      Real.sin_pi_div_four, Real.sin_pi_div_six]
  have hsix : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsix]
  ring

/-! ## §4 `√6 > 1 + √2`. -/

/-- **`sqrt_six_gt_one_add_sqrt_two`** — `√6 > 1 + √2`.

Both sides positive; squaring gives `6 > (1+√2)² = 3 + 2√2`, i.e., `3 > 2√2`,
i.e., `9 > 8`. -/
lemma sqrt_six_gt_one_add_sqrt_two :
    (1 : ℝ) + Real.sqrt 2 < Real.sqrt 6 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs6 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  -- Both sides nonneg; compare via squaring.
  have hkey : (1 + Real.sqrt 2) ^ 2 < Real.sqrt 6 ^ 2 := by
    have hexpand : (1 + Real.sqrt 2) ^ 2 = 1 + 2 * Real.sqrt 2 + Real.sqrt 2 ^ 2 := by
      ring
    rw [hexpand, h2, h6]
    -- Need 1 + 2√2 + 2 < 6, i.e., 2√2 < 3, i.e., √2 < 3/2.
    have hs2_lt : Real.sqrt 2 < 3 / 2 := by nlinarith [h2, hs2]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hs6 hkey

/-! ## §5 The key upper bound on `cos(π · √2)`. -/

/-- **`pi_mul_sqrt_two_sub_pi_lt_five_pi_div_twelve`** — `π(√2 − 1) < 5π/12`. -/
lemma pi_mul_sqrt_two_sub_pi_lt_five_pi_div_twelve :
    π * (Real.sqrt 2 - 1) < 5 * π / 12 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := sqrt_two_lt_seventeen_twelfths
  nlinarith

/-- **`pi_mul_sqrt_two_sub_pi_gt_pi_div_three`** — `π(√2 − 1) > π/3`. -/
lemma pi_mul_sqrt_two_sub_pi_gt_pi_div_three :
    π / 3 < π * (Real.sqrt 2 - 1) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := sqrt_two_gt_four_thirds
  nlinarith

/-- **`cos_pi_mul_sqrt_two_lt_neg_bound`** — `cos(π · √2) < -(√6 − √2)/4`.

Set `y := π(√2 − 1) ∈ (π/3, 5π/12) ⊂ [0, π]`. `Real.strictAntiOn_cos` on
`[0, π]` gives `cos(y) > cos(5π/12) = (√6 − √2)/4`. Then
`cos(π · √2) = cos(y + π) = -cos(y) < -(√6 − √2)/4`. -/
lemma cos_pi_mul_sqrt_two_lt_neg_bound :
    Real.cos (π * Real.sqrt 2) < -((Real.sqrt 6 - Real.sqrt 2) / 4) := by
  set y := π * (Real.sqrt 2 - 1) with hy_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hy_gt : π / 3 < y := pi_mul_sqrt_two_sub_pi_gt_pi_div_three
  have hy_lt : y < 5 * π / 12 := pi_mul_sqrt_two_sub_pi_lt_five_pi_div_twelve
  have h5pi12_mem : 5 * π / 12 ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩; linarith
  have hy_mem : y ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨?_, ?_⟩ <;> [linarith; linarith]
  have hcos_gt : Real.cos (5 * π / 12) < Real.cos y :=
    Real.strictAntiOn_cos hy_mem h5pi12_mem hy_lt
  rw [cos_five_pi_div_twelve] at hcos_gt
  have heq : π * Real.sqrt 2 = y + π := by rw [hy_def]; ring
  rw [heq, Real.cos_add_pi]
  linarith

/-! ## §6 The positivity lower bound. -/

/-- **`cos_pi_mul_sqrt_two_gt_neg_half`** — `cos(π · √2) > -1/2`.

Symmetric argument using `y > π/3`: `cos(y) < cos(π/3) = 1/2`, so
`cos(π · √2) = -cos(y) > -1/2`. -/
lemma cos_pi_mul_sqrt_two_gt_neg_half :
    -(1 : ℝ) / 2 < Real.cos (π * Real.sqrt 2) := by
  set y := π * (Real.sqrt 2 - 1) with hy_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hy_gt : π / 3 < y := pi_mul_sqrt_two_sub_pi_gt_pi_div_three
  have hy_lt : y < 5 * π / 12 :=
    pi_mul_sqrt_two_sub_pi_lt_five_pi_div_twelve
  have hpi3_mem : π / 3 ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩; linarith
  have hy_mem : y ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨?_, ?_⟩ <;> [linarith; linarith]
  have hcos_lt : Real.cos y < Real.cos (π / 3) :=
    Real.strictAntiOn_cos hpi3_mem hy_mem hy_gt
  rw [Real.cos_pi_div_three] at hcos_lt
  have heq : π * Real.sqrt 2 = y + π := by rw [hy_def]; ring
  rw [heq, Real.cos_add_pi]
  linarith

/-! ## §7 The sharp bracket. -/

/-- **`sigma_alphaP_lt_neg_logb_three_two`** — the sharp α_P upper bracket.

`σ(α_P = √2) < -log₃ 2 = -log 2 / log 3`.

Chain:
- `cos(π · √2) < -(√6 − √2)/4` from §5.
- `1 + 2·cos(π · √2) < 1 − (√6 − √2)/2 = (2 − √6 + √2)/2`.
- `(2 − √6 + √2)/2 < 1/2` via §4 (`√6 > 1 + √2`).
- `cos(π · √2) > -1/2` from §6, so `1 + 2·cos(π · √2) > 0`.
- `|1 + 2·cos(π · √2)| = 1 + 2·cos(π · √2) ∈ (0, 1/2)`.
- `σ = log₃|·| < log₃(1/2) = -log₃ 2`. -/
theorem sigma_alphaP_lt_neg_logb_three_two :
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) < -Real.logb 3 2 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hupper := cos_pi_mul_sqrt_two_lt_neg_bound
  have hlower := cos_pi_mul_sqrt_two_gt_neg_half
  have hs6 := sqrt_six_gt_one_add_sqrt_two
  have hval_lt_half : 1 + 2 * Real.cos (π * Real.sqrt 2) < 1 / 2 := by nlinarith
  have hval_pos : 0 < 1 + 2 * Real.cos (π * Real.sqrt 2) := by linarith
  rw [abs_of_pos hval_pos]
  have hstep : Real.logb 3 (1 + 2 * Real.cos (π * Real.sqrt 2)) < Real.logb 3 (1 / 2) :=
    Real.logb_lt_logb (by norm_num : (1:ℝ) < 3) hval_pos hval_lt_half
  have h_half : Real.logb 3 (1 / 2 : ℝ) = -Real.logb 3 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv]
  linarith [h_half ▸ hstep]

/-! ## §8 The Cantor-tie form. -/

/-- **`sigma_alphaP_lt_neg_cantor_hausdorff_dim`** — the Cantor-tie form.

`σ(α_P = √2) < -log 2 / log 3`, i.e., strictly below the negation of
r236's Cantor Hausdorff dim value. Together with r243's
`σ_Hodge < +log 2 / log 3`, the Cantor value bounds both irrational
pillars — Hodge from above (positive side), P from below (negative side). -/
theorem sigma_alphaP_lt_neg_cantor_hausdorff_dim :
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) < -(Real.log 2 / Real.log 3) := by
  have h := sigma_alphaP_lt_neg_logb_three_two
  unfold Real.logb at h
  linarith

/-! ## §9 r223 elevation. -/

/-- **`SO_αP_sigma_lt_neg_logb_three_two`** — universal over data-fit. -/
theorem SO_αP_sigma_lt_neg_logb_three_two (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αP A φ₀ hA).sigma < -Real.logb 3 2 := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) < -Real.logb 3 2
  exact sigma_alphaP_lt_neg_logb_three_two

/-! ## §10 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaPUpperBracketNegCantor.sqrt_two_lt_seventeen_twelfths
#print axioms PrincipiaTractalis.AlphaPUpperBracketNegCantor.sqrt_two_gt_four_thirds
#print axioms PrincipiaTractalis.AlphaPUpperBracketNegCantor.cos_five_pi_div_twelve
#print axioms PrincipiaTractalis.AlphaPUpperBracketNegCantor.sqrt_six_gt_one_add_sqrt_two
#print axioms PrincipiaTractalis.AlphaPUpperBracketNegCantor.cos_pi_mul_sqrt_two_lt_neg_bound
#print axioms PrincipiaTractalis.AlphaPUpperBracketNegCantor.cos_pi_mul_sqrt_two_gt_neg_half
#print axioms PrincipiaTractalis.AlphaPUpperBracketNegCantor.sigma_alphaP_lt_neg_logb_three_two
#print axioms PrincipiaTractalis.AlphaPUpperBracketNegCantor.sigma_alphaP_lt_neg_cantor_hausdorff_dim

end PrincipiaTractalis.AlphaPUpperBracketNegCantor
