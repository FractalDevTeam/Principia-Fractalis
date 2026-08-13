/-
# r243: SHARP HODGE UPPER BRACKET — σ(α_Hodge) < log 2 / log 3 = σ(1/3).

★ 2026-08-13 r243 — the FIRST sharp bracket landing. `σ(α_Hodge) < log 2 / log 3`,
tying Hodge pillar σ strictly below r236's Cantor Hausdorff value σ(1/3).
Pure-algebra proof — no Taylor bounds needed, purely from `φ < 5/3` and cos
strict antitonicity on `[0, π]`. ★

## The bracket

**Upper end**: σ(α_Hodge = φ) < log 2 / log 3 = log₃ 2.

Because:
1. `φ < 5/3` — new bound, tighter than r226's `φ < 2`, via `√5 < 7/3`
   (i.e., 45 < 49).
2. `π · φ < 5π/3`, hence `y := 2π − π · φ > π/3`.
3. `y ∈ (0, π/2)` (from r226) ⊂ `[0, π]`, and cos is strictly antitone
   on `[0, π]`; so `y > π/3 → cos(y) < cos(π/3) = 1/2`.
4. `cos(π · φ) = cos(y)` (from r226's setup), so `cos(π · φ) < 1/2`.
5. `1 + 2·cos(π · φ) < 2`, and since it's positive (r226), so is `|·|`.
6. `σ(α_Hodge) = log₃|1 + 2·cos(π · φ)| < log₃ 2 = log 2 / log 3`.

## Why this is sharp — and why it matters

The corpus σ-sign machine (r226) says σ_Hodge > 0. r241's ceiling says σ_Hodge ≤ 1.
r212 excludes σ_Hodge ∈ {0, 1} and (`sigma_eq_half_iff` route) σ_Hodge ≠ 1/2.

r243 sharpens: σ_Hodge < `log 2 / log 3 ≈ 0.6309`. Combined with r236's
`σ(1/3) = log 2 / log 3 = Cantor Hausdorff dim`, this puts σ_Hodge strictly
BELOW the Cantor dim in the substrate σ table:

    σ(α_Hodge = φ) < σ(1/3) = log 2 / log 3.

Substrate anchors Hodge pillar strictly below the Cantor Hausdorff value.
No approximation, no Taylor — pure `√5 < 7/3` algebra plus cos monotonicity.

Also: r242 gave `σ(α_Hodge) < σ(α_YM) = 1` (from r241's ceiling + r212 misses).
r243 sharpens that gap: not merely `< 1`, but `< log₃ 2 ≈ 0.631`.

## Note on the 1/2 threshold

`σ_Hodge < 1/2` would be a TIGHTER bracket than r243's `< log₃ 2 ≈ 0.631`.
That tighter bound is TRUE numerically (σ_Hodge ≈ 0.496) but requires Taylor
bounds on sin/cos that aren't in mathlib yet — deferred.

r243 is the sharpest ALGEBRAIC (Taylor-free) upper bracket available with the
existing substrate + mathlib toolkit.

## Contents

§1 `sqrt_five_lt_seven_thirds` — the key tightening `√5 < 7/3`.
§2 `goldenRatio_lt_five_thirds` — `φ < 5/3` via §1.
§3 `pi_mul_goldenRatio_lt_five_pi_div_three` — `π · φ < 5π/3`.
§4 `two_pi_sub_pi_mul_goldenRatio_gt_pi_div_three` — the y > π/3 bound.
§5 `cos_pi_mul_goldenRatio_lt_half` — the key cos bound via strictAntiOn.
§6 `sigma_alphaHodge_lt_logb_three_two` — the σ_Hodge sharp bracket.
§7 `sigma_alphaHodge_lt_cantor_hausdorff_dim` — the Cantor-tie form.
§8 `SO_αHodge_sigma_lt_logb_three_two` — r223 elevation.
§9 Axiom check.

## Scope

* NOT novel — pure algebra + cos monotonicity.
* NOT a Millennium discharge.
* NOT the tightest possible bracket (`< 1/2` numerically holds; needs Taylor).
* IS the first sharp substrate bracket: σ_Hodge strictly below `log 2 / log 3`,
  the Cantor Hausdorff dim, via Taylor-free algebra.

First sharp bracket landing after the r239 exact-table + r240/r241/r242
structural arc.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaHodgeSigmaPositive_r226
import PF.AlphaYMCorpusMaximum_r242

open scoped Real

namespace PrincipiaTractalis.AlphaHodgeUpperBracketCantor

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.AlphaHodgeSigmaPositive
open PrincipiaTractalis

/-! ## §1 `√5 < 7/3` — the key tightening. -/

/-- **`sqrt_five_lt_seven_thirds`** — `√5 < 7/3`.

Via `nlinarith` on `(7/3)² = 49/9 > 5 = 45/9`. This is a strict tightening of
r226's `sqrt_five_lt_three`, and it is the algebraic seed of the whole bracket. -/
lemma sqrt_five_lt_seven_thirds : Real.sqrt 5 < 7 / 3 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [Real.sqrt_nonneg 5, h5]

/-! ## §2 `φ < 5/3`. -/

/-- **`goldenRatio_lt_five_thirds`** — `φ < 5/3`.

φ = (1 + √5)/2 < (1 + 7/3)/2 = (10/3)/2 = 5/3 via §1. -/
lemma goldenRatio_lt_five_thirds : Real.goldenRatio < 5 / 3 := by
  unfold Real.goldenRatio
  have := sqrt_five_lt_seven_thirds
  linarith

/-! ## §3 `π · φ < 5π/3`. -/

/-- **`pi_mul_goldenRatio_lt_five_pi_div_three`** — `π · φ < 5π/3`. -/
lemma pi_mul_goldenRatio_lt_five_pi_div_three :
    π * Real.goldenRatio < 5 * π / 3 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := goldenRatio_lt_five_thirds
  nlinarith

/-! ## §4 The angle-y bound. -/

/-- **`two_pi_sub_pi_mul_goldenRatio_gt_pi_div_three`** — `2π − π · φ > π/3`.

Directly from §3: `y := 2π − π · φ > 2π − 5π/3 = π/3`. -/
lemma two_pi_sub_pi_mul_goldenRatio_gt_pi_div_three :
    π / 3 < 2 * π - π * Real.goldenRatio := by
  have := pi_mul_goldenRatio_lt_five_pi_div_three
  linarith

/-! ## §5 `cos(π · φ) < 1/2`. -/

/-- **`cos_pi_mul_goldenRatio_lt_half`** — `cos(π · φ) < 1/2`.

Route: set `y := 2π − π · φ`; §4 gives `y > π/3`; r226 gives `y < π/2`.
Both `π/3` and `y` lie in `[0, π]`, cos is strictly antitone there
(mathlib `Real.strictAntiOn_cos`), so `cos(y) < cos(π/3) = 1/2`.
Then `cos(π · φ) = cos(-y + 2π) = cos(y)` via periodicity + evenness. -/
lemma cos_pi_mul_goldenRatio_lt_half : Real.cos (π * Real.goldenRatio) < 1 / 2 := by
  set y := 2 * π - π * Real.goldenRatio with hy_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hy_gt : π / 3 < y := two_pi_sub_pi_mul_goldenRatio_gt_pi_div_three
  have hy_lt : y < π / 2 := by
    rw [hy_def]; linarith [three_pi_div_two_lt_pi_mul_goldenRatio]
  -- cos y = cos(π · φ) via the periodicity/evenness route (mirrors r226).
  have heq : π * Real.goldenRatio = -y + 2 * π := by rw [hy_def]; ring
  have hcos_eq : Real.cos (π * Real.goldenRatio) = Real.cos y := by
    rw [heq, cos_add_two_pi, Real.cos_neg]
  rw [hcos_eq]
  -- Both π/3 and y in [0, π]; cos strictly antitone there.
  have hpi3_mem : π / 3 ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩; linarith
  have hy_mem : y ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨?_, ?_⟩
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have hcos_lt : Real.cos y < Real.cos (π / 3) :=
    Real.strictAntiOn_cos hpi3_mem hy_mem hy_gt
  rw [Real.cos_pi_div_three] at hcos_lt
  exact hcos_lt

/-! ## §6 The sharp bracket: `σ(α_Hodge) < log₃ 2`. -/

/-- **`sigma_alphaHodge_lt_logb_three_two`** — the sharp Hodge upper bracket.

`σ(α_Hodge = φ) < log₃ 2 = log 2 / log 3`.

Route:
- `cos(π · φ) < 1/2` from §5.
- `1 + 2·cos(π · φ) < 2`.
- Both positive (r226's positivity chain), so `|1 + 2·cos(π · φ)| < 2`.
- `log₃` strictly monotone on positive reals gives `σ < log₃ 2`. -/
theorem sigma_alphaHodge_lt_logb_three_two :
    PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio < Real.logb 3 2 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos_pos := cos_pi_mul_goldenRatio_pos
  have hcos_lt_half := cos_pi_mul_goldenRatio_lt_half
  have hval_pos : 0 < 1 + 2 * Real.cos (π * Real.goldenRatio) := by linarith
  have hval_lt_two : 1 + 2 * Real.cos (π * Real.goldenRatio) < 2 := by linarith
  rw [abs_of_pos hval_pos]
  exact Real.logb_lt_logb (by norm_num : (1:ℝ) < 3) hval_pos hval_lt_two

/-! ## §7 The Cantor-tie form. -/

/-- **`sigma_alphaHodge_lt_cantor_hausdorff_dim`** — the tie to r236.

`σ(α_Hodge = φ) < log 2 / log 3`, i.e., strictly below r236's Cantor
Hausdorff dim value `σ(1/3) = log 2 / log 3`. -/
theorem sigma_alphaHodge_lt_cantor_hausdorff_dim :
    PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio < Real.log 2 / Real.log 3 := by
  have h := sigma_alphaHodge_lt_logb_three_two
  unfold Real.logb at h
  exact h

/-! ## §8 r223 elevation. -/

/-- **`SO_αHodge_sigma_lt_logb_three_two`** — universal over data-fit.

For every `A ≠ 0`, `φ₀`, the r223 SubstrateOscillator at α_Hodge has
`sigma < log₃ 2`. Pillar-intrinsic, not tuning-dependent. -/
theorem SO_αHodge_sigma_lt_logb_three_two (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αHodge A φ₀ hA).sigma < Real.logb 3 2 := by
  show PrincipiaTractalis.SigmaAbscissa.sigma Real.goldenRatio < Real.logb 3 2
  exact sigma_alphaHodge_lt_logb_three_two

/-! ## §9 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaHodgeUpperBracketCantor.sqrt_five_lt_seven_thirds
#print axioms PrincipiaTractalis.AlphaHodgeUpperBracketCantor.goldenRatio_lt_five_thirds
#print axioms PrincipiaTractalis.AlphaHodgeUpperBracketCantor.cos_pi_mul_goldenRatio_lt_half
#print axioms PrincipiaTractalis.AlphaHodgeUpperBracketCantor.sigma_alphaHodge_lt_logb_three_two
#print axioms PrincipiaTractalis.AlphaHodgeUpperBracketCantor.sigma_alphaHodge_lt_cantor_hausdorff_dim

end PrincipiaTractalis.AlphaHodgeUpperBracketCantor
