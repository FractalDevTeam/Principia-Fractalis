/-
# r245: SHARP α_BSD UPPER BRACKET — σ(α_BSD) < log 2 / log 3 = Cantor Hausdorff dim.

★ 2026-08-13 r245 — the THIRD sharp bracket landing. `σ(α_BSD = 3π/4) <
log 2 / log 3 = log₃ 2 = σ(1/3) = Cantor Hausdorff dim`. Ties BSD strictly
below the Cantor value, sharing the r243 bound on σ_Hodge and completing
the picture of the three σ > 0 corpus pillars vs. the Cantor value:

    0 < σ(α_Hodge = φ)   < log 2 / log 3   (r243)
    0 < σ(α_BSD = 3π/4)  < log 2 / log 3   (r245)
    0 < σ(α_NP = φ+1/4)  < ??               (Hodge > NP has σ > Cantor numerically)

## The bracket

**Upper end**: `σ(α_BSD = 3π/4) < log 2 / log 3 = log₃ 2`.

Because:
1. `α_BSD = 3π/4`, so `π · α_BSD = 3π²/4`.
2. Set `z := π · α_BSD − 2π = π(3π − 8)/4`. Then `3π²/4 = 2π + z`.
3. `z > π/3`: needs `π(3π − 8)/4 > π/3`, i.e., `3(3π − 8) > 4`, i.e.,
   `9π > 28`. Since `π > 3.14`, `9π > 28.26 > 28` ✓.
4. `z < π/2`: needs `π(3π − 8)/4 < π/2`, i.e., `3π − 8 < 2`, i.e., `π < 10/3`.
   Since `π < 3.15 < 3.334`, ✓.
5. Hence `z ∈ (π/3, π/2) ⊂ [0, π]`, and `Real.strictAntiOn_cos` on `[0, π]`
   gives `cos(z) < cos(π/3) = 1/2`.
6. `cos(π · α_BSD) = cos(2π + z) = cos(z) < 1/2` via `cos_add_two_pi`.
7. `1 + 2·cos(π · α_BSD) < 2`, positive by r228 (`cos_pi_mul_alphaBSD_pos`).
8. `σ(α_BSD) = log₃|·| = log₃(·) < log₃ 2 = log 2 / log 3`.

## Position in the substrate σ map

Together with r243 (`σ_Hodge < log 2 / log 3`) and r244 (`σ_P < -log 2 / log 3`),
we now have three of the four r212 σ-sign > 0 irrational pillars bounded
by the Cantor value:

- σ(α_Hodge = φ) < Cantor dim.   (r243)
- σ(α_BSD = 3π/4) < Cantor dim.  (r245)
- σ(α_NP = φ+1/4) NOT < Cantor dim numerically (≈ 0.947 > 0.631). Would need
  a different, higher bracket point.

And on the negative side:
- σ(α_P = √2) < -Cantor dim.     (r244)
- σ(α_QG = √(2π)) ≈ -0.039 not bounded by -Cantor dim (much closer to 0).
- σ(α_NS = 3π/2) ≈ -1.308 clearly < -Cantor dim = -0.631, provable.

## Contents

§1 `nine_pi_gt_twenty_eight` — `9π > 28`.
§2 `three_pi_lt_ten` — `3π < 10`.
§3 `pi_mul_alphaBSD_sub_two_pi_gt_pi_div_three` — `π·(3π/4) − 2π > π/3`.
§4 `pi_mul_alphaBSD_sub_two_pi_lt_pi_div_two` — `π·(3π/4) − 2π < π/2`.
§5 `cos_pi_mul_alphaBSD_lt_half` — the key cos bound via strictAntiOn.
§6 `sigma_alphaBSD_lt_logb_three_two` — the sharp bracket.
§7 `sigma_alphaBSD_lt_cantor_hausdorff_dim` — the Cantor-tie form.
§8 `SO_αBSD_sigma_lt_logb_three_two` — r223 elevation.
§9 Axiom check.

## Scope

* NOT novel — pure algebra + `Real.strictAntiOn_cos` + mathlib pi bounds.
* NOT the tightest possible (σ_BSD ≈ 0.572 vs the 0.631 bracket).
* NOT a Millennium discharge.
* IS the third sharp substrate bracket, extending the r243/r244 Cantor-value
  bounding pattern to the third σ > 0 corpus pillar.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaBSDSigmaPositive_r228
import PF.AlphaPUpperBracketNegCantor_r244

open scoped Real

namespace PrincipiaTractalis.AlphaBSDUpperBracketCantor

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.AlphaBSDSigmaPositive
open PrincipiaTractalis

/-! ## §1 `9π > 28`. -/

/-- **`nine_pi_gt_twenty_eight`** — from `Real.pi_gt_d2 : π > 3.14`. -/
lemma nine_pi_gt_twenty_eight : (28 : ℝ) < 9 * π := by
  have := Real.pi_gt_d2
  linarith

/-! ## §2 `3π < 10`. -/

/-- **`three_pi_lt_ten`** — from `Real.pi_lt_d2 : π < 3.15`. -/
lemma three_pi_lt_ten : 3 * π < 10 := by
  have := Real.pi_lt_d2
  linarith

/-! ## §3 The lower angle bracket: `π·α_BSD − 2π > π/3`. -/

/-- **`pi_mul_alphaBSD_sub_two_pi_gt_pi_div_three`** — `3π²/4 − 2π > π/3`.

Chain: `9π > 28` (§1), so `9π − 24 > 4`, so `π(9π − 24)/12 > π · 4/12 = π/3`,
so `π(3π − 8)/4 > π/3`. -/
lemma pi_mul_alphaBSD_sub_two_pi_gt_pi_div_three :
    π / 3 < π * (3 * π / 4) - 2 * π := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h9 := nine_pi_gt_twenty_eight
  nlinarith [h9, hpi]

/-! ## §4 The upper angle bracket: `π·α_BSD − 2π < π/2`. -/

/-- **`pi_mul_alphaBSD_sub_two_pi_lt_pi_div_two`** — `3π²/4 − 2π < π/2`.

Chain: `3π < 10` (§2), so `π(3π − 8) < π · 2`, so `π(3π − 8)/4 < π/2`. -/
lemma pi_mul_alphaBSD_sub_two_pi_lt_pi_div_two :
    π * (3 * π / 4) - 2 * π < π / 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h3 := three_pi_lt_ten
  nlinarith [h3, hpi]

/-! ## §5 `cos(π · α_BSD) < 1/2`. -/

/-- **`cos_pi_mul_alphaBSD_lt_half`** — `cos(π · 3π/4) < 1/2`.

Set `z := π · (3π/4) − 2π`. Then `z ∈ (π/3, π/2)` (§3/§4), `z ∈ [0, π]`,
and `Real.strictAntiOn_cos` on `[0, π]` gives `cos(z) < cos(π/3) = 1/2`.
`cos(π · 3π/4) = cos(z + 2π) = cos(z)` via `cos_add_two_pi`. -/
lemma cos_pi_mul_alphaBSD_lt_half :
    Real.cos (π * (3 * π / 4)) < 1 / 2 := by
  set z := π * (3 * π / 4) - 2 * π with hz_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hz_gt : π / 3 < z := pi_mul_alphaBSD_sub_two_pi_gt_pi_div_three
  have hz_lt : z < π / 2 := pi_mul_alphaBSD_sub_two_pi_lt_pi_div_two
  have hpi3_mem : π / 3 ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩; linarith
  have hz_mem : z ∈ Set.Icc (0 : ℝ) π := by
    refine ⟨?_, ?_⟩ <;> [linarith; linarith]
  have hcos_lt : Real.cos z < Real.cos (π / 3) :=
    Real.strictAntiOn_cos hpi3_mem hz_mem hz_gt
  rw [Real.cos_pi_div_three] at hcos_lt
  have heq : π * (3 * π / 4) = z + 2 * π := by rw [hz_def]; ring
  rw [heq, cos_add_two_pi]
  exact hcos_lt

/-! ## §6 The sharp bracket. -/

/-- **`sigma_alphaBSD_lt_logb_three_two`** — the sharp α_BSD upper bracket.

`σ(α_BSD = 3π/4) < log₃ 2 = log 2 / log 3`.

Chain:
- `cos(π · α_BSD) < 1/2` from §5.
- `1 + 2·cos(π · α_BSD) < 2`.
- `1 + 2·cos(π · α_BSD) > 0` (from r228, since cos > 0 for α_BSD).
- `|·| = 1 + 2·cos(π · α_BSD) ∈ (0, 2)`.
- `σ = log₃|·| < log₃ 2` via `Real.logb_lt_logb`. -/
theorem sigma_alphaBSD_lt_logb_three_two :
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) < Real.logb 3 2 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  have hcos_pos := cos_pi_mul_alphaBSD_pos
  have hcos_lt_half := cos_pi_mul_alphaBSD_lt_half
  have hval_pos : 0 < 1 + 2 * Real.cos (π * (3 * π / 4)) := by linarith
  have hval_lt_two : 1 + 2 * Real.cos (π * (3 * π / 4)) < 2 := by linarith
  rw [abs_of_pos hval_pos]
  exact Real.logb_lt_logb (by norm_num : (1:ℝ) < 3) hval_pos hval_lt_two

/-! ## §7 The Cantor-tie form. -/

/-- **`sigma_alphaBSD_lt_cantor_hausdorff_dim`** — the Cantor-tie form.

`σ(α_BSD = 3π/4) < log 2 / log 3` — strictly below the Cantor Hausdorff
value. Companion to r243's `σ_Hodge < log 2 / log 3`: BOTH σ_Hodge and
σ_BSD are bounded above by the Cantor value in the substrate spectrum. -/
theorem sigma_alphaBSD_lt_cantor_hausdorff_dim :
    PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) < Real.log 2 / Real.log 3 := by
  have h := sigma_alphaBSD_lt_logb_three_two
  unfold Real.logb at h
  exact h

/-! ## §8 r223 elevation. -/

/-- **`SO_αBSD_sigma_lt_logb_three_two`** — universal over data-fit. -/
theorem SO_αBSD_sigma_lt_logb_three_two (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αBSD A φ₀ hA).sigma < Real.logb 3 2 := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) < Real.logb 3 2
  exact sigma_alphaBSD_lt_logb_three_two

/-! ## §9 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaBSDUpperBracketCantor.nine_pi_gt_twenty_eight
#print axioms PrincipiaTractalis.AlphaBSDUpperBracketCantor.three_pi_lt_ten
#print axioms PrincipiaTractalis.AlphaBSDUpperBracketCantor.cos_pi_mul_alphaBSD_lt_half
#print axioms PrincipiaTractalis.AlphaBSDUpperBracketCantor.sigma_alphaBSD_lt_logb_three_two
#print axioms PrincipiaTractalis.AlphaBSDUpperBracketCantor.sigma_alphaBSD_lt_cantor_hausdorff_dim

end PrincipiaTractalis.AlphaBSDUpperBracketCantor
