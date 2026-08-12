/-
# r227: α_NP = φ + 1/4 pillar — σ(α_NP) > 0 (envelope-growing tier).

★ 2026-08-12 r227 — elevating the NP pillar (α_NP = φ + 1/4) via the sharp
SIGN characterisation `σ(α_NP) > 0`. FIFTH σ-sign class formalised; joins
r226 (α_Hodge > 0) on the envelope-growing side. Reuses r226's golden
ratio brackets and 2π periodicity lemma. ★

## Corpus tally of σ-sign classes after r227

    σ = +1     α_YM                      (r224 linear-growth tier)
    σ > 0      α_Hodge = φ               (r226)
               α_NP = φ + 1/4 (THIS)     (envelope-growing tier)
    σ = 0      α_Poincaré = 1            (r221 constant-amplitude tier)
               α_RH = 3/2                (r221)
    σ < 0      α_P = √2                  (r225 envelope-decaying tier)
    pending    α_BSD = 3π/4              (σ > 0 predicted; π² brackets needed)
               α_QG = √(2π)              (σ < 0 near-critical; π² brackets)
               α_NS = 3π/2               (σ < 0 predicted; π² brackets)

Five of nine canonical pillars now have σ-sign explicitly formalised.

## What this file proves

The substrate reading at α_NP = φ + 1/4:

1. `3/2 < φ < 2` (r226).
2. `7π/4 < π · (φ + 1/4) < 9π/4` — multiply by π > 0 and shift.
3. Let `z := π · (φ + 1/4) - 2π`. Then `z ∈ (-π/4, π/4) ⊂ (-π/2, π/2)`.
4. `cos(π · α_NP) = cos(z + 2π) = cos(z)` via r226's `cos_add_two_pi`.
5. `cos(z) > 0` via `Real.cos_pos_of_mem_Ioo`.
6. `1 + 2 · cos(π · α_NP) > 1`.
7. **`σ(α_NP) > 0`** via `Real.logb_pos`.
8. Elevated to r223: `SO_αNP_sigma_pos`.

Note: `π · α_NP` STRADDLES 2π (interval (7π/4, 9π/4) crosses 2π). The 2π
shift is what handles this cleanly — no case split needed. This trick will
recur for α_QG at 2π + small.

## Contrast: r226 vs r227

Both are σ > 0 pillars via golden ratio. Structural difference:

- r226 (α_Hodge = φ): `π·φ ∈ (3π/2, 2π)`. Shift by 2π: `z = -y ∈ (-π/2, 0)`.
- r227 (α_NP = φ + 1/4): `π·(φ+1/4) ∈ (7π/4, 9π/4)`. Shift by 2π: `z ∈ (-π/4, π/4)` — STRADDLES zero.

Both land inside `(-π/2, π/2)` after the 2π shift, so `Real.cos_pos_of_mem_Ioo` closes both.

## Consistency with r212

r212's `sigma_alphaNP_ne_zero_one : σ(φ+1/4) ≠ 0 ∧ σ(φ+1/4) ≠ 1` combined
with r227's `σ(φ+1/4) > 0` gives:

    σ(α_NP) ∈ (0, 1) \ {1/2 possibly?}

r212's `irrational_goldenRatio_add_quarter` supports the irrationality
of α_NP. Corpus value σ(α_NP) ≈ 0.947 — very close to 1 (the α_YM tier).
Sharp bracket (`σ ∈ (0.94, 0.95)` or similar) is future substrate work.

## Scope

* NOT an NP-completeness discharge (nor even a P vs NP one — that was r225's α_P).
* NOT a substrate derivation of `α_NP = φ + 1/4`.
* NOT a physical claim about complexity theory.
* IS the sharp SIGN characterisation of σ at the NP pillar. IS a substrate
  consequence: envelope-growing observable for α_NP.

## Contents

§1 The π · (φ+1/4) interval: `7π/4 < π · α_NP < 9π/4`.
§2 `cos(π · α_NP) > 0` via 2π shift into (-π/4, π/4).
§3 `1 < 1 + 2·cos(π · α_NP)` and its `|·|` form.
§4 **`sigma_alphaNP_gt_zero`** — the named stone.
§5 Elevated to r223: `SO_αNP_sigma_pos`.
§6 Axiom check.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.AlphaHodgeSigmaPositive_r226

open scoped Real

namespace PrincipiaTractalis.AlphaNPSigmaPositive

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis.AlphaHodgeSigmaPositive
open PrincipiaTractalis

/-! ## §1 The π · (φ + 1/4) interval. -/

lemma seven_pi_div_four_lt_pi_mul_alphaNP :
    7 * π / 4 < π * (Real.goldenRatio + 1 / 4) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := three_halves_lt_goldenRatio
  nlinarith

lemma pi_mul_alphaNP_lt_nine_pi_div_four :
    π * (Real.goldenRatio + 1 / 4) < 9 * π / 4 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := goldenRatio_lt_two
  nlinarith

/-! ## §2 `cos(π · α_NP) > 0` via 2π shift into (-π/4, π/4). -/

/-- **`cos(π · (φ + 1/4)) > 0`.**  The interval `(7π/4, 9π/4)` straddles 2π.
Shift by `-2π` to land in `(-π/4, π/4) ⊂ (-π/2, π/2)` where cos > 0. -/
lemma cos_pi_mul_alphaNP_pos :
    0 < Real.cos (π * (Real.goldenRatio + 1 / 4)) := by
  set z := π * (Real.goldenRatio + 1 / 4) - 2 * π with hz_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hz_lower : -(π / 4) < z := by
    rw [hz_def]; linarith [seven_pi_div_four_lt_pi_mul_alphaNP]
  have hz_upper : z < π / 4 := by
    rw [hz_def]; linarith [pi_mul_alphaNP_lt_nine_pi_div_four]
  have hz_gt : -(π / 2) < z := by linarith
  have hz_lt : z < π / 2 := by linarith
  have heq : π * (Real.goldenRatio + 1 / 4) = z + 2 * π := by
    rw [hz_def]; ring
  rw [heq, cos_add_two_pi]
  exact Real.cos_pos_of_mem_Ioo ⟨hz_gt, hz_lt⟩

/-! ## §3 `|1 + 2 · cos(π · α_NP)| > 1`. -/

lemma one_lt_one_add_two_cos_pi_mul_alphaNP :
    1 < 1 + 2 * Real.cos (π * (Real.goldenRatio + 1 / 4)) := by
  linarith [cos_pi_mul_alphaNP_pos]

lemma abs_one_add_two_cos_pi_mul_alphaNP_gt_one :
    1 < |1 + 2 * Real.cos (π * (Real.goldenRatio + 1 / 4))| := by
  have h := one_lt_one_add_two_cos_pi_mul_alphaNP
  rw [abs_of_pos (by linarith :
      (0 : ℝ) < 1 + 2 * Real.cos (π * (Real.goldenRatio + 1 / 4)))]
  exact h

/-! ## §4 The named stone — `σ(α_NP) > 0`. -/

/-- **`sigma_alphaNP_gt_zero`** — the substrate sign at the NP pillar.

`σ(α_NP) > 0` where α_NP = φ + 1/4.  The NP substrate observable has
envelope `a^σ` with σ > 0 — amplitude GROWS toward the past (a → 0),
sub-linearly.  Together with r212's `sigma_alphaNP_ne_zero_one`, we have
`σ(α_NP) ∈ (0, 1)` — corpus value ≈ 0.947 (very close to α_YM's σ = 1). -/
theorem sigma_alphaNP_gt_zero :
    0 < PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1 / 4) := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 3)
  exact abs_one_add_two_cos_pi_mul_alphaNP_gt_one

/-! ## §5 Elevated to r223's `SubstrateOscillator`. -/

/-- **`SO_αNP_sigma_pos`** — the r223 `SubstrateOscillator` method form.

For every data-fit `A ≠ 0` and every `φ₀`, the α_NP substrate oscillator has
`sigma > 0`.  Universal over the two data-fit parameters. -/
theorem SO_αNP_sigma_pos (A φ₀ : ℝ) (hA : A ≠ 0) :
    0 < (SO_αNP A φ₀ hA).sigma := by
  show 0 < PrincipiaTractalis.SigmaAbscissa.sigma (Real.goldenRatio + 1 / 4)
  exact sigma_alphaNP_gt_zero

/-! ## §6 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaNPSigmaPositive.seven_pi_div_four_lt_pi_mul_alphaNP
#print axioms PrincipiaTractalis.AlphaNPSigmaPositive.pi_mul_alphaNP_lt_nine_pi_div_four
#print axioms PrincipiaTractalis.AlphaNPSigmaPositive.cos_pi_mul_alphaNP_pos
#print axioms PrincipiaTractalis.AlphaNPSigmaPositive.one_lt_one_add_two_cos_pi_mul_alphaNP
#print axioms PrincipiaTractalis.AlphaNPSigmaPositive.abs_one_add_two_cos_pi_mul_alphaNP_gt_one
#print axioms PrincipiaTractalis.AlphaNPSigmaPositive.sigma_alphaNP_gt_zero
#print axioms PrincipiaTractalis.AlphaNPSigmaPositive.SO_αNP_sigma_pos

end PrincipiaTractalis.AlphaNPSigmaPositive
