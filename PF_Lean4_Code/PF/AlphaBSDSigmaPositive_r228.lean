/-
# r228: α_BSD = 3π/4 pillar — σ(α_BSD) > 0 (envelope-growing tier).

★ 2026-08-12 r228 — elevating the BSD pillar (α_BSD = 3π/4) via the sharp
SIGN characterisation `σ(α_BSD) > 0`. SIXTH σ-sign class formalised. First
pillar in the "π² tier" since `π · α_BSD = 3π²/4`, but the brackets reduce
to π-only via division, no π²-specific machinery required. ★

## Corpus tally after r228

    σ = +1     α_YM                                    (r224)
    σ > 0      α_Hodge, α_NP, α_BSD (THIS)            (r226, r227, r228)
    σ = 0      α_Poincaré, α_RH                        (r221)
    σ < 0      α_P                                     (r225)
    pending    α_QG (near-critical), α_NS

Six of nine pillars now have σ-sign explicitly formalised.

## What this file proves

α_BSD = 3π/4 (a rational multiple of π). Then π · α_BSD = 3π²/4.

1. `π > 3` (mathlib's `Real.pi_gt_three`) → `3π/4 > 9/4 > 2` → `3π²/4 > 2π`.
2. `π < 315/100` (mathlib's `Real.pi_lt_315`) → `3π/4 < 945/400 < 5/2`
   → `3π²/4 < 5π/2`.
3. So `3π²/4 ∈ (2π, 5π/2)`. Shift by `-2π`: `z := 3π²/4 - 2π ∈ (0, π/2)`.
4. `cos(3π²/4) = cos(z + 2π) = cos(z) > 0` (r226-style, local `cos_add_two_pi`).
5. `|1 + 2·cos(π · α_BSD)| > 1` → `σ(α_BSD) > 0` via `Real.logb_pos`.
6. Elevated to r223: `SO_αBSD_sigma_pos`.

Note: `π²` never appears explicitly. The key is that dividing `3π²/4 < 5π/2`
by π > 0 gives `3π/4 < 5/2`, a linear-in-π inequality settled by
`Real.pi_lt_315`. Same trick for the lower bound.

## Consistency with r212

r212's `sigma_alphaBSD_ne_zero_one : σ(α_BSD) ≠ 0 ∧ σ(α_BSD) ≠ 1` combined
with r228's `σ(α_BSD) > 0` gives `σ(α_BSD) ∈ (0, 1)`. Corpus value ≈ 0.571.

Additionally r212 has `irrational_three_pi_div_four`, so α_BSD is
irrational — half-integer / odd-integer / even-integer level sets from
r221/r224 are all misses (as documented in r224's corpus miss theorems).

## Contents

§0 Local: `cos_add_two_pi` (2π periodicity via two `cos_add_pi`).
§1 π-only brackets: `2π < 3π²/4 < 5π/2`, using `Real.pi_gt_three` and
   `Real.pi_lt_315`.
§2 `cos(π · α_BSD) > 0` via 2π shift into (0, π/2).
§3 `|1 + 2·cos(π · α_BSD)| > 1`.
§4 **`sigma_alphaBSD_gt_zero`** — the named stone.
§5 Elevated to r223: `SO_αBSD_sigma_pos`.
§6 Axiom check.

## Scope

* NOT a BSD conjecture discharge.
* NOT a substrate derivation of `α_BSD = 3π/4`.
* NOT a physical claim about elliptic curves, L-functions, or rational points.
* IS the sharp SIGN characterisation of σ at the BSD pillar. IS a substrate
  consequence: envelope-growing observable for α_BSD.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.SubstrateOscillator_r223

open scoped Real

namespace PrincipiaTractalis.AlphaBSDSigmaPositive

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §0 Local `cos_add_two_pi`. -/

/-- 2π periodicity of cos, from two `cos_add_pi`. Local copy — could reuse
r226's `PrincipiaTractalis.AlphaHodgeSigmaPositive.cos_add_two_pi` but this
file keeps its own for import minimality (depends only on r223). -/
lemma cos_add_two_pi (x : ℝ) : Real.cos (x + 2 * π) = Real.cos x := by
  have h : x + 2 * π = (x + π) + π := by ring
  rw [h, Real.cos_add_pi, Real.cos_add_pi]
  ring

/-! ## §1 The π · α_BSD = 3π²/4 interval. -/

/-- **`2π < 3π²/4`** — the lower interval endpoint.

Reduces to `2 < 3π/4` (divide by π > 0), i.e. `8/3 < π`. From `3 < π` we
get `8/3 < 3 < π`, done. -/
lemma two_pi_lt_pi_mul_alphaBSD : 2 * π < π * (3 * π / 4) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hpi_gt_three : 3 < π := Real.pi_gt_three
  nlinarith

/-- **`3π²/4 < 5π/2`** — the upper interval endpoint.

Reduces to `3π/4 < 5/2` (divide by π > 0), i.e. `π < 10/3`. From
`π < 3.15` (mathlib's `Real.pi_lt_d2`) we get `π < 3.15 < 10/3`. -/
lemma pi_mul_alphaBSD_lt_five_pi_div_two : π * (3 * π / 4) < 5 * π / 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hpi_lt : π < 3.15 := Real.pi_lt_d2
  nlinarith

/-! ## §2 `cos(π · α_BSD) > 0` via 2π shift. -/

/-- **`cos(3π²/4) > 0`.** Since `3π²/4 ∈ (2π, 5π/2)`, shift by -2π to land
in `(0, π/2) ⊂ (-π/2, π/2)` where cos > 0. -/
lemma cos_pi_mul_alphaBSD_pos : 0 < Real.cos (π * (3 * π / 4)) := by
  set z := π * (3 * π / 4) - 2 * π with hz_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hz_pos : 0 < z := by
    rw [hz_def]; linarith [two_pi_lt_pi_mul_alphaBSD]
  have hz_lt_pi_div_two : z < π / 2 := by
    rw [hz_def]; linarith [pi_mul_alphaBSD_lt_five_pi_div_two]
  have hz_gt_neg : -(π / 2) < z := by linarith
  have heq : π * (3 * π / 4) = z + 2 * π := by rw [hz_def]; ring
  rw [heq, cos_add_two_pi]
  exact Real.cos_pos_of_mem_Ioo ⟨hz_gt_neg, hz_lt_pi_div_two⟩

/-! ## §3 `|1 + 2·cos(π · α_BSD)| > 1`. -/

lemma one_lt_one_add_two_cos_pi_mul_alphaBSD :
    1 < 1 + 2 * Real.cos (π * (3 * π / 4)) := by
  linarith [cos_pi_mul_alphaBSD_pos]

lemma abs_one_add_two_cos_pi_mul_alphaBSD_gt_one :
    1 < |1 + 2 * Real.cos (π * (3 * π / 4))| := by
  have h := one_lt_one_add_two_cos_pi_mul_alphaBSD
  rw [abs_of_pos (by linarith :
      (0 : ℝ) < 1 + 2 * Real.cos (π * (3 * π / 4)))]
  exact h

/-! ## §4 The named stone — `σ(α_BSD) > 0`. -/

/-- **`sigma_alphaBSD_gt_zero`** — the substrate sign at the BSD pillar.

`σ(α_BSD) > 0` where α_BSD = 3π/4. Consequence: the BSD substrate observable
has envelope `a^σ` with σ > 0 — amplitude GROWS toward the past (a → 0).
Together with r212's `sigma_alphaBSD_ne_zero_one` we have σ(α_BSD) ∈ (0, 1).
Corpus value ≈ 0.571. -/
theorem sigma_alphaBSD_gt_zero :
    0 < PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4) := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 3)
  exact abs_one_add_two_cos_pi_mul_alphaBSD_gt_one

/-! ## §5 Elevated to r223's `SubstrateOscillator`. -/

/-- **`SO_αBSD_sigma_pos`** — the r223 `SubstrateOscillator` method form.

For every data-fit `A ≠ 0` and every `φ₀`, the α_BSD substrate oscillator
has `sigma > 0`.  Universal over the two data-fit parameters. -/
theorem SO_αBSD_sigma_pos (A φ₀ : ℝ) (hA : A ≠ 0) :
    0 < (SO_αBSD A φ₀ hA).sigma := by
  show 0 < PrincipiaTractalis.SigmaAbscissa.sigma (3 * π / 4)
  exact sigma_alphaBSD_gt_zero

/-! ## §6 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaBSDSigmaPositive.cos_add_two_pi
#print axioms PrincipiaTractalis.AlphaBSDSigmaPositive.two_pi_lt_pi_mul_alphaBSD
#print axioms PrincipiaTractalis.AlphaBSDSigmaPositive.pi_mul_alphaBSD_lt_five_pi_div_two
#print axioms PrincipiaTractalis.AlphaBSDSigmaPositive.cos_pi_mul_alphaBSD_pos
#print axioms PrincipiaTractalis.AlphaBSDSigmaPositive.one_lt_one_add_two_cos_pi_mul_alphaBSD
#print axioms PrincipiaTractalis.AlphaBSDSigmaPositive.abs_one_add_two_cos_pi_mul_alphaBSD_gt_one
#print axioms PrincipiaTractalis.AlphaBSDSigmaPositive.sigma_alphaBSD_gt_zero
#print axioms PrincipiaTractalis.AlphaBSDSigmaPositive.SO_αBSD_sigma_pos

end PrincipiaTractalis.AlphaBSDSigmaPositive
