/-
# r225: α_P = √2 pillar — σ(α_P) < 0 (envelope-decaying tier).

★ 2026-08-12 r225 — elevating the P vs NP pillar (α_P = √2) via the sharp
SIGN characterisation of its substrate abscissa: `σ(α_P) < 0`. Together
with r221 (σ = 0 hits: Poincaré, RH) and r224 (σ = 1 hits: YM), this gives
the third explicit sign class of σ across the corpus:

    σ = 0     α_Poincaré, α_RH         (r221 constant-amplitude tier)
    σ = 1     α_YM                      (r224 linear-growth tier)
    σ < 0     α_P (THIS FILE)          (envelope-decaying tier)

Other irrational pillars (α_Hodge, α_NP, α_BSD, α_QG, α_NS) also miss
`σ ∈ {0, 1}` via r212's per-alpha theorems, but their SIGN partition
(σ > 0 vs σ < 0) is only formalised so far for α_P here — future
substrate work.

## What this file proves

The substrate reading at α_P = √2 assembled from six elementary steps:

1. `1 < √2 < 3/2`                                     (elementary, square comparison)
2. `π < π · √2 < 3π/2`                                 (multiply by π > 0)
3. `cos(π · √2) < 0`                                   (via `cos(π + y) = -cos(y)` with
                                                       y = π(√2 - 1) ∈ (0, π/2))
4. `cos(π · √2) > -1`                                  (else √2 = 1 + 2k for some k : ℤ,
                                                       contradicting `Irrational √2`)
5. `1 + 2·cos(π · √2) ≠ 0`                             (else √2 = 2k/3 rational,
                                                       via r212's `cos_pi_mul_eq_neg_half_imp_rational`)
6. `|1 + 2·cos(π · √2)| ∈ (0, 1)`                      (combines 3, 4, 5)
7. **`σ(α_P) < 0`**                                   (log₃ of a value in (0, 1))

Elevated to r223's `SubstrateOscillator`: `(SO_αP A φ₀ hA).sigma < 0` for
every data-fit `A ≠ 0` and every `φ₀`. The P vs NP substrate observable
therefore has envelope `a^σ` with σ < 0 — amplitude DECAYS toward the
past (a → 0).

## The three-sign partition of the substrate

Combining r221 + r224 + r225 with r212's dichotomy theorems:

| pillar     | α       | σ sign      | envelope behaviour            |
|------------|---------|-------------|-------------------------------|
| α_YM       | 2       | σ = +1      | LINEAR GROWTH toward past     |
| α_BSD      | 3π/4    | σ > 0*      | sub-linear growth (r212 miss) |
| α_Hodge    | φ       | σ > 0*      | sub-linear growth (r212 miss) |
| α_NP       | φ+1/4   | σ > 0*      | sub-linear growth (r212 miss) |
| α_Poincaré | 1       | σ = 0       | CONSTANT amplitude            |
| α_RH       | 3/2     | σ = 0       | CONSTANT amplitude            |
| α_QG       | √(2π)   | σ < 0*      | near-critical decay (r212 miss)|
| α_P        | √2      | σ < 0       | DECAY toward past             |
| α_NS       | 3π/2    | σ < 0*      | decay (r212 miss + r221 miss) |

Entries marked * have r212 misses at `σ ∈ {0, 1}` but no formalised sign.
This file establishes the sign for α_P concretely.

## Scope

* NOT a P vs NP discharge.
* NOT a substrate derivation of `α_P = √2`.
* NOT a physical claim about complexity theory.
* IS the sharp SIGN characterisation of σ at the P vs NP pillar. IS a
  substrate consequence: envelope-decaying observable for α_P.

## Contents

§1 `sqrt_two` brackets: `1 < √2 < 3/2` (elementary).
§2 π · √2 interval: `π < π · √2 < 3π/2`.
§3 `cos(π · √2) < 0` via cos(π + y) = -cos(y) and y ∈ (0, π/2).
§4 `cos(π · √2) > -1` via irrationality.
§5 `1 + 2·cos(π · √2) ≠ 0` via irrationality + r212 degenerate branch.
§6 `|1 + 2·cos(π · √2)| ∈ (0, 1)`.
§7 **`sigma_alphaP_lt_zero`**  — `σ(α_P) < 0`.
§8 Elevated to r223: `SO_αP_sigma_neg` — the SubstrateOscillator method.
§9 Axiom check.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.SubstrateOscillator_r223

open scoped Real

namespace PrincipiaTractalis.AlphaPSigmaNegative

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §1 Elementary brackets on `√2`. -/

/-- `1 < √2`. -/
lemma one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have h : Real.sqrt 1 < Real.sqrt 2 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simpa [Real.sqrt_one] using h

/-- `√2 < 3/2`. -/
lemma sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  have h : Real.sqrt 2 < Real.sqrt ((3 / 2) ^ 2) := by
    apply Real.sqrt_lt_sqrt (by norm_num)
    norm_num
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)] at h

/-! ## §2 The `π · √2` interval. -/

/-- `π < π · √2`. -/
lemma pi_lt_pi_mul_sqrt_two : π < π * Real.sqrt 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := one_lt_sqrt_two
  nlinarith

/-- `π · √2 < 3π/2`. -/
lemma pi_mul_sqrt_two_lt_three_pi_div_two : π * Real.sqrt 2 < 3 * π / 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := sqrt_two_lt_three_halves
  nlinarith

/-! ## §3 `cos(π · √2) < 0` — the negativity of cosine. -/

/-- **`cos(π · √2) < 0`.**  Via `cos(π + y) = -cos(y)` with
`y = π · (√2 - 1) ∈ (0, π/2)` where cos is positive. -/
lemma cos_pi_mul_sqrt_two_neg : Real.cos (π * Real.sqrt 2) < 0 := by
  set y := π * (Real.sqrt 2 - 1) with hy_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hy_eq : π * Real.sqrt 2 = y + π := by rw [hy_def]; ring
  have hy_pos : 0 < y := by
    rw [hy_def]
    have := one_lt_sqrt_two
    nlinarith
  have hy_lt_pi_div_two : y < π / 2 := by
    rw [hy_def]
    have := sqrt_two_lt_three_halves
    nlinarith
  have hcos_pos : 0 < Real.cos y := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith
    · exact hy_lt_pi_div_two
  rw [hy_eq, Real.cos_add_pi]
  linarith

/-! ## §4 `cos(π · √2) > -1` via irrationality of `√2`. -/

/-- **`cos(π · √2) > -1`.**  Equality would give `√2 = 1 + 2k` for some
`k : ℤ` (via r212's `cos_pi_mul_eq_neg_one_iff`), contradicting the
irrationality of `√2`. -/
lemma cos_pi_mul_sqrt_two_gt_neg_one : -1 < Real.cos (π * Real.sqrt 2) := by
  have hge : -1 ≤ Real.cos (π * Real.sqrt 2) := Real.neg_one_le_cos _
  rcases lt_or_eq_of_le hge with h | h
  · exact h
  · exfalso
    have hEq : Real.cos (π * Real.sqrt 2) = -1 := h.symm
    obtain ⟨k, hk⟩ := (cos_pi_mul_eq_neg_one_iff (Real.sqrt 2)).mp hEq
    have hirr : Irrational (Real.sqrt 2) := Nat.prime_two.irrational_sqrt
    exact hirr ⟨(1 + 2 * k : ℚ), by push_cast; linarith⟩

/-! ## §5 `1 + 2 · cos(π · √2) ≠ 0` via irrationality. -/

/-- **`1 + 2 · cos(π · √2) ≠ 0`.**  Equality would give `cos(π · √2) = -1/2`,
forcing `√2 = 2k/3` rational (via r212's `cos_pi_mul_eq_neg_half_imp_rational`).
Contradicts irrationality of `√2`. -/
lemma one_add_two_cos_pi_mul_sqrt_two_ne_zero :
    1 + 2 * Real.cos (π * Real.sqrt 2) ≠ 0 := by
  intro hEq
  obtain ⟨k, hk⟩ := cos_pi_mul_eq_neg_half_imp_rational (Real.sqrt 2) hEq
  have hirr : Irrational (Real.sqrt 2) := Nat.prime_two.irrational_sqrt
  exact hirr ⟨(2 * k / 3 : ℚ), by push_cast; linarith⟩

/-! ## §6 `|1 + 2 · cos(π · √2)| ∈ (0, 1)`. -/

/-- Strictly positive: from §5. -/
lemma abs_one_add_two_cos_pi_mul_sqrt_two_pos :
    0 < |1 + 2 * Real.cos (π * Real.sqrt 2)| :=
  abs_pos.mpr one_add_two_cos_pi_mul_sqrt_two_ne_zero

/-- Strictly less than one: from §3 and §4. -/
lemma abs_one_add_two_cos_pi_mul_sqrt_two_lt_one :
    |1 + 2 * Real.cos (π * Real.sqrt 2)| < 1 := by
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · linarith [cos_pi_mul_sqrt_two_gt_neg_one]
  · linarith [cos_pi_mul_sqrt_two_neg]

/-! ## §7 The named stone — `σ(α_P) < 0`. -/

/-- **`sigma_alphaP_lt_zero`** — the substrate sign at the P vs NP pillar.

`σ(α_P) < 0` where α_P = √2.  Consequence: the substrate observable at
α_P has envelope `a^σ` with σ < 0 — the amplitude DECAYS toward the past
(a → 0).  Contrast: α_YM has σ = 1 (linear growth), α_Poincaré and α_RH
have σ = 0 (constant amplitude). -/
theorem sigma_alphaP_lt_zero :
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) < 0 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  apply Real.logb_neg (by norm_num : (1 : ℝ) < 3)
  · exact abs_one_add_two_cos_pi_mul_sqrt_two_pos
  · exact abs_one_add_two_cos_pi_mul_sqrt_two_lt_one

/-! ## §8 Elevated to r223's `SubstrateOscillator`. -/

/-- **`SO_αP_sigma_neg`** — the r223 `SubstrateOscillator` method form.

For every data-fit `A ≠ 0` and every `φ₀`, the α_P substrate oscillator has
`sigma < 0`.  Universal over the two data-fit parameters — the sign is
pillar-intrinsic, not tuning-dependent. -/
theorem SO_αP_sigma_neg (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αP A φ₀ hA).sigma < 0 := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt 2) < 0
  exact sigma_alphaP_lt_zero

/-! ## §9 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaPSigmaNegative.one_lt_sqrt_two
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.sqrt_two_lt_three_halves
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.pi_lt_pi_mul_sqrt_two
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.pi_mul_sqrt_two_lt_three_pi_div_two
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.cos_pi_mul_sqrt_two_neg
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.cos_pi_mul_sqrt_two_gt_neg_one
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.one_add_two_cos_pi_mul_sqrt_two_ne_zero
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.abs_one_add_two_cos_pi_mul_sqrt_two_pos
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.abs_one_add_two_cos_pi_mul_sqrt_two_lt_one
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.sigma_alphaP_lt_zero
#print axioms PrincipiaTractalis.AlphaPSigmaNegative.SO_αP_sigma_neg

end PrincipiaTractalis.AlphaPSigmaNegative
