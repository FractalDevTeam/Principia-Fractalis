/-
# r230: α_QG = √(2π) pillar — σ(α_QG) < 0 (near-critical envelope-decaying tier).

★ 2026-08-12 r230 — elevating the QUANTUM GRAVITY pillar (α_QG = √(2π))
via the sharp SIGN characterisation `σ(α_QG) < 0`. NINTH and FINAL σ-sign
class formalised — **all nine canonical corpus pillars now have their
substrate σ-sign explicit in Lean**. ★

## The completed corpus σ-sign partition

    σ = +1     α_YM = 2                     (r224 linear-growth tier)
    σ > 0      α_Hodge = φ                  (r226 sub-linear growth)
               α_NP = φ + 1/4                (r227)
               α_BSD = 3π/4                  (r228)
    σ = 0      α_Poincaré = 1                (r221 constant-amplitude tier)
               α_RH = 3/2                    (r221)
    σ < 0      α_P = √2                      (r225 envelope-decaying tier)
               α_QG = √(2π) (THIS, near-critical) (r230)
               α_NS = 3π/2                   (r229)

Corpus σ-sign complete. **Nine landings today** (r221–r230) each kernel-clean
under `[propext, Classical.choice, Quot.sound]`.

## What's special about α_QG — near-critical

α_QG's abscissa is `σ(α_QG) ≈ -0.039` — the CLOSEST to zero of all six
irrational corpus pillars. Physically, this means the QG substrate
oscillator's envelope `a^σ` is *barely* decaying (only ~4% envelope
attenuation per factor-3 rescaling in `a`) — a near-marginal case.

The r230 sign proof establishes `σ < 0` (the qualitative direction). A
SHARP bracket `σ ∈ (-0.05, -0.03)` or similar would need Taylor-series
enclosure of `cos(π · √(2π))` (analogous to r212's
`sigma_goldenRatio_ne_half` machinery). r230 does the qualitative claim;
tight numerical bracket is future substrate work.

## What this file proves

α_QG = √(2π). Then π · α_QG = π · √(2π).

1. π-brackets: `π > 3.14` (`Real.pi_gt_d2`), so `2π > 6.28 > 25/4`, so
   `√(2π) > 5/2`. And `π < 3.15` (`Real.pi_lt_d2`), so `2π < 6.30 < 9`,
   so `√(2π) < 3`.
2. Multiplied by π: `5π/2 < π · √(2π) < 3π`.
3. Let `z := π · √(2π) - 2π`. Then `z ∈ (π/2, π)`.
4. `cos(π · √(2π)) = cos(z + 2π) = cos(z) < 0` (r229-style chain via
   `cos_pi_sub` and `cos_pos_of_mem_Ioo`).
5. `cos(π · √(2π)) > -1` via r212's `irrational_sqrt_two_pi`.
6. `1 + 2·cos(π · √(2π)) ≠ 0` via same irrationality trick.
7. `|1 + 2·cos(π · √(2π))| ∈ (0, 1)`.
8. **`sigma_alphaQG_lt_zero`** via `Real.logb_neg`.
9. Elevated to r223: `SO_αQG_sigma_neg`.

## Contents

§0 Local `cos_add_two_pi` (2π periodicity via two `cos_add_pi`).
§1 `√(2π)` brackets: `5/2 < √(2π) < 3`.
§2 π · √(2π) brackets: `5π/2 < π · √(2π) < 3π`.
§3 `cos(π · α_QG) < 0` via 2π shift into (π/2, π), then `cos_pi_sub`.
§4 `cos(π · α_QG) > -1` via irrationality.
§5 `1 + 2·cos(π · α_QG) ≠ 0` via irrationality.
§6 `|1 + 2·cos(π · α_QG)| ∈ (0, 1)`.
§7 **`sigma_alphaQG_lt_zero`** — the named stone.
§8 Elevated to r223: `SO_αQG_sigma_neg`.
§9 Axiom check.

## Scope

* NOT a quantum gravity discharge (no substrate ToE for gravity claims here).
* NOT a substrate derivation of `α_QG = √(2π)`.
* NOT a physical claim about spacetime, gravitational field theory, or
  the cosmological constant (that's α_NS = 3π/2, cf. r229).
* IS the sharp SIGN characterisation of σ at the QG pillar. IS a substrate
  consequence: envelope-decaying observable for α_QG, near-critical (very
  small |σ|).

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.SubstrateOscillator_r223

open scoped Real

namespace PrincipiaTractalis.AlphaQGSigmaNegative

open PrincipiaTractalis.SigmaAbscissa
open PrincipiaTractalis

/-! ## §0 Local: `cos_add_two_pi`. -/

lemma cos_add_two_pi (x : ℝ) : Real.cos (x + 2 * π) = Real.cos x := by
  have h : x + 2 * π = (x + π) + π := by ring
  rw [h, Real.cos_add_pi, Real.cos_add_pi]
  ring

/-! ## §1 `√(2π)` brackets: `5/2 < √(2π) < 3`. -/

/-- **`5/2 < √(2π)`**.  Since `π > 3.14 > 25/8`, we have `2π > 25/4`,
so taking square roots gives `√(2π) > 5/2`. -/
lemma five_halves_lt_sqrt_two_pi : (5 : ℝ) / 2 < Real.sqrt (2 * π) := by
  have h2pi_gt : (25 : ℝ) / 4 < 2 * π := by
    have := Real.pi_gt_d2  -- π > 3.14
    linarith
  have hnn : (0 : ℝ) ≤ 25 / 4 := by norm_num
  have hlt : Real.sqrt (25 / 4) < Real.sqrt (2 * π) :=
    Real.sqrt_lt_sqrt hnn h2pi_gt
  have heq : Real.sqrt ((25 : ℝ) / 4) = 5 / 2 := by
    rw [show ((25 : ℝ) / 4) = (5 / 2) ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 2)
  linarith

/-- **`√(2π) < 3`**.  Since `π < 3.15 < 9/2`, we have `2π < 9`, so
taking square roots gives `√(2π) < 3`. -/
lemma sqrt_two_pi_lt_three : Real.sqrt (2 * π) < 3 := by
  have h2pi_lt : 2 * π < 9 := by
    have := Real.pi_lt_d2  -- π < 3.15
    linarith
  have hlt : Real.sqrt (2 * π) < Real.sqrt 9 :=
    Real.sqrt_lt_sqrt (by positivity) h2pi_lt
  have heq : Real.sqrt (9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)
  linarith

/-! ## §2 π · √(2π) brackets: `5π/2 < π · √(2π) < 3π`. -/

/-- **`5π/2 < π · √(2π)`** — multiply §1 lower bound by π > 0. -/
lemma five_pi_div_two_lt_pi_mul_alphaQG :
    5 * π / 2 < π * Real.sqrt (2 * π) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := five_halves_lt_sqrt_two_pi
  nlinarith

/-- **`π · √(2π) < 3π`** — multiply §1 upper bound by π > 0. -/
lemma pi_mul_alphaQG_lt_three_pi :
    π * Real.sqrt (2 * π) < 3 * π := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have := sqrt_two_pi_lt_three
  nlinarith

/-! ## §3 `cos(π · α_QG) < 0` via 2π shift into (π/2, π). -/

/-- **`cos(π · √(2π)) < 0`.**  Shift by -2π: `z := π·√(2π) - 2π ∈ (π/2, π)`.
Rewrite `cos(z) = -cos(π - z)` with `π - z ∈ (0, π/2)` where cos > 0. -/
lemma cos_pi_mul_alphaQG_neg : Real.cos (π * Real.sqrt (2 * π)) < 0 := by
  set z := π * Real.sqrt (2 * π) - 2 * π with hz_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hz_gt : π / 2 < z := by
    rw [hz_def]; linarith [five_pi_div_two_lt_pi_mul_alphaQG]
  have hz_lt : z < π := by
    rw [hz_def]; linarith [pi_mul_alphaQG_lt_three_pi]
  set w := π - z with hw_def
  have hw_pos : 0 < w := by rw [hw_def]; linarith
  have hw_lt : w < π / 2 := by rw [hw_def]; linarith
  have hw_gt_neg : -(π / 2) < w := by linarith
  have hcos_w_pos : 0 < Real.cos w :=
    Real.cos_pos_of_mem_Ioo ⟨hw_gt_neg, hw_lt⟩
  have hz_eq : z = π - w := by rw [hw_def]; ring
  have hcos_z : Real.cos z = -Real.cos w := by
    rw [hz_eq]; exact Real.cos_pi_sub w
  have heq : π * Real.sqrt (2 * π) = z + 2 * π := by rw [hz_def]; ring
  rw [heq, cos_add_two_pi, hcos_z]
  linarith

/-! ## §4 `cos(π · α_QG) > -1` via irrationality of √(2π). -/

/-- **`cos(π · √(2π)) > -1`.** Equality would give `√(2π) = 1 + 2k` odd
integer via r212's `cos_pi_mul_eq_neg_one_iff`, contradicting r212's
`irrational_sqrt_two_pi`. -/
lemma cos_pi_mul_alphaQG_gt_neg_one :
    -1 < Real.cos (π * Real.sqrt (2 * π)) := by
  have hge : -1 ≤ Real.cos (π * Real.sqrt (2 * π)) := Real.neg_one_le_cos _
  rcases lt_or_eq_of_le hge with h | h
  · exact h
  · exfalso
    have hEq : Real.cos (π * Real.sqrt (2 * π)) = -1 := h.symm
    obtain ⟨k, hk⟩ := (cos_pi_mul_eq_neg_one_iff (Real.sqrt (2 * π))).mp hEq
    exact irrational_sqrt_two_pi ⟨(1 + 2 * k : ℚ), by push_cast; linarith⟩

/-! ## §5 `1 + 2·cos(π · α_QG) ≠ 0` via irrationality. -/

/-- **`1 + 2 · cos(π · √(2π)) ≠ 0`.** Equality would give `√(2π) = 2k/3`
rational via r212's `cos_pi_mul_eq_neg_half_imp_rational`, contradicting
`irrational_sqrt_two_pi`. -/
lemma one_add_two_cos_pi_mul_alphaQG_ne_zero :
    1 + 2 * Real.cos (π * Real.sqrt (2 * π)) ≠ 0 := by
  intro hEq
  obtain ⟨k, hk⟩ :=
    cos_pi_mul_eq_neg_half_imp_rational (Real.sqrt (2 * π)) hEq
  exact irrational_sqrt_two_pi ⟨(2 * k / 3 : ℚ), by push_cast; linarith⟩

/-! ## §6 `|1 + 2 · cos(π · α_QG)| ∈ (0, 1)`. -/

lemma abs_one_add_two_cos_pi_mul_alphaQG_pos :
    0 < |1 + 2 * Real.cos (π * Real.sqrt (2 * π))| :=
  abs_pos.mpr one_add_two_cos_pi_mul_alphaQG_ne_zero

lemma abs_one_add_two_cos_pi_mul_alphaQG_lt_one :
    |1 + 2 * Real.cos (π * Real.sqrt (2 * π))| < 1 := by
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · linarith [cos_pi_mul_alphaQG_gt_neg_one]
  · linarith [cos_pi_mul_alphaQG_neg]

/-! ## §7 The named stone — `σ(α_QG) < 0`. -/

/-- **`sigma_alphaQG_lt_zero`** — the substrate sign at the QG pillar.

`σ(α_QG) < 0` where α_QG = √(2π).  The QG substrate observable has envelope
`a^σ` with σ < 0 (near-critical, |σ| ≈ 0.039 empirically). Amplitude decays
toward the past (a → 0) but only barely — the QG oscillator sits close to
the constant-amplitude tier that hosts α_Poincaré and α_RH. -/
theorem sigma_alphaQG_lt_zero :
    PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) < 0 := by
  unfold PrincipiaTractalis.SigmaAbscissa.sigma
  apply Real.logb_neg (by norm_num : (1 : ℝ) < 3)
  · exact abs_one_add_two_cos_pi_mul_alphaQG_pos
  · exact abs_one_add_two_cos_pi_mul_alphaQG_lt_one

/-! ## §8 Elevated to r223's `SubstrateOscillator`. -/

/-- **`SO_αQG_sigma_neg`** — the r223 `SubstrateOscillator` method form.

For every data-fit `A ≠ 0` and every `φ₀`, the α_QG substrate oscillator has
`sigma < 0`. Universal over data-fit. Completes the corpus σ-sign coverage:
every canonical pillar in `SubstrateOscillator`'s 9-instance list now has
an explicit sign theorem. -/
theorem SO_αQG_sigma_neg (A φ₀ : ℝ) (hA : A ≠ 0) :
    (SO_αQG A φ₀ hA).sigma < 0 := by
  show PrincipiaTractalis.SigmaAbscissa.sigma (Real.sqrt (2 * π)) < 0
  exact sigma_alphaQG_lt_zero

/-! ## §9 Axiom check. -/

#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.cos_add_two_pi
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.five_halves_lt_sqrt_two_pi
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.sqrt_two_pi_lt_three
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.five_pi_div_two_lt_pi_mul_alphaQG
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.pi_mul_alphaQG_lt_three_pi
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.cos_pi_mul_alphaQG_neg
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.cos_pi_mul_alphaQG_gt_neg_one
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.one_add_two_cos_pi_mul_alphaQG_ne_zero
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.abs_one_add_two_cos_pi_mul_alphaQG_pos
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.abs_one_add_two_cos_pi_mul_alphaQG_lt_one
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.sigma_alphaQG_lt_zero
#print axioms PrincipiaTractalis.AlphaQGSigmaNegative.SO_αQG_sigma_neg

end PrincipiaTractalis.AlphaQGSigmaNegative
