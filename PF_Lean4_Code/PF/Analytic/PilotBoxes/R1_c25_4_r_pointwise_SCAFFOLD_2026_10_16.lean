/-
# PF.Analytic.PilotBoxes.R1_c25_4_r_pointwise_SCAFFOLD_2026_10_16

**Gate-1 pilot SCAFFOLD at c = 25/4, r = 1/16.** Mirror of the c = 6 SCAFFOLD
for the adjacent-box pilot. Box `[99/16, 101/16] = [6.1875, 6.3125]`.

### Explicit parameters

* `c = 25/4 = 6.25`, `r = 1/16`, box `= [99/16, 101/16]`.
* `Mc_lb = 1/8`, `L = 1`, strict margin: `L · r = 1/16 < 1/8 = Mc_lb` ✓.
* Gate-1 arithmetic (from `re_xi_at_s` at σ=1, t=25/4):
    `Re ξ(1 + (25/4)i) = (1 - (25/4)² · Re Λ₀ - (25/4) · Im Λ₀) / 2`.
  Target `Re ξ(1 + (25/4)i) ≥ 1/8`
    ⟺ `1 - (25/4)² · Re Λ₀ - (25/4) · Im Λ₀ ≥ 1/4`
    ⟺ `(25/4)² · Re Λ₀ + (25/4) · Im Λ₀ ≤ 3/4`
    ⟺ `(625/16) · Re Λ₀ + (25/4) · Im Λ₀ ≤ 3/4` — the input numeric hypothesis.
* Gate-2 cross-multiplied inequality at `|t| ≤ 101/16`:
    `(1 + 2|t|) · 50 + (t² + |t|) · 50 ≤ 2 · 1727`, closed by `nlinarith`.

### No sorry, native_decide, axiom, Prop := True. autoImplicit off.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c25_4_r_pointwise_SCAFFOLD_20261016

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — Gate 1 (conditional): `1/8 ≤ Re ξ(1 + (25/4)i)` from Λ₀ slots -/

/-- **Gate 1 for the c = 25/4 pilot (CONDITIONAL).** Given rational enclosure
bounds on `(Re, Im) Λ₀(1 + (25/4)i)` and the numeric gate inequality
`(625/16) · R_ub + (25/4) · I_ub ≤ 3/4`, concludes
`1/8 ≤ Re ξ(1 + (25/4)i)`. -/
theorem pilot_r1_hvalue_lb_at_c25_4_scaffold
    (R_lb R_ub I_lb I_ub : ℝ)
    (hR_lb : R_lb ≤ (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).re)
    (hR_ub : (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).re ≤ R_ub)
    (hI_lb : I_lb ≤ (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).im)
    (hI_ub : (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).im ≤ I_ub)
    (h_gate : (625/16 : ℝ) * R_ub + (25/4) * I_ub ≤ 3/4) :
    (1 / 8 : ℝ) ≤ (riemannXiEntire (⟨1, 25/4⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  set re := (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).re with hre_def
  set im := (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).im with him_def
  have h_re_up : re ≤ R_ub := hR_ub
  have h_im_up : im ≤ I_ub := hI_ub
  have h_combo : (625/16 : ℝ) * re + (25/4 : ℝ) * im ≤ 3/4 := by
    have h_c2 : (625/16 : ℝ) * re ≤ (625/16 : ℝ) * R_ub :=
      mul_le_mul_of_nonneg_left h_re_up (by norm_num : (0 : ℝ) ≤ 625/16)
    have h_c  : (25/4 : ℝ) * im ≤ (25/4 : ℝ) * I_ub :=
      mul_le_mul_of_nonneg_left h_im_up (by norm_num : (0 : ℝ) ≤ 25/4)
    linarith
  -- The goal after `rw [re_xi_at_s]` is
  --   1/8 ≤ (1 + (1·0 - (25/4)²) · re - (25/4)·(2·1 - 1) · im) / 2
  -- which reduces to (625/16) · re + (25/4) · im ≤ 3/4.
  have hNum :
      (1 * (1 - 1) - (25/4 : ℝ) ^ 2) * re - (25/4 : ℝ) * (2 * 1 - 1) * im
        = -((625/16 : ℝ) * re + (25/4) * im) := by ring
  linarith

/-! ## §2 — Gate 2 (unconditional): `|deriv edgeRe t| ≤ 1` on `|t| ≤ 101/16` -/

/-- Numerator-norm bound used by `‖deriv ξ(1+it)‖ ≤ 1` at `|t| ≤ 101/16`. -/
private lemma gate2_num_bound_c25_4_r1_16 {t : ℝ} (ht : |t| ≤ 101/16) :
    (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (50 / 1727) ≤ 2 := by
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (101/16) ^ 2 := by nlinarith [abs_le.mp ht]
  nlinarith [h_t_sq_bd, h_abs_nn, ht]

/-- **Gate 2 numerator norm.** For `|t| ≤ 101/16`,
`‖(2s - 1) · Λ₀ + s(s - 1) · Λ₀'‖ ≤ 2`, hence `‖deriv ξ‖ = ‖·‖/2 ≤ 1`. -/
theorem norm_deriv_riemannXiEntire_le_one_at_t_le_c25_4_r {t : ℝ}
    (ht : |t| ≤ (25/4 + 1/16 : ℝ)) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  have ht' : |t| ≤ 101/16 := by
    have : (25/4 + 1/16 : ℝ) = 101/16 := by norm_num
    rw [this] at ht; exact ht
  rw [deriv_riemannXiEntire_at]
  have h_Λ  := lambda0_abs_le_fifty_over_1727 t
  have h_Λ' := lambda0_prime_abs_le_fifty_over_1727 t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  rw [norm_div]
  have h2_norm : ‖(2 : ℂ)‖ = 2 := by
    show ‖((2 : ℕ) : ℂ)‖ = 2
    rw [Complex.norm_natCast]; norm_num
  rw [h2_norm]
  have h_num_bound :
      ‖(2 * (⟨1, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
          + (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
              * deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h_mul1 :
        ‖2 * (⟨1, t⟩ : ℂ) - 1‖ * ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
          ≤ (1 + 2 * |t|) * (50 / 1727) := by
      apply mul_le_mul h_2s h_Λ (norm_nonneg _)
      linarith
    have h_mul2 :
        ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖
          * ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
          ≤ (t ^ 2 + |t|) * (50 / 1727) := by
      apply mul_le_mul h_ss h_Λ' (norm_nonneg _)
      linarith
    have h_sum := gate2_num_bound_c25_4_r1_16 ht'
    linarith
  linarith

/-- Chain-rule descent: `|deriv edgeRe t| ≤ ‖deriv ξ(1+it)‖ ≤ 1`. -/
theorem abs_deriv_edgeRe_le_one_at_t_le_c25_4_r {t : ℝ}
    (ht : |t| ≤ (25/4 + 1/16 : ℝ)) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le :
      |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
        ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_one_at_t_le_c25_4_r ht
  linarith

/-- Specialisation of Gate 2 to the box `[99/16, 101/16]`. -/
theorem pilot_r1_hbound_c25_4_r1_16 :
    ∀ x ∈ Set.Icc ((99 : ℝ) / 16) (101 / 16), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ (25/4 + 1/16 : ℝ) := by
    have heq : (25/4 + 1/16 : ℝ) = 101/16 := by norm_num
    rw [heq, abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_one_at_t_le_c25_4_r hx_abs

/-! ## §3 — SCAFFOLD composition: conditional pilot box -/

/-- **SCAFFOLD** final c = 25/4 pilot (CONDITIONAL). -/
theorem pilot_r1_box_c25_4_r1_16_pointwise_closed
    (R_lb R_ub I_lb I_ub : ℝ)
    (hR_lb : R_lb ≤ (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).re)
    (hR_ub : (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).re ≤ R_ub)
    (hI_lb : I_lb ≤ (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).im)
    (hI_ub : (completedRiemannZeta₀ (⟨1, 25/4⟩ : ℂ)).im ≤ I_ub)
    (h_gate : (625/16 : ℝ) * R_ub + (25/4) * I_ub ≤ 3/4) :
    ∀ t ∈ Icc ((99/16 : ℝ)) (101/16),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((99/16 : ℝ)) (101/16)
      = Icc ((25/4 : ℝ) - 1/16) ((25/4 : ℝ) + 1/16) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 25/4) (r := 1/16) (L := 1) (Mc_lb := 1/8)
    (by norm_num : (0 : ℝ) ≤ 1/16)
    (pilot_r1_hvalue_lb_at_c25_4_scaffold R_lb R_ub I_lb I_ub
      hR_lb hR_ub hI_lb hI_ub h_gate)
    ?_
    (by norm_num : (1 : ℝ) * (1/16) < 1/8)
  intro x hx
  have hx' : x ∈ Icc ((99/16 : ℝ)) (101/16) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_c25_4_r1_16 x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_hvalue_lb_at_c25_4_scaffold
#print axioms gate2_num_bound_c25_4_r1_16
#print axioms norm_deriv_riemannXiEntire_le_one_at_t_le_c25_4_r
#print axioms abs_deriv_edgeRe_le_one_at_t_le_c25_4_r
#print axioms pilot_r1_hbound_c25_4_r1_16
#print axioms pilot_r1_box_c25_4_r1_16_pointwise_closed

end PilotR1Box_c25_4_r_pointwise_SCAFFOLD_20261016
end PrincipiaTractalis
