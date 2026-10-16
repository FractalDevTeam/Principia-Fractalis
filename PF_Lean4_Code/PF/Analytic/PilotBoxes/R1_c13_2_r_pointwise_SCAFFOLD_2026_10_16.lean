/-
# PF.Analytic.PilotBoxes.R1_c13_2_r_pointwise_SCAFFOLD_2026_10_16

**Gate-1 pilot SCAFFOLD at c = 13/2, r = 1/16.** Mirror of the c = 6 SCAFFOLD
for the adjacent-box pilot. Box `[103/16, 105/16] = [6.4375, 6.5625]`.

### Explicit parameters

* `c = 13/2 = 6.5`, `r = 1/16`, box `= [103/16, 105/16]`.
* `Mc_lb = 1/8`, `L = 1`, strict margin: `L · r = 1/16 < 1/8 = Mc_lb` ✓.
* Gate-1 arithmetic (from `re_xi_at_s` at σ=1, t=13/2):
    `Re ξ(1 + (13/2)i) = (1 - (13/2)² · Re Λ₀ - (13/2) · Im Λ₀) / 2`.
  Target `Re ξ(1 + (13/2)i) ≥ 1/8`
    ⟺ `1 - (13/2)² · Re Λ₀ - (13/2) · Im Λ₀ ≥ 1/4`
    ⟺ `(13/2)² · Re Λ₀ + (13/2) · Im Λ₀ ≤ 3/4`
    ⟺ `(169/4) · Re Λ₀ + (13/2) · Im Λ₀ ≤ 3/4` — the input numeric hypothesis.
* Gate-2 cross-multiplied inequality at `|t| ≤ 105/16`:
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
namespace PilotR1Box_c13_2_r_pointwise_SCAFFOLD_20261016

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — Gate 1 (conditional): `1/8 ≤ Re ξ(1 + (13/2)i)` from Λ₀ slots -/

/-- **Gate 1 for the c = 13/2 pilot (CONDITIONAL).** Given rational enclosure
bounds on `(Re, Im) Λ₀(1 + (13/2)i)` and the numeric gate inequality
`(169/4) · R_ub + (13/2) · I_ub ≤ 3/4`, concludes
`1/8 ≤ Re ξ(1 + (13/2)i)`. -/
theorem pilot_r1_hvalue_lb_at_c13_2_scaffold
    (R_lb R_ub I_lb I_ub : ℝ)
    (hR_lb : R_lb ≤ (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).re)
    (hR_ub : (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).re ≤ R_ub)
    (hI_lb : I_lb ≤ (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).im)
    (hI_ub : (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).im ≤ I_ub)
    (h_gate : (169/4 : ℝ) * R_ub + (13/2) * I_ub ≤ 3/4) :
    (1 / 8 : ℝ) ≤ (riemannXiEntire (⟨1, 13/2⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  set re := (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).re with hre_def
  set im := (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).im with him_def
  have h_re_up : re ≤ R_ub := hR_ub
  have h_im_up : im ≤ I_ub := hI_ub
  have h_combo : (169/4 : ℝ) * re + (13/2 : ℝ) * im ≤ 3/4 := by
    have h_c2 : (169/4 : ℝ) * re ≤ (169/4 : ℝ) * R_ub :=
      mul_le_mul_of_nonneg_left h_re_up (by norm_num : (0 : ℝ) ≤ 169/4)
    have h_c  : (13/2 : ℝ) * im ≤ (13/2 : ℝ) * I_ub :=
      mul_le_mul_of_nonneg_left h_im_up (by norm_num : (0 : ℝ) ≤ 13/2)
    linarith
  -- The goal after `rw [re_xi_at_s]` is
  --   1/8 ≤ (1 + (1·0 - (13/2)²) · re - (13/2)·(2·1 - 1) · im) / 2
  -- which reduces to (169/4) · re + (13/2) · im ≤ 3/4.
  have hNum :
      (1 * (1 - 1) - (13/2 : ℝ) ^ 2) * re - (13/2 : ℝ) * (2 * 1 - 1) * im
        = -((169/4 : ℝ) * re + (13/2) * im) := by ring
  linarith

/-! ## §2 — Gate 2 (unconditional): `|deriv edgeRe t| ≤ 1` on `|t| ≤ 105/16` -/

/-- Numerator-norm bound used by `‖deriv ξ(1+it)‖ ≤ 1` at `|t| ≤ 105/16`. -/
private lemma gate2_num_bound_c13_2_r1_16 {t : ℝ} (ht : |t| ≤ 105/16) :
    (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (50 / 1727) ≤ 2 := by
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (105/16) ^ 2 := by nlinarith [abs_le.mp ht]
  nlinarith [h_t_sq_bd, h_abs_nn, ht]

/-- **Gate 2 numerator norm.** For `|t| ≤ 105/16`,
`‖(2s - 1) · Λ₀ + s(s - 1) · Λ₀'‖ ≤ 2`, hence `‖deriv ξ‖ = ‖·‖/2 ≤ 1`. -/
theorem norm_deriv_riemannXiEntire_le_one_at_t_le_c13_2_r {t : ℝ}
    (ht : |t| ≤ (13/2 + 1/16 : ℝ)) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  have ht' : |t| ≤ 105/16 := by
    have : (13/2 + 1/16 : ℝ) = 105/16 := by norm_num
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
    have h_sum := gate2_num_bound_c13_2_r1_16 ht'
    linarith
  linarith

/-- Chain-rule descent: `|deriv edgeRe t| ≤ ‖deriv ξ(1+it)‖ ≤ 1`. -/
theorem abs_deriv_edgeRe_le_one_at_t_le_c13_2_r {t : ℝ}
    (ht : |t| ≤ (13/2 + 1/16 : ℝ)) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le :
      |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
        ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_one_at_t_le_c13_2_r ht
  linarith

/-- Specialisation of Gate 2 to the box `[103/16, 105/16]`. -/
theorem pilot_r1_hbound_c13_2_r1_16 :
    ∀ x ∈ Set.Icc ((103 : ℝ) / 16) (105 / 16), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ (13/2 + 1/16 : ℝ) := by
    have heq : (13/2 + 1/16 : ℝ) = 105/16 := by norm_num
    rw [heq, abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_one_at_t_le_c13_2_r hx_abs

/-! ## §3 — SCAFFOLD composition: conditional pilot box -/

/-- **SCAFFOLD** final c = 13/2 pilot (CONDITIONAL). -/
theorem pilot_r1_box_c13_2_r1_16_pointwise_closed
    (R_lb R_ub I_lb I_ub : ℝ)
    (hR_lb : R_lb ≤ (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).re)
    (hR_ub : (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).re ≤ R_ub)
    (hI_lb : I_lb ≤ (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).im)
    (hI_ub : (completedRiemannZeta₀ (⟨1, 13/2⟩ : ℂ)).im ≤ I_ub)
    (h_gate : (169/4 : ℝ) * R_ub + (13/2) * I_ub ≤ 3/4) :
    ∀ t ∈ Icc ((103/16 : ℝ)) (105/16),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((103/16 : ℝ)) (105/16)
      = Icc ((13/2 : ℝ) - 1/16) ((13/2 : ℝ) + 1/16) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 13/2) (r := 1/16) (L := 1) (Mc_lb := 1/8)
    (by norm_num : (0 : ℝ) ≤ 1/16)
    (pilot_r1_hvalue_lb_at_c13_2_scaffold R_lb R_ub I_lb I_ub
      hR_lb hR_ub hI_lb hI_ub h_gate)
    ?_
    (by norm_num : (1 : ℝ) * (1/16) < 1/8)
  intro x hx
  have hx' : x ∈ Icc ((103/16 : ℝ)) (105/16) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_c13_2_r1_16 x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_hvalue_lb_at_c13_2_scaffold
#print axioms gate2_num_bound_c13_2_r1_16
#print axioms norm_deriv_riemannXiEntire_le_one_at_t_le_c13_2_r
#print axioms abs_deriv_edgeRe_le_one_at_t_le_c13_2_r
#print axioms pilot_r1_hbound_c13_2_r1_16
#print axioms pilot_r1_box_c13_2_r1_16_pointwise_closed

end PilotR1Box_c13_2_r_pointwise_SCAFFOLD_20261016
end PrincipiaTractalis
