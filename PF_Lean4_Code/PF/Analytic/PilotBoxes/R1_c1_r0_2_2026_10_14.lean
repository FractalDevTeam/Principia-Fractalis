/-
# PF.Analytic.PilotBoxes.R1_c1_r0_2_2026_10_14

**THIRD FULL CENTERED-FORM PILOT BOX, EXTENDS R1 COVERAGE TO A NEW REGION.**

Specialises `CenteredFormBridge20261013.R1_box_centered_of_lb` at pilot box
`(c = 1, r = 1/5)`:

* Box = `[4/5, 6/5]` — disjoint from the first two pilots' union `[3/10, 7/10]`.
* `Mc_lb = 1/4`, `L = 1`, `L · r = 1/5 < 1/4` ✓.

Combined with pilots 1-2, R1 is now kernel-clean on `[3/10, 7/10] ∪ [4/5, 6/5]`.
(Gap `(7/10, 4/5)` remains — a successor pilot at `c = 3/4, r = 1/20` or similar
closes it; left for a batched campaign.)

Uses the tight uniform bounds `‖Λ₀‖, ‖deriv Λ₀‖ ≤ 2/21`
(`Lambda0TightBounds_2026_10_14`). Derivative-modulus chain at `|t| ≤ 6/5`
gives `|deriv edgeRe x| ≤ 151/525 < 1`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0TightBounds_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c1_r0_2_20261014

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0TightBounds20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — `1/4 ≤ Re ξ(1 + i)` from the tight uniform bound -/

theorem pilot_r1_hvalue_lb_at_one :
    (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 1⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  have hΛ := lambda0_abs_le_two_twentyfirsts (1 : ℝ)
  have h_re_abs :
      |(completedRiemannZeta₀ (⟨1, 1⟩ : ℂ)).re| ≤ 2 / 21 :=
    (abs_re_le_norm _).trans hΛ
  have h_im_abs :
      |(completedRiemannZeta₀ (⟨1, 1⟩ : ℂ)).im| ≤ 2 / 21 :=
    (abs_im_le_norm _).trans hΛ
  have h_re_bd := abs_le.mp h_re_abs
  have h_im_bd := abs_le.mp h_im_abs
  nlinarith [h_re_bd.1, h_re_bd.2, h_im_bd.1, h_im_bd.2]

/-! ## §2 — Derivative bound on `|t| ≤ 6/5` -/

theorem norm_deriv_riemannXiEntire_le_at_t_le_6_5 {t : ℝ} (ht : |t| ≤ 6 / 5) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_two_twentyfirsts t
  have h_Λ' := lambda0_prime_abs_le_two_twentyfirsts t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (6 / 5) ^ 2 := by nlinarith [abs_le.mp ht]
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
    have h_mul1 : ‖2 * (⟨1, t⟩ : ℂ) - 1‖ * ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
                 ≤ (1 + 2 * |t|) * (2 / 21) := by
      apply mul_le_mul h_2s h_Λ (norm_nonneg _)
      linarith
    have h_mul2 : ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖
                   * ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
                 ≤ (t ^ 2 + |t|) * (2 / 21) := by
      apply mul_le_mul h_ss h_Λ' (norm_nonneg _)
      linarith
    have h_sum : (1 + 2 * |t|) * (2 / 21) + (t ^ 2 + |t|) * (2 / 21) ≤ 2 := by
      nlinarith [h_t_sq_bd, h_abs_nn, ht]
    linarith
  linarith

theorem abs_deriv_edgeRe_le_at_t_le_6_5 {t : ℝ} (ht : |t| ≤ 6 / 5) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le : |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
                 ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_at_t_le_6_5 ht
  linarith

/-- Pilot hbound at box `[4/5, 6/5]`: `|deriv edgeRe x| ≤ 1`. -/
theorem pilot_r1_hbound_at_one :
    ∀ x ∈ Set.Icc ((4 : ℝ) / 5) (6 / 5), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 6 / 5 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_at_t_le_6_5 hx_abs

/-! ## §3 — THE THIRD PILOT BOX, closed end-to-end -/

/-- **THIRD PILOT.** R1 on `[4/5, 6/5]` — zero hypotheses, kernel-clean. -/
theorem pilot_r1_box_c1_r0_2_closed :
    ∀ t ∈ Icc ((4 : ℝ) / 5) (6 / 5),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((4 : ℝ) / 5) (6 / 5)
      = Icc ((1 : ℝ) - 1 / 5) ((1 : ℝ) + 1 / 5) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 1) (r := 1 / 5) (L := 1) (Mc_lb := 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 5)
    pilot_r1_hvalue_lb_at_one
    ?_
    (by norm_num : (1 : ℝ) * (1 / 5) < 1 / 4)
  intro x hx
  have hx' : x ∈ Icc ((4 : ℝ) / 5) (6 / 5) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_at_one x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_hvalue_lb_at_one
#print axioms norm_deriv_riemannXiEntire_le_at_t_le_6_5
#print axioms abs_deriv_edgeRe_le_at_t_le_6_5
#print axioms pilot_r1_hbound_at_one
#print axioms pilot_r1_box_c1_r0_2_closed

end PilotR1Box_c1_r0_2_20261014
end PrincipiaTractalis
