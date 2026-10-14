/-
# PF.Analytic.PilotBoxes.R1_c1_5_r0_1_2026_10_14

**PILOT 5' (Prong B — fill left gap toward endpoint neighborhood).**

Specialises `CenteredFormBridge20261013.R1_box_centered_of_lb` at pilot box
`(c = 1/5, r = 1/10)`:

* Box = `[1/10, 3/10]` — closes the gap between pilot 2's left endpoint
  `3/10` and the endpoint `R1_on_neighborhood` region near `t = 0`.
* `Mc_lb = 1/4`, `L = 1`, `L · r = 1/10 < 1/4` ✓.

**Why `c = 1/5` and `r = 1/10`:** this is the symmetric left-prong of
pilot 2 (which runs `[3/10, 7/10]` from `c = 1/2, r = 1/5`). Gate 1 at
`c = 1/5`: `(1 − (1/25 + 1/5)·(2/21))/2 = (1 − 4/175)/2 = 171/350 ≈ 0.489`,
very comfortable margin (vs. pilot 6's `1/100`). Gate 2 at `|t| ≤ 3/10`
is correspondingly loose.

After this pilot (and in combination with pilot 6), R1 kernel-clean on
**connected `[1/10, 2]`** — pilots 5' ∪ 2 ∪ 4 ∪ 3 ∪ 5 ∪ 6. 1.9-wide
positive-length segment, 15% of the full R1 target `[0, 13]`.

Derivative-modulus chain at `|t| ≤ 3/10`:
  `(1 + 2·|t|)·(2/21) + (t² + |t|)·(2/21) ≤ 199/1050`,
  giving `‖deriv ξ‖ ≤ 199/2100 ≪ 1`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0TightBounds_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c1_5_r0_1_20261014

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0TightBounds20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — `1/4 ≤ Re ξ(1 + i/5)` -/

theorem pilot_r1_hvalue_lb_at_one_fifth :
    (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 1 / 5⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  have hΛ := lambda0_abs_le_two_twentyfirsts (1 / 5 : ℝ)
  have h_re_abs :
      |(completedRiemannZeta₀ (⟨1, 1 / 5⟩ : ℂ)).re| ≤ 2 / 21 :=
    (abs_re_le_norm _).trans hΛ
  have h_im_abs :
      |(completedRiemannZeta₀ (⟨1, 1 / 5⟩ : ℂ)).im| ≤ 2 / 21 :=
    (abs_im_le_norm _).trans hΛ
  have h_re_bd := abs_le.mp h_re_abs
  have h_im_bd := abs_le.mp h_im_abs
  nlinarith [h_re_bd.1, h_re_bd.2, h_im_bd.1, h_im_bd.2]

/-! ## §2 — Derivative bound on `|t| ≤ 3/10` -/

theorem norm_deriv_riemannXiEntire_le_at_t_le_3_10 {t : ℝ} (ht : |t| ≤ 3 / 10) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_two_twentyfirsts t
  have h_Λ' := lambda0_prime_abs_le_two_twentyfirsts t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (3 / 10) ^ 2 := by nlinarith [abs_le.mp ht]
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

theorem abs_deriv_edgeRe_le_at_t_le_3_10 {t : ℝ} (ht : |t| ≤ 3 / 10) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le : |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
                 ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_at_t_le_3_10 ht
  linarith

theorem pilot_r1_hbound_at_one_fifth :
    ∀ x ∈ Set.Icc ((1 : ℝ) / 10) (3 / 10), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 3 / 10 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_at_t_le_3_10 hx_abs

/-! ## §3 — PILOT 5' BOX, closed end-to-end -/

/-- **PILOT 5'.** R1 on `[1/10, 3/10]`, adjacent to pilot 2's left endpoint,
extending the connected R1-coverage (jointly with pilot 6) to `[1/10, 2]`.
Zero hypotheses, kernel-clean. -/
theorem pilot_r1_box_c1_5_r0_1_closed :
    ∀ t ∈ Icc ((1 : ℝ) / 10) (3 / 10),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((1 : ℝ) / 10) (3 / 10)
      = Icc ((1 / 5 : ℝ) - 1 / 10) ((1 / 5 : ℝ) + 1 / 10) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 1 / 5) (r := 1 / 10) (L := 1) (Mc_lb := 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 10)
    pilot_r1_hvalue_lb_at_one_fifth
    ?_
    (by norm_num : (1 : ℝ) * (1 / 10) < 1 / 4)
  intro x hx
  have hx' : x ∈ Icc ((1 : ℝ) / 10) (3 / 10) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_at_one_fifth x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_hvalue_lb_at_one_fifth
#print axioms norm_deriv_riemannXiEntire_le_at_t_le_3_10
#print axioms abs_deriv_edgeRe_le_at_t_le_3_10
#print axioms pilot_r1_hbound_at_one_fifth
#print axioms pilot_r1_box_c1_5_r0_1_closed

end PilotR1Box_c1_5_r0_1_20261014
end PrincipiaTractalis
