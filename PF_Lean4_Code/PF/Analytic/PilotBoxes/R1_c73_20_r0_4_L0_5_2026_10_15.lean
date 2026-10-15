/-
# PF.Analytic.PilotBoxes.R1_c73_20_r0_4_L0_5_2026_10_15

**THIRTEENTH PILOT BOX — near the 50/1727 ceiling.**

Specialises `CenteredFormBridge20261013.R1_box_centered_of_lb` at
`(c = 73/20, r = 2/5, L = 1/2)`:

* Box = `[13/4, 81/20]` = `[3.25, 4.05]` — extends past pilot 12's `[16/5, 4]`.
* `Mc_lb = 1/4`, `L = 1/2`, `L · r = 1/5 < 1/4` ✓.

**Why `c = 73/20`:** this is near the feasible-`c` ceiling under `‖Λ₀‖ ≤
50/1727` (which gives `c ≤ (-1 + √70.08)/2 ≈ 3.686`). Gate 1 at `c = 73/20`:
`B = (6789/400)·(50/1727) = 848.625/1727 ≈ 0.4915`, so `(1 − B)/2 ≈ 0.2543`,
margin `≈ 0.004` — the tightest of the entire 13-pilot block.

After this pilot, R1 kernel-clean on **connected `[0, 81/20]`** = `[0, 4.05]`
— 31.2% of the full R1 target `[0, 13]`.

Derivative-modulus chain at `|t| ≤ 81/20`:
  `(1 + 2·|t|)·(50/1727) + (t² + |t|)·(50/1727) ≤ 29.5525·(50/1727)`
   `= 1477.625/1727 ≈ 0.856 ≤ 1`,
giving `‖deriv ξ‖ ≤ 0.856/2 ≈ 0.428 ≤ 1/2` ✓ (confirms `L = 1/2`).

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c73_20_r0_4_L0_5_20261015

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — `1/4 ≤ Re ξ(1 + 73i/20)` -/

theorem pilot_r1_hvalue_lb_at_seventythree_twentieths :
    (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 73 / 20⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  have hΛ := lambda0_abs_le_fifty_over_1727 (73 / 20 : ℝ)
  have h_re_abs :
      |(completedRiemannZeta₀ (⟨1, 73 / 20⟩ : ℂ)).re| ≤ 50 / 1727 :=
    (abs_re_le_norm _).trans hΛ
  have h_im_abs :
      |(completedRiemannZeta₀ (⟨1, 73 / 20⟩ : ℂ)).im| ≤ 50 / 1727 :=
    (abs_im_le_norm _).trans hΛ
  have h_re_bd := abs_le.mp h_re_abs
  have h_im_bd := abs_le.mp h_im_abs
  nlinarith [h_re_bd.1, h_re_bd.2, h_im_bd.1, h_im_bd.2]

/-! ## §2 — Derivative bound `≤ 1/2` on `|t| ≤ 81/20` -/

theorem norm_deriv_riemannXiEntire_le_half_at_t_le_81_20 {t : ℝ}
    (ht : |t| ≤ 81 / 20) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 / 2 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_fifty_over_1727 t
  have h_Λ' := lambda0_prime_abs_le_fifty_over_1727 t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (81 / 20) ^ 2 := by nlinarith [abs_le.mp ht]
  rw [norm_div]
  have h2_norm : ‖(2 : ℂ)‖ = 2 := by
    show ‖((2 : ℕ) : ℂ)‖ = 2
    rw [Complex.norm_natCast]; norm_num
  rw [h2_norm]
  have h_num_bound :
      ‖(2 * (⟨1, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
          + (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
              * deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h_mul1 : ‖2 * (⟨1, t⟩ : ℂ) - 1‖ * ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
                 ≤ (1 + 2 * |t|) * (50 / 1727) := by
      apply mul_le_mul h_2s h_Λ (norm_nonneg _)
      linarith
    have h_mul2 : ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖
                   * ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
                 ≤ (t ^ 2 + |t|) * (50 / 1727) := by
      apply mul_le_mul h_ss h_Λ' (norm_nonneg _)
      linarith
    have h_sum :
        (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (50 / 1727) ≤ 1 := by
      nlinarith [h_t_sq_bd, h_abs_nn, ht]
    linarith
  linarith

theorem abs_deriv_edgeRe_le_half_at_t_le_81_20 {t : ℝ}
    (ht : |t| ≤ 81 / 20) :
    |deriv edgeRe t| ≤ 1 / 2 := by
  rw [deriv_edgeRe_eq]
  have h_re_le : |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
                 ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_half_at_t_le_81_20 ht
  linarith

theorem pilot_r1_hbound_at_seventythree_twentieths :
    ∀ x ∈ Set.Icc ((13 : ℝ) / 4) (81 / 20), |deriv edgeRe x| ≤ 1 / 2 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 81 / 20 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_half_at_t_le_81_20 hx_abs

/-! ## §3 — THE THIRTEENTH PILOT BOX, closed end-to-end -/

/-- **THIRTEENTH PILOT.** R1 on `[13/4, 81/20]` — near the 50/1727 ceiling,
extending the connected R1-coverage to `[0, 81/20]`. Zero hypotheses,
kernel-clean. -/
theorem pilot_r1_box_c73_20_r0_4_L0_5_closed :
    ∀ t ∈ Icc ((13 : ℝ) / 4) (81 / 20),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((13 : ℝ) / 4) (81 / 20)
      = Icc ((73 / 20 : ℝ) - 2 / 5) ((73 / 20 : ℝ) + 2 / 5) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 73 / 20) (r := 2 / 5) (L := 1 / 2) (Mc_lb := 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 2 / 5)
    pilot_r1_hvalue_lb_at_seventythree_twentieths
    ?_
    (by norm_num : (1 / 2 : ℝ) * (2 / 5) < 1 / 4)
  intro x hx
  have hx' : x ∈ Icc ((13 : ℝ) / 4) (81 / 20) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_at_seventythree_twentieths x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_hvalue_lb_at_seventythree_twentieths
#print axioms norm_deriv_riemannXiEntire_le_half_at_t_le_81_20
#print axioms abs_deriv_edgeRe_le_half_at_t_le_81_20
#print axioms pilot_r1_hbound_at_seventythree_twentieths
#print axioms pilot_r1_box_c73_20_r0_4_L0_5_closed

end PilotR1Box_c73_20_r0_4_L0_5_20261015
end PrincipiaTractalis
