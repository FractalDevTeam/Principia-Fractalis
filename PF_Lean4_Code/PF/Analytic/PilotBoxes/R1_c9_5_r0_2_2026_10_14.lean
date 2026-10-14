/-
# PF.Analytic.PilotBoxes.R1_c9_5_r0_2_2026_10_14

**SIXTH FULL CENTERED-FORM PILOT BOX (Prong A — extend right from pilot 5).**

Specialises `CenteredFormBridge20261013.R1_box_centered_of_lb` at pilot box
`(c = 9/5, r = 1/5)`:

* Box = `[8/5, 2]` — adjacent to pilot 5's right endpoint `8/5`.
* `Mc_lb = 1/4`, `L = 1`, `L · r = 1/5 < 1/4` ✓.

**Why `c = 9/5` (and not `c = 2`):** at `c = 2` the loose triangle bound
gives `Mc_lb ≥ (1 − (4+2)·(2/21))/2 = 3/14 < 1/4`, so Gate 1 of the pilot
algorithm fails. The provable rational lower bound is what matters; the
true `Mc` at `c = 2` is comfortably above `1/4` but we cannot access it
through the current `‖Λ₀‖ ≤ 2/21` chain. The max feasible `c` satisfying
`(c² + c)·(2/21) ≤ 1/2` is `c = (−1 + √22)/2 ≈ 1.845`, so `c = 9/5 = 1.8`
is clean but near the limit (margin `1/100`).

After this pilot, R1 kernel-clean on **connected `[3/10, 2]`** — pilots
2 ∪ 4 ∪ 3 ∪ 5 ∪ 6. 1.7-wide positive-length segment, 13% of the full R1
target `[0, 13]`.

Derivative-modulus chain at `|t| ≤ 2`:
  `(1 + 2·|t|)·(2/21) + (t² + |t|)·(2/21) ≤ 22/21 < 2`,
  giving `‖deriv ξ‖ ≤ 11/21 ≤ 1`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0TightBounds_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c9_5_r0_2_20261014

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0TightBounds20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — `1/4 ≤ Re ξ(1 + 9i/5)` -/

theorem pilot_r1_hvalue_lb_at_nine_fifths :
    (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 9 / 5⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  have hΛ := lambda0_abs_le_two_twentyfirsts (9 / 5 : ℝ)
  have h_re_abs :
      |(completedRiemannZeta₀ (⟨1, 9 / 5⟩ : ℂ)).re| ≤ 2 / 21 :=
    (abs_re_le_norm _).trans hΛ
  have h_im_abs :
      |(completedRiemannZeta₀ (⟨1, 9 / 5⟩ : ℂ)).im| ≤ 2 / 21 :=
    (abs_im_le_norm _).trans hΛ
  have h_re_bd := abs_le.mp h_re_abs
  have h_im_bd := abs_le.mp h_im_abs
  nlinarith [h_re_bd.1, h_re_bd.2, h_im_bd.1, h_im_bd.2]

/-! ## §2 — Derivative bound on `|t| ≤ 2` -/

theorem norm_deriv_riemannXiEntire_le_at_t_le_2 {t : ℝ} (ht : |t| ≤ 2) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_two_twentyfirsts t
  have h_Λ' := lambda0_prime_abs_le_two_twentyfirsts t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith [abs_le.mp ht]
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

theorem abs_deriv_edgeRe_le_at_t_le_2 {t : ℝ} (ht : |t| ≤ 2) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le : |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
                 ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_at_t_le_2 ht
  linarith

theorem pilot_r1_hbound_at_nine_fifths :
    ∀ x ∈ Set.Icc ((8 : ℝ) / 5) 2, |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 2 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_at_t_le_2 hx_abs

/-! ## §3 — THE SIXTH PILOT BOX, closed end-to-end -/

/-- **SIXTH PILOT.** R1 on `[8/5, 2]`, adjacent to pilot 5's right endpoint,
extending the connected R1-coverage to `[3/10, 2]`. Zero hypotheses,
kernel-clean. -/
theorem pilot_r1_box_c9_5_r0_2_closed :
    ∀ t ∈ Icc ((8 : ℝ) / 5) 2,
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((8 : ℝ) / 5) 2
      = Icc ((9 / 5 : ℝ) - 1 / 5) ((9 / 5 : ℝ) + 1 / 5) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 9 / 5) (r := 1 / 5) (L := 1) (Mc_lb := 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 5)
    pilot_r1_hvalue_lb_at_nine_fifths
    ?_
    (by norm_num : (1 : ℝ) * (1 / 5) < 1 / 4)
  intro x hx
  have hx' : x ∈ Icc ((8 : ℝ) / 5) 2 := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_at_nine_fifths x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_hvalue_lb_at_nine_fifths
#print axioms norm_deriv_riemannXiEntire_le_at_t_le_2
#print axioms abs_deriv_edgeRe_le_at_t_le_2
#print axioms pilot_r1_hbound_at_nine_fifths
#print axioms pilot_r1_box_c9_5_r0_2_closed

end PilotR1Box_c9_5_r0_2_20261014
end PrincipiaTractalis
