/-
# PF.Analytic.PilotBoxes.R1_c18_5_r0_4_L0_5_2026_10_14

**TWELFTH PILOT BOX — wider box via `L = 1/2` on the 50/1727 bound.**

First pilot that pushes past the `c = 18/5 = 3.6` center (previously
blocked under the `1/33` ceiling of `c ≈ 3.593`). Also demonstrates the
`L = 1/2` variant that doubles `r` under the bridge's `L · r < 1/4` gate.

Specialises `CenteredFormBridge20261013.R1_box_centered_of_lb` at
`(c = 18/5, r = 2/5, L = 1/2)`:

* Box = `[16/5, 20/5] = [3.2, 4]` — adjacent to pilot 11's right endpoint `18/5`,
  extends to `t = 4`.
* `Mc_lb = 1/4`, `L = 1/2`, `L · r = 1/5 < 1/4` ✓.

**Why `c = 18/5` works now:** under the previous `1/33` bound, Gate 1 at
`c = 18/5` gave `B = (414/25)·(1/33) ≈ 0.502`, failing. Under the new
`50/1727` bound: `B = (414/25)·(50/1727) = 20700/43175 = 828/1727 ≈ 0.479`,
so `(1 − B)/2 ≈ 0.260 ≥ 1/4` ✓ (margin `≈ 0.010`).

**Why `L = 1/2` works:** the derivative chain `(1 + 2|t|)·BOUND + (t²+|t|)·BOUND`
at `|t| ≤ 4` under `50/1727`: `(9 + 20)·(50/1727) = 1450/1727 ≈ 0.840 ≤ 1`,
giving `‖deriv ξ‖ ≤ 1450/3454 = 725/1727 ≤ 1/2`.

After this pilot, R1 kernel-clean on **connected `[0, 4]`** — pilots
7 ∪ 5' ∪ 2 ∪ 4 ∪ 3 ∪ 5 ∪ 6 ∪ 8 ∪ 9 ∪ 10 ∪ 11 ∪ 12. 30.8% of `[0, 13]`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c18_5_r0_4_L0_5_20261014

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — `1/4 ≤ Re ξ(1 + 18i/5)` under `50/1727` -/

theorem pilot_r1_hvalue_lb_at_eighteen_fifths :
    (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 18 / 5⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  have hΛ := lambda0_abs_le_fifty_over_1727 (18 / 5 : ℝ)
  have h_re_abs :
      |(completedRiemannZeta₀ (⟨1, 18 / 5⟩ : ℂ)).re| ≤ 50 / 1727 :=
    (abs_re_le_norm _).trans hΛ
  have h_im_abs :
      |(completedRiemannZeta₀ (⟨1, 18 / 5⟩ : ℂ)).im| ≤ 50 / 1727 :=
    (abs_im_le_norm _).trans hΛ
  have h_re_bd := abs_le.mp h_re_abs
  have h_im_bd := abs_le.mp h_im_abs
  nlinarith [h_re_bd.1, h_re_bd.2, h_im_bd.1, h_im_bd.2]

/-! ## §2 — Derivative bound ≤ 1/2 on `|t| ≤ 4` -/

theorem norm_deriv_riemannXiEntire_le_half_at_t_le_4 {t : ℝ} (ht : |t| ≤ 4) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 / 2 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_fifty_over_1727 t
  have h_Λ' := lambda0_prime_abs_le_fifty_over_1727 t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (4 : ℝ) ^ 2 := by nlinarith [abs_le.mp ht]
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
    have h_sum : (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (50 / 1727) ≤ 1 := by
      nlinarith [h_t_sq_bd, h_abs_nn, ht]
    linarith
  linarith

theorem abs_deriv_edgeRe_le_half_at_t_le_4 {t : ℝ} (ht : |t| ≤ 4) :
    |deriv edgeRe t| ≤ 1 / 2 := by
  rw [deriv_edgeRe_eq]
  have h_re_le : |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
                 ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_half_at_t_le_4 ht
  linarith

theorem pilot_r1_hbound_at_eighteen_fifths :
    ∀ x ∈ Set.Icc ((16 : ℝ) / 5) 4, |deriv edgeRe x| ≤ 1 / 2 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 4 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_half_at_t_le_4 hx_abs

/-! ## §3 — THE TWELFTH PILOT BOX, closed end-to-end -/

/-- **TWELFTH PILOT.** R1 on `[16/5, 4]`, extending the connected
R1-coverage past the former `1/33` ceiling to `[0, 4]`. First pilot using
the `50/1727` bound AND the `L = 1/2` variant. Zero hypotheses,
kernel-clean. -/
theorem pilot_r1_box_c18_5_r0_4_L0_5_closed :
    ∀ t ∈ Icc ((16 : ℝ) / 5) 4,
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((16 : ℝ) / 5) 4
      = Icc ((18 / 5 : ℝ) - 2 / 5) ((18 / 5 : ℝ) + 2 / 5) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 18 / 5) (r := 2 / 5) (L := 1 / 2) (Mc_lb := 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 2 / 5)
    pilot_r1_hvalue_lb_at_eighteen_fifths
    ?_
    (by norm_num : (1 / 2 : ℝ) * (2 / 5) < 1 / 4)
  intro x hx
  have hx' : x ∈ Icc ((16 : ℝ) / 5) 4 := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_at_eighteen_fifths x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_hvalue_lb_at_eighteen_fifths
#print axioms norm_deriv_riemannXiEntire_le_half_at_t_le_4
#print axioms abs_deriv_edgeRe_le_half_at_t_le_4
#print axioms pilot_r1_hbound_at_eighteen_fifths
#print axioms pilot_r1_box_c18_5_r0_4_L0_5_closed

end PilotR1Box_c18_5_r0_4_L0_5_20261014
end PrincipiaTractalis
