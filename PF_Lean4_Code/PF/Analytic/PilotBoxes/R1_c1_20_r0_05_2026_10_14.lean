/-
# PF.Analytic.PilotBoxes.R1_c1_20_r0_05_2026_10_14

**SEVENTH PILOT BOX (Prong B tail — close down to the endpoint `t = 0`).**

Specialises `CenteredFormBridge20261013.R1_box_centered_of_lb` at pilot box
`(c = 1/20, r = 1/20)`:

* Box = `[0, 1/10]` — closes the gap between the endpoint `t = 0`
  (where `ξ(1)` is real and positive) and pilot 5''s left endpoint `1/10`.
* `Mc_lb = 1/4`, `L = 1`, `L · r = 1/20 < 1/4` ✓.

**Why `c = 1/20`, not pushing further right past `c = 9/5`:** the rightward
prong hit the natural ceiling of the uniform `‖Λ₀‖ ≤ 2/21` bound. The max
feasible `c` satisfying `(c² + c)·(2/21) ≤ 1/2` is `c = (−1 + √22)/2 ≈ 1.845`
(pilot 6 at `c = 9/5 = 1.800` sat on margin `1/100`). Extending right of
`c = 2` requires either a `|t|`-dependent Λ₀ bound (replacing the uniform)
or a different `Mc_lb` strategy at larger `c` — both are new research
directions, not pilot execution. So pilot 7 completes the LEFT prong by
closing to the endpoint.

Gate 1 at `c = 1/20`: `B = (1/400 + 1/20)·(2/21) = 1/200`, margin
`(1 − 1/200)/2 − 1/4 = 99/400 ≈ 0.2475` — the most comfortable margin of
the entire pilot block.

After this pilot, R1 kernel-clean on **connected `[0, 2]`** — pilots
7 ∪ 5' ∪ 2 ∪ 4 ∪ 3 ∪ 5 ∪ 6. 2.0-wide positive-length segment, 15.4%
of the full R1 target `[0, 13]`.

Derivative-modulus chain at `|t| ≤ 1/10`:
  `(1 + 1/5)·(2/21) + (1/100 + 1/10)·(2/21) = (131/100)·(2/21) ≈ 0.125`,
  giving `‖deriv ξ‖ ≤ 131/4200 ≪ 1`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0TightBounds_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c1_20_r0_05_20261014

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0TightBounds20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — `1/4 ≤ Re ξ(1 + i/20)` -/

theorem pilot_r1_hvalue_lb_at_one_twentieth :
    (1 / 4 : ℝ) ≤ (riemannXiEntire (⟨1, 1 / 20⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  have hΛ := lambda0_abs_le_two_twentyfirsts (1 / 20 : ℝ)
  have h_re_abs :
      |(completedRiemannZeta₀ (⟨1, 1 / 20⟩ : ℂ)).re| ≤ 2 / 21 :=
    (abs_re_le_norm _).trans hΛ
  have h_im_abs :
      |(completedRiemannZeta₀ (⟨1, 1 / 20⟩ : ℂ)).im| ≤ 2 / 21 :=
    (abs_im_le_norm _).trans hΛ
  have h_re_bd := abs_le.mp h_re_abs
  have h_im_bd := abs_le.mp h_im_abs
  nlinarith [h_re_bd.1, h_re_bd.2, h_im_bd.1, h_im_bd.2]

/-! ## §2 — Derivative bound on `|t| ≤ 1/10` -/

theorem norm_deriv_riemannXiEntire_le_at_t_le_1_10 {t : ℝ} (ht : |t| ≤ 1 / 10) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_two_twentyfirsts t
  have h_Λ' := lambda0_prime_abs_le_two_twentyfirsts t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (1 / 10) ^ 2 := by nlinarith [abs_le.mp ht]
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

theorem abs_deriv_edgeRe_le_at_t_le_1_10 {t : ℝ} (ht : |t| ≤ 1 / 10) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le : |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
                 ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_at_t_le_1_10 ht
  linarith

theorem pilot_r1_hbound_at_one_twentieth :
    ∀ x ∈ Set.Icc (0 : ℝ) (1 / 10), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 1 / 10 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_at_t_le_1_10 hx_abs

/-! ## §3 — THE SEVENTH PILOT BOX, closed end-to-end -/

/-- **SEVENTH PILOT.** R1 on `[0, 1/10]`, closing the connected
R1-coverage all the way down to the endpoint `t = 0`. Zero hypotheses,
kernel-clean. -/
theorem pilot_r1_box_c1_20_r0_05_closed :
    ∀ t ∈ Icc (0 : ℝ) (1 / 10),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc (0 : ℝ) (1 / 10)
      = Icc ((1 / 20 : ℝ) - 1 / 20) ((1 / 20 : ℝ) + 1 / 20) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 1 / 20) (r := 1 / 20) (L := 1) (Mc_lb := 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 20)
    pilot_r1_hvalue_lb_at_one_twentieth
    ?_
    (by norm_num : (1 : ℝ) * (1 / 20) < 1 / 4)
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) (1 / 10) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_at_one_twentieth x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_hvalue_lb_at_one_twentieth
#print axioms norm_deriv_riemannXiEntire_le_at_t_le_1_10
#print axioms abs_deriv_edgeRe_le_at_t_le_1_10
#print axioms pilot_r1_hbound_at_one_twentieth
#print axioms pilot_r1_box_c1_20_r0_05_closed

end PilotR1Box_c1_20_r0_05_20261014
end PrincipiaTractalis
