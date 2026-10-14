/-
# PF.Analytic.PilotBoxes.R1_c0_5_r0_2_2026_10_14

**SECOND FULL CENTERED-FORM PILOT BOX, 4× WIDER THAN THE FIRST.**

Specialises `CenteredFormBridge20261013.R1_box_centered_of_lb` at `c = 1/2,
r = 1/5` with `Mc_lb = 1/4` and `L = 1`:

  margin check: `L · r = 1/5 < 1/4 = Mc_lb` ✓.

Uses the tighter uniform bounds `‖Λ₀‖, ‖deriv Λ₀‖ ≤ 2/21` from
`Lambda0TightBounds_2026_10_14`. The derivative-modulus chain gives
`|deriv edgeRe x| ≤ 359/2100 ≈ 0.17` on `[3/10, 7/10]`, well under `L = 1`.

Covers `t ∈ [3/10, 7/10]` of R1 — 4× wider than the first pilot box
(`[9/20, 11/20]`, width 1/10).

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0TightBounds_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c0_5_r0_2_20261014

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UniformBound20261014
open PrincipiaTractalis.Lambda0TightBounds20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — Tighter derivative bound `|deriv edgeRe x| ≤ 1` on `|t| ≤ 7/10` -/

theorem norm_deriv_riemannXiEntire_le_at_wide {t : ℝ} (ht : |t| ≤ 7 / 10) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_two_twentyfirsts t
  have h_Λ' := lambda0_prime_abs_le_two_twentyfirsts t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (7 / 10) ^ 2 := by nlinarith [abs_le.mp ht]
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

theorem abs_deriv_edgeRe_le_at_wide {t : ℝ} (ht : |t| ≤ 7 / 10) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le : |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
                 ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_at_wide ht
  linarith

/-- Pilot hbound at `r = 1/5`: `|deriv edgeRe x| ≤ 1` on `[3/10, 7/10]`. -/
theorem pilot_r1_hbound_wide :
    ∀ x ∈ Set.Icc ((3 : ℝ) / 10) (7 / 10), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 7 / 10 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_at_wide hx_abs

/-! ## §2 — THE SECOND PILOT BOX, closed end-to-end -/

/-- **SECOND PILOT, 4× WIDER.** R1 on `[3/10, 7/10]` — zero hypotheses,
kernel-clean. -/
theorem pilot_r1_box_c0_5_r0_2_closed :
    ∀ t ∈ Icc ((3 : ℝ) / 10) (7 / 10),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((3 : ℝ) / 10) (7 / 10)
      = Icc ((1 / 2 : ℝ) - 1 / 5) ((1 / 2 : ℝ) + 1 / 5) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 1 / 2) (r := 1 / 5) (L := 1) (Mc_lb := 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 5)
    pilot_r1_hvalue_lb
    ?_
    (by norm_num : (1 : ℝ) * (1 / 5) < 1 / 4)
  intro x hx
  have hx' : x ∈ Icc ((3 : ℝ) / 10) (7 / 10) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_wide x hx'

end

/-! ## §Axiom check -/

#print axioms norm_deriv_riemannXiEntire_le_at_wide
#print axioms abs_deriv_edgeRe_le_at_wide
#print axioms pilot_r1_hbound_wide
#print axioms pilot_r1_box_c0_5_r0_2_closed

end PilotR1Box_c0_5_r0_2_20261014
end PrincipiaTractalis
