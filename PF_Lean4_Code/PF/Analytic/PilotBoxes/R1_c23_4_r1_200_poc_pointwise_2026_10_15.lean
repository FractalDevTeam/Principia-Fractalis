/-
# PF.Analytic.PilotBoxes.R1_c23_4_r1_200_poc_pointwise_2026_10_15

**Cauchy–Schwarz pointwise-form pilot at c = 23/4.**

Follows the recipe of the c = 11/2 proof-of-concept at `d47577f1`: the
aggregate Cauchy–Schwarz form

  (c²·Re Λ₀ + c·Im Λ₀)² ≤ c²(c²+1)·(Re² + Im²) ≤ c²(c²+1)·B²

replaces the pilot-1..13 component-wise triangle (which fails here because
`(c² + c)·B > 1` once `c > 1/((√5-1)/(2·B))` ≈ 3.69). Combined with
uniform `‖Λ₀‖ ≤ 50/1727` plus the exact algebra
`Re ξ(1+it) = (1 − t²·Re Λ₀ − t·Im Λ₀)/2`.

Parameters:
* `c = 23/4`, `r = 1/200`, box = `[1149/200, 1151/200] (= [5.745, 5.755])`.
* `Mc_lb = 1/100`, `L = 1`, `L · r = 1/200 < 1/100` ✓.
* Gate 1 squared: `c²(c²+1)·B² = 180190625/190881856` ≤ `(1 − 2·Mc_lb)² = 2401/2500`.
* L=1 at |t| ≤ 1151/200: `(1+2|t|)·B + (t²+|t|)·B ≤ 2` ✓.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c23_4_r1_200_poc_pointwise_20261015

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — Gate 1 via Cauchy–Schwarz -/

private lemma norm_sq_decomp (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  linarith [Complex.sq_norm_sub_sq_re z]

theorem pilot_r1_hvalue_lb_at_c23_4_r1_200 :
    (1/100 : ℝ) ≤ (riemannXiEntire (⟨1, 23/4⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  set re := (completedRiemannZeta₀ (⟨1, 23/4⟩ : ℂ)).re with hre
  set im := (completedRiemannZeta₀ (⟨1, 23/4⟩ : ℂ)).im with him
  have hΛ : ‖completedRiemannZeta₀ (⟨1, 23/4⟩ : ℂ)‖ ≤ 50 / 1727 :=
    lambda0_abs_le_fifty_over_1727 (23/4 : ℝ)
  have hNormSq : re ^ 2 + im ^ 2 ≤ (50 / 1727 : ℝ) ^ 2 := by
    have h1 : re ^ 2 + im ^ 2 = ‖completedRiemannZeta₀ (⟨1, 23/4⟩ : ℂ)‖ ^ 2 :=
      norm_sq_decomp _
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg _) hΛ 2
  -- Cauchy–Schwarz polynomial identity:
  --   (c²·re + c·im)² + (c·re − c²·im)² = (c² + c⁴)·(re² + im²)
  have hCS :
      ((529/16 : ℝ) * re + (23/4) * im) ^ 2
        ≤ (288305/256) * (re ^ 2 + im ^ 2) := by
    nlinarith [sq_nonneg ((23/4 : ℝ) * re - (529/16) * im),
               sq_nonneg re, sq_nonneg im]
  have hQ_sq_bd :
      ((529/16 : ℝ) * re + (23/4) * im) ^ 2 ≤ (49/50 : ℝ) ^ 2 := by
    have hArith :
        (288305/256 : ℝ) * (50 / 1727) ^ 2 ≤ (49/50 : ℝ) ^ 2 := by
      norm_num
    have hChain :
        (288305/256 : ℝ) * (re ^ 2 + im ^ 2)
          ≤ (288305/256) * (50 / 1727) ^ 2 :=
      mul_le_mul_of_nonneg_left hNormSq (by norm_num : (0 : ℝ) ≤ 288305/256)
    linarith
  have hQ_bd :
      (529/16 : ℝ) * re + (23/4) * im ≤ 49/50 := by
    nlinarith [hQ_sq_bd,
               sq_nonneg ((529/16 : ℝ) * re + (23/4) * im - 49/50),
               sq_nonneg ((529/16 : ℝ) * re + (23/4) * im + 49/50)]
  linarith

/-! ## §2 — Gate 2: `|deriv edgeRe t| ≤ 1` on `|t| ≤ 1151/200` -/

private lemma gate2_num_bound_c23_4_r1_200 {t : ℝ} (ht : |t| ≤ 1151/200) :
    (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (50 / 1727) ≤ 2 := by
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (1151/200) ^ 2 := by nlinarith [abs_le.mp ht]
  nlinarith [h_t_sq_bd, h_abs_nn, ht]

theorem norm_deriv_riemannXiEntire_le_one_at_c23_4_r1_200 {t : ℝ}
    (ht : |t| ≤ 1151/200) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_fifty_over_1727 t
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
    have h_sum := gate2_num_bound_c23_4_r1_200 ht
    linarith
  linarith

theorem abs_deriv_edgeRe_le_one_at_c23_4_r1_200 {t : ℝ}
    (ht : |t| ≤ 1151/200) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le :
      |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
        ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_one_at_c23_4_r1_200 ht
  linarith

theorem pilot_r1_hbound_c23_4_r1_200 :
    ∀ x ∈ Set.Icc (1149/200 : ℝ) (1151/200), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 1151/200 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_one_at_c23_4_r1_200 hx_abs

/-! ## §3 — The pilot box, closed end-to-end -/

/-- **Pilot** at `c = 23/4` on `[1149/200, 1151/200] (= [5.745, 5.755])`. Zero hypotheses, kernel-clean. -/
theorem pilot_r1_box_c23_4_r1_200_poc_closed :
    ∀ t ∈ Icc (1149/200 : ℝ) (1151/200),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc (1149/200 : ℝ) (1151/200)
      = Icc ((23/4 : ℝ) - 1/200) ((23/4 : ℝ) + 1/200) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 23/4) (r := 1/200) (L := 1) (Mc_lb := 1/100)
    (by norm_num : (0 : ℝ) ≤ 1/200)
    pilot_r1_hvalue_lb_at_c23_4_r1_200
    ?_
    (by norm_num : (1 : ℝ) * (1/200) < 1/100)
  intro x hx
  have hx' : x ∈ Icc (1149/200 : ℝ) (1151/200) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_c23_4_r1_200 x hx'

end

/-! ## §Axiom check -/

#print axioms norm_sq_decomp
#print axioms pilot_r1_hvalue_lb_at_c23_4_r1_200
#print axioms gate2_num_bound_c23_4_r1_200
#print axioms norm_deriv_riemannXiEntire_le_one_at_c23_4_r1_200
#print axioms abs_deriv_edgeRe_le_one_at_c23_4_r1_200
#print axioms pilot_r1_hbound_c23_4_r1_200
#print axioms pilot_r1_box_c23_4_r1_200_poc_closed

end PilotR1Box_c23_4_r1_200_poc_pointwise_20261015
end PrincipiaTractalis
