/-
# PF.Analytic.PilotBoxes.R1_c9_2_r1_50_poc_pointwise_2026_10_15

**Cauchy–Schwarz pointwise-form pilot at c = 9/2.**

Follows the recipe of the c = 11/2 proof-of-concept at `d47577f1`: the
aggregate Cauchy–Schwarz form

  (c²·Re Λ₀ + c·Im Λ₀)² ≤ c²(c²+1)·(Re² + Im²) ≤ c²(c²+1)·B²

replaces the pilot-1..13 component-wise triangle (which fails here because
`(c² + c)·B > 1` once `c > 1/((√5-1)/(2·B))` ≈ 3.69). Combined with
uniform `‖Λ₀‖ ≤ 50/1727` plus the exact algebra
`Re ξ(1+it) = (1 − t²·Re Λ₀ − t·Im Λ₀)/2`.

Parameters:
* `c = 9/2`, `r = 1/50`, box = `[224/50, 226/50]  (= [4.48, 4.52])`.
* `Mc_lb = 1/8`, `L = 1`, `L · r = 1/50 < 1/8` ✓.
* Gate 1 squared: `c²(c²+1)·B² = 4303125/11930116` ≤ `(1 − 2·Mc_lb)² = 9/16`.
* L=1 at |t| ≤ 113/25: `(1+2|t|)·B + (t²+|t|)·B ≤ 2` ✓.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c9_2_r1_50_poc_pointwise_20261015

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

theorem pilot_r1_hvalue_lb_at_c9_2_r1_50 :
    (1/8 : ℝ) ≤ (riemannXiEntire (⟨1, 9/2⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  set re := (completedRiemannZeta₀ (⟨1, 9/2⟩ : ℂ)).re with hre
  set im := (completedRiemannZeta₀ (⟨1, 9/2⟩ : ℂ)).im with him
  have hΛ : ‖completedRiemannZeta₀ (⟨1, 9/2⟩ : ℂ)‖ ≤ 50 / 1727 :=
    lambda0_abs_le_fifty_over_1727 (9/2 : ℝ)
  have hNormSq : re ^ 2 + im ^ 2 ≤ (50 / 1727 : ℝ) ^ 2 := by
    have h1 : re ^ 2 + im ^ 2 = ‖completedRiemannZeta₀ (⟨1, 9/2⟩ : ℂ)‖ ^ 2 :=
      norm_sq_decomp _
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg _) hΛ 2
  -- Cauchy–Schwarz polynomial identity:
  --   (c²·re + c·im)² + (c·re − c²·im)² = (c² + c⁴)·(re² + im²)
  have hCS :
      ((81/4 : ℝ) * re + (9/2) * im) ^ 2
        ≤ (6885/16) * (re ^ 2 + im ^ 2) := by
    nlinarith [sq_nonneg ((9/2 : ℝ) * re - (81/4) * im),
               sq_nonneg re, sq_nonneg im]
  have hQ_sq_bd :
      ((81/4 : ℝ) * re + (9/2) * im) ^ 2 ≤ (3/4 : ℝ) ^ 2 := by
    have hArith :
        (6885/16 : ℝ) * (50 / 1727) ^ 2 ≤ (3/4 : ℝ) ^ 2 := by
      norm_num
    have hChain :
        (6885/16 : ℝ) * (re ^ 2 + im ^ 2)
          ≤ (6885/16) * (50 / 1727) ^ 2 :=
      mul_le_mul_of_nonneg_left hNormSq (by norm_num : (0 : ℝ) ≤ 6885/16)
    linarith
  have hQ_bd :
      (81/4 : ℝ) * re + (9/2) * im ≤ 3/4 := by
    nlinarith [hQ_sq_bd,
               sq_nonneg ((81/4 : ℝ) * re + (9/2) * im - 3/4),
               sq_nonneg ((81/4 : ℝ) * re + (9/2) * im + 3/4)]
  linarith

/-! ## §2 — Gate 2: `|deriv edgeRe t| ≤ 1` on `|t| ≤ 113/25` -/

private lemma gate2_num_bound_c9_2_r1_50 {t : ℝ} (ht : |t| ≤ 113/25) :
    (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (50 / 1727) ≤ 2 := by
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (113/25) ^ 2 := by nlinarith [abs_le.mp ht]
  nlinarith [h_t_sq_bd, h_abs_nn, ht]

theorem norm_deriv_riemannXiEntire_le_one_at_c9_2_r1_50 {t : ℝ}
    (ht : |t| ≤ 113/25) :
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
    have h_sum := gate2_num_bound_c9_2_r1_50 ht
    linarith
  linarith

theorem abs_deriv_edgeRe_le_one_at_c9_2_r1_50 {t : ℝ}
    (ht : |t| ≤ 113/25) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le :
      |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
        ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_one_at_c9_2_r1_50 ht
  linarith

theorem pilot_r1_hbound_c9_2_r1_50 :
    ∀ x ∈ Set.Icc (112/25 : ℝ) (113/25), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 113/25 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_one_at_c9_2_r1_50 hx_abs

/-! ## §3 — The pilot box, closed end-to-end -/

/-- **Pilot** at `c = 9/2` on `[224/50, 226/50]  (= [4.48, 4.52])`. Zero hypotheses, kernel-clean. -/
theorem pilot_r1_box_c9_2_r1_50_poc_closed :
    ∀ t ∈ Icc (112/25 : ℝ) (113/25),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc (112/25 : ℝ) (113/25)
      = Icc ((9/2 : ℝ) - 1/50) ((9/2 : ℝ) + 1/50) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 9/2) (r := 1/50) (L := 1) (Mc_lb := 1/8)
    (by norm_num : (0 : ℝ) ≤ 1/50)
    pilot_r1_hvalue_lb_at_c9_2_r1_50
    ?_
    (by norm_num : (1 : ℝ) * (1/50) < 1/8)
  intro x hx
  have hx' : x ∈ Icc (112/25 : ℝ) (113/25) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_c9_2_r1_50 x hx'

end

/-! ## §Axiom check -/

#print axioms norm_sq_decomp
#print axioms pilot_r1_hvalue_lb_at_c9_2_r1_50
#print axioms gate2_num_bound_c9_2_r1_50
#print axioms norm_deriv_riemannXiEntire_le_one_at_c9_2_r1_50
#print axioms abs_deriv_edgeRe_le_one_at_c9_2_r1_50
#print axioms pilot_r1_hbound_c9_2_r1_50
#print axioms pilot_r1_box_c9_2_r1_50_poc_closed

end PilotR1Box_c9_2_r1_50_poc_pointwise_20261015
end PrincipiaTractalis
