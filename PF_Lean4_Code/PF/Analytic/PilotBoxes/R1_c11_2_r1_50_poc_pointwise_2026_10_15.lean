/-
# PF.Analytic.PilotBoxes.R1_c11_2_r1_50_poc_pointwise_2026_10_15

**POC pilot box — first R1 box PAST the 50/1727 Gate-1-with-Mc_lb=1/4 ceiling.**

### What this file is

A proof-of-concept pilot at `(c = 11/2, r = 1/50)` demonstrating that the
pilot-13-style modulus bound `‖Λ₀‖ ≤ 50/1727` can be made to pass `Re ξ > 0`
on an interval STRICTLY PAST the previous uniform ceiling at `c = 81/20 = 4.05`,
by:

1. Dropping the fixed `Mc_lb = 1/4` margin used in pilots 1–13 (that choice
   caps feasible `c` at ≈ 3.69 under the triangle estimate, extended to 4.05
   via sharper arithmetic). Here `Mc_lb = 1/40` — chosen to pass Gate 1 at
   `c = 11/2`.
2. Replacing the pilot-13 Gate-1 proof (component-wise `|Re Λ₀|, |Im Λ₀| ≤ B`
   plus `nlinarith`) with the aggregate Cauchy–Schwarz form
   `(c²·Re Λ₀ + c·Im Λ₀)² ≤ c²(c²+1)·(Re² + Im²) ≤ c²(c²+1)·B²`,
   which is tight at `c = 11/2` where `c²(c²+1)·B² = 37812500/47720464 < 361/400
   = (1 − 2·Mc_lb)²`. The component-wise form fails here because
   `(c² + c)·B > 1`.
3. Keeping Gate-2 at `L = 1` via the existing `norm_two_s_minus_one_le`,
   `norm_s_mul_s_minus_one_le`, `lambda0_abs_le_fifty_over_1727`,
   `lambda0_prime_abs_le_fifty_over_1727` chain. At `|t| ≤ 138/25`,
   `(1 + 2|t|)·(50/1727) + (t² + |t|)·(50/1727) ≤ 2`, giving
   `‖deriv ξ‖ ≤ 1`, hence `|deriv edgeRe t| ≤ 1`.

### What this file is NOT

* **NOT the pointwise-eval framework** promised in the P2 feasibility report.
  The feasibility report's (i) `Re ξ(1+ic)` via certified integral panels is
  not needed yet, because the uniform `‖Λ₀‖ ≤ 50/1727` bound (plus
  Cauchy–Schwarz on components) already proves `Re ξ > 0` up to the true
  uniform-sufficient ceiling `c ≈ 5.88`. Beyond that, panel-level pointwise
  evaluation would be the next step.
* **NOT a connected extension of R1 coverage.** The box `[137/25, 138/25]`
  = `[5.48, 5.52]` is disjoint from pilot 13's `[13/4, 81/20] = [3.25, 4.05]`;
  closing the gap `(4.05, 5.48)` would require more pilots in the same style.
  This POC validates the method; coverage tiling is a follow-on batch.
* **NOT a claim about the open Riemann Hypothesis.** `rh_below_15_conditional`
  is RH on one finite rectangle, classically known since Riemann and Gram.
  Nothing here bears on the open problem.

### Explicit parameters

* `c = 11/2`, `r = 1/50`, so box `= [137/25, 138/25]`.
* `Mc_lb = 1/40`, `L = 1`, `L · r = 1/50 < 1/40 = Mc_lb` ✓ (strict margin).
* Gate 1 cross-multiplied inequality: `37812500 · 400 ≤ 361 · 47720464`,
  i.e. `15 125 000 000 ≤ 17 227 087 504` ✓.
* Gate 2 cross-multiplied inequality: `(1 + 2|t|)·50 + (t² + |t|)·50 ≤ 2·1727`
  at `|t| ≤ 138/25`, closed by `nlinarith`.

### No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c11_2_r1_50_poc_pointwise_20261015

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — Gate 1: `1/40 ≤ Re ξ(1 + 11i/2)` via Cauchy–Schwarz -/

/-- Decomposition of `‖z‖²` into `z.re² + z.im²`. -/
private lemma norm_sq_decomp (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  linarith [Complex.sq_norm_sub_sq_re z]

/-- **Gate 1 for the POC pilot.** At `c = 11/2`, Cauchy–Schwarz on the
components of `Λ₀(1 + 11i/2)` yields `1/40 ≤ Re ξ(1 + 11i/2)`, kernel-clean. -/
theorem pilot_r1_hvalue_lb_at_eleven_halves :
    (1 / 40 : ℝ) ≤ (riemannXiEntire (⟨1, 11 / 2⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  -- after rw: 1/40 ≤ (1 + (1·0 - (11/2)²)·Re Λ₀ - (11/2)·(2·1-1)·Im Λ₀) / 2
  --        =  (1 - (121/4)·Re Λ₀ - (11/2)·Im Λ₀) / 2
  set re := (completedRiemannZeta₀ (⟨1, 11 / 2⟩ : ℂ)).re with hre
  set im := (completedRiemannZeta₀ (⟨1, 11 / 2⟩ : ℂ)).im with him
  have hΛ : ‖completedRiemannZeta₀ (⟨1, 11 / 2⟩ : ℂ)‖ ≤ 50 / 1727 :=
    lambda0_abs_le_fifty_over_1727 (11 / 2 : ℝ)
  -- Step 1: re² + im² ≤ (50/1727)²
  have hNormSq : re ^ 2 + im ^ 2 ≤ (50 / 1727 : ℝ) ^ 2 := by
    have h1 : re ^ 2 + im ^ 2 = ‖completedRiemannZeta₀ (⟨1, 11 / 2⟩ : ℂ)‖ ^ 2 :=
      norm_sq_decomp _
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg _) hΛ 2
  -- Step 2: Cauchy–Schwarz (polynomial identity)
  --   ((121/4)·re + (11/2)·im)² + ((11/2)·re − (121/4)·im)² = (15125/16)·(re² + im²)
  -- Hint: sq_nonneg ((11/2)·re − (121/4)·im)
  have hCS :
      ((121 / 4 : ℝ) * re + (11 / 2) * im) ^ 2
        ≤ (15125 / 16) * (re ^ 2 + im ^ 2) := by
    nlinarith [sq_nonneg ((11 / 2 : ℝ) * re - (121 / 4) * im),
               sq_nonneg re, sq_nonneg im]
  -- Step 3: scaled norm bound ⇒ Q² ≤ (19/20)²
  have hQ_sq_bd : ((121 / 4 : ℝ) * re + (11 / 2) * im) ^ 2 ≤ (19 / 20 : ℝ) ^ 2 := by
    have hArith : (15125 / 16 : ℝ) * (50 / 1727) ^ 2 ≤ (19 / 20 : ℝ) ^ 2 := by
      norm_num
    have hChain :
        (15125 / 16 : ℝ) * (re ^ 2 + im ^ 2) ≤ (15125 / 16) * (50 / 1727) ^ 2 :=
      mul_le_mul_of_nonneg_left hNormSq (by norm_num : (0 : ℝ) ≤ 15125 / 16)
    linarith
  -- Step 4: from Q² ≤ (19/20)² (and 19/20 > 0), derive Q ≤ 19/20
  have hQ_bd : (121 / 4 : ℝ) * re + (11 / 2) * im ≤ 19 / 20 := by
    nlinarith [hQ_sq_bd,
               sq_nonneg ((121 / 4 : ℝ) * re + (11 / 2) * im - 19 / 20),
               sq_nonneg ((121 / 4 : ℝ) * re + (11 / 2) * im + 19 / 20)]
  -- Step 5: close
  have hNum : (1 * (1 - 1) - (11 / 2 : ℝ) ^ 2) * re
                - (11 / 2) * (2 * 1 - 1) * im
              = -((121 / 4) * re + (11 / 2) * im) := by ring
  linarith [hQ_bd]

/-! ## §2 — Gate 2: `|deriv edgeRe t| ≤ 1` on `|t| ≤ 138/25` -/

/-- Numerator-norm bound used by `‖deriv ξ(1+it)‖ ≤ 1`: at `|t| ≤ 138/25`,
`(1 + 2|t|)·(50/1727) + (t² + |t|)·(50/1727) ≤ 2`. -/
private lemma gate2_num_bound {t : ℝ} (ht : |t| ≤ 138 / 25) :
    (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (50 / 1727) ≤ 2 := by
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (138 / 25) ^ 2 := by nlinarith [abs_le.mp ht]
  nlinarith [h_t_sq_bd, h_abs_nn, ht]

/-- **Gate 2 numerator norm.** For `|t| ≤ 138/25`,
`‖(2s-1)·Λ₀ + s(s-1)·Λ₀'‖ ≤ 2`, hence `‖deriv ξ‖ = ‖·‖/2 ≤ 1`. -/
theorem norm_deriv_riemannXiEntire_le_one_at_t_le_138_25 {t : ℝ}
    (ht : |t| ≤ 138 / 25) :
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
    have h_sum := gate2_num_bound ht
    linarith
  linarith

/-- Chain-rule descent: `|deriv edgeRe t| ≤ ‖deriv ξ(1+it)‖ ≤ 1`. -/
theorem abs_deriv_edgeRe_le_one_at_t_le_138_25 {t : ℝ}
    (ht : |t| ≤ 138 / 25) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le :
      |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
        ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_one_at_t_le_138_25 ht
  linarith

/-- Specialisation of Gate 2 to the box `[137/25, 138/25]`. -/
theorem pilot_r1_hbound_poc :
    ∀ x ∈ Set.Icc ((137 : ℝ) / 25) (138 / 25), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 138 / 25 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_one_at_t_le_138_25 hx_abs

/-! ## §3 — THE POC PILOT BOX, closed end-to-end -/

/-- **POC PILOT.** R1 on `[137/25, 138/25]` = `[5.48, 5.52]` via the
pointwise-form Gate 1 (Cauchy–Schwarz) plus pilot-era Gate 2. Zero hypotheses,
kernel-clean. First box PAST the previous `c ≤ 81/20` uniform-bound ceiling. -/
theorem pilot_r1_box_c11_2_r1_50_poc_closed :
    ∀ t ∈ Icc ((137 : ℝ) / 25) (138 / 25),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((137 : ℝ) / 25) (138 / 25)
      = Icc ((11 / 2 : ℝ) - 1 / 50) ((11 / 2 : ℝ) + 1 / 50) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 11 / 2) (r := 1 / 50) (L := 1) (Mc_lb := 1 / 40)
    (by norm_num : (0 : ℝ) ≤ 1 / 50)
    pilot_r1_hvalue_lb_at_eleven_halves
    ?_
    (by norm_num : (1 : ℝ) * (1 / 50) < 1 / 40)
  intro x hx
  have hx' : x ∈ Icc ((137 : ℝ) / 25) (138 / 25) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_poc x hx'

end

/-! ## §Axiom check -/

#print axioms norm_sq_decomp
#print axioms pilot_r1_hvalue_lb_at_eleven_halves
#print axioms gate2_num_bound
#print axioms norm_deriv_riemannXiEntire_le_one_at_t_le_138_25
#print axioms abs_deriv_edgeRe_le_one_at_t_le_138_25
#print axioms pilot_r1_hbound_poc
#print axioms pilot_r1_box_c11_2_r1_50_poc_closed

end PilotR1Box_c11_2_r1_50_poc_pointwise_20261015
end PrincipiaTractalis
