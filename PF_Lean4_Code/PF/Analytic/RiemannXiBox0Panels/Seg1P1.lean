/-
# PF.Analytic.RiemannXiBox0Panels.Seg1P1  (PRODUCTION)

Stage-1 Segment [3/2, 25/16] Panel 1: nodes 0, 1, 2.

**Production exact-endpoint architecture** per directive: instantiate sign
consumers with `A_hi = Astar(u) = u^(-23/32) + u^(-25/32)` and `W_hi = W(u)`
as EXACT REAL EXPRESSIONS, not rational approximations.  This makes the
consumer output the exact adverse product `Astar(u)·C(u)·W(u)`, and Interval
only certifies ONE final rational lower bound on that product.

Per node numerical certificates required:
* Re adverse: `RE_LO_i ≤ Astar(u_i)·C(u_i)·W(u_i)` (single Interval product)
* Im adverse: `Dstar(u_i)·S(u_i)·W(u_i) ≤ IM_HI_i` (positive-sin) or
  `IM_LO_i ≤ Dstar(u_i)·S(u_i)·W(u_i)` (negative-sin)
* cos sign: `C(u) ≤ 0`
* sin sign: `0 ≤ S(u)` or `S(u) ≤ 0`

At each node u_i, generator emits outward-safe rational `RE_LO_i` and
Im endpoint from mpmath dps=100.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import Interval.Interval.Conversion
import Interval.Interval.Exp
import Interval.Interval.Log
import Interval.Interval.Sincos
import Interval.Interval.Pi
import Interval.Interval.Order
import Interval.Interval.Mul
import Interval.Tactic.Approx

namespace PrincipiaTractalis.RiemannXiBox0Panels.Seg1P1

open scoped Real
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes
open PrincipiaTractalis.XiQuadrature

/-! ## Helper — rpow via exp -/

/-- `x^(-a) = exp(-(log x · a))` for `x > 0`.  Aligns rpow with Interval.exp form. -/
private theorem rpow_neg_eq_exp {x a : ℝ} (hx : 0 < x) :
    x ^ (-a) = Real.exp (-(Real.log x * a)) := by
  rw [Real.rpow_def_of_pos hx]; ring_nf

/-- omegaPartial 3 unfold to closed form. -/
private theorem omegaPartial_3_closed {u : ℝ} :
    omegaPartial 3 u = Real.exp (-(π * u)) + Real.exp (-(π * 4 * u))
      + Real.exp (-(π * 9 * u)) := by
  unfold omegaPartial
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, one_pow]
  ring_nf

/-! ## Node 0 at u = 1105/736 — positive sin -/

/-- Sign: `cos((15/2)·log(1105/736)) ≤ 0`. -/
private theorem u0_cos_np : Real.cos ((15/2 : ℝ) * Real.log (1105/736 : ℝ)) ≤ 0 := by
  have hlt : Real.cos ((15/2 : ℝ) * Real.log (1105/736 : ℝ)) < (0 : ℝ) := by
    refine _root_.Interval.approx_lt
      (_root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
          (_root_.Interval.ofRat ((1105 : ℚ)/736))))
      ((0 : _root_.Interval))
      (Real.cos ((15/2 : ℝ) * Real.log (1105/736 : ℝ)))
      (0 : ℝ)
      (_root_.Interval.mem_approx_cos (by approx))
      (by approx)
      ?_
    decide +kernel
  linarith

/-- Sign: `0 ≤ sin((15/2)·log(1105/736))`. -/
private theorem u0_sin_nn : (0 : ℝ) ≤ Real.sin ((15/2 : ℝ) * Real.log (1105/736 : ℝ)) := by
  refine _root_.Interval.approx_le
    ((0 : _root_.Interval))
    (_root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736))))
    (0 : ℝ)
    (Real.sin ((15/2 : ℝ) * Real.log (1105/736 : ℝ)))
    (by approx)
    (_root_.Interval.mem_approx_sin (by approx))
    ?_
  decide +kernel

/-- Re adverse product bound: `RE_LO_0 ≤ Astar(u_0)·C(u_0)·W(u_0)`.
Numerical: Astar·C·W ≈ -0.013133; choose RE_LO_0 = -1314/100000. -/
private theorem u0_re_adverse_ge :
    (-1314/100000 : ℝ)
      ≤ ((1105/736 : ℝ) ^ (-(23/32 : ℝ)) + (1105/736 : ℝ) ^ (-(25/32 : ℝ)))
        * Real.cos ((15/2 : ℝ) * Real.log (1105/736 : ℝ))
        * omegaPartial 3 (1105/736 : ℝ) := by
  have hu0 : (0 : ℝ) < (1105/736 : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine _root_.Interval.approx_le
    ((-1314/100000 : _root_.Interval))
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736)) * _root_.Interval.ofRat (23/32)))
      + _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736)) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736)))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ((1105 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ((1105 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ((1105 : ℚ)/736)))))
    (-1314/100000 : ℝ)
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel

/-- Im adverse product bound: `Dstar(u_0)·S(u_0)·W(u_0) ≤ IM_HI_0`.
Numerical: Dstar·S·W ≈ 1.569·10⁻⁵; choose IM_HI_0 = 157/10⁷ = 1.57·10⁻⁵. -/
private theorem u0_im_adverse_le :
    ((1105/736 : ℝ) ^ (-(23/32 : ℝ)) - (1105/736 : ℝ) ^ (-(25/32 : ℝ)))
      * Real.sin ((15/2 : ℝ) * Real.log (1105/736 : ℝ))
      * omegaPartial 3 (1105/736 : ℝ)
      ≤ (157/10000000 : ℝ) := by
  have hu0 : (0 : ℝ) < (1105/736 : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine le_of_lt <| _root_.Interval.approx_lt
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736)) * _root_.Interval.ofRat (23/32)))
      - _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736)) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736)))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ((1105 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ((1105 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ((1105 : ℚ)/736)))))
    ((157/10000000 : _root_.Interval))
    _
    (157/10000000 : ℝ)
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel

/-- ★ Node 0 production bounds (u_0 = 1105/736, positive sin).
Uses exact-endpoint sign-consumer architecture. -/
theorem node_0_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-1314/100000 : ℝ) ≤ realThetaReIntegrandN 3 σ 15 (1105/736 : ℝ)
    ∧ realThetaReIntegrandN 3 σ 15 (1105/736 : ℝ) ≤ 0
    ∧ (0 : ℝ) ≤ realThetaImIntegrandN 3 σ 15 (1105/736 : ℝ)
    ∧ realThetaImIntegrandN 3 σ 15 (1105/736 : ℝ) ≤ (157/10000000 : ℝ) := by
  have hu1 : (1 : ℝ) ≤ (1105/736 : ℝ) := by norm_num
  -- Amplitude symbolic bounds (σ-uniform)
  have hA_nn : (0 : ℝ) ≤ (1105/736 : ℝ)^(σ/2 - 1) + (1105/736 : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_sum_nonneg σ hu1
  have hA_hi : (1105/736 : ℝ)^(σ/2 - 1) + (1105/736 : ℝ)^((1-σ)/2 - 1)
      ≤ (1105/736 : ℝ)^(-(23/32 : ℝ)) + (1105/736 : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_sum_tight_ub hu1 hσ0 hσ1
  have hD_nn : (0 : ℝ) ≤ (1105/736 : ℝ)^(σ/2 - 1) - (1105/736 : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_diff_nonneg hσ0 hu1
  have hD_hi : (1105/736 : ℝ)^(σ/2 - 1) - (1105/736 : ℝ)^((1-σ)/2 - 1)
      ≤ (1105/736 : ℝ)^(-(23/32 : ℝ)) - (1105/736 : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_diff_ub hσ0 hσ1 hu1
  have hW_nn : (0 : ℝ) ≤ omegaPartial 3 (1105/736 : ℝ) := omegaPartial_nonneg_here 3 _
  -- Astar (u_0) ≥ 0 via nonneg at σ=9/16 (definitional exact match)
  have hAstar_nn : (0 : ℝ) ≤ (1105/736 : ℝ)^(-(23/32 : ℝ)) + (1105/736 : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_sum_nonneg (9/16 : ℝ) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h
    exact h
  -- Dstar (u_0) ≥ 0 via diff_nonneg at σ=9/16
  have hDstar_nn : (0 : ℝ) ≤ (1105/736 : ℝ)^(-(23/32 : ℝ)) - (1105/736 : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_diff_nonneg (σ := 9/16) (by norm_num) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h
    exact h
  -- cos and sin
  have hC_np : Real.cos ((15/2 : ℝ) * Real.log (1105/736 : ℝ)) ≤ 0 := u0_cos_np
  have hS_nn : (0 : ℝ) ≤ Real.sin ((15/2 : ℝ) * Real.log (1105/736 : ℝ)) := u0_sin_nn
  -- Re sign consumer with exact endpoints
  have hRe := re_scalar_bounds_cos_neg
    (A_lo := 0)
    (A_hi := (1105/736 : ℝ)^(-(23/32 : ℝ)) + (1105/736 : ℝ)^(-(25/32 : ℝ)))
    (C_lo := Real.cos ((15/2 : ℝ) * Real.log (1105/736 : ℝ)))
    (C_hi := 0)
    (W_lo := 0)
    (W_hi := omegaPartial 3 (1105/736 : ℝ))
    (le_refl 0) hAstar_nn hC_np hC_np (le_refl 0)
    (le_refl 0) hW_nn
    hA_nn hA_hi (le_refl _) hC_np hW_nn (le_refl _)
  -- Im sign consumer with exact endpoints
  have hIm := im_scalar_bounds_sin_nonneg
    (D_lo := 0)
    (D_hi := (1105/736 : ℝ)^(-(23/32 : ℝ)) - (1105/736 : ℝ)^(-(25/32 : ℝ)))
    (S_lo := 0)
    (S_hi := Real.sin ((15/2 : ℝ) * Real.log (1105/736 : ℝ)))
    (W_lo := 0)
    (W_hi := omegaPartial 3 (1105/736 : ℝ))
    (le_refl 0) hDstar_nn (le_refl 0) hS_nn (le_refl 0) hW_nn
    hD_nn hD_hi hS_nn (le_refl _) hW_nn (le_refl _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- RE_LO ≤ ReN via hRe.1 (adverse product) + u0_re_adverse_ge
    unfold realThetaReIntegrandN
    have h1 := hRe.1
    have h2 := u0_re_adverse_ge
    linarith
  · unfold realThetaReIntegrandN
    have h1 := hRe.2
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith
  · unfold realThetaImIntegrandN
    have h1 := hIm.1
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith
  · unfold realThetaImIntegrandN
    have h1 := hIm.2
    have h2 := u0_im_adverse_le
    linarith

/-! ## Node 1 at u = 1107/736 — positive sin

Numerical: Astar·C·W ≈ -0.013019 → RE_LO_1 = -1302/100000.
Dstar·S·W ≈ 1.336·10⁻⁵ → IM_HI_1 = 134/10⁷. -/

private theorem u1_cos_np : Real.cos ((15/2 : ℝ) * Real.log (1107/736 : ℝ)) ≤ 0 := by
  have hlt : Real.cos ((15/2 : ℝ) * Real.log (1107/736 : ℝ)) < (0 : ℝ) := by
    refine _root_.Interval.approx_lt
      (_root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
          (_root_.Interval.ofRat ((1107 : ℚ)/736))))
      ((0 : _root_.Interval))
      (Real.cos ((15/2 : ℝ) * Real.log (1107/736 : ℝ)))
      (0 : ℝ)
      (_root_.Interval.mem_approx_cos (by approx))
      (by approx)
      ?_
    decide +kernel
  linarith

private theorem u1_sin_nn : (0 : ℝ) ≤ Real.sin ((15/2 : ℝ) * Real.log (1107/736 : ℝ)) := by
  refine _root_.Interval.approx_le
    ((0 : _root_.Interval))
    (_root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1107 : ℚ)/736))))
    (0 : ℝ)
    (Real.sin ((15/2 : ℝ) * Real.log (1107/736 : ℝ)))
    (by approx)
    (_root_.Interval.mem_approx_sin (by approx))
    ?_
  decide +kernel

private theorem u1_re_adverse_ge :
    (-1302/100000 : ℝ)
      ≤ ((1107/736 : ℝ) ^ (-(23/32 : ℝ)) + (1107/736 : ℝ) ^ (-(25/32 : ℝ)))
        * Real.cos ((15/2 : ℝ) * Real.log (1107/736 : ℝ))
        * omegaPartial 3 (1107/736 : ℝ) := by
  have hu0 : (0 : ℝ) < (1107/736 : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine _root_.Interval.approx_le
    ((-1302/100000 : _root_.Interval))
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1107 : ℚ)/736)) * _root_.Interval.ofRat (23/32)))
      + _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1107 : ℚ)/736)) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1107 : ℚ)/736)))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ((1107 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ((1107 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ((1107 : ℚ)/736)))))
    (-1302/100000 : ℝ)
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel

private theorem u1_im_adverse_le :
    ((1107/736 : ℝ) ^ (-(23/32 : ℝ)) - (1107/736 : ℝ) ^ (-(25/32 : ℝ)))
      * Real.sin ((15/2 : ℝ) * Real.log (1107/736 : ℝ))
      * omegaPartial 3 (1107/736 : ℝ)
      ≤ (134/10000000 : ℝ) := by
  have hu0 : (0 : ℝ) < (1107/736 : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine le_of_lt <| _root_.Interval.approx_lt
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1107 : ℚ)/736)) * _root_.Interval.ofRat (23/32)))
      - _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1107 : ℚ)/736)) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1107 : ℚ)/736)))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ((1107 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ((1107 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ((1107 : ℚ)/736)))))
    ((134/10000000 : _root_.Interval))
    _
    (134/10000000 : ℝ)
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel

theorem node_1_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-1302/100000 : ℝ) ≤ realThetaReIntegrandN 3 σ 15 (1107/736 : ℝ)
    ∧ realThetaReIntegrandN 3 σ 15 (1107/736 : ℝ) ≤ 0
    ∧ (0 : ℝ) ≤ realThetaImIntegrandN 3 σ 15 (1107/736 : ℝ)
    ∧ realThetaImIntegrandN 3 σ 15 (1107/736 : ℝ) ≤ (134/10000000 : ℝ) := by
  have hu1 : (1 : ℝ) ≤ (1107/736 : ℝ) := by norm_num
  have hA_nn : (0 : ℝ) ≤ (1107/736 : ℝ)^(σ/2 - 1) + (1107/736 : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_sum_nonneg σ hu1
  have hA_hi : (1107/736 : ℝ)^(σ/2 - 1) + (1107/736 : ℝ)^((1-σ)/2 - 1)
      ≤ (1107/736 : ℝ)^(-(23/32 : ℝ)) + (1107/736 : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_sum_tight_ub hu1 hσ0 hσ1
  have hD_nn : (0 : ℝ) ≤ (1107/736 : ℝ)^(σ/2 - 1) - (1107/736 : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_diff_nonneg hσ0 hu1
  have hD_hi : (1107/736 : ℝ)^(σ/2 - 1) - (1107/736 : ℝ)^((1-σ)/2 - 1)
      ≤ (1107/736 : ℝ)^(-(23/32 : ℝ)) - (1107/736 : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_diff_ub hσ0 hσ1 hu1
  have hW_nn : (0 : ℝ) ≤ omegaPartial 3 (1107/736 : ℝ) := omegaPartial_nonneg_here 3 _
  have hAstar_nn : (0 : ℝ) ≤ (1107/736 : ℝ)^(-(23/32 : ℝ)) + (1107/736 : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_sum_nonneg (9/16 : ℝ) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h; exact h
  have hDstar_nn : (0 : ℝ) ≤ (1107/736 : ℝ)^(-(23/32 : ℝ)) - (1107/736 : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_diff_nonneg (σ := 9/16) (by norm_num) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h; exact h
  have hC_np : Real.cos ((15/2 : ℝ) * Real.log (1107/736 : ℝ)) ≤ 0 := u1_cos_np
  have hS_nn : (0 : ℝ) ≤ Real.sin ((15/2 : ℝ) * Real.log (1107/736 : ℝ)) := u1_sin_nn
  have hRe := re_scalar_bounds_cos_neg
    (A_lo := 0)
    (A_hi := (1107/736 : ℝ)^(-(23/32 : ℝ)) + (1107/736 : ℝ)^(-(25/32 : ℝ)))
    (C_lo := Real.cos ((15/2 : ℝ) * Real.log (1107/736 : ℝ)))
    (C_hi := 0) (W_lo := 0) (W_hi := omegaPartial 3 (1107/736 : ℝ))
    (le_refl 0) hAstar_nn hC_np hC_np (le_refl 0)
    (le_refl 0) hW_nn
    hA_nn hA_hi (le_refl _) hC_np hW_nn (le_refl _)
  have hIm := im_scalar_bounds_sin_nonneg
    (D_lo := 0)
    (D_hi := (1107/736 : ℝ)^(-(23/32 : ℝ)) - (1107/736 : ℝ)^(-(25/32 : ℝ)))
    (S_lo := 0)
    (S_hi := Real.sin ((15/2 : ℝ) * Real.log (1107/736 : ℝ)))
    (W_lo := 0) (W_hi := omegaPartial 3 (1107/736 : ℝ))
    (le_refl 0) hDstar_nn (le_refl 0) hS_nn (le_refl 0) hW_nn
    hD_nn hD_hi hS_nn (le_refl _) hW_nn (le_refl _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold realThetaReIntegrandN
    linarith [hRe.1, u1_re_adverse_ge]
  · unfold realThetaReIntegrandN
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith [hRe.2]
  · unfold realThetaImIntegrandN
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith [hIm.1]
  · unfold realThetaImIntegrandN
    linarith [hIm.2, u1_im_adverse_le]

/-! ## Node 2 at u = 1109/736 — positive sin

Numerical: Astar·C·W ≈ -0.012904 → RE_LO_2 = -1291/100000.
Dstar·S·W ≈ 1.105·10⁻⁵ → IM_HI_2 = 111/10⁷. -/

private theorem u2_cos_np : Real.cos ((15/2 : ℝ) * Real.log (1109/736 : ℝ)) ≤ 0 := by
  have hlt : Real.cos ((15/2 : ℝ) * Real.log (1109/736 : ℝ)) < (0 : ℝ) := by
    refine _root_.Interval.approx_lt
      (_root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
          (_root_.Interval.ofRat ((1109 : ℚ)/736))))
      ((0 : _root_.Interval))
      (Real.cos ((15/2 : ℝ) * Real.log (1109/736 : ℝ)))
      (0 : ℝ)
      (_root_.Interval.mem_approx_cos (by approx))
      (by approx)
      ?_
    decide +kernel
  linarith

private theorem u2_sin_nn : (0 : ℝ) ≤ Real.sin ((15/2 : ℝ) * Real.log (1109/736 : ℝ)) := by
  refine _root_.Interval.approx_le
    ((0 : _root_.Interval))
    (_root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1109 : ℚ)/736))))
    (0 : ℝ)
    (Real.sin ((15/2 : ℝ) * Real.log (1109/736 : ℝ)))
    (by approx)
    (_root_.Interval.mem_approx_sin (by approx))
    ?_
  decide +kernel

private theorem u2_re_adverse_ge :
    (-1291/100000 : ℝ)
      ≤ ((1109/736 : ℝ) ^ (-(23/32 : ℝ)) + (1109/736 : ℝ) ^ (-(25/32 : ℝ)))
        * Real.cos ((15/2 : ℝ) * Real.log (1109/736 : ℝ))
        * omegaPartial 3 (1109/736 : ℝ) := by
  have hu0 : (0 : ℝ) < (1109/736 : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine _root_.Interval.approx_le
    ((-1291/100000 : _root_.Interval))
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1109 : ℚ)/736)) * _root_.Interval.ofRat (23/32)))
      + _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1109 : ℚ)/736)) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1109 : ℚ)/736)))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ((1109 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ((1109 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ((1109 : ℚ)/736)))))
    (-1291/100000 : ℝ)
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel

private theorem u2_im_adverse_le :
    ((1109/736 : ℝ) ^ (-(23/32 : ℝ)) - (1109/736 : ℝ) ^ (-(25/32 : ℝ)))
      * Real.sin ((15/2 : ℝ) * Real.log (1109/736 : ℝ))
      * omegaPartial 3 (1109/736 : ℝ)
      ≤ (111/10000000 : ℝ) := by
  have hu0 : (0 : ℝ) < (1109/736 : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine le_of_lt <| _root_.Interval.approx_lt
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1109 : ℚ)/736)) * _root_.Interval.ofRat (23/32)))
      - _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1109 : ℚ)/736)) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1109 : ℚ)/736)))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ((1109 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ((1109 : ℚ)/736)))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ((1109 : ℚ)/736)))))
    ((111/10000000 : _root_.Interval))
    _
    (111/10000000 : ℝ)
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel

theorem node_2_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-1291/100000 : ℝ) ≤ realThetaReIntegrandN 3 σ 15 (1109/736 : ℝ)
    ∧ realThetaReIntegrandN 3 σ 15 (1109/736 : ℝ) ≤ 0
    ∧ (0 : ℝ) ≤ realThetaImIntegrandN 3 σ 15 (1109/736 : ℝ)
    ∧ realThetaImIntegrandN 3 σ 15 (1109/736 : ℝ) ≤ (111/10000000 : ℝ) := by
  have hu1 : (1 : ℝ) ≤ (1109/736 : ℝ) := by norm_num
  have hA_nn : (0 : ℝ) ≤ (1109/736 : ℝ)^(σ/2 - 1) + (1109/736 : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_sum_nonneg σ hu1
  have hA_hi : (1109/736 : ℝ)^(σ/2 - 1) + (1109/736 : ℝ)^((1-σ)/2 - 1)
      ≤ (1109/736 : ℝ)^(-(23/32 : ℝ)) + (1109/736 : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_sum_tight_ub hu1 hσ0 hσ1
  have hD_nn : (0 : ℝ) ≤ (1109/736 : ℝ)^(σ/2 - 1) - (1109/736 : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_diff_nonneg hσ0 hu1
  have hD_hi : (1109/736 : ℝ)^(σ/2 - 1) - (1109/736 : ℝ)^((1-σ)/2 - 1)
      ≤ (1109/736 : ℝ)^(-(23/32 : ℝ)) - (1109/736 : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_diff_ub hσ0 hσ1 hu1
  have hW_nn : (0 : ℝ) ≤ omegaPartial 3 (1109/736 : ℝ) := omegaPartial_nonneg_here 3 _
  have hAstar_nn : (0 : ℝ) ≤ (1109/736 : ℝ)^(-(23/32 : ℝ)) + (1109/736 : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_sum_nonneg (9/16 : ℝ) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h; exact h
  have hDstar_nn : (0 : ℝ) ≤ (1109/736 : ℝ)^(-(23/32 : ℝ)) - (1109/736 : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_diff_nonneg (σ := 9/16) (by norm_num) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h; exact h
  have hC_np : Real.cos ((15/2 : ℝ) * Real.log (1109/736 : ℝ)) ≤ 0 := u2_cos_np
  have hS_nn : (0 : ℝ) ≤ Real.sin ((15/2 : ℝ) * Real.log (1109/736 : ℝ)) := u2_sin_nn
  have hRe := re_scalar_bounds_cos_neg
    (A_lo := 0)
    (A_hi := (1109/736 : ℝ)^(-(23/32 : ℝ)) + (1109/736 : ℝ)^(-(25/32 : ℝ)))
    (C_lo := Real.cos ((15/2 : ℝ) * Real.log (1109/736 : ℝ)))
    (C_hi := 0) (W_lo := 0) (W_hi := omegaPartial 3 (1109/736 : ℝ))
    (le_refl 0) hAstar_nn hC_np hC_np (le_refl 0)
    (le_refl 0) hW_nn
    hA_nn hA_hi (le_refl _) hC_np hW_nn (le_refl _)
  have hIm := im_scalar_bounds_sin_nonneg
    (D_lo := 0)
    (D_hi := (1109/736 : ℝ)^(-(23/32 : ℝ)) - (1109/736 : ℝ)^(-(25/32 : ℝ)))
    (S_lo := 0)
    (S_hi := Real.sin ((15/2 : ℝ) * Real.log (1109/736 : ℝ)))
    (W_lo := 0) (W_hi := omegaPartial 3 (1109/736 : ℝ))
    (le_refl 0) hDstar_nn (le_refl 0) hS_nn (le_refl 0) hW_nn
    hD_nn hD_hi hS_nn (le_refl _) hW_nn (le_refl _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold realThetaReIntegrandN
    linarith [hRe.1, u2_re_adverse_ge]
  · unfold realThetaReIntegrandN
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith [hRe.2]
  · unfold realThetaImIntegrandN
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith [hIm.1]
  · unfold realThetaImIntegrandN
    linarith [hIm.2, u2_im_adverse_le]

/-! ## P1 chunk sum: nodes 0, 1, 2 (production tight) -/

theorem seg1_p1_chunk_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-3907/100000 : ℝ)
      ≤ realThetaReIntegrandN 3 σ 15 (1105/736 : ℝ)
        + realThetaReIntegrandN 3 σ 15 (1107/736 : ℝ)
        + realThetaReIntegrandN 3 σ 15 (1109/736 : ℝ)
    ∧ realThetaReIntegrandN 3 σ 15 (1105/736 : ℝ)
        + realThetaReIntegrandN 3 σ 15 (1107/736 : ℝ)
        + realThetaReIntegrandN 3 σ 15 (1109/736 : ℝ) ≤ 0
    ∧ (0 : ℝ)
      ≤ realThetaImIntegrandN 3 σ 15 (1105/736 : ℝ)
        + realThetaImIntegrandN 3 σ 15 (1107/736 : ℝ)
        + realThetaImIntegrandN 3 σ 15 (1109/736 : ℝ)
    ∧ realThetaImIntegrandN 3 σ 15 (1105/736 : ℝ)
        + realThetaImIntegrandN 3 σ 15 (1107/736 : ℝ)
        + realThetaImIntegrandN 3 σ 15 (1109/736 : ℝ) ≤ (402/10000000 : ℝ) := by
  -- Re: -1314/100000 - 1302/100000 - 1291/100000 = -3907/100000
  -- Im: 157/10^7 + 134/10^7 + 111/10^7 = 402/10^7
  have h0 := node_0_bounds σ hσ0 hσ1
  have h1 := node_1_bounds σ hσ0 hσ1
  have h2 := node_2_bounds σ hσ0 hσ1
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [h0.1, h1.1, h2.1]
  · linarith [h0.2.1, h1.2.1, h2.2.1]
  · linarith [h0.2.2.1, h1.2.2.1, h2.2.2.1]
  · linarith [h0.2.2.2, h1.2.2.2, h2.2.2.2]

end PrincipiaTractalis.RiemannXiBox0Panels.Seg1P1
