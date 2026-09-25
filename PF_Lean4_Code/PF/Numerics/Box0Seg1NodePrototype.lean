/-
# PF.Numerics.Box0Seg1NodePrototype

Prototype for ONE Stage-1 node theorem at u_0 = 1105/736.

Pattern: use §9.7-tight `box0_pow_sum_tight_lb/ub` to bound the σ-uniform
amplitude, then Interval-certify the scalar transcendental factors, then
apply sign consumer `re_scalar_bounds_cos_neg` (cos < 0 at this u).

Once this ONE node builds green, the pattern replicates mechanically for
all 23 nodes.

For u = 1105/736 numerical values (mpmath dps=60):
* p24 = u^(-3/4)   ≈ 0.7373
* p23 = u^(-23/32) ≈ 0.7467
* p25 = u^(-25/32) ≈ 0.7280
* cos(7.5 log u)   ≈ -0.9956
* sin(7.5 log u)   ≈ +0.0937
* omegaPartial 3 u ≈ 0.008945

Re range (uniform σ ∈ [1/2, 9/16]): [-0.01315, -0.01311].

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

namespace PrincipiaTractalis.Box0Seg1NodePrototype

open scoped Real
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes
open PrincipiaTractalis.XiQuadrature

/-! ## Scalar transcendental certificates at u = 1105/736 -/

/-- Rational upper bound: `(1105/736)^(-23/32) + (1105/736)^(-25/32) < 3/2`.
Numerical ≈ 1.4747. Rewrite `x^(-a) = exp(-(log x · a))` to align with Interval mirror. -/
theorem u0_A_hi_lt : ((1105/736 : ℝ) ^ (-(23/32 : ℝ)))
    + ((1105/736 : ℝ) ^ (-(25/32 : ℝ))) < (3/2 : ℝ) := by
  have hu0 : (0 : ℝ) < (1105/736 : ℝ) := by norm_num
  have h_eq1 : (1105/736 : ℝ) ^ (-(23/32 : ℝ))
      = Real.exp (-(Real.log (1105/736 : ℝ) * (23/32 : ℝ))) := by
    rw [Real.rpow_def_of_pos hu0]; ring_nf
  have h_eq2 : (1105/736 : ℝ) ^ (-(25/32 : ℝ))
      = Real.exp (-(Real.log (1105/736 : ℝ) * (25/32 : ℝ))) := by
    rw [Real.rpow_def_of_pos hu0]; ring_nf
  rw [h_eq1, h_eq2]
  refine _root_.Interval.approx_lt
    (_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736)) * _root_.Interval.ofRat (23/32)))
      + _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736)) * _root_.Interval.ofRat (25/32))))
    ((3/2 : _root_.Interval))
    _
    (3/2 : ℝ)
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel

/-- Rational lower bound: `2·(1105/736)^(-3/4) > 29/20` (numerical ≈ 1.4746). -/
theorem u0_A_lo_gt : (29/20 : ℝ) < 2 * (1105/736 : ℝ) ^ (-(3/4 : ℝ)) := by
  have hu0 : (0 : ℝ) < (1105/736 : ℝ) := by norm_num
  have h_eq : (1105/736 : ℝ) ^ (-(3/4 : ℝ))
      = Real.exp (-(Real.log (1105/736 : ℝ) * (3/4 : ℝ))) := by
    rw [Real.rpow_def_of_pos hu0]; ring_nf
  rw [h_eq]
  refine _root_.Interval.approx_lt
    ((29/20 : _root_.Interval))
    (2 * _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736)) * _root_.Interval.ofRat (3/4))))
    (29/20 : ℝ)
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel

/-- Rational cos upper bound: `cos((15/2)·log(1105/736)) < -0.99`. -/
theorem u0_C_lt : Real.cos ((15/2 : ℝ) * Real.log (1105/736 : ℝ)) < (-99/100 : ℝ) := by
  refine _root_.Interval.approx_lt
    (_root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ((1105 : ℚ)/736))))
    ((-99/100 : _root_.Interval))
    (Real.cos ((15/2 : ℝ) * Real.log (1105/736 : ℝ)))
    (-99/100 : ℝ)
    (_root_.Interval.mem_approx_cos (by approx))
    (by approx)
    ?_
  decide +kernel

/-- Rational omegaPartial upper bound: `omegaPartial 3 (1105/736) < 1/100`. -/
theorem u0_W_lt : omegaPartial 3 (1105/736 : ℝ) < (1/100 : ℝ) := by
  -- omegaPartial 3 u = exp(-π·1·u) + exp(-π·4·u) + exp(-π·9·u)
  have h_omega : omegaPartial 3 (1105/736 : ℝ)
      = Real.exp (-(π * (1105/736 : ℝ)))
        + Real.exp (-(π * 4 * (1105/736 : ℝ)))
        + Real.exp (-(π * 9 * (1105/736 : ℝ))) := by
    unfold omegaPartial
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
               Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, one_pow]
    ring_nf
  rw [h_omega]
  refine _root_.Interval.approx_lt
    (_root_.Interval.exp (-(_root_.Interval.pi *
        _root_.Interval.ofRat ((1105 : ℚ)/736)))
     + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
                              _root_.Interval.ofRat ((1105 : ℚ)/736)))
     + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
                              _root_.Interval.ofRat ((1105 : ℚ)/736))))
    ((1/100 : _root_.Interval))
    _
    (1/100 : ℝ)
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel

end PrincipiaTractalis.Box0Seg1NodePrototype
