/-
# PF.Numerics.Box0Seg1MPrototype

Scratch prototype: split M_j at L=3/2 into 3 fixed terms with LOOSE
bounds (7/5, 1/100, 1/100), combine → M < 3.

Attacks the specific failure mode identified in the previous attempt:
`by approx` reconstruction on the whole unfolded Finset sum.  Instead
each T_n is a fixed transcendental expression normalized to canonical
form BEFORE Interval is invoked.

Values (mpmath dps=100):
  T0 = exp(-3π/2) · (78705/1024 + π² + (265/16)·π) ≈ 1.2465
  T1 = exp(-6π)   · (81321/1024 + 16π² + (325/16)·π) ≈ 2.88·10⁻⁶
  T2 = exp(-27π/2) · (109089/1024 + 81π² + (505/16)·π) ≈ 5.12·10⁻¹⁶

Chose 7/5 = 1.4, 1/100, 1/100 as loose bounds.  Sum: 2·(7/5+1/100+1/100)
= 71/25 = 2.84 < 3.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import Interval.Interval.Conversion
import Interval.Interval.Exp
import Interval.Interval.Pi
import Interval.Interval.Order
import Interval.Interval.Mul
import Interval.Tactic.Approx

namespace PrincipiaTractalis.Box0Seg1MPrototype

open scoped Real
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes

/-! ## Closed-form normalization of each T_n at (t=15, p1=25/32, p2=1425/1024, L=3/2) -/

/-- `thetaPowTermM 15 (25/32) (1425/1024) (3/2) 0` in canonical π/exp form. -/
theorem seg1_T0_closed :
    thetaPowTermM 15 (25/32) (1425/1024) (3/2) 0
      = Real.exp (-(π * (3/2))) * ((78705/1024 : ℝ) + π * π + (265/16 : ℝ) * π) := by
  unfold thetaPowTermM
  have h_abs : |(15 : ℝ)| = 15 := by rw [abs_of_pos]; norm_num
  simp only [Nat.cast_zero, zero_add, h_abs, one_pow]
  ring

/-- `thetaPowTermM ... 1` in canonical form.
Coefficient constant part is 78705/1024 (n-independent),
π² coefficient is 16 (from (n+1)²)²=16 at n=1),
π coefficient is (n+1)²·265/16 = 4·265/16 = 1060/16 = 265/4. -/
theorem seg1_T1_closed :
    thetaPowTermM 15 (25/32) (1425/1024) (3/2) 1
      = Real.exp (-(π * 6)) * ((78705/1024 : ℝ) + 16 * (π * π) + (265/4 : ℝ) * π) := by
  unfold thetaPowTermM
  have h_abs : |(15 : ℝ)| = 15 := by rw [abs_of_pos]; norm_num
  simp only [Nat.cast_one, h_abs]
  ring

/-- `thetaPowTermM ... 2` in canonical form.
π² coefficient is 81 (from (n+1)^4 = 3^4 = 81),
π coefficient is (n+1)²·265/16 = 9·265/16 = 2385/16. -/
theorem seg1_T2_closed :
    thetaPowTermM 15 (25/32) (1425/1024) (3/2) 2
      = Real.exp (-(π * (27/2))) * ((78705/1024 : ℝ) + 81 * (π * π) + (2385/16 : ℝ) * π) := by
  unfold thetaPowTermM
  have h_abs : |(15 : ℝ)| = 15 := by rw [abs_of_pos]; norm_num
  simp only [Nat.cast_ofNat, h_abs]
  ring

/-! ## Interval mirrors — one per term -/

/-- Mirror of T0. -/
noncomputable def T0_mirror : _root_.Interval :=
  _root_.Interval.exp (-(_root_.Interval.pi * _root_.Interval.ofRat (3/2))) *
    (_root_.Interval.ofRat (78705/1024)
     + _root_.Interval.pi * _root_.Interval.pi
     + _root_.Interval.ofRat (265/16) * _root_.Interval.pi)

/-- Mirror of T1. -/
noncomputable def T1_mirror : _root_.Interval :=
  _root_.Interval.exp (-(_root_.Interval.pi * (6 : _root_.Interval))) *
    (_root_.Interval.ofRat (78705/1024)
     + (16 : _root_.Interval) * (_root_.Interval.pi * _root_.Interval.pi)
     + _root_.Interval.ofRat (265/4) * _root_.Interval.pi)

/-- Mirror of T2. -/
noncomputable def T2_mirror : _root_.Interval :=
  _root_.Interval.exp (-(_root_.Interval.pi * _root_.Interval.ofRat (27/2))) *
    (_root_.Interval.ofRat (78705/1024)
     + (81 : _root_.Interval) * (_root_.Interval.pi * _root_.Interval.pi)
     + _root_.Interval.ofRat (2385/16) * _root_.Interval.pi)

/-! ## Individual term bounds -/

/-- T0 < 7/5.  Numerical: T0 ≈ 1.2465 < 1.4. -/
theorem seg1_T0_lt : thetaPowTermM 15 (25/32) (1425/1024) (3/2) 0 < (7/5 : ℝ) := by
  rw [seg1_T0_closed]
  refine _root_.Interval.approx_lt
    T0_mirror
    (_root_.Interval.ofRat (7/5))
    (Real.exp (-(π * (3/2))) * ((78705/1024 : ℝ) + π * π + (265/16 : ℝ) * π))
    (7/5 : ℝ)
    ?_
    (by approx)
    ?_
  · unfold T0_mirror
    approx
  · decide +kernel

/-- T1 < 1/100.  Numerical: T1 ≈ 2.88·10⁻⁶. -/
theorem seg1_T1_lt : thetaPowTermM 15 (25/32) (1425/1024) (3/2) 1 < (1/100 : ℝ) := by
  rw [seg1_T1_closed]
  refine _root_.Interval.approx_lt
    T1_mirror
    (_root_.Interval.ofRat (1/100))
    (Real.exp (-(π * 6)) * ((78705/1024 : ℝ) + 16 * (π * π) + (265/4 : ℝ) * π))
    (1/100 : ℝ)
    ?_
    (by approx)
    ?_
  · unfold T1_mirror
    approx
  · decide +kernel

/-- T2 < 1/100.  Numerical: T2 ≈ 5.12·10⁻¹⁶. -/
theorem seg1_T2_lt : thetaPowTermM 15 (25/32) (1425/1024) (3/2) 2 < (1/100 : ℝ) := by
  rw [seg1_T2_closed]
  refine _root_.Interval.approx_lt
    T2_mirror
    (_root_.Interval.ofRat (1/100))
    (Real.exp (-(π * (27/2))) * ((78705/1024 : ℝ) + 81 * (π * π) + (2385/16 : ℝ) * π))
    (1/100 : ℝ)
    ?_
    (by approx)
    ?_
  · unfold T2_mirror
    approx
  · decide +kernel

/-! ## Structural: Finset sum expansion -/

theorem seg1_M_expand :
    2 * ∑ n ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) (3/2) n
      = 2 * (thetaPowTermM 15 (25/32) (1425/1024) (3/2) 0
             + thetaPowTermM 15 (25/32) (1425/1024) (3/2) 1
             + thetaPowTermM 15 (25/32) (1425/1024) (3/2) 2) := by
  simp [Finset.sum_range_succ]

/-! ## ★ M_j at L=3/2 is < 3 -/

theorem box0_seg1_M_lt_three :
    2 * ∑ n ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) (3/2) n < (3 : ℝ) := by
  rw [seg1_M_expand]
  have h0 := seg1_T0_lt
  have h1 := seg1_T1_lt
  have h2 := seg1_T2_lt
  linarith

theorem box0_seg1_M_le_three :
    2 * ∑ n ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) (3/2) n ≤ (3 : ℝ) :=
  le_of_lt box0_seg1_M_lt_three

end PrincipiaTractalis.Box0Seg1MPrototype
