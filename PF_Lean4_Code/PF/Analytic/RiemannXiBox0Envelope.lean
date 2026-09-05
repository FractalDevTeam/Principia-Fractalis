/-
# PF.Analytic.RiemannXiBox0Envelope

Exact-rational majorant for the §8 analytic truncation/tail envelope at
`N = 3`, `T = 5` — the ONLY error term applied globally, exactly once, after
the 40 certified segment integrals are summed.

The envelope is the literal right-hand side of
`PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes.re_Lambda0_close_to_truncated_integral`
(and its `im` twin):

    2 * (T - 1) * (Real.exp (-π * ((N : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)))
      + 2 / π * Real.exp (-π * T) / (1 - Real.exp (-π))

There is NO named definition for it upstream; it occurs only inline.

At `N = 3, T = 5` its true value is `1.0027288368073684533e-7`.  We majorize by
`1/5000000 = 2e-7` rather than by a tight `1.00273e-7`: the Box-0 Re headroom
before the analytic term is `+1.287524e-6`, so the loose bound still leaves
`+1.0875e-6`, and every sub-bound below is then provable with generous slack.

Sub-bounds used (each strictly loose):
  exp(-π)        ≤ 1/20            (π > 3 ⇒ exp(-π) < exp(-3) < 0.0498)
  1 - exp(-π)    ≥ 19/20
  exp(-π * 5)    ≤ 151/10^9        (true ≈ 1.50699e-7)
  exp(-π * 16)   ≤ 1/10^21         (true ≈ 1.478e-22)
  2 / π          ≤ 7/10            (π > 20/7)

giving
  term₁ ≤ 8 · 10⁻²¹ · (20/19) < 10⁻¹⁹
  term₂ ≤ (7/10) · 151·10⁻⁹ · (20/19) = 21140/1.9e11 ≈ 1.1126e-7
  total < 2e-7.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import Interval.Interval.Conversion
import Interval.Interval.Exp
import Interval.Interval.Pi
import Interval.Interval.Order
import Interval.Interval.Mul
import Interval.Tactic.Approx

namespace PrincipiaTractalis.RiemannXiBox0Envelope

open scoped Real

/-! ## §E.1 — elementary bounds on the exponential factors -/

/-- `π > 3`, in the form used repeatedly below. -/
private theorem pi_gt_three : (3 : ℝ) < π := Real.pi_gt_three

/-- `exp (-π) ≤ 1/20`. -/
theorem exp_neg_pi_le : Real.exp (-π) ≤ (1/20 : ℝ) := by
  have h3 : (3 : ℝ) < π := pi_gt_three
  have hmono : Real.exp (-π) ≤ Real.exp (-3 : ℝ) := by
    apply Real.exp_le_exp.mpr; linarith
  have h3bound : Real.exp (-3 : ℝ) ≤ (1/20 : ℝ) := by
    refine le_of_lt <| _root_.Interval.approx_lt
      (_root_.Interval.exp (-(3 : _root_.Interval)))
      ((1/20 : _root_.Interval))
      (Real.exp (-3 : ℝ))
      (1/20 : ℝ)
      ?_
      (by approx)
      ?_
    · approx
    · decide +kernel
  linarith

/-- `19/20 ≤ 1 - exp (-π)`, the denominator lower bound. -/
theorem one_sub_exp_neg_pi_ge : (19/20 : ℝ) ≤ 1 - Real.exp (-π) := by
  have := exp_neg_pi_le
  linarith

/-- The denominator is strictly positive. -/
theorem one_sub_exp_neg_pi_pos : (0 : ℝ) < 1 - Real.exp (-π) := by
  have := one_sub_exp_neg_pi_ge; linarith

/-- `exp (-π * 5) ≤ 151/10^9`.  True value ≈ 1.50699e-7. -/
theorem exp_neg_five_pi_le : Real.exp (-π * 5) ≤ (151/1000000000 : ℝ) := by
  have hrw : (-π * 5 : ℝ) = -(π * 5) := by ring
  rw [hrw]
  refine le_of_lt <| _root_.Interval.approx_lt
    (_root_.Interval.exp (-(_root_.Interval.pi * (5 : _root_.Interval))))
    ((151/1000000000 : _root_.Interval))
    (Real.exp (-(π * 5)))
    (151/1000000000 : ℝ)
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel

/-- `exp (-π * 16) ≤ 10⁻²¹`.  True value ≈ 1.478e-22. -/
theorem exp_neg_sixteen_pi_le :
    Real.exp (-π * ((3 : ℝ) + 1) ^ 2) ≤ (1/1000000000000000000000 : ℝ) := by
  have hrw : (-π * ((3 : ℝ) + 1) ^ 2) = -(π * 16) := by ring
  rw [hrw]
  refine le_of_lt <| _root_.Interval.approx_lt
    (_root_.Interval.exp (-(_root_.Interval.pi * (16 : _root_.Interval))))
    ((1/1000000000000000000000 : _root_.Interval))
    (Real.exp (-(π * 16)))
    (1/1000000000000000000000 : ℝ)
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel

/-- `2 / π ≤ 7/10`, since `π > 20/7`. -/
theorem two_div_pi_le : 2 / π ≤ (7/10 : ℝ) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h3 : (3 : ℝ) < π := pi_gt_three
  rw [div_le_iff₀ hpi]
  linarith

/-! ## §E.2 — the assembled majorant -/

/-- **The §8 envelope at `N = 3`, `T = 5` is at most `1/5000000`.**

The left-hand side is exactly the right-hand side of
`re_Lambda0_close_to_truncated_integral` / `im_Lambda0_close_to_truncated_integral`
instantiated at `N := 3`, `T := 5` (after `push_cast` on the `(N : ℝ)` cast). -/
theorem box0_envelope_le :
    2 * ((5 : ℝ) - 1)
        * (Real.exp (-π * ((3 : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)))
      + 2 / π * Real.exp (-π * 5) / (1 - Real.exp (-π))
      ≤ (1/5000000 : ℝ) := by
  have hden_pos : (0 : ℝ) < 1 - Real.exp (-π) := one_sub_exp_neg_pi_pos
  have hden_ge : (19/20 : ℝ) ≤ 1 - Real.exp (-π) := one_sub_exp_neg_pi_ge
  have hinv : 1 / (1 - Real.exp (-π)) ≤ (20/19 : ℝ) := by
    rw [div_le_iff₀ hden_pos]; linarith
  have hinv_nn : (0 : ℝ) ≤ 1 / (1 - Real.exp (-π)) := le_of_lt (by positivity)
  -- first term
  have he16 := exp_neg_sixteen_pi_le
  have he16_nn : (0 : ℝ) ≤ Real.exp (-π * ((3 : ℝ) + 1) ^ 2) := le_of_lt (Real.exp_pos _)
  have hterm1 :
      2 * ((5 : ℝ) - 1) * (Real.exp (-π * ((3 : ℝ) + 1) ^ 2) / (1 - Real.exp (-π)))
        ≤ (1/100000000000000000000 : ℝ) := by
    have hsplit : Real.exp (-π * ((3 : ℝ) + 1) ^ 2) / (1 - Real.exp (-π))
        = Real.exp (-π * ((3 : ℝ) + 1) ^ 2) * (1 / (1 - Real.exp (-π))) := by
      field_simp
    rw [hsplit]
    have hprod : Real.exp (-π * ((3 : ℝ) + 1) ^ 2) * (1 / (1 - Real.exp (-π)))
        ≤ (1/1000000000000000000000 : ℝ) * (20/19 : ℝ) :=
      mul_le_mul he16 hinv hinv_nn (by norm_num)
    nlinarith [hprod]
  -- second term
  have he5 := exp_neg_five_pi_le
  have he5_nn : (0 : ℝ) ≤ Real.exp (-π * 5) := le_of_lt (Real.exp_pos _)
  have hpi_nn : (0 : ℝ) ≤ 2 / π := le_of_lt (by positivity)
  have hterm2 :
      2 / π * Real.exp (-π * 5) / (1 - Real.exp (-π)) ≤ (12/100000000 : ℝ) := by
    have hsplit : 2 / π * Real.exp (-π * 5) / (1 - Real.exp (-π))
        = (2 / π) * Real.exp (-π * 5) * (1 / (1 - Real.exp (-π))) := by
      field_simp
    rw [hsplit]
    have h1 : (2 / π) * Real.exp (-π * 5) ≤ (7/10 : ℝ) * (151/1000000000 : ℝ) :=
      mul_le_mul two_div_pi_le he5 he5_nn (by norm_num)
    have h1_nn : (0 : ℝ) ≤ (2 / π) * Real.exp (-π * 5) := mul_nonneg hpi_nn he5_nn
    have h2 : (2 / π) * Real.exp (-π * 5) * (1 / (1 - Real.exp (-π)))
        ≤ ((7/10 : ℝ) * (151/1000000000 : ℝ)) * (20/19 : ℝ) :=
      mul_le_mul h1 hinv hinv_nn (by norm_num)
    nlinarith [h2]
  linarith [hterm1, hterm2]

end PrincipiaTractalis.RiemannXiBox0Envelope
