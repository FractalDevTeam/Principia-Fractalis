/-
# r314d: Symbolic bound `|R_geq_2| ≤ exp(-4π)/(2π·(1-exp(-4π)))`
#       via integration of r314c's geometric bound

★ 2026-08-22 r314d — integration of r314c's pointwise geometric bound
`tail(y) ≤ 2·exp(-4πy)/(1-exp(-4π))` for `y ≥ 1` into a symbolic bound on
`|R_geq_2|`.

## Route

- Bound `∫_{Ioi 1} tail·y^(-3/4)` above by `∫_{Ioi 1} (2·exp(-4πy)/(1-exp(-4π)))·y^(-3/4)`
  via `setIntegral_mono_on` + r314c's `tail_le_geometric_dominator` + `y^(-3/4) > 0`.

- Factor the constant out via `integral_const_mul`.

- Bound `∫_{Ioi 1} exp(-4πy)·y^(-3/4) ≤ ∫_{Ioi 1} exp(-4πy)` via `y^(-3/4) ≤ 1`
  on `Ioi 1` and `exp(-4πy) ≥ 0`.

- Compute `∫_{Ioi 1} exp(-4πy) dy = exp(-4π)/(4π)` via `integral_exp_mul_Ioi`
  at `a = -4π` (negative).

- Combine with r314b's `|R_geq_2| ≤ ∫ tail·y^(-3/4)` to conclude
  `|R_geq_2| ≤ exp(-4π)/(2π·(1-exp(-4π)))`.

## Framework-first status (per MASTER DIRECTIVE)

NOT a numerical discharge. Symbolic bound in mathlib primitives (`Real.exp`,
`Real.pi`). Rationalization to explicit rational `E < 10^(-6)` is r314e.

Standing rules absolute: no `sorry`, no `native_decide`, no floating-point-as-proof,
no hidden oracle, no assumed transcendental enclosure.

## What r314d delivers

- `integral_exp_neg_four_pi_Ioi_one` : `∫ y in Ioi 1, exp(-4πy) dy = exp(-4π)/(4π)`.
- `exp_neg_four_pi_times_ypow_integrable` : `IntegrableOn (fun y => exp(-4πy) · y^(-3/4)) (Ioi 1)`.
- `integral_exp_neg_four_pi_times_ypow_le` :
    `∫ y in Ioi 1, exp(-4πy) · y^(-3/4) ≤ exp(-4π)/(4π)`.
- `integral_tail_times_ypow_le_symbolic` :
    `∫ y in Ioi 1, tail(y) · y^(-3/4) ≤ exp(-4π)/(2π·(1-exp(-4π)))`.
- `abs_R_geq_2_le_symbolic_bound` : `|R_geq_2| ≤ exp(-4π)/(2π·(1-exp(-4π)))`.

## r314e direction

Rationalize `exp(-4π) < ε` via `exp(π) > 22` (Taylor `∑_{k=0}^{N} π^k/k!` with
`π > 3.14`) → `exp(4π) > 22^4 = 234256` → `exp(-4π) < 1/234256 < 4.3·10^(-6)`.
Then chain: `|R_geq_2| < 4.3·10^(-6)/(2π·(1-4.3·10^(-6))) < 7·10^(-7) < 10^(-6)`.
Endpoint: `|R_geq_2| ≤ E` for rational `E < 10^(-6)`.

Book anchors: Ch 20 § 20.4, Ch 34A § 34A.5.
-/

import PF.Analytic.ChiPositive15RgeqTwoGeometricBound_r314c
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound

open MeasureTheory Set Real
open HurwitzZeta
open PrincipiaTractalis.ChiPositive15ThetaTruncation
open PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm
open PrincipiaTractalis.ChiPositive15RgeqTwoPointwiseBound
open PrincipiaTractalis.ChiPositive15RgeqTwoGeometricBound

/-! ## §1 Direct computation `∫ y in Ioi 1, exp(-4πy) dy = exp(-4π)/(4π)`. -/

/-- **`integral_exp_neg_four_pi_Ioi_one`** —

  `∫ y in Ioi 1, exp(-(4π · y)) dy = exp(-(4π))/(4π)`.

Via mathlib's `integral_exp_mul_Ioi` at `a = -(4π)` (negative), `c = 1`. -/
theorem integral_exp_neg_four_pi_Ioi_one :
    (∫ y in Ioi (1 : ℝ), Real.exp (-(4 * Real.pi * y)))
      = Real.exp (-(4 * Real.pi)) / (4 * Real.pi) := by
  have hpi : (0 : ℝ) < 4 * Real.pi := by
    have := Real.pi_pos; linarith
  have h_neg : -(4 * Real.pi) < 0 := by linarith
  have h_ident : ∀ y : ℝ, Real.exp (-(4 * Real.pi * y)) = Real.exp ((-(4 * Real.pi)) * y) := by
    intro y; congr 1; ring
  have h_int := integral_exp_mul_Ioi (a := -(4 * Real.pi)) h_neg 1
  -- h_int : ∫ x in Ioi 1, exp(-(4π) · x) = -exp(-(4π) · 1) / (-(4π))
  simp only [mul_one] at h_int
  rw [show (fun y => Real.exp (-(4 * Real.pi * y)))
        = (fun y => Real.exp ((-(4 * Real.pi)) * y)) from funext h_ident]
  rw [h_int]
  field_simp

/-! ## §2 Integrability of `exp(-4πy)·y^(-3/4)` on `Ioi 1`. -/

/-- **`exp_neg_four_pi_integrable_on_ioi_one`** — `exp(-(4π·y))` integrable on `Ioi 1`
via `integrableOn_exp_mul_Ioi`. -/
theorem exp_neg_four_pi_integrable_on_ioi_one :
    IntegrableOn (fun y : ℝ => Real.exp (-(4 * Real.pi * y))) (Ioi (1 : ℝ)) := by
  have hpi_pos : (0 : ℝ) < 4 * Real.pi := by have := Real.pi_pos; linarith
  have h_neg : -(4 * Real.pi) < 0 := by linarith
  have h_ident : (fun y : ℝ => Real.exp (-(4 * Real.pi * y)))
                 = (fun y : ℝ => Real.exp ((-(4 * Real.pi)) * y)) := by
    funext y; congr 1; ring
  rw [h_ident]
  exact integrableOn_exp_mul_Ioi h_neg 1

/-- **`exp_neg_four_pi_times_ypow_integrable`** — `exp(-(4π·y)) · y^(-3/4)` integrable
on `Ioi 1` via `Integrable.mono'` bounded by `exp(-(4π·y))`. -/
theorem exp_neg_four_pi_times_ypow_integrable :
    IntegrableOn (fun y : ℝ => Real.exp (-(4 * Real.pi * y)) * y^(-((3 : ℝ)/4))) (Ioi (1 : ℝ)) := by
  refine Integrable.mono' exp_neg_four_pi_integrable_on_ioi_one ?_ ?_
  · -- AEStronglyMeasurable
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · exact (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg).continuousOn
    · intro y hy
      have hy_pos : 0 < y := lt_trans zero_lt_one hy
      exact (Real.continuousAt_rpow_const _ _ (Or.inl hy_pos.ne')).continuousWithinAt
  · -- ∀ᵐ y, ‖exp(-4πy)·y^(-3/4)‖ ≤ exp(-4πy)
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun y hy => ?_))
    have hy_pos : (0 : ℝ) < y := lt_trans zero_lt_one hy
    have h_exp_nn : 0 ≤ Real.exp (-(4 * Real.pi * y)) := (Real.exp_pos _).le
    have h_rpow_pos : 0 < y^(-((3 : ℝ)/4)) := Real.rpow_pos_of_pos hy_pos _
    have h_rpow_le : y^(-((3 : ℝ)/4)) ≤ 1 := by
      rw [show (1 : ℝ) = y^(0 : ℝ) from (Real.rpow_zero y).symm]
      exact Real.rpow_le_rpow_of_exponent_le hy.le (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h_exp_nn h_rpow_pos.le)]
    calc Real.exp (-(4 * Real.pi * y)) * y^(-((3 : ℝ)/4))
        ≤ Real.exp (-(4 * Real.pi * y)) * 1 := mul_le_mul_of_nonneg_left h_rpow_le h_exp_nn
      _ = Real.exp (-(4 * Real.pi * y)) := by ring

/-! ## §3 Bound `∫ exp(-4πy)·y^(-3/4) ≤ ∫ exp(-4πy) = exp(-4π)/(4π)`. -/

/-- **`integral_exp_neg_four_pi_times_ypow_le`** —

  `∫ y in Ioi 1, exp(-(4π·y)) · y^(-3/4) ≤ exp(-(4π))/(4π)`.

Via `setIntegral_mono_on` bounding the integrand by `exp(-(4π·y))` (using
`y^(-3/4) ≤ 1` for `y ≥ 1`), then `integral_exp_neg_four_pi_Ioi_one`. -/
theorem integral_exp_neg_four_pi_times_ypow_le :
    (∫ y in Ioi (1 : ℝ), Real.exp (-(4 * Real.pi * y)) * y^(-((3 : ℝ)/4)))
      ≤ Real.exp (-(4 * Real.pi)) / (4 * Real.pi) := by
  rw [← integral_exp_neg_four_pi_Ioi_one]
  refine setIntegral_mono_on exp_neg_four_pi_times_ypow_integrable
    exp_neg_four_pi_integrable_on_ioi_one measurableSet_Ioi (fun y hy => ?_)
  have hy_pos : (0 : ℝ) < y := lt_trans zero_lt_one hy
  have h_exp_nn : 0 ≤ Real.exp (-(4 * Real.pi * y)) := (Real.exp_pos _).le
  have h_rpow_le : y^(-((3 : ℝ)/4)) ≤ 1 := by
    rw [show (1 : ℝ) = y^(0 : ℝ) from (Real.rpow_zero y).symm]
    exact Real.rpow_le_rpow_of_exponent_le hy.le (by norm_num)
  calc Real.exp (-(4 * Real.pi * y)) * y^(-((3 : ℝ)/4))
      ≤ Real.exp (-(4 * Real.pi * y)) * 1 := mul_le_mul_of_nonneg_left h_rpow_le h_exp_nn
    _ = Real.exp (-(4 * Real.pi * y)) := by ring

/-! ## §4 Integrability of the geometric-dominator integrand. -/

/-- **`geometric_dominator_integrable`** — `(2·exp(-(4π·y))/(1-exp(-(4π)))) · y^(-3/4)` integrable on `Ioi 1`.

Via `IntegrableOn.const_mul` (equivalent) on `exp_neg_four_pi_times_ypow_integrable`. -/
theorem geometric_dominator_integrable :
    IntegrableOn
      (fun y : ℝ => 2 * Real.exp (-(4 * Real.pi * y)) / (1 - Real.exp (-(4 * Real.pi)))
                      * y^(-((3 : ℝ)/4)))
      (Ioi (1 : ℝ)) := by
  have h_const : ∀ y : ℝ,
      2 * Real.exp (-(4 * Real.pi * y)) / (1 - Real.exp (-(4 * Real.pi))) * y^(-((3 : ℝ)/4))
        = (2 / (1 - Real.exp (-(4 * Real.pi))))
            * (Real.exp (-(4 * Real.pi * y)) * y^(-((3 : ℝ)/4))) := by
    intro y; ring
  rw [show (fun y : ℝ =>
    2 * Real.exp (-(4 * Real.pi * y)) / (1 - Real.exp (-(4 * Real.pi))) * y^(-((3 : ℝ)/4)))
    = (fun y => (2 / (1 - Real.exp (-(4 * Real.pi))))
                * (Real.exp (-(4 * Real.pi * y)) * y^(-((3 : ℝ)/4)))) from funext h_const]
  exact exp_neg_four_pi_times_ypow_integrable.const_mul _

/-! ## §5 Bound `∫ tail·y^(-3/4) ≤ exp(-4π)/(2π·(1-exp(-4π)))`. -/

/-- **`integral_tail_times_ypow_le_symbolic`** —

  `∫ y in Ioi 1, tail(y) · y^(-3/4)
     ≤ exp(-(4π))/(2π · (1 - exp(-(4π))))`.

Route: (a) `∫ tail·y^(-3/4) ≤ ∫ (2·exp(-(4π·y))/(1-exp(-(4π))))·y^(-3/4)` via
`setIntegral_mono_on` + r314c's `tail_le_geometric_dominator`.
(b) Factor constant: `= (2/(1-exp(-(4π)))) · ∫ exp(-(4π·y))·y^(-3/4)`.
(c) `≤ (2/(1-exp(-(4π)))) · exp(-(4π))/(4π)` via `integral_exp_neg_four_pi_times_ypow_le`.
(d) Simplify to `exp(-(4π))/(2π·(1-exp(-(4π))))`. -/
theorem integral_tail_times_ypow_le_symbolic :
    (∫ y in Ioi (1 : ℝ), tail y * y^(-((3 : ℝ)/4)))
      ≤ Real.exp (-(4 * Real.pi)) / (2 * Real.pi * (1 - Real.exp (-(4 * Real.pi)))) := by
  have h_one_sub_pos : 0 < 1 - Real.exp (-(4 * Real.pi)) := one_sub_exp_neg_four_pi_pos
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Step (a): setIntegral_mono_on
  have h_step_a :
      (∫ y in Ioi (1 : ℝ), tail y * y^(-((3 : ℝ)/4)))
        ≤ ∫ y in Ioi (1 : ℝ),
            2 * Real.exp (-(4 * Real.pi * y)) / (1 - Real.exp (-(4 * Real.pi)))
              * y^(-((3 : ℝ)/4)) := by
    refine setIntegral_mono_on tail_times_ypow_integrable_on_ioi_one
      geometric_dominator_integrable measurableSet_Ioi (fun y hy => ?_)
    have hy_ge : (1 : ℝ) ≤ y := le_of_lt hy
    have hy_pos : (0 : ℝ) < y := lt_trans zero_lt_one hy
    have h_rpow_nn : 0 ≤ y^(-((3 : ℝ)/4)) := (Real.rpow_pos_of_pos hy_pos _).le
    have h_geom := tail_le_geometric_dominator hy_ge
    exact mul_le_mul_of_nonneg_right h_geom h_rpow_nn
  -- Step (b): factor constant + step (c): bound
  have h_step_bc :
      (∫ y in Ioi (1 : ℝ),
          2 * Real.exp (-(4 * Real.pi * y)) / (1 - Real.exp (-(4 * Real.pi)))
            * y^(-((3 : ℝ)/4)))
        ≤ Real.exp (-(4 * Real.pi)) / (2 * Real.pi * (1 - Real.exp (-(4 * Real.pi)))) := by
    -- Rewrite integrand as const * (exp·y^(-3/4)):
    have h_rewrite :
        (fun y : ℝ =>
          2 * Real.exp (-(4 * Real.pi * y)) / (1 - Real.exp (-(4 * Real.pi)))
            * y^(-((3 : ℝ)/4)))
        = (fun y : ℝ =>
          (2 / (1 - Real.exp (-(4 * Real.pi))))
            * (Real.exp (-(4 * Real.pi * y)) * y^(-((3 : ℝ)/4)))) := by
      funext y; ring
    rw [h_rewrite, integral_const_mul]
    have h_const_nn : 0 ≤ 2 / (1 - Real.exp (-(4 * Real.pi))) := by
      apply div_nonneg (by norm_num) h_one_sub_pos.le
    calc 2 / (1 - Real.exp (-(4 * Real.pi)))
            * ∫ y in Ioi (1 : ℝ), Real.exp (-(4 * Real.pi * y)) * y^(-((3 : ℝ)/4))
        ≤ 2 / (1 - Real.exp (-(4 * Real.pi)))
            * (Real.exp (-(4 * Real.pi)) / (4 * Real.pi)) := by
          exact mul_le_mul_of_nonneg_left integral_exp_neg_four_pi_times_ypow_le h_const_nn
      _ = Real.exp (-(4 * Real.pi)) / (2 * Real.pi * (1 - Real.exp (-(4 * Real.pi)))) := by
          field_simp; ring
  linarith

/-! ## §6 THE r314d CORE SYMBOLIC BOUND. -/

/-- **`abs_R_geq_2_le_symbolic_bound`** — THE r314d CORE SYMBOLIC BOUND:

  `|R_geq_2| ≤ exp(-(4π))/(2π · (1 - exp(-(4π))))`.

Combines r314b's `abs_R_geq_2_le_integral_tail_times_ypow` with
`integral_tail_times_ypow_le_symbolic` (this file). -/
theorem abs_R_geq_2_le_symbolic_bound :
    |R_geq_2| ≤ Real.exp (-(4 * Real.pi)) / (2 * Real.pi * (1 - Real.exp (-(4 * Real.pi)))) :=
  abs_R_geq_2_le_integral_tail_times_ypow.trans integral_tail_times_ypow_le_symbolic

/-! ## §7 Axiom checks. -/

#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound.integral_exp_neg_four_pi_Ioi_one
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound.exp_neg_four_pi_integrable_on_ioi_one
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound.exp_neg_four_pi_times_ypow_integrable
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound.integral_exp_neg_four_pi_times_ypow_le
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound.geometric_dominator_integrable
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound.integral_tail_times_ypow_le_symbolic
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound.abs_R_geq_2_le_symbolic_bound

end PrincipiaTractalis.ChiPositive15RgeqTwoSymbolicBound
