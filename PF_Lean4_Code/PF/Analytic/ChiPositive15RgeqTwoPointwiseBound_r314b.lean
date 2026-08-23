/-
# r314b: Pointwise `|piece_2 y| ≤ tail(y) · y^(-3/4)` on `Ioi 1`
#       + `tail · y^(-3/4)` integrable on `Ioi 1` via `Integrable.mono'`
#       + refined bound `|R_geq_2| ≤ ∫ y in Ioi 1, tail(y) · y^(-3/4) dy`

★ 2026-08-22 r314b — pointwise refinement of r314's triangle inequality. Bounds
`|piece_2(y)|` above by the nonneg function `tail(y) · y^(-3/4)` on `Ioi 1`,
where `tail(y) := evenKernel 0 y − 1 − 2·exp(−π·y)` (nonneg by r313's
`tail_nonneg_of_pos`). Proves integrability of the RHS via `Integrable.mono'`
dominated by `evenKernel 0 y − 1` (integrable via mathlib's
`isBigO_atTop_evenKernel_sub` + `integrable_of_isBigO_exp_neg`).

Endpoint: `|R_geq_2| ≤ ∫ y in Ioi 1, tail(y) · y^(-3/4) dy`.

## Framework-first status (per MASTER DIRECTIVE)

NOT a numerical discharge. Analytic refinement. Removes the naked `|piece_2|`
inside the integral and replaces it with the manifestly nonneg
`tail · y^(-3/4)`, which is directly attackable via geometric domination in r314c.

Standing rules absolute: no `sorry`, no `native_decide`, no floating-point-as-proof,
no hidden oracle, no assumed transcendental enclosure.

## What r314b delivers

- `evenKernel_zero_sub_one_integrable_on_ioi_one` : `IntegrableOn (evenKernel 0 · − 1) (Ioi 1)`
  via `isBigO_atTop_evenKernel_sub 0` + `integrable_of_isBigO_exp_neg`.

- `tail_times_ypow_le_evenKernel_sub_one` : `∀ y ∈ Ioi 1, tail(y) · y^(-3/4) ≤ evenKernel 0 y − 1`
  via `tail ≤ evenKernel 0 y − 1` (since `2·exp(−π·y) ≥ 0`) and `y^(-3/4) ≤ 1` (for `y ≥ 1`).

- `tail_times_ypow_integrable_on_ioi_one` : `IntegrableOn (fun y => tail y · y^(-3/4)) (Ioi 1)`
  via `Integrable.mono'` with `evenKernel_zero_sub_one_integrable_on_ioi_one` as dominator.

- `abs_piece_2_le_tail_mul_ypow` : `∀ y ∈ Ioi 1, |piece_2 y| ≤ tail(y) · y^(-3/4)`
  via `tail_nonneg_of_pos` (r313) + `|cos| ≤ 1` + `y^(-3/4) > 0`.

- `abs_R_geq_2_le_integral_tail_times_ypow` : `|R_geq_2| ≤ ∫ y in Ioi 1, tail(y) · y^(-3/4) dy`
  via r314's `abs_R_geq_2_le_integral_abs_piece_2` + `setIntegral_mono_on`.

## r314c direction

Prove `∀ y ≥ 1, tail(y) ≤ 2·exp(−4πy)/(1 − exp(−4π))` via
`hasSum_evenKernel_zero_sub_one` (r313) shifted at `n ↦ n+2` giving
`HasSum (fun n => 2·exp(−π(n+2)²·y)) (tail y)`, then termwise domination
`exp(−π(n+2)²·y) ≤ exp(−4πy) · (exp(−4π))^n` (using `(n+2)² ≥ 4 + 4n` for
`n ≥ 0` and `y ≥ 1`), then `hasSum_geometric_of_lt_one`. Integrate:
`∫ y in Ioi 1, exp(−4πy) · y^(-3/4) dy ≤ ∫ y in Ioi 1, exp(−4πy) dy = exp(−4π)/(4π)`.
Endpoint: `|R_geq_2| ≤ exp(−4π) / (2π · (1 − exp(−4π)))`.

Book anchors: Ch 20 § 20.4, Ch 34A § 34A.5.
-/

import PF.Analytic.ChiPositive15RgeqTwoIntegralForm_r314
import Mathlib.MeasureTheory.Integral.ExpDecay

namespace PrincipiaTractalis.ChiPositive15RgeqTwoPointwiseBound

open Complex MeasureTheory Set Real
open HurwitzZeta
open PrincipiaTractalis.ChiPositive15ThetaTruncation
open PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm

/-! ## §1 The tail function `tail(y) := evenKernel 0 y − 1 − 2·exp(−π·y)`. -/

/-- The tail function `tail(y) := evenKernel 0 y − 1 − 2·exp(−π·y)`, nonneg for `y > 0`
by r313's `tail_nonneg_of_pos`. -/
noncomputable def tail (y : ℝ) : ℝ := evenKernel 0 y - 1 - 2 * Real.exp (-Real.pi * y)

/-! ## §2 Integrability of `evenKernel 0 · − 1` on `Ioi 1`. -/

/-- **`evenKernel_zero_sub_one_integrable_on_ioi_one`** — the theta-minus-1
function is integrable on `Ioi 1` via `isBigO_atTop_evenKernel_sub 0`
(mathlib) + `integrable_of_isBigO_exp_neg`. -/
theorem evenKernel_zero_sub_one_integrable_on_ioi_one :
    IntegrableOn (fun y : ℝ => evenKernel 0 y - 1) (Ioi (1 : ℝ)) := by
  obtain ⟨p, hp_pos, hp_bigO⟩ := isBigO_atTop_evenKernel_sub (0 : UnitAddCircle)
  -- hp_bigO : (fun y => evenKernel 0 y - (if 0 = 0 then 1 else 0)) =O[atTop] exp(-p * ·)
  simp only at hp_bigO
  -- Note: (if 0 = 0 then 1 else 0) = 1 should simplify automatically or via if_pos rfl
  -- hp_bigO : (fun y => evenKernel 0 y - 1) =O[atTop] fun x => rexp (-p * x)
  refine integrable_of_isBigO_exp_neg (b := p) hp_pos ?_ hp_bigO
  -- ContinuousOn (fun y => evenKernel 0 y - 1) (Ici 1)
  refine ContinuousOn.sub ?_ continuousOn_const
  exact (continuousOn_evenKernel (0 : UnitAddCircle)).mono
    (fun y hy => mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one hy))

/-! ## §3 Pointwise bound `tail(y) · y^(-3/4) ≤ evenKernel 0 y − 1` on `Ioi 1`. -/

/-- **`tail_times_ypow_le_evenKernel_sub_one`** — pointwise domination:

  `∀ y ∈ Ioi 1, tail(y) · y^(-3/4) ≤ evenKernel 0 y − 1`.

Uses: `tail(y) ≤ evenKernel 0 y - 1` (since `2·exp(−π·y) ≥ 0`) and `y^(-3/4) ≤ 1` (for `y ≥ 1`).
Both are nonneg, so the product is bounded by the LHS product with 1 = the dominator. -/
theorem tail_times_ypow_le_evenKernel_sub_one {y : ℝ} (hy : y ∈ Ioi (1 : ℝ)) :
    tail y * y^(-((3 : ℝ)/4)) ≤ evenKernel 0 y - 1 := by
  have hy_pos : (0 : ℝ) < y := lt_trans zero_lt_one hy
  have h_tail_nn : 0 ≤ tail y := tail_nonneg_of_pos hy_pos
  have h_ek_ge_tail : tail y ≤ evenKernel 0 y - 1 := by
    unfold tail
    have h_exp_nonneg : 0 ≤ Real.exp (-Real.pi * y) := (Real.exp_pos _).le
    linarith
  have h_ek_sub_nn : 0 ≤ evenKernel 0 y - 1 := le_trans h_tail_nn h_ek_ge_tail
  have h_rpow_le : y^(-((3 : ℝ)/4)) ≤ 1 := by
    rw [show (1 : ℝ) = y^(0 : ℝ) from (Real.rpow_zero y).symm]
    exact Real.rpow_le_rpow_of_exponent_le hy.le (by norm_num)
  have h_rpow_nn : 0 ≤ y^(-((3 : ℝ)/4)) := (Real.rpow_pos_of_pos hy_pos _).le
  calc tail y * y^(-((3 : ℝ)/4))
      ≤ tail y * 1 := by exact mul_le_mul_of_nonneg_left h_rpow_le h_tail_nn
    _ = tail y := by ring
    _ ≤ evenKernel 0 y - 1 := h_ek_ge_tail

/-! ## §4 Integrability of `tail · y^(-3/4)` on `Ioi 1`. -/

/-- **`tail_times_ypow_integrable_on_ioi_one`** — `tail · y^(-3/4)` is integrable
on `Ioi 1` via `Integrable.mono'` bounded above by `evenKernel 0 y - 1` (integrable). -/
theorem tail_times_ypow_integrable_on_ioi_one :
    IntegrableOn (fun y : ℝ => tail y * y^(-((3 : ℝ)/4))) (Ioi (1 : ℝ)) := by
  refine Integrable.mono' evenKernel_zero_sub_one_integrable_on_ioi_one ?_ ?_
  · -- AEStronglyMeasurable (fun y => tail y * y^(-3/4)) (volume.restrict (Ioi 1))
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    unfold tail
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_const) ?_
      · exact (continuousOn_evenKernel (0 : UnitAddCircle)).mono
          (fun y hy => mem_Ioi.mpr (lt_trans zero_lt_one hy))
      · exact (continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul continuous_id))).continuousOn
    · intro y hy
      have hy_pos : 0 < y := lt_trans zero_lt_one hy
      exact (Real.continuousAt_rpow_const _ _ (Or.inl hy_pos.ne')).continuousWithinAt
  · -- ∀ᵐ y ∂(volume.restrict Ioi 1), ‖tail y * y^(-3/4)‖ ≤ evenKernel 0 y - 1
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun y hy => ?_))
    have hy_pos : (0 : ℝ) < y := lt_trans zero_lt_one hy
    have h_tail_nn : 0 ≤ tail y := tail_nonneg_of_pos hy_pos
    have h_rpow_nn : 0 ≤ y^(-((3 : ℝ)/4)) := (Real.rpow_pos_of_pos hy_pos _).le
    have h_prod_nn : 0 ≤ tail y * y^(-((3 : ℝ)/4)) := mul_nonneg h_tail_nn h_rpow_nn
    rw [Real.norm_eq_abs, abs_of_nonneg h_prod_nn]
    exact tail_times_ypow_le_evenKernel_sub_one hy

/-! ## §5 Pointwise `|piece_2 y| ≤ tail(y) · y^(-3/4)`. -/

/-- **`abs_piece_2_le_tail_mul_ypow`** — pointwise absolute-value bound on `Ioi 1`:

  `∀ y ∈ Ioi 1, |piece_2 y| ≤ tail(y) · y^(-3/4)`.

Uses `tail(y) ≥ 0` (r313), `y^(-3/4) > 0`, `|cos| ≤ 1`. -/
theorem abs_piece_2_le_tail_mul_ypow {y : ℝ} (hy : y ∈ Ioi (1 : ℝ)) :
    |piece_2 y| ≤ tail y * y^(-((3 : ℝ)/4)) := by
  have hy_pos : 0 < y := lt_trans zero_lt_one hy
  have h_tail_nn : 0 ≤ tail y := tail_nonneg_of_pos hy_pos
  have h_rpow_pos : 0 < y^(-((3 : ℝ)/4)) := Real.rpow_pos_of_pos hy_pos _
  have h_cos : |Real.cos ((15 / 2) * Real.log y)| ≤ 1 := Real.abs_cos_le_one _
  unfold piece_2 tail
  calc |(evenKernel 0 y - 1 - 2 * Real.exp (-Real.pi * y)) * y^(-((3 : ℝ)/4))
          * Real.cos ((15 / 2) * Real.log y)|
      = |evenKernel 0 y - 1 - 2 * Real.exp (-Real.pi * y)| * y^(-((3 : ℝ)/4))
          * |Real.cos ((15 / 2) * Real.log y)| := by
        rw [abs_mul, abs_mul, abs_of_pos h_rpow_pos]
    _ = (evenKernel 0 y - 1 - 2 * Real.exp (-Real.pi * y)) * y^(-((3 : ℝ)/4))
          * |Real.cos ((15 / 2) * Real.log y)| := by
        congr 2
        exact abs_of_nonneg h_tail_nn
    _ ≤ (evenKernel 0 y - 1 - 2 * Real.exp (-Real.pi * y)) * y^(-((3 : ℝ)/4)) * 1 := by
        apply mul_le_mul_of_nonneg_left h_cos
        exact mul_nonneg h_tail_nn h_rpow_pos.le
    _ = (evenKernel 0 y - 1 - 2 * Real.exp (-Real.pi * y)) * y^(-((3 : ℝ)/4)) := by ring

/-! ## §6 The refined analytic bound `|R_geq_2| ≤ ∫ tail · y^(-3/4)`. -/

/-- **`abs_R_geq_2_le_integral_tail_times_ypow`** — THE r314b CORE REFINED BOUND:

  `|R_geq_2| ≤ ∫ y in Ioi 1, tail(y) · y^(-3/4) dy`.

Combines r314's `abs_R_geq_2_le_integral_abs_piece_2` with the pointwise bound
`abs_piece_2_le_tail_mul_ypow` via `setIntegral_mono_on` (requires integrability
of both sides: `|piece_2|` from r314's `piece_2_integrable_on_ioi_one.norm`;
`tail · y^(-3/4)` from §4). -/
theorem abs_R_geq_2_le_integral_tail_times_ypow :
    |R_geq_2| ≤ ∫ y in Ioi (1 : ℝ), tail y * y^(-((3 : ℝ)/4)) := by
  refine abs_R_geq_2_le_integral_abs_piece_2.trans ?_
  refine setIntegral_mono_on piece_2_integrable_on_ioi_one.norm
    tail_times_ypow_integrable_on_ioi_one measurableSet_Ioi (fun y hy => ?_)
  exact abs_piece_2_le_tail_mul_ypow hy

/-! ## §7 Axiom checks. -/

#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoPointwiseBound.evenKernel_zero_sub_one_integrable_on_ioi_one
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoPointwiseBound.tail_times_ypow_le_evenKernel_sub_one
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoPointwiseBound.tail_times_ypow_integrable_on_ioi_one
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoPointwiseBound.abs_piece_2_le_tail_mul_ypow
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoPointwiseBound.abs_R_geq_2_le_integral_tail_times_ypow

end PrincipiaTractalis.ChiPositive15RgeqTwoPointwiseBound
