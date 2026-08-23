/-
# r314: `R_{≥2}` integral form + triangle inequality
#      `R_geq_2 = ∫_{Ioi 1} piece_2` and `|R_geq_2| ≤ ∫_{Ioi 1} |piece_2|`

★ 2026-08-22 r314 — analytic scaffolding for the certified `R_{≥2}` remainder
theorem. Establishes:

- `piece_1 := 2·exp(−π·y) · y^(−3/4) · cos((15/2) log y)` is integrable on `Ioi 1`
  via `integrable_of_isBigO_exp_neg` at `b = π` (bounded by `2·exp(−π·y)` for `y ≥ 1`).

- `piece_2 := (evenKernel 0 y − 1 − 2·exp(−π·y)) · y^(−3/4) · cos((15/2) log y)` is
  integrable on `Ioi 1` via `IntegrableOn.sub` (`i15 − piece_1`, both integrable).

- Integral form: `R_geq_2 = ∫ y in Ioi 1, piece_2(y) dy`. Follows from
  `R_geq_2 := I_15 − J_1`, `I_15 = ∫ i15_integrand`, `J_1 = ∫ piece_1`, and
  `∫ (i15 − piece_1) = ∫ piece_2` (via `integral_sub`).

- Triangle inequality: `|R_geq_2| ≤ ∫ y in Ioi 1, |piece_2(y)| dy`. Via
  `norm_integral_le_integral_norm` on the Bochner integral.

## Framework-first scope (SPLIT per Pabs's authorization)

Per Pabs's r313 directive authorizing splits "along mathematically necessary
boundaries":

- **r314 (this)**: measure-theoretic analytic scaffolding — piece integrability,
  integral form of `R_geq_2`, triangle inequality bound.
- **r314b** (next): pointwise `|piece_2(y)| ≤ tail(y) · y^(-3/4)` on `Ioi 1`
  (via `tail ≥ 0` from r313 + `|cos| ≤ 1`); integrability of `tail · y^(-3/4)`
  via `Integrable.mono'` bounded by `evenKernel 0 y - 1` (integrable via
  `isBigO_atTop_evenKernel_sub`).
- **r314c** (after): geometric bound `∀ y ≥ 1, tail(y) ≤ 2·exp(−4πy)/(1 − exp(−4π))`
  via `(n+2)² ≥ 4 + 4n` for `n ≥ 0` + series-theoretic geometric domination.
- **r314d** (after): integrate to `|R_geq_2| ≤ exp(−4π)/(2π·(1−exp(−4π)))` + rationalize
  via `exp(4π) > 22^4` (Taylor `π > 3.14` + truncated `exp(π) > 22`) yielding rational
  `E < 10^(-6)`.

Each split is along a genuinely distinct mathematical machinery. r314 uses
Bochner integration / integral_sub / norm_integral_le. r314b uses pointwise
absolute-value + tail-nonneg + `Integrable.mono'`. r314c uses `hasSum_geometric`
+ termwise domination. r314d uses `Real.exp` Taylor bounds. Splitting reduces
cognitive/verification load per landing while each step removes a dependency.

Standing rules absolute: no `sorry`, no `native_decide`, no floating-point-as-proof,
no hidden oracle, no assumed transcendental enclosure.

## What r314 delivers

- `piece_1`, `piece_2`, `i15_integrand` definitions.
- `i15_integrand_eq_piece_1_add_piece_2` / `piece_2_eq_i15_sub_piece_1` — algebra.
- `piece_1_integrable_on_ioi_one` — via `integrable_of_isBigO_exp_neg` at `b = π`.
- `i15_integrand_integrable_on_ioi_one` — via r312's cosine-integrand chain.
- `piece_2_integrable_on_ioi_one` — via `IntegrableOn.sub` on `i15 − piece_1`.
- `J_1_eq_integral_piece_1` — `J_1 = ∫ piece_1` (unfold + `integral_const_mul`).
- `I_15_eq_integral_i15_integrand` — `I_15 = ∫ i15_integrand` (`rfl`).
- `R_geq_2_eq_integral_piece_2` — `R_geq_2 = ∫ piece_2` (via `integral_sub`).
- `abs_R_geq_2_le_integral_abs_piece_2` — `|R_geq_2| ≤ ∫ |piece_2|` (triangle inequality).

Book anchors: Ch 20 § 20.4, Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.ChiPositive15ThetaTruncation_r313
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm

open Complex MeasureTheory Set Real
open HurwitzZeta
open PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit
open PrincipiaTractalis.ChiPositive15ThetaTruncation

/-! ## §1 Integrand shorthands. -/

/-- **`piece_1`** — the `n = 1` (`k = 1` theta) contribution:
`2·exp(−π·y) · y^(−3/4) · cos((15/2) log y)`. -/
noncomputable def piece_1 : ℝ → ℝ := fun y =>
  2 * Real.exp (-Real.pi * y) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y)

/-- **`piece_2`** — the tail (indices `k ≥ 2` theta) contribution:
`(evenKernel 0 y − 1 − 2·exp(−π·y)) · y^(−3/4) · cos((15/2) log y)`. -/
noncomputable def piece_2 : ℝ → ℝ := fun y =>
  (evenKernel 0 y - 1 - 2 * Real.exp (-Real.pi * y))
    * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y)

/-- **`i15_integrand`** — the `I_15` integrand:
`(evenKernel 0 y − 1) · y^(−3/4) · cos((15/2) log y)`. -/
noncomputable def i15_integrand : ℝ → ℝ := fun y =>
  (evenKernel 0 y - 1) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y)

/-- Pointwise identity `i15_integrand = piece_1 + piece_2`. -/
theorem i15_integrand_eq_piece_1_add_piece_2 (y : ℝ) :
    i15_integrand y = piece_1 y + piece_2 y := by
  unfold i15_integrand piece_1 piece_2
  ring

/-- Pointwise identity `piece_2 = i15_integrand − piece_1`. -/
theorem piece_2_eq_i15_sub_piece_1 (y : ℝ) :
    piece_2 y = i15_integrand y - piece_1 y := by
  unfold i15_integrand piece_1 piece_2
  ring

/-! ## §2 Integrability of `piece_1` on `Ioi 1`. -/

/-- **`piece_1_integrable_on_ioi_one`** — `piece_1` is integrable on `Ioi 1`.

Via `integrable_of_isBigO_exp_neg` at `b = π`: `piece_1` is continuous on `Ici 1`
(product of continuous functions, `y^(-3/4)` continuous on `Ioi 0 ⊃ Ici 1`,
`log y` continuous on `Ioi 0 ⊃ Ici 1`) and `|piece_1(y)| ≤ 2·exp(−π·y)` for
`y ≥ 1` (since `y^(-3/4) ≤ 1` and `|cos| ≤ 1`), giving
`piece_1 =O[atTop] fun x => exp(-π*x)`. -/
theorem piece_1_integrable_on_ioi_one : IntegrableOn piece_1 (Ioi (1 : ℝ)) := by
  refine integrable_of_isBigO_exp_neg (b := Real.pi) Real.pi_pos ?_ ?_
  · -- ContinuousOn piece_1 (Ici 1)
    unfold piece_1
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).continuousOn
    · intro y hy
      have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy
      exact (Real.continuousAt_rpow_const _ _ (Or.inl hy_pos.ne')).continuousWithinAt
    · intro y hy
      have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy
      refine ContinuousAt.continuousWithinAt ?_
      exact Real.continuous_cos.continuousAt.comp
        ((continuousAt_const).mul (Real.continuousAt_log hy_pos.ne'))
  · -- piece_1 =O[atTop] fun x => exp(-π * x)
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy
    have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy
    unfold piece_1
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h_cos : |Real.cos ((15 / 2) * Real.log y)| ≤ 1 := Real.abs_cos_le_one _
    have h_rpow_pos : 0 < y^(-((3 : ℝ)/4)) := Real.rpow_pos_of_pos hy_pos _
    have h_rpow_le : y^(-((3 : ℝ)/4)) ≤ 1 := by
      rw [show (1 : ℝ) = y^(0 : ℝ) from (Real.rpow_zero y).symm]
      exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    have h_exp_nonneg : 0 ≤ Real.exp (-Real.pi * y) := (Real.exp_pos _).le
    calc |2 * Real.exp (-Real.pi * y) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y)|
        = 2 * Real.exp (-Real.pi * y) * y^(-((3 : ℝ)/4))
            * |Real.cos ((15 / 2) * Real.log y)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
              abs_of_nonneg h_exp_nonneg, abs_of_pos h_rpow_pos]
      _ ≤ 2 * Real.exp (-Real.pi * y) * y^(-((3 : ℝ)/4)) * 1 := by
          apply mul_le_mul_of_nonneg_left h_cos
          positivity
      _ = 2 * Real.exp (-Real.pi * y) * y^(-((3 : ℝ)/4)) := by ring
      _ ≤ 2 * Real.exp (-Real.pi * y) * 1 := by
          apply mul_le_mul_of_nonneg_left h_rpow_le
          positivity
      _ = 2 * Real.exp (-Real.pi * y) := by ring
      _ = 2 * |Real.exp (-Real.pi * y)| := by rw [abs_of_nonneg h_exp_nonneg]

/-! ## §3 Integrability of `piece_2` on `Ioi 1`. -/

/-- **`i15_integrand_integrable_on_ioi_one`** — the `I_15` integrand is integrable
on `Ioi 1`. From r312's `tail_integrable_on_ioi_one` (complex integrand) via
`integral_re`'s integrability transfer + r312's `integrand_re_pointwise` giving
pointwise equality on `Ioi 1`. -/
theorem i15_integrand_integrable_on_ioi_one : IntegrableOn i15_integrand (Ioi (1 : ℝ)) := by
  unfold i15_integrand
  have h_complex := tail_integrable_on_ioi_one
  have h_re := h_complex.re
  refine h_re.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun y hy => ?_))
  exact integrand_re_pointwise hy

/-- **`piece_2_integrable_on_ioi_one`** — `piece_2` is integrable on `Ioi 1`.

Via `IntegrableOn.sub` on the difference `piece_2 = i15_integrand - piece_1`
(pointwise via `piece_2_eq_i15_sub_piece_1`), both integrable from §2 and §3. -/
theorem piece_2_integrable_on_ioi_one : IntegrableOn piece_2 (Ioi (1 : ℝ)) := by
  have h_sub := i15_integrand_integrable_on_ioi_one.sub piece_1_integrable_on_ioi_one
  refine h_sub.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun y _hy => ?_))
  exact (piece_2_eq_i15_sub_piece_1 y).symm

/-! ## §4 Integral form of `R_geq_2`. -/

/-- **`J_1_eq_integral_piece_1`** — the definitional equality `J_1 = ∫ piece_1`. -/
theorem J_1_eq_integral_piece_1 : J_1 = ∫ y in Ioi (1 : ℝ), piece_1 y := by
  unfold J_1 piece_1
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _hy => ?_)
  ring

/-- **`I_15_eq_integral_i15_integrand`** — the definitional equality
`I_15 = ∫ i15_integrand`. -/
theorem I_15_eq_integral_i15_integrand :
    I_15 = ∫ y in Ioi (1 : ℝ), i15_integrand y := rfl

/-- **`R_geq_2_eq_integral_piece_2`** — THE KEY INTEGRAL FORM:

  `R_geq_2 = ∫ y in Ioi 1, piece_2 y`.

Via `R_geq_2 := I_15 − J_1`, `I_15 = ∫ i15_integrand`, `J_1 = ∫ piece_1`, and
`∫ i15_integrand − ∫ piece_1 = ∫ (i15_integrand − piece_1) = ∫ piece_2`
via `integral_sub` (both integrable). -/
theorem R_geq_2_eq_integral_piece_2 :
    R_geq_2 = ∫ y in Ioi (1 : ℝ), piece_2 y := by
  unfold R_geq_2
  rw [I_15_eq_integral_i15_integrand, J_1_eq_integral_piece_1,
      ← integral_sub i15_integrand_integrable_on_ioi_one piece_1_integrable_on_ioi_one]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _hy => ?_)
  exact (piece_2_eq_i15_sub_piece_1 y).symm

/-! ## §5 Triangle inequality: `|R_geq_2| ≤ ∫ |piece_2|`. -/

/-- **`abs_R_geq_2_le_integral_abs_piece_2`** — THE r314 CORE TRIANGLE BOUND:

  `|R_geq_2| ≤ ∫ y in Ioi 1, |piece_2 y| dy`.

Via `norm_integral_le_integral_norm` on the Bochner integral, using
`Real.norm_eq_abs` to convert. This is the entry point for r314b to bound
`∫ |piece_2|` via the pointwise `|piece_2(y)| ≤ tail(y) · y^(-3/4)` on `Ioi 1`. -/
theorem abs_R_geq_2_le_integral_abs_piece_2 :
    |R_geq_2| ≤ ∫ y in Ioi (1 : ℝ), |piece_2 y| := by
  rw [R_geq_2_eq_integral_piece_2,
      show |∫ y in Ioi (1 : ℝ), piece_2 y| = ‖∫ y in Ioi (1 : ℝ), piece_2 y‖ from
        (Real.norm_eq_abs _).symm]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine le_of_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _hy => ?_)
  exact Real.norm_eq_abs _

/-! ## §6 Axiom checks. -/

#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm.piece_1_integrable_on_ioi_one
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm.i15_integrand_integrable_on_ioi_one
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm.piece_2_integrable_on_ioi_one
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm.J_1_eq_integral_piece_1
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm.I_15_eq_integral_i15_integrand
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm.R_geq_2_eq_integral_piece_2
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm.abs_R_geq_2_le_integral_abs_piece_2

end PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm
