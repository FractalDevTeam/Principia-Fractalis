/-
# Trig Book Brackets — axiom-free discharge of `CosBookBracket` / `SinBookBracket`

Closes the two residual `Prop`s named in `PF/Analytic/GammaIntervalBounds.lean`
(lines 516, 522):

  CosBookBracket : 0.27 < cos(0.41·π) ∧ cos(0.41·π) < 0.29
  SinBookBracket : 0.95 < sin(0.41·π) ∧ sin(0.41·π) < 0.97

True values: cos(0.41·π) ≈ 0.2790, sin(0.41·π) ≈ 0.9603.

## Strategy

Use the complementary-angle identities `cos(π/2 - t) = sin t` and
`sin(π/2 - t) = cos t` with `t := 0.09·π` (so `π/2 - t = 0.41·π`).
Then apply mathlib's centered Taylor remainder bounds

  `Real.sin_bound : |x| ≤ 1 → |sin x − (x − x³/6)| ≤ |x|⁴ · (5/96)`
  `Real.cos_bound : |x| ≤ 1 → |cos x − (1 − x²/2)| ≤ |x|⁴ · (5/96)`

For `t ∈ (0.2827, 0.2828)` (from mathlib's `Real.pi_gt_d6`, `Real.pi_lt_d6`),
the centered Taylor approximations sit deep inside the requested brackets and
the `5/96 · t⁴` error term is ~3·10⁻⁴, leaving margins of ~0.01 on both ends.

No project axioms, no `sorry`, no `decide`/`native_decide`.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import PF.Analytic.GammaIntervalBounds

namespace PrincipiaTractalis.Analytic

open Real

/-! ## Step 1 — Numerical bracket on `t = 0.09 · π` -/

/-- Two-sided rational bracket on `0.09·π` derived from `Real.pi_gt_d6`
    (`3.141592 < π`) and `Real.pi_lt_d6` (`π < 3.141593`). -/
lemma t_bracket : (0.28274328 : ℝ) < 0.09 * Real.pi ∧ 0.09 * Real.pi < 0.28274337 := by
  have h_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have h_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  refine ⟨?_, ?_⟩
  · have := mul_lt_mul_of_pos_left h_lo (by norm_num : (0 : ℝ) < 0.09)
    linarith
  · have := mul_lt_mul_of_pos_left h_hi (by norm_num : (0 : ℝ) < 0.09)
    linarith

/-- `0.09·π` is positive. -/
lemma t_pos : 0 < 0.09 * Real.pi := lt_trans (by norm_num : (0:ℝ) < 0.28274328) t_bracket.1

/-- `|0.09·π| ≤ 1` so the centered Taylor bounds apply. -/
lemma abs_t_le_one : |0.09 * Real.pi| ≤ 1 := by
  rw [abs_of_pos t_pos]
  have := t_bracket.2
  linarith

/-! ## Step 2 — Complementary-angle rewrites -/

/-- `0.41·π = π/2 − 0.09·π` (algebraic). -/
lemma split_041 : (0.41 : ℝ) * Real.pi = Real.pi / 2 - 0.09 * Real.pi := by ring

/-- `cos(0.41·π) = sin(0.09·π)`. -/
lemma cos_041_eq_sin_009 :
    Real.cos (0.41 * Real.pi) = Real.sin (0.09 * Real.pi) := by
  rw [split_041, Real.cos_pi_div_two_sub]

/-- `sin(0.41·π) = cos(0.09·π)`. -/
lemma sin_041_eq_cos_009 :
    Real.sin (0.41 * Real.pi) = Real.cos (0.09 * Real.pi) := by
  rw [split_041, Real.sin_pi_div_two_sub]

/-! ## Step 3 — Bracket on the Taylor centers `t − t³/6` and `1 − t²/2` -/

/-- `t − t³/6` lies in `(0.27893, 0.27907)` for `t = 0.09·π`. -/
lemma sin_taylor_center_bracket :
    (0.27893 : ℝ) < 0.09 * Real.pi - (0.09 * Real.pi)^3 / 6 ∧
    0.09 * Real.pi - (0.09 * Real.pi)^3 / 6 < 0.27907 := by
  set t := 0.09 * Real.pi with ht_def
  obtain ⟨h_lo, h_hi⟩ := t_bracket
  have hpos : 0 < t := t_pos
  -- bracket t² then t³
  have ht_sq_lo : (0.07994 : ℝ) < t^2 := by nlinarith [h_lo, hpos]
  have ht_sq_hi : t^2 < (0.07995 : ℝ) := by nlinarith [h_hi, hpos]
  have ht_cu_lo : (0.02259 : ℝ) < t^3 := by nlinarith [h_lo, hpos, ht_sq_lo]
  have ht_cu_hi : t^3 < (0.02263 : ℝ) := by nlinarith [h_hi, hpos, ht_sq_hi]
  -- now `t - t³/6`
  refine ⟨?_, ?_⟩
  · -- t - t³/6 > 0.27893: use t > 0.28274328 and t³ < 0.02263
    have : t - t^3 / 6 > 0.28274328 - 0.02263 / 6 := by linarith
    linarith
  · -- t - t³/6 < 0.27907: use t < 0.28274337 and t³ > 0.02259
    have : t - t^3 / 6 < 0.28274337 - 0.02259 / 6 := by linarith
    linarith

/-- `1 − t²/2` lies in `(0.96002, 0.96003)` for `t = 0.09·π`. -/
lemma cos_taylor_center_bracket :
    (0.96002 : ℝ) < 1 - (0.09 * Real.pi)^2 / 2 ∧
    1 - (0.09 * Real.pi)^2 / 2 < 0.96003 := by
  set t := 0.09 * Real.pi with ht_def
  obtain ⟨h_lo, h_hi⟩ := t_bracket
  have hpos : 0 < t := t_pos
  have ht_sq_lo : (0.07994 : ℝ) < t^2 := by nlinarith [h_lo, hpos]
  have ht_sq_hi : t^2 < (0.07995 : ℝ) := by nlinarith [h_hi, hpos]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-! ## Step 4 — Bracket on the Taylor remainder `|t|⁴ · 5/96` -/

/-- The Taylor remainder satisfies `|0.09·π|⁴ · (5/96) < 0.00034`. -/
lemma remainder_bound : |0.09 * Real.pi|^4 * (5 / 96) < (0.00034 : ℝ) := by
  rw [abs_of_pos t_pos]
  set t := 0.09 * Real.pi with ht_def
  obtain ⟨_, h_hi⟩ := t_bracket
  have hpos : 0 < t := t_pos
  -- t < 0.28274337  ⇒  t² < 0.07995  ⇒  t⁴ < 0.07995² < 0.00639201
  have ht_sq_hi : t^2 < (0.07995 : ℝ) := by nlinarith [h_hi, hpos]
  have ht_sq_pos : 0 < t^2 := by positivity
  have ht_q_hi : t^4 < (0.0064 : ℝ) := by nlinarith [ht_sq_hi, ht_sq_pos]
  have ht_q_pos : 0 < t^4 := by positivity
  -- t⁴ · 5/96 < 0.0064 · 5/96 ≈ 0.000334
  have : t^4 * (5 / 96) < (0.0064 : ℝ) * (5 / 96) := by
    exact mul_lt_mul_of_pos_right ht_q_hi (by norm_num)
  linarith

/-! ## Step 5 — Discharge `CosBookBracket` and `SinBookBracket` -/

/-- **CosBookBracket discharged**: `0.27 < cos(0.41·π) < 0.29`, axiom-free. -/
theorem cosBookBracket_proved : CosBookBracket := by
  rw [CosBookBracket, cos_041_eq_sin_009]
  -- sin(t) is within `5/96 · |t|⁴` of `t − t³/6`, where t = 0.09·π
  have h_bound : |Real.sin (0.09 * Real.pi) - (0.09 * Real.pi - (0.09 * Real.pi)^3 / 6)|
                  ≤ |0.09 * Real.pi|^4 * (5 / 96) :=
    Real.sin_bound abs_t_le_one
  have h_center := sin_taylor_center_bracket
  have h_rem := remainder_bound
  -- Convert |a − b| ≤ c to b − c ≤ a ≤ b + c
  have h_abs_unpack := abs_le.mp h_bound
  refine ⟨?_, ?_⟩
  · -- lower
    linarith [h_abs_unpack.1, h_center.1, h_center.2, h_rem]
  · -- upper
    linarith [h_abs_unpack.2, h_center.1, h_center.2, h_rem]

/-- **SinBookBracket discharged**: `0.95 < sin(0.41·π) < 0.97`, axiom-free. -/
theorem sinBookBracket_proved : SinBookBracket := by
  rw [SinBookBracket, sin_041_eq_cos_009]
  have h_bound : |Real.cos (0.09 * Real.pi) - (1 - (0.09 * Real.pi)^2 / 2)|
                  ≤ |0.09 * Real.pi|^4 * (5 / 96) :=
    Real.cos_bound abs_t_le_one
  have h_center := cos_taylor_center_bracket
  have h_rem := remainder_bound
  have h_abs_unpack := abs_le.mp h_bound
  refine ⟨?_, ?_⟩
  · -- lower
    linarith [h_abs_unpack.1, h_center.1, h_center.2, h_rem]
  · -- upper
    linarith [h_abs_unpack.2, h_center.1, h_center.2, h_rem]

/-- Bundled discharge of the composite numerical residual named in
    `GammaIntervalBounds.lean`: both trig brackets at once. -/
theorem cos_and_sin_book_brackets_proved : CosBookBracket ∧ SinBookBracket :=
  ⟨cosBookBracket_proved, sinBookBracket_proved⟩

end PrincipiaTractalis.Analytic
