/-
# Full axiom-free discharge of `BookEval019_ShiftBound`

This file composes the already-proven ingredients
  * `Gamma_0_19_lt`, `Gamma_0_19_pos`                (`GammaIntervalBounds.lean`)
  * `beta_book_pos`                                    (ditto)
  * `rpowBookBracketProved`                            (`RpowBookBracket.lean`)
  * `log_z_book_eq`, `log_z_book_ne_zero`              (`BookEvalBound018.lean`,
                                                       `LogZBookNeZero.lean`)
  * `bookEvaluation_019_lower_bound_of_shift_bound`    (`BookEvalNumericalBounds.lean`)

with a NEW Taylor-remainder bracket on `Real.sin (0.405·π)` to prove

  `BookEval019_ShiftBound`
    := `(0.222144147 : ℝ) <
         Complex.re (polyLogMonodromyShift (-1) ((0.19 : ℝ) : ℂ) z_book)`

axiom-free.

## Trig-angle correction note

`TrigBookBrackets.lean` proves brackets at `0.41·π`, but the shift formula
at `s = 0.19` involves `0.405·π = π(1 − s)/2`. We build a new bracket at
`0.405·π` via the same complementary-angle Taylor route.

## Closed-form for `Re(shift)`

  log z_book = (β:ℂ) · (−I)               where β := 2π − π√2 > 0
  log (log z_book) = log β − (π/2)·I
  (log z_book)^(0.19−1)
       = β^(−0.81) · (cos(0.405π) + sin(0.405π) · I)
  shift = −2π · I · β^(−0.81) · (cos(0.405π) + sin(0.405π) · I) / Γ(0.19)
  Re(shift) = 2π · β^(−0.81) · sin(0.405π) / Γ(0.19)

## Numerical sanity (margin ≈ 0.49)

  2π · 0.60 · 0.95 / 5.04 ≈ 0.71      vs target 0.222144147

0 project axioms, 0 sorries, 0 `decide`/`native_decide` in this file.
-/

import PF.Analytic.BookEvalNumericalBounds
import PF.Analytic.BookEvalBound019
import PF.Analytic.LogZBookNeZero
import PF.Analytic.RpowBookBracket
import PF.Analytic.GammaIntervalBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Section 1 — Taylor bracket on `Real.sin (0.405 · π)`

Complementary-angle identity `sin(π/2 − t) = cos t` with `t = 0.095·π`,
then `Real.cos_bound` (centered Taylor of `cos` to order 2 with remainder
`|t|⁴ · 5/96`).
-/

lemma s_bracket : (0.29845124 : ℝ) < 0.095 * Real.pi ∧
                  0.095 * Real.pi < 0.29845134 := by
  have h_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have h_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  refine ⟨?_, ?_⟩
  · have := mul_lt_mul_of_pos_left h_lo (by norm_num : (0 : ℝ) < 0.095)
    linarith
  · have := mul_lt_mul_of_pos_left h_hi (by norm_num : (0 : ℝ) < 0.095)
    linarith

lemma s_pos : 0 < 0.095 * Real.pi :=
  lt_trans (by norm_num : (0:ℝ) < 0.29845124) s_bracket.1

lemma abs_s_le_one : |0.095 * Real.pi| ≤ 1 := by
  rw [abs_of_pos s_pos]
  have := s_bracket.2
  linarith

lemma split_0405 : (0.405 : ℝ) * Real.pi = Real.pi / 2 - 0.095 * Real.pi := by ring

lemma sin_0405_eq_cos_0095 :
    Real.sin (0.405 * Real.pi) = Real.cos (0.095 * Real.pi) := by
  rw [split_0405, Real.sin_pi_div_two_sub]

/-- `1 − t²/2 ∈ (0.95546, 0.95547)` for `t = 0.095·π`. -/
lemma cos_taylor_center_bracket_0095 :
    (0.95546 : ℝ) < 1 - (0.095 * Real.pi)^2 / 2 ∧
    1 - (0.095 * Real.pi)^2 / 2 < 0.95547 := by
  set t := 0.095 * Real.pi with ht_def
  obtain ⟨h_lo, h_hi⟩ := s_bracket
  have hpos : 0 < t := s_pos
  -- 0.29845124² ≈ 0.0890731, 0.29845134² ≈ 0.0890734, so t² ∈ (0.089073, 0.089075).
  have ht_sq_lo : (0.089073 : ℝ) < t^2 := by nlinarith [h_lo, hpos]
  have ht_sq_hi : t^2 < (0.089075 : ℝ) := by nlinarith [h_hi, hpos]
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- Taylor remainder bound: `|0.095·π|⁴ · (5/96) < 0.00042`. -/
lemma remainder_bound_0095 : |0.095 * Real.pi|^4 * (5 / 96) < (0.00042 : ℝ) := by
  rw [abs_of_pos s_pos]
  set t := 0.095 * Real.pi with ht_def
  obtain ⟨_, h_hi⟩ := s_bracket
  have hpos : 0 < t := s_pos
  have ht_sq_hi : t^2 < (0.089075 : ℝ) := by nlinarith [h_hi, hpos]
  have ht_sq_pos : 0 < t^2 := by positivity
  have ht_q_hi : t^4 < (0.00794 : ℝ) := by nlinarith [ht_sq_hi, ht_sq_pos]
  have : t^4 * (5 / 96) < (0.00794 : ℝ) * (5 / 96) := by
    exact mul_lt_mul_of_pos_right ht_q_hi (by norm_num)
  linarith

/-- **Lower bracket on `sin(0.405·π)`**: `0.95 < sin(0.405·π)`. -/
theorem sin_0405_pi_gt : (0.95 : ℝ) < Real.sin (0.405 * Real.pi) := by
  rw [sin_0405_eq_cos_0095]
  have h_bound : |Real.cos (0.095 * Real.pi) - (1 - (0.095 * Real.pi)^2 / 2)|
                  ≤ |0.095 * Real.pi|^4 * (5 / 96) :=
    Real.cos_bound abs_s_le_one
  have h_center := cos_taylor_center_bracket_0095
  have h_rem := remainder_bound_0095
  have h_abs_unpack := abs_le.mp h_bound
  linarith [h_abs_unpack.1, h_center.1, h_center.2, h_rem]

/-! ## Section 2 — Closed-form algebraic identity for `Re(shift)` -/

/-- `log z_book = (β:ℂ) · (-I)` where `β = 2π − π·√2 > 0`. -/
lemma log_z_book_as_beta_neg_I :
    Complex.log z_book = (beta_book : ℂ) * (-I) := by
  rw [log_z_book_eq]
  unfold beta_book
  push_cast
  ring

/-- `Complex.log(log z_book) = (Real.log β : ℂ) - (π/2 : ℂ) · I`. -/
lemma log_log_z_book :
    Complex.log (Complex.log z_book) =
      (Real.log beta_book : ℂ) - ((Real.pi / 2 : ℝ) : ℂ) * I := by
  rw [log_z_book_as_beta_neg_I]
  have hβ : (0 : ℝ) < beta_book := beta_book_pos
  have hI_ne : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  rw [Complex.log_ofReal_mul hβ hI_ne, Complex.log_neg_I]
  push_cast
  ring

/-- Algebraic identity in ℂ: the exponent `((log β :ℂ) − (π/2 :ℂ)·I) · (0.19 − 1)`
    equals `(−0.81·log β :ℂ) + (0.405·π :ℂ)·I`. -/
private lemma exponent_simp :
    ((Real.log beta_book : ℂ) - ((Real.pi / 2 : ℝ) : ℂ) * I) *
        (((0.19 : ℝ) : ℂ) - 1) =
      ((-0.81 * Real.log beta_book : ℝ) : ℂ) +
      ((0.405 * Real.pi : ℝ) : ℂ) * I := by
  -- Switch all the real-coerced literals to canonical complex form.
  have h019 : ((0.19 : ℝ) : ℂ) = (0.19 : ℂ) := by norm_cast
  have hπ2 : ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 := by push_cast; ring
  have h_neg81 : ((-0.81 * Real.log beta_book : ℝ) : ℂ) =
                 -0.81 * (Real.log beta_book : ℂ) := by
    rw [Complex.ofReal_mul]; norm_num
  have h_405 : ((0.405 * Real.pi : ℝ) : ℂ) = 0.405 * (Real.pi : ℂ) := by
    rw [Complex.ofReal_mul]; norm_num
  rw [h019, hπ2, h_neg81, h_405]
  ring

/-- **Closed-form of `(log z_book)^(((0.19:ℝ):ℂ)-1)`**:
      `(log z_book)^(-0.81) = β^(-0.81) · (cos(0.405π) + sin(0.405π)·I)`. -/
lemma cpow_log_z_book_closed_form :
    (Complex.log z_book) ^ (((0.19 : ℝ) : ℂ) - 1) =
      (Real.rpow beta_book (-0.81) : ℂ) *
        ((Real.cos (0.405 * Real.pi) : ℂ) +
         (Real.sin (0.405 * Real.pi) : ℂ) * I) := by
  have hne : Complex.log z_book ≠ 0 := log_z_book_ne_zero
  -- cpow x y = exp(log x * y) when x ≠ 0
  rw [Complex.cpow_def_of_ne_zero hne]
  -- substitute log(log z_book) and simplify the exponent algebraically
  rw [log_log_z_book, exponent_simp]
  -- exp(a + b·I) = exp(a) · (cos b + sin b · I) (for complex a, b)
  rw [Complex.exp_add_mul_I]
  -- exp(real coerced) = Real.exp real coerced
  rw [← Complex.ofReal_exp]
  -- cos / sin of real coerced
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  -- Real.exp (-0.81 · log β) = β^(-0.81) = Real.rpow β (-0.81)
  have h_exp_eq_rpow :
      Real.exp ((-0.81 : ℝ) * Real.log beta_book) = Real.rpow beta_book (-0.81) := by
    -- Real.rpow β y = exp(log β * y)
    show Real.exp ((-0.81 : ℝ) * Real.log beta_book) = beta_book ^ ((-0.81) : ℝ)
    rw [Real.rpow_def_of_pos beta_book_pos]
    congr 1
    ring
  rw [h_exp_eq_rpow]

/-! ### Real and imag parts of the multiplicative kernel `B · (C + S·I)` -/

/-- `Re[(a:ℂ) * ((c:ℂ) + (s:ℂ)·I)] = a · c`. -/
private lemma re_real_times_cos_plus_sin_I (a c s : ℝ) :
    ((((a : ℂ)) * ((c : ℂ) + (s : ℂ) * I))).re = a * c := by
  simp [Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im]

/-- `Im[(a:ℂ) * ((c:ℂ) + (s:ℂ)·I)] = a · s`. -/
private lemma im_real_times_cos_plus_sin_I (a c s : ℝ) :
    ((((a : ℂ)) * ((c : ℂ) + (s : ℂ) * I))).im = a * s := by
  simp [Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im]

/-- **Real part of the shift at `s = 0.19`** as a single product of real factors. -/
lemma shift_019_re_closed_form :
    Complex.re (polyLogMonodromyShift (-1) ((0.19 : ℝ) : ℂ) z_book) =
      2 * Real.pi * Real.rpow beta_book (-0.81) *
        Real.sin (0.405 * Real.pi) / Real.Gamma 0.19 := by
  unfold polyLogMonodromyShift
  -- shift = 2π · I · (-1) · (log z_book)^(0.19-1) / Γ(0.19)
  -- Step 1: substitute the closed-form for the cpow
  rw [cpow_log_z_book_closed_form]
  -- Step 2: substitute Complex.Gamma with Real.Gamma
  have h_Gamma : Complex.Gamma ((0.19 : ℝ) : ℂ) = ((Real.Gamma 0.19 : ℝ) : ℂ) := by
    rw [Complex.Gamma_ofReal]
  rw [h_Gamma]
  -- Step 3: name the real quantities
  set B : ℝ := Real.rpow beta_book (-0.81) with hB_def
  set C : ℝ := Real.cos (0.405 * Real.pi) with hC_def
  set S : ℝ := Real.sin (0.405 * Real.pi) with hS_def
  set G : ℝ := Real.Gamma 0.19 with hG_def
  have hG_pos : 0 < G := Gamma_0_19_pos
  -- Step 4: simplify (-1 : ℤ) to (-1 : ℂ) and pull out -2π
  have h_negone : (((-1 : ℤ) : ℂ)) = -1 := by push_cast; rfl
  rw [h_negone]
  -- Now goal:
  --   (2 * (π : ℂ) * I * (-1) * ((B : ℂ) * ((C : ℂ) + (S : ℂ) * I)) / (G : ℂ)).re
  --     = 2 * π * B * S / G
  -- Step 5: Rewrite the LHS as (Re of the numerator) / G using ofReal_div semantics
  -- For z = w / (G : ℂ) with G real, z.re = w.re / G.
  -- We use `Complex.div_ofReal_re`.
  rw [show (2 * (Real.pi : ℂ) * I * (-1 : ℂ) *
            ((B : ℂ) * ((C : ℂ) + (S : ℂ) * I)) / (G : ℂ)) =
          ((2 * Real.pi * B * S : ℝ) : ℂ) / (G : ℂ) -
          ((2 * Real.pi * B * C : ℝ) : ℂ) / (G : ℂ) * I from ?_]
  · -- Apply Re to the simplified form
    simp [Complex.sub_re, Complex.mul_re, Complex.div_re,
          Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im,
          Complex.normSq_ofReal]
    -- The result simplifies to 2·π·B·S/G ⋯ but `simp` may leave fragments;
    -- we handle the algebra with `ring` + `field_simp`.
    have hG_ne : G ≠ 0 := hG_pos.ne'
    field_simp
  · -- prove the rewrite: -2π·I·B·(C+S·I)/G = (2π·B·S - 2π·B·C·I)/G
    have hI_sq : (I : ℂ) * I = -1 := Complex.I_mul_I
    have hG_ne : (G : ℂ) ≠ 0 := by exact_mod_cast hG_pos.ne'
    -- Multiply through: -2π·I·B·(C+S·I) = 2π·B·S - 2π·B·C·I
    -- using I² = -1
    have h_num :
        (2 * (Real.pi : ℂ) * I * (-1 : ℂ) *
            ((B : ℂ) * ((C : ℂ) + (S : ℂ) * I))) =
          ((2 * Real.pi * B * S : ℝ) : ℂ) -
          ((2 * Real.pi * B * C : ℝ) : ℂ) * I := by
      have : (2 * (Real.pi : ℂ) * I * (-1 : ℂ) *
              ((B : ℂ) * ((C : ℂ) + (S : ℂ) * I))) =
             -(2 * (Real.pi : ℂ) * (B : ℂ) * (C : ℂ)) * I
               - 2 * (Real.pi : ℂ) * (B : ℂ) * (S : ℂ) * (I * I) := by ring
      rw [this, hI_sq]
      push_cast
      ring
    rw [show (2 * (Real.pi : ℂ) * I * (-1 : ℂ) *
              ((B : ℂ) * ((C : ℂ) + (S : ℂ) * I)) / (G : ℂ)) =
            ((2 * (Real.pi : ℂ) * I * (-1 : ℂ) *
              ((B : ℂ) * ((C : ℂ) + (S : ℂ) * I))) / (G : ℂ)) from rfl]
    rw [h_num]
    -- Now: ((2πBS : ℝ) - (2πBC : ℝ)·I) / (G : ℂ)
    --     = (2πBS : ℝ)/G - (2πBC : ℝ)·I/G
    ring

/-! ## Section 3 — Final numerical inequality -/

/-- **`BookEval019_ShiftBound` discharged** (axiom-free, no sorry). -/
theorem bookEval019_ShiftBound_proved : BookEval019_ShiftBound := by
  unfold BookEval019_ShiftBound
  rw [shift_019_re_closed_form]
  -- Goal: 0.222144147 < 2π · β^(-0.81) · sin(0.405π) / Γ(0.19)
  have h_pi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_rpow := rpowBookBracketProved
  have h_rpow_gt : (0.60 : ℝ) < Real.rpow beta_book (-0.81) := h_rpow.1
  have h_rpow_pos : 0 < Real.rpow beta_book (-0.81) := lt_trans (by norm_num) h_rpow_gt
  have h_sin_gt : (0.95 : ℝ) < Real.sin (0.405 * Real.pi) := sin_0405_pi_gt
  have h_gamma_lt : Real.Gamma 0.19 < 5.04 := Gamma_0_19_lt
  have h_gamma_pos : 0 < Real.Gamma 0.19 := Gamma_0_19_pos
  -- Lower bound on the numerator: 2π · β^(-0.81) · sin > (2 · 3.141592) · 0.60 · 0.95
  have step1 : (2 * 3.141592 : ℝ) < 2 * Real.pi := by linarith
  have h2π_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have step2 : (2 * 3.141592 : ℝ) * 0.60 < 2 * Real.pi * 0.60 :=
    mul_lt_mul_of_pos_right step1 (by norm_num)
  have step3 : (2 * Real.pi) * 0.60 < 2 * Real.pi * Real.rpow beta_book (-0.81) :=
    mul_lt_mul_of_pos_left h_rpow_gt h2π_pos
  have step4 : (2 * 3.141592 : ℝ) * 0.60 * 0.95 <
               2 * Real.pi * Real.rpow beta_book (-0.81) * 0.95 := by
    calc (2 * 3.141592 : ℝ) * 0.60 * 0.95
        < (2 * Real.pi * 0.60) * 0.95 := mul_lt_mul_of_pos_right step2 (by norm_num)
      _ < (2 * Real.pi * Real.rpow beta_book (-0.81)) * 0.95 :=
          mul_lt_mul_of_pos_right step3 (by norm_num)
  have h_lhs_pos : 0 < 2 * Real.pi * Real.rpow beta_book (-0.81) :=
    mul_pos h2π_pos h_rpow_pos
  have step5 : 2 * Real.pi * Real.rpow beta_book (-0.81) * 0.95 <
               2 * Real.pi * Real.rpow beta_book (-0.81) * Real.sin (0.405 * Real.pi) :=
    mul_lt_mul_of_pos_left h_sin_gt h_lhs_pos
  have h_num_gt : (3.58141488 : ℝ) <
      2 * Real.pi * Real.rpow beta_book (-0.81) * Real.sin (0.405 * Real.pi) := by
    have : (3.58141488 : ℝ) = (2 * 3.141592 : ℝ) * 0.60 * 0.95 := by norm_num
    linarith
  -- Reduce divisor: a < b/c ↔ a · c < b (for c > 0)
  rw [lt_div_iff₀ h_gamma_pos]
  have h_lhs_bound : (0.222144147 : ℝ) * Real.Gamma 0.19 < 0.222144147 * 5.04 :=
    mul_lt_mul_of_pos_left h_gamma_lt (by norm_num : (0:ℝ) < 0.222144147)
  have h_lhs_num : (0.222144147 : ℝ) * 5.04 < 3.58141488 := by norm_num
  linarith

/-! ## Section 4 — Composition through to `bookEvaluation` -/

/-- **`bookEvaluation 0.19 > 0.222144147`** (unconditional, axiom-free):
    Input #4 of `axiom_content_FIVE_INPUTS` is now a fully proven
    theorem in the current Lean polyLog encoding. -/
theorem bookEvaluation_019_lower_bound_unconditional :
    (0.222144147 : ℝ) < bookEvaluation (0.19 : ℝ) :=
  bookEvaluation_019_lower_bound_of_shift_bound bookEval019_ShiftBound_proved

end PrincipiaTractalis.Analytic
