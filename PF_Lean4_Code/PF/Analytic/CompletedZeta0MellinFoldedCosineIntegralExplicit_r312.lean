/-
# r312: Explicit real cosine integrand form — `Re(mellin f_modif ⟨1/4, 15/2⟩) = 2 · I_15`
#      where `I_15 := ∫ x in Ioi 1, (evenKernel 0 x − 1) · x^(-3/4) · cos((15/2) log x)`
#      + strengthened chain-closer `4/901 < I_15 → Xi_Positive_At_15`

★ 2026-08-22 r312 — completes the folded-cosine-integral pipeline started in r311.
Unpacks r311's complex tail integral `∫ y in Ioi 1, (y : ℂ)^(q - 1) • F y` to
the explicit real cosine integral form Pabs specified.

## What r312 delivers

- `cpow_at_q_minus_one_re` : `((y : ℂ)^(q - 1)).re = y^(-3/4) · cos((15/2) · log y)`
  for `y > 0`. Via `Complex.cpow_def_of_ne_zero` + `Complex.ofReal_log` +
  `Complex.exp_re` + `Real.rpow_def_of_pos`.

- `cpow_at_q_minus_one_im` : `((y : ℂ)^(q - 1)).im = y^(-3/4) · sin((15/2) · log y)`
  for `y > 0`. Same technique as `_re` with `Complex.exp_im`.

- `f_modif_apply_on_ioi_one` : `F y = ((evenKernel 0 y - 1 : ℝ) : ℂ)`
  for `y ∈ Ioi 1`. Case-split on `WeakFEPair.f_modif`.

- `integrand_re_pointwise` : `((y : ℂ)^(q - 1) • F y).re = (evenKernel 0 y - 1) · y^(-3/4) · cos((15/2) · log y)`
  for `y ∈ Ioi 1`. Combines pointwise polar decomposition + F unfolding.

- `re_tail_eq_folded_cosine_integral` :
    `(∫ y in Ioi 1, (y : ℂ)^(q - 1) • F y).re
       = ∫ y in Ioi 1, (evenKernel 0 y - 1) · y^(-3/4) · cos((15/2) · log y)`.
  Via `integral_re` (with integrability from `MellinConvergent`) + pointwise.

- `re_mellin_F_at_q_eq_two_folded_cosine_integral` :
    `(mellin F q).re = 2 · ∫ y in Ioi 1, (evenKernel 0 y - 1) · y^(-3/4) · cos((15/2) · log y)`.
  Combining r311's `re_mellin_F_at_q_eq_two_re_tail` with §5.

- `Xi_Positive_At_15_from_folded_cosine_integral_lower_bound` : STRENGTHENED
  CHAIN-CLOSER:
    `4/901 < ∫ y in Ioi 1, (evenKernel 0 y - 1) · y^(-3/4) · cos((15/2) · log y)
       → Xi_Positive_At_15`.
  This is Pabs's exact chain-closer specification for r311's "end".

## Framework-first status

NOT a numerical discharge. Structural expansion: unpacks r311's complex tail
integral to the real cosine integral form via three mechanical pieces —
polar decomposition of `(y : ℂ)^(q - 1)`, `F` unfolding on `Ioi 1`, and
`integral_re` swap. Standing rules: no numerical approximation, no forced
exponent (the `-3/4` and `(15/2) log y` emerge from `q - 1 = ⟨-3/4, 15/2⟩`
via `Complex.exp_re/im` + `Real.rpow_def_of_pos`), no scaffolding.

Book anchors: Ch 20 § 20.4 (RH via Fractal Resonance), Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.CompletedZeta0MellinFoldedCosineIntegral_r311
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit

open Complex MeasureTheory Set Real
open HurwitzZeta
open PrincipiaTractalis.CompletedZeta0MellinReduction
open PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15
open PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral

/-- Local shorthand for `F` (the modified theta kernel). -/
private noncomputable abbrev F : ℝ → ℂ := (hurwitzEvenFEPair 0).f_modif

/-- Local shorthand for `q = ⟨1/4, 15/2⟩`. -/
private noncomputable abbrev q : ℂ := ⟨(1 : ℝ)/4, (15 : ℝ)/2⟩

/-! ## §1 Polar decomposition of `(y : ℂ)^(q - 1)` at `y > 0`. -/

/-- **`cpow_at_q_minus_one_re`** — for `y > 0`,

  `((y : ℂ)^(q - 1)).re = y^(-3/4) · cos((15/2) · log y)`.

Via `Complex.cpow_def_of_ne_zero` + `Complex.ofReal_log` (reversed) +
`Complex.exp_re` + `Real.rpow_def_of_pos` (reversed). Uses that
`q - 1 = ⟨-3/4, 15/2⟩` gives `(Real.log y : ℂ) * (q - 1)` real part
`-(3/4) · Real.log y` and imag part `(15/2) · Real.log y`. -/
theorem cpow_at_q_minus_one_re {y : ℝ} (hy : 0 < y) :
    ((y : ℂ)^(q - 1)).re = y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y) := by
  have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [Complex.cpow_def_of_ne_zero hy_ne, ← Complex.ofReal_log hy.le,
      Complex.exp_re]
  -- Compute the .re and .im of (Real.log y : ℂ) * (q - 1)
  -- q = ⟨1/4, 15/2⟩, so q - 1 = ⟨-3/4, 15/2⟩
  -- (Real.log y : ℂ) * (q - 1) = ⟨Real.log y, 0⟩ * ⟨-3/4, 15/2⟩
  --                             = ⟨Real.log y · (-3/4), Real.log y · 15/2⟩
  have h_prod_re : ((Real.log y : ℂ) * (q - 1)).re = -(3 / 4) * Real.log y := by
    simp [q, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]; ring
  have h_prod_im : ((Real.log y : ℂ) * (q - 1)).im = (15 / 2) * Real.log y := by
    simp [q, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]; ring
  rw [h_prod_re, h_prod_im]
  -- Real.exp (-(3/4) · Real.log y) = y^(-(3/4)) via Real.rpow_def_of_pos
  congr 1
  rw [show (-(3 / 4 : ℝ)) * Real.log y = Real.log y * (-(3 / 4 : ℝ)) from mul_comm _ _,
      ← Real.rpow_def_of_pos hy]

/-- **`cpow_at_q_minus_one_im`** — companion imaginary-part formula:
`((y : ℂ)^(q - 1)).im = y^(-3/4) · sin((15/2) · log y)` for `y > 0`. -/
theorem cpow_at_q_minus_one_im {y : ℝ} (hy : 0 < y) :
    ((y : ℂ)^(q - 1)).im = y^(-((3 : ℝ)/4)) * Real.sin ((15 / 2) * Real.log y) := by
  have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [Complex.cpow_def_of_ne_zero hy_ne, ← Complex.ofReal_log hy.le,
      Complex.exp_im]
  have h_prod_re : ((Real.log y : ℂ) * (q - 1)).re = -(3 / 4) * Real.log y := by
    simp [q, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]; ring
  have h_prod_im : ((Real.log y : ℂ) * (q - 1)).im = (15 / 2) * Real.log y := by
    simp [q, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]; ring
  rw [h_prod_re, h_prod_im]
  congr 1
  rw [show (-(3 / 4 : ℝ)) * Real.log y = Real.log y * (-(3 / 4 : ℝ)) from mul_comm _ _,
      ← Real.rpow_def_of_pos hy]

/-! ## §2 `F` explicit form on `Ioi 1`. -/

/-- **`f_modif_apply_on_ioi_one`** — `F y = ((evenKernel 0 y - 1 : ℝ) : ℂ)` for
`y ∈ Ioi 1`. Direct case-split on `WeakFEPair.f_modif` indicators. -/
theorem f_modif_apply_on_ioi_one {y : ℝ} (hy : y ∈ Ioi (1 : ℝ)) :
    F y = ((evenKernel 0 y - 1 : ℝ) : ℂ) := by
  have hy2 : y ∉ Ioo (0 : ℝ) 1 := fun h => absurd (mem_Ioo.mp h).2 (not_lt.mpr (le_of_lt hy))
  simp only [F, WeakFEPair.f_modif, Pi.add_apply, Set.indicator_of_mem hy,
    Set.indicator_of_notMem hy2, add_zero]
  -- goal: P.f y - P.f₀ = ofReal(evenKernel 0 y - 1)
  simp [hurwitzEvenFEPair, Function.comp_apply, Complex.ofReal_sub, Complex.ofReal_one]

/-! ## §3 Pointwise integrand `.re` on `Ioi 1`. -/

/-- **`integrand_re_pointwise`** — combining §1 and §2:

  `((y : ℂ)^(q - 1) • F y).re
     = (evenKernel 0 y - 1) · y^(-3/4) · cos((15/2) · log y)`

for `y ∈ Ioi 1`. Multiplication `(a + bi) · c = ac + bci` at `c` real; `.re = ac`. -/
theorem integrand_re_pointwise {y : ℝ} (hy : y ∈ Ioi (1 : ℝ)) :
    ((y : ℂ)^(q - 1) • F y).re
      = (evenKernel 0 y - 1) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y) := by
  have hy_pos : (0 : ℝ) < y := lt_trans zero_lt_one hy
  rw [f_modif_apply_on_ioi_one hy, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    cpow_at_q_minus_one_re hy_pos]
  ring

/-! ## §4 Swap `.re` and integral on the tail. -/

/-- **`tail_integrable_on_ioi_one`** — integrand `(y : ℂ)^(q - 1) • F y` is
integrable on `Ioi 1` (restriction of `MellinConvergent`). -/
theorem tail_integrable_on_ioi_one :
    IntegrableOn (fun y : ℝ => (y : ℂ)^(q - 1) • F y) (Ioi (1 : ℝ)) := by
  have h_conv : MellinConvergent F q :=
    ((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin q).1
  exact h_conv.mono_set (fun x (hx : x ∈ Ioi (1 : ℝ)) => mem_Ioi.mpr (zero_lt_one.trans hx))

/-- **`re_tail_eq_integral_re`** — swap `.re` and `∫` on the tail via
`integral_re` + integrability. -/
theorem re_tail_eq_integral_re :
    (∫ y in Ioi (1 : ℝ), (y : ℂ)^(q - 1) • F y).re
      = ∫ y in Ioi (1 : ℝ), ((y : ℂ)^(q - 1) • F y).re :=
  (integral_re tail_integrable_on_ioi_one).symm

/-! ## §5 The folded cosine-integral identity for the tail. -/

/-- **`re_tail_eq_folded_cosine_integral`** — the final tail identity:

  `(∫ y in Ioi 1, (y : ℂ)^(q - 1) • F y).re
     = ∫ y in Ioi 1, (evenKernel 0 y - 1) · y^(-3/4) · cos((15/2) · log y)`.

Combines §4 (swap `.re` and `∫`) with §3 (pointwise integrand). -/
theorem re_tail_eq_folded_cosine_integral :
    (∫ y in Ioi (1 : ℝ), (y : ℂ)^(q - 1) • F y).re
      = ∫ y in Ioi (1 : ℝ),
          (evenKernel 0 y - 1) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y) := by
  rw [re_tail_eq_integral_re]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  exact integrand_re_pointwise hy

/-! ## §6 Combining with r311 to get the full folded cosine integral form. -/

/-- **`re_mellin_F_at_q_eq_two_folded_cosine_integral`** — THE FINAL IDENTITY:

  `(mellin F q).re = 2 · ∫ y in Ioi 1, (evenKernel 0 y - 1) · y^(-3/4) · cos((15/2) · log y)`.

Combines r311's `re_mellin_F_at_q_eq_two_re_tail` with §5. -/
theorem re_mellin_F_at_q_eq_two_folded_cosine_integral :
    (mellin F q).re
      = 2 * ∫ y in Ioi (1 : ℝ),
          (evenKernel 0 y - 1) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y) := by
  rw [re_mellin_F_at_q_eq_two_re_tail, re_tail_eq_folded_cosine_integral]

/-! ## §7 Chain-closer — the r311 endpoint Pabs specified. -/

/-- **`Xi_Positive_At_15_from_folded_cosine_integral_lower_bound`** —
STRENGTHENED CHAIN-CLOSER: any real number `a > 4/901` bounded above by the
folded cosine integral discharges the aggregate's `Xi_Positive_At_15`
witness residual:

  `4/901 < a → a ≤ ∫ y in Ioi 1, (evenKernel 0 y - 1) · y^(-3/4) · cos((15/2) · log y)
     → Xi_Positive_At_15`.

Combines `re_mellin_F_at_q_eq_two_folded_cosine_integral` with r309's
`Xi_Positive_At_15_from_re_mellin_lower_bound` at `2 · a` and `8/901`.
The `4/901` (vs r309's `8/901`) is the factor-of-2 absorbed from
`(mellin F q).re = 2 · (folded cosine integral)`. -/
theorem Xi_Positive_At_15_from_folded_cosine_integral_lower_bound
    {a : ℝ} (ha : (4 : ℝ)/901 < a)
    (h : a ≤ ∫ y in Ioi (1 : ℝ),
        (evenKernel 0 y - 1) * y^(-((3 : ℝ)/4)) * Real.cos ((15 / 2) * Real.log y)) :
    PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning.Xi_Positive_At_15 := by
  refine Xi_Positive_At_15_from_re_mellin_lower_bound (a := 2 * a) ?_ ?_
  · linarith
  · rw [re_mellin_F_at_q_eq_two_folded_cosine_integral]
    linarith

/-! ## §8 Axiom checks. -/

#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit.cpow_at_q_minus_one_re
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit.cpow_at_q_minus_one_im
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit.f_modif_apply_on_ioi_one
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit.integrand_re_pointwise
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit.tail_integrable_on_ioi_one
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit.re_tail_eq_integral_re
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit.re_tail_eq_folded_cosine_integral
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit.re_mellin_F_at_q_eq_two_folded_cosine_integral
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit.Xi_Positive_At_15_from_folded_cosine_integral_lower_bound

end PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegralExplicit
