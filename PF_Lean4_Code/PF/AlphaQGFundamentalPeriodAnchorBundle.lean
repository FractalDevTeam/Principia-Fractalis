/-
# PF.AlphaQGFundamentalPeriodAnchorBundle

★★★ 2026-06-17 — FUN: α_QG² = 2π as fundamental period. Trig values
at canonical fractions α_QG²/n give clean closed forms.

## Identities

  cos(α_QG² · 1/2) = cos(π) = -1
  sin(α_QG² · 1/2) = sin(π) = 0
  cos(α_QG² · 1/3) = cos(2π/3) = -1/2
  sin(α_QG² · 1/3) = sin(2π/3) = √3/2
  cos(α_QG² · 1/4) = cos(π/2) = 0
  sin(α_QG² · 1/4) = sin(π/2) = 1
  cos(α_QG² · 1/6) = cos(π/3) = 1/2
  sin(α_QG² · 1/6) = sin(π/3) = √3/2

The framework's α_QG² is the canonical fundamental period generator;
divisions by 2, 3, 4, 6 (the regular polygon vertex divisors) give
clean trig closed forms.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaQGFundamentalPeriodAnchorBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — Halves -/

theorem cos_α_QG_sq_div_two_eq_neg_one : Real.cos (α_QG ^ 2 / 2) = -1 := by
  rw [α_QG_sq_eq_two_pi]
  rw [show (2 * Real.pi / 2 : ℝ) = Real.pi by ring]
  exact Real.cos_pi

theorem sin_α_QG_sq_div_two_eq_zero : Real.sin (α_QG ^ 2 / 2) = 0 := by
  rw [α_QG_sq_eq_two_pi]
  rw [show (2 * Real.pi / 2 : ℝ) = Real.pi by ring]
  exact Real.sin_pi

/-! ## §2 — Thirds -/

theorem cos_α_QG_sq_div_three_eq_neg_half : Real.cos (α_QG ^ 2 / 3) = -1/2 := by
  rw [α_QG_sq_eq_two_pi]
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring]
  rw [Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

theorem sin_α_QG_sq_div_three_eq_sqrt_three_halves :
    Real.sin (α_QG ^ 2 / 3) = Real.sqrt 3 / 2 := by
  rw [α_QG_sq_eq_two_pi]
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring]
  rw [Real.sin_pi_sub, Real.sin_pi_div_three]

/-! ## §3 — Quarters -/

theorem cos_α_QG_sq_div_four_eq_zero : Real.cos (α_QG ^ 2 / 4) = 0 := by
  rw [α_QG_sq_eq_two_pi]
  rw [show (2 * Real.pi / 4 : ℝ) = Real.pi / 2 by ring]
  exact Real.cos_pi_div_two

theorem sin_α_QG_sq_div_four_eq_one : Real.sin (α_QG ^ 2 / 4) = 1 := by
  rw [α_QG_sq_eq_two_pi]
  rw [show (2 * Real.pi / 4 : ℝ) = Real.pi / 2 by ring]
  exact Real.sin_pi_div_two

/-! ## §4 — Sixths -/

theorem cos_α_QG_sq_div_six_eq_half : Real.cos (α_QG ^ 2 / 6) = 1/2 := by
  rw [α_QG_sq_eq_two_pi]
  rw [show (2 * Real.pi / 6 : ℝ) = Real.pi / 3 by ring]
  exact Real.cos_pi_div_three

theorem sin_α_QG_sq_div_six_eq_sqrt_three_halves :
    Real.sin (α_QG ^ 2 / 6) = Real.sqrt 3 / 2 := by
  rw [α_QG_sq_eq_two_pi]
  rw [show (2 * Real.pi / 6 : ℝ) = Real.pi / 3 by ring]
  exact Real.sin_pi_div_three

/-! ## §5 — Bundle capstone -/

/-- **★★★ THE FUNDAMENTAL-PERIOD ANCHOR CAPSTONE ★★★** —
    eight clean trig closed forms at α_QG² divided by canonical regular
    polygon vertex divisors {2, 3, 4, 6}. -/
theorem α_QG_fundamental_period_anchor_capstone :
    Real.cos (α_QG ^ 2 / 2) = -1 ∧
    Real.sin (α_QG ^ 2 / 2) = 0 ∧
    Real.cos (α_QG ^ 2 / 3) = -1/2 ∧
    Real.sin (α_QG ^ 2 / 3) = Real.sqrt 3 / 2 ∧
    Real.cos (α_QG ^ 2 / 4) = 0 ∧
    Real.sin (α_QG ^ 2 / 4) = 1 ∧
    Real.cos (α_QG ^ 2 / 6) = 1/2 ∧
    Real.sin (α_QG ^ 2 / 6) = Real.sqrt 3 / 2 :=
  ⟨cos_α_QG_sq_div_two_eq_neg_one,
   sin_α_QG_sq_div_two_eq_zero,
   cos_α_QG_sq_div_three_eq_neg_half,
   sin_α_QG_sq_div_three_eq_sqrt_three_halves,
   cos_α_QG_sq_div_four_eq_zero,
   sin_α_QG_sq_div_four_eq_one,
   cos_α_QG_sq_div_six_eq_half,
   sin_α_QG_sq_div_six_eq_sqrt_three_halves⟩

end AlphaQGFundamentalPeriodAnchorBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.AlphaQGFundamentalPeriodAnchorBundle.α_QG_fundamental_period_anchor_capstone
