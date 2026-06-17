/-
# PF.AlphaTrigPiAlphaBundle

★★★ 2026-06-17 — FUN: trig identities at π · α-axis arguments.

## Identities

  cos(π·α_Poincaré) = -1    (Euler-classic)
  sin(π·α_Poincaré) = 0
  cos(π·α_RH)       = 0     (= cos(3π/2))
  sin(π·α_RH)       = -1
  cos(π·α_YM)       = 1     (= cos(2π))
  sin(π·α_YM)       = 0

The framework's THREE rational α-axes (Poincaré, RH, YM) sit at
canonical positions on the unit circle when multiplied by π:
  α_Poincaré → angle π   (half-rotation, -1)
  α_RH       → angle 3π/2 (three-quarter rotation, -i in ℂ)
  α_YM       → angle 2π  (full rotation, 1)

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaTrigPiAlphaBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — Trig at π · α_Poincaré -/

theorem cos_pi_α_Poincare_eq_neg_one : Real.cos (Real.pi * α_Poincare) = -1 := by
  unfold α_Poincare
  rw [show (Real.pi * 1 : ℝ) = Real.pi by ring]
  exact Real.cos_pi

theorem sin_pi_α_Poincare_eq_zero : Real.sin (Real.pi * α_Poincare) = 0 := by
  unfold α_Poincare
  rw [show (Real.pi * 1 : ℝ) = Real.pi by ring]
  exact Real.sin_pi

/-! ## §2 — Trig at π · α_RH -/

theorem cos_pi_α_RH_eq_zero : Real.cos (Real.pi * α_RH) = 0 := by
  unfold α_RH
  -- π·(3/2) = 3π/2
  rw [show (Real.pi * (3/2) : ℝ) = 3 * Real.pi / 2 by ring]
  rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
  rw [Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
  ring

theorem sin_pi_α_RH_eq_neg_one : Real.sin (Real.pi * α_RH) = -1 := by
  unfold α_RH
  rw [show (Real.pi * (3/2) : ℝ) = 3 * Real.pi / 2 by ring]
  rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
  rw [Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two]
  ring

/-! ## §3 — Trig at π · α_YM -/

theorem cos_pi_α_YM_eq_one : Real.cos (Real.pi * α_YM) = 1 := by
  unfold α_YM
  rw [show (Real.pi * 2 : ℝ) = 2 * Real.pi by ring]
  exact Real.cos_two_pi

theorem sin_pi_α_YM_eq_zero : Real.sin (Real.pi * α_YM) = 0 := by
  unfold α_YM
  rw [show (Real.pi * 2 : ℝ) = 2 * Real.pi by ring]
  exact Real.sin_two_pi

/-! ## §4 — Bundle capstone -/

/-- **★★★ THE π · α-AXIS TRIG BUNDLE ★★★** —
    six closed forms exhibiting the framework's three rational
    α-axes at canonical unit-circle positions:

      π · α_Poincaré → angle π    (half rotation, cos = -1)
      π · α_RH       → angle 3π/2 (three-quarter rotation, sin = -1)
      π · α_YM       → angle 2π   (full rotation, cos = 1)

    The three rational Clay axes (P, RH, YM) → half, three-quarter,
    full unit-circle rotations. -/
theorem α_trig_pi_alpha_bundle_capstone :
    Real.cos (Real.pi * α_Poincare) = -1 ∧
    Real.sin (Real.pi * α_Poincare) = 0 ∧
    Real.cos (Real.pi * α_RH) = 0 ∧
    Real.sin (Real.pi * α_RH) = -1 ∧
    Real.cos (Real.pi * α_YM) = 1 ∧
    Real.sin (Real.pi * α_YM) = 0 :=
  ⟨cos_pi_α_Poincare_eq_neg_one,
   sin_pi_α_Poincare_eq_zero,
   cos_pi_α_RH_eq_zero,
   sin_pi_α_RH_eq_neg_one,
   cos_pi_α_YM_eq_one,
   sin_pi_α_YM_eq_zero⟩

end AlphaTrigPiAlphaBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaTrigPiAlphaBundle.cos_pi_α_Poincare_eq_neg_one
#print axioms PrincipiaTractalis.AlphaTrigPiAlphaBundle.cos_pi_α_RH_eq_zero
#print axioms PrincipiaTractalis.AlphaTrigPiAlphaBundle.sin_pi_α_RH_eq_neg_one
#print axioms PrincipiaTractalis.AlphaTrigPiAlphaBundle.cos_pi_α_YM_eq_one
#print axioms PrincipiaTractalis.AlphaTrigPiAlphaBundle.α_trig_pi_alpha_bundle_capstone
