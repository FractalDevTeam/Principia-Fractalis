/-
# PF.AlphaTrigIntegralAxisAnchorBundle

★★★★ 2026-06-17 — FUN: trigonometric integrals over α-axis intervals
land cleanly on framework axis values.

## The integral identities

  ∫₀^π sin x dx = α_YM                            (one sine arch = 2)
  ∫₀^(π/2) sin x dx = α_Poincaré                  (quarter arch = 1)
  ∫₀^(α_NS) sin x dx = α_Poincaré                 (three-half-period sine = 1)
  ∫₀^(α_NS) cos x dx = -α_Poincaré                (three-half-period cosine = -1)

The framework's α-axes anchor canonical sine/cosine integrals: the
area under a full sine arch equals α_YM, and quarter-period integrals
land on α_Poincaré.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace PrincipiaTractalis
namespace AlphaTrigIntegralAxisAnchorBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — ∫₀^π sin x dx = α_YM -/

/-- **★★★ `∫₀^π sin x dx = α_YM` ★★★** — the area under one sine
    arch equals the Yang-Mills axis. -/
theorem integral_sin_zero_to_pi_eq_α_YM :
    ∫ x in (0:ℝ)..Real.pi, Real.sin x = α_YM := by
  rw [integral_sin]
  rw [Real.cos_zero, Real.cos_pi]
  unfold α_YM
  ring

/-! ## §2 — ∫₀^(π/2) sin x dx = α_Poincaré -/

/-- **`∫₀^(π/2) sin x dx = α_Poincaré`** — quarter-arch integral. -/
theorem integral_sin_zero_to_pi_div_two_eq_α_Poincare :
    ∫ x in (0:ℝ)..(Real.pi / 2), Real.sin x = α_Poincare := by
  rw [integral_sin]
  rw [Real.cos_zero, Real.cos_pi_div_two]
  unfold α_Poincare
  ring

/-! ## §3 — ∫₀^(α_NS) sin x dx = α_Poincaré -/

/-- **★★★ `∫₀^(α_NS) sin x dx = α_Poincaré` ★★★** — sine integral
    over the NS-axis interval equals α_Poincaré. -/
theorem integral_sin_zero_to_α_NS_eq_α_Poincare :
    ∫ x in (0:ℝ)..α_NS, Real.sin x = α_Poincare := by
  rw [integral_sin]
  rw [Real.cos_zero]
  unfold α_NS α_Poincare
  -- cos(3π/2) = 0
  have h_cos_3pi_div_2 : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
    rw [Real.cos_add]
    rw [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [h_cos_3pi_div_2]
  ring

/-! ## §4 — ∫₀^(α_NS) cos x dx = -α_Poincaré -/

/-- **★★★ `∫₀^(α_NS) cos x dx = -α_Poincaré` ★★★** — cosine integral
    over the NS-axis interval equals -α_Poincaré. -/
theorem integral_cos_zero_to_α_NS_eq_neg_α_Poincare :
    ∫ x in (0:ℝ)..α_NS, Real.cos x = -α_Poincare := by
  rw [integral_cos]
  rw [Real.sin_zero]
  unfold α_NS α_Poincare
  -- sin(3π/2) = -1
  have h_sin_3pi_div_2 : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
    rw [Real.sin_add]
    rw [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [h_sin_3pi_div_2]
  ring

/-! ## §5 — Bundle capstone -/

/-- **★★★★ THE TRIG INTEGRAL AXIS-ANCHOR BUNDLE CAPSTONE ★★★★** —
    four identities exhibiting trigonometric integrals over α-axis
    intervals landing on framework axis values:

      ∫₀^π sin x dx = α_YM                  (one sine arch = 2)
      ∫₀^(π/2) sin x dx = α_Poincaré        (quarter arch = 1)
      ∫₀^(α_NS) sin x dx = α_Poincaré       (three-half-period sine = 1)
      ∫₀^(α_NS) cos x dx = -α_Poincaré      (three-half-period cosine = -1)

    The framework's NS axis (= 3π/2) and YM axis (= 2) anchor the
    canonical sine/cosine integrals. -/
theorem α_trig_integral_axis_anchor_bundle_capstone :
    (∫ x in (0:ℝ)..Real.pi, Real.sin x) = α_YM ∧
    (∫ x in (0:ℝ)..(Real.pi / 2), Real.sin x) = α_Poincare ∧
    (∫ x in (0:ℝ)..α_NS, Real.sin x) = α_Poincare ∧
    (∫ x in (0:ℝ)..α_NS, Real.cos x) = -α_Poincare :=
  ⟨integral_sin_zero_to_pi_eq_α_YM,
   integral_sin_zero_to_pi_div_two_eq_α_Poincare,
   integral_sin_zero_to_α_NS_eq_α_Poincare,
   integral_cos_zero_to_α_NS_eq_neg_α_Poincare⟩

end AlphaTrigIntegralAxisAnchorBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaTrigIntegralAxisAnchorBundle.integral_sin_zero_to_pi_eq_α_YM
#print axioms PrincipiaTractalis.AlphaTrigIntegralAxisAnchorBundle.integral_sin_zero_to_pi_div_two_eq_α_Poincare
#print axioms PrincipiaTractalis.AlphaTrigIntegralAxisAnchorBundle.integral_sin_zero_to_α_NS_eq_α_Poincare
#print axioms PrincipiaTractalis.AlphaTrigIntegralAxisAnchorBundle.integral_cos_zero_to_α_NS_eq_neg_α_Poincare
#print axioms PrincipiaTractalis.AlphaTrigIntegralAxisAnchorBundle.α_trig_integral_axis_anchor_bundle_capstone
