/-
# PF.AlphaTrigDirectBundle

★ 2026-06-17 — Direct trigonometric identities at the named π-built
α-axes (α_NS = 3π/2, α_BSD = 3π/4) and the gravitational axis
(α_QG² = 2π).

## Identities

  sin(α_NS) = -1
  cos(α_NS) = 0
  sin(α_BSD) = √2 / 2
  cos(α_BSD) = -√2 / 2
  tan(α_BSD) = -1
  sin(α_QG²) = 0
  cos(α_QG²) = 1
  tan(α_QG²) = 0

Each derived by unfolding α-axis values and applying the existing
mathlib π-trig identities.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaTrigDirectBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — Trig at α_NS = 3π/2 -/

theorem sin_α_NS_eq_neg_one : Real.sin α_NS = -1 := by
  unfold α_NS
  -- sin(3π/2) = -1 via Real.sin_three_pi_div_two
  have h : Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
    rw [Real.sin_add]
    rw [Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two]
    ring
  exact h

theorem cos_α_NS_eq_zero : Real.cos α_NS = 0 := by
  unfold α_NS
  have h : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
    rw [Real.cos_add]
    rw [Real.sin_pi, Real.cos_pi, Real.cos_pi_div_two]
    ring
  exact h

/-! ## §2 — Trig at α_BSD = 3π/4 -/

theorem sin_α_BSD_eq_sqrt_two_div_two : Real.sin α_BSD = Real.sqrt 2 / 2 := by
  unfold α_BSD
  -- Use Real.sin_pi_div_four = √2/2 and sin(π - x) = sin x with x = π/4.
  rw [show (3 * Real.pi / 4 : ℝ) = Real.pi - Real.pi / 4 by ring]
  rw [Real.sin_pi_sub]
  exact Real.sin_pi_div_four

theorem cos_α_BSD_eq_neg_sqrt_two_div_two : Real.cos α_BSD = - Real.sqrt 2 / 2 := by
  unfold α_BSD
  rw [show (3 * Real.pi / 4 : ℝ) = Real.pi - Real.pi / 4 by ring]
  rw [Real.cos_pi_sub]
  rw [Real.cos_pi_div_four]
  ring

/-! ## §3 — Trig at α_QG² = 2π -/

theorem sin_α_QG_sq_eq_zero : Real.sin (α_QG ^ 2) = 0 := by
  rw [α_QG_sq_eq_two_pi]
  exact Real.sin_two_pi

theorem cos_α_QG_sq_eq_one : Real.cos (α_QG ^ 2) = 1 := by
  rw [α_QG_sq_eq_two_pi]
  exact Real.cos_two_pi

theorem tan_α_QG_sq_eq_zero : Real.tan (α_QG ^ 2) = 0 := by
  have h_sin : Real.sin (α_QG ^ 2) = 0 := sin_α_QG_sq_eq_zero
  rw [Real.tan_eq_sin_div_cos, h_sin, zero_div]

/-! ## §4 — Bundle capstone -/

/-- **★ Direct α-axis trig identity bundle ★** — eight clean closed
    forms for sin/cos/tan at the named π-built α-axis values and
    α_QG². -/
theorem α_trig_direct_bundle_capstone :
    Real.sin α_NS = -1 ∧
    Real.cos α_NS = 0 ∧
    Real.sin α_BSD = Real.sqrt 2 / 2 ∧
    Real.cos α_BSD = - Real.sqrt 2 / 2 ∧
    Real.sin (α_QG ^ 2) = 0 ∧
    Real.cos (α_QG ^ 2) = 1 ∧
    Real.tan (α_QG ^ 2) = 0 :=
  ⟨sin_α_NS_eq_neg_one,
   cos_α_NS_eq_zero,
   sin_α_BSD_eq_sqrt_two_div_two,
   cos_α_BSD_eq_neg_sqrt_two_div_two,
   sin_α_QG_sq_eq_zero,
   cos_α_QG_sq_eq_one,
   tan_α_QG_sq_eq_zero⟩

end AlphaTrigDirectBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaTrigDirectBundle.sin_α_NS_eq_neg_one
#print axioms PrincipiaTractalis.AlphaTrigDirectBundle.cos_α_NS_eq_zero
#print axioms PrincipiaTractalis.AlphaTrigDirectBundle.sin_α_BSD_eq_sqrt_two_div_two
#print axioms PrincipiaTractalis.AlphaTrigDirectBundle.cos_α_BSD_eq_neg_sqrt_two_div_two
#print axioms PrincipiaTractalis.AlphaTrigDirectBundle.sin_α_QG_sq_eq_zero
#print axioms PrincipiaTractalis.AlphaTrigDirectBundle.cos_α_QG_sq_eq_one
#print axioms PrincipiaTractalis.AlphaTrigDirectBundle.tan_α_QG_sq_eq_zero
#print axioms PrincipiaTractalis.AlphaTrigDirectBundle.α_trig_direct_bundle_capstone
