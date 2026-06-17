/-
# PF.AlphaExpDirectBundle

★ 2026-06-17 — Direct exp-identities at the named α-axis values and at
key α-squared expressions.

## Identities

  exp(α_Poincaré)   = e            [since α_Poincaré = 1]
  exp(α_YM)         = e²           [since α_YM = 2]
  exp(α_P²)         = e²           [since α_P² = 2]
  exp(α_QG²)        = e^(2π)       [since α_QG² = 2π]
  exp(α_P² / 2)     = e            [from α_P² = 2]
  exp(α_QG² / (2·π)) = e            [from α_QG² = 2π]

Each closed form is a direct consequence of the α-axis substrate
equations.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaExpDirectBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — Direct exp at rational α-axes -/

theorem exp_α_Poincare_eq_e : Real.exp α_Poincare = Real.exp 1 := by
  unfold α_Poincare; rfl

theorem exp_α_YM_eq_e_sq : Real.exp α_YM = Real.exp 2 := by
  unfold α_YM; rfl

/-! ## §2 — exp at α_P² and α_QG² -/

/-- **`exp(α_P²) = e²`** — since α_P² = 2. -/
theorem exp_α_P_sq_eq_e_sq : Real.exp (α_P ^ 2) = Real.exp 2 := by
  have h : α_P ^ 2 = 2 := by
    rw [α_P_sq_eq_α_YM]; unfold α_YM; norm_num
  rw [h]

/-- **`exp(α_QG²) = e^(2π)`** — since α_QG² = 2π. -/
theorem exp_α_QG_sq_eq_exp_two_pi :
    Real.exp (α_QG ^ 2) = Real.exp (2 * Real.pi) := by
  rw [α_QG_sq_eq_two_pi]

/-! ## §3 — Half-square identities -/

/-- **`exp(α_P²/2) = e`** — standard-normal connection. -/
theorem exp_α_P_sq_div_two_eq_e : Real.exp (α_P ^ 2 / 2) = Real.exp 1 := by
  have h : α_P ^ 2 / 2 = 1 := by
    have h_sq : α_P ^ 2 = 2 := by
      rw [α_P_sq_eq_α_YM]; unfold α_YM; norm_num
    rw [h_sq]; norm_num
  rw [h]

/-- **`exp(α_QG² / (2π)) = e`** — gravitational normalization. -/
theorem exp_α_QG_sq_div_two_pi_eq_e :
    Real.exp (α_QG ^ 2 / (2 * Real.pi)) = Real.exp 1 := by
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h : α_QG ^ 2 / (2 * Real.pi) = 1 := by
    rw [α_QG_sq_eq_two_pi]
    field_simp
  rw [h]

/-! ## §4 — Bundle capstone -/

/-- **★ Direct exp α-axis bundle ★** — six closed forms for exp at
    the named α-axis values and key α-squared expressions. -/
theorem α_exp_direct_bundle_capstone :
    Real.exp α_Poincare = Real.exp 1 ∧
    Real.exp α_YM = Real.exp 2 ∧
    Real.exp (α_P ^ 2) = Real.exp 2 ∧
    Real.exp (α_QG ^ 2) = Real.exp (2 * Real.pi) ∧
    Real.exp (α_P ^ 2 / 2) = Real.exp 1 ∧
    Real.exp (α_QG ^ 2 / (2 * Real.pi)) = Real.exp 1 :=
  ⟨exp_α_Poincare_eq_e,
   exp_α_YM_eq_e_sq,
   exp_α_P_sq_eq_e_sq,
   exp_α_QG_sq_eq_exp_two_pi,
   exp_α_P_sq_div_two_eq_e,
   exp_α_QG_sq_div_two_pi_eq_e⟩

end AlphaExpDirectBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaExpDirectBundle.exp_α_Poincare_eq_e
#print axioms PrincipiaTractalis.AlphaExpDirectBundle.exp_α_YM_eq_e_sq
#print axioms PrincipiaTractalis.AlphaExpDirectBundle.exp_α_P_sq_eq_e_sq
#print axioms PrincipiaTractalis.AlphaExpDirectBundle.exp_α_QG_sq_eq_exp_two_pi
#print axioms PrincipiaTractalis.AlphaExpDirectBundle.exp_α_P_sq_div_two_eq_e
#print axioms PrincipiaTractalis.AlphaExpDirectBundle.exp_α_QG_sq_div_two_pi_eq_e
#print axioms PrincipiaTractalis.AlphaExpDirectBundle.α_exp_direct_bundle_capstone
