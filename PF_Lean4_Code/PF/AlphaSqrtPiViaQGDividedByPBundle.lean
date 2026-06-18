/-
# PF.AlphaSqrtPiViaQGDividedByPBundle

★★★★ 2026-06-17 — FUN: the canonical Gaussian normalization √π appears
in framework form as `α_QG / α_P`.

## Headline

  √π = α_QG / α_P

This is the canonical Gaussian normalization: `∫ℝ e^(−x²) dx = √π`.
Equivalently `Γ(1/2) = √π` (mathlib `Real.Gamma_one_half_eq`).

## Corollary

  α_QG · α_P = α_YM · √π

since `α_QG · α_P = 2·√π = α_YM · √π`. The gravitational axis paired
multiplicatively with the P-class axis yields twice the Gaussian
normalization.

## Γ(1/2) in framework form

  Real.Gamma(1/2) = α_QG / α_P

The Gamma function at the canonical half-integer point reduces to
α_QG/α_P, exhibiting Stirling's normalization in framework form.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace PrincipiaTractalis
namespace AlphaSqrtPiViaQGDividedByPBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — √π = α_QG / α_P -/

/-- **★★★ `√π = α_QG / α_P` ★★★** — canonical Gaussian normalization
    in framework form. -/
theorem sqrt_pi_eq_α_QG_div_α_P :
    Real.sqrt Real.pi = α_QG / α_P := by
  have h_pi_nonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  have h_two_nonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  have h_sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  have h_lhs_nonneg : (0 : ℝ) ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have h_rhs_nonneg : (0 : ℝ) ≤ α_QG / α_P := by
    unfold α_QG α_P
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_squared : (Real.sqrt Real.pi)^2 = (α_QG / α_P)^2 := by
    rw [Real.sq_sqrt h_pi_nonneg]
    unfold α_QG α_P
    rw [div_pow,
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Real.pi),
        Real.sq_sqrt h_two_nonneg]
    ring
  nlinarith [h_squared, h_lhs_nonneg, h_rhs_nonneg,
             sq_nonneg (Real.sqrt Real.pi - α_QG / α_P),
             sq_nonneg (Real.sqrt Real.pi + α_QG / α_P)]

/-! ## §2 — α_QG · α_P = α_YM · √π -/

/-- **★★★ `α_QG · α_P = α_YM · √π` ★★★** — multiplicative companion
    identity. -/
theorem α_QG_mul_α_P_eq_α_YM_mul_sqrt_pi :
    α_QG * α_P = α_YM * Real.sqrt Real.pi := by
  have h_p_pos : 0 < α_P := by
    unfold α_P
    exact Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  have h_p_sq : α_P ^ 2 = α_YM := α_P_sq_eq_α_YM
  have h_sqrt_pi : Real.sqrt Real.pi = α_QG / α_P :=
    sqrt_pi_eq_α_QG_div_α_P
  rw [h_sqrt_pi, ← h_p_sq]
  field_simp

/-! ## §3 — Real.Gamma(1/2) = α_QG / α_P -/

/-- **★★★ `Γ(1/2) = α_QG / α_P` ★★★** — Gamma function at the canonical
    half-integer point in framework form. -/
theorem Gamma_one_half_eq_α_QG_div_α_P :
    Real.Gamma (1 / 2) = α_QG / α_P := by
  rw [Real.Gamma_one_half_eq]
  exact sqrt_pi_eq_α_QG_div_α_P

/-! ## §4 — Bundle capstone -/

/-- **★★★★ THE √π-VIA-α_QG/α_P BUNDLE CAPSTONE ★★★★** —
    three identities exhibiting the canonical Gaussian normalization
    √π in framework form:

      √π = α_QG / α_P                  (Gaussian integral ratio)
      α_QG · α_P = α_YM · √π           (multiplicative corollary)
      Γ(1/2) = α_QG / α_P              (canonical Gamma anchor)

    The Gaussian normalization that anchors Stirling's formula, the
    n-sphere volume, and probability theory is exactly the ratio of
    the framework's gravitational axis to the P-class axis. -/
theorem α_sqrt_pi_via_α_QG_div_α_P_bundle_capstone :
    Real.sqrt Real.pi = α_QG / α_P ∧
    α_QG * α_P = α_YM * Real.sqrt Real.pi ∧
    Real.Gamma (1 / 2) = α_QG / α_P :=
  ⟨sqrt_pi_eq_α_QG_div_α_P,
   α_QG_mul_α_P_eq_α_YM_mul_sqrt_pi,
   Gamma_one_half_eq_α_QG_div_α_P⟩

end AlphaSqrtPiViaQGDividedByPBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaSqrtPiViaQGDividedByPBundle.sqrt_pi_eq_α_QG_div_α_P
#print axioms PrincipiaTractalis.AlphaSqrtPiViaQGDividedByPBundle.α_QG_mul_α_P_eq_α_YM_mul_sqrt_pi
#print axioms PrincipiaTractalis.AlphaSqrtPiViaQGDividedByPBundle.Gamma_one_half_eq_α_QG_div_α_P
#print axioms PrincipiaTractalis.AlphaSqrtPiViaQGDividedByPBundle.α_sqrt_pi_via_α_QG_div_α_P_bundle_capstone
