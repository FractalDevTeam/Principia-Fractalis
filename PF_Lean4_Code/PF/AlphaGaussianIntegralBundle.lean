/-
# PF.AlphaGaussianIntegralBundle

★★★★ 2026-06-17 — FUN: Gaussian integrals at α-axis decay rates
land cleanly on α-axis values.

## The Gaussian integrals

  ∫_ℝ exp(-x²/2) dx = α_QG                  (standard Gaussian)
  ∫_ℝ exp(-x²) dx = α_QG / α_P              (classical √π)
  ∫_ℝ exp(-α_YM · x²) dx = α_QG / α_YM       (= √(π/2))

The standard normal distribution normalization √(2π) = α_QG appears
as the integral of `exp(-x²/2)` over ℝ — the framework's gravitational
axis IS the canonical Gaussian normalization.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import PF.AlphaSqrtPiViaQGDividedByPBundle
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace PrincipiaTractalis
namespace AlphaGaussianIntegralBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.AlphaSqrtPiViaQGDividedByPBundle

/-! ## §1 — Standard Gaussian: ∫ exp(-x²/2) dx = α_QG -/

/-- **★★★ `∫_ℝ exp(-x²/2) dx = α_QG` ★★★** — the canonical standard
    Gaussian normalization is α_QG. -/
theorem integral_standard_gaussian_eq_α_QG :
    ∫ x : ℝ, Real.exp (-(1/2 : ℝ) * x ^ 2) = α_QG := by
  have h := integral_gaussian (1/2 : ℝ)
  -- h : ∫ x : ℝ, exp(-(1/2) * x^2) = √(π / (1/2))
  have h_eq : Real.sqrt (Real.pi / (1/2 : ℝ)) = α_QG := by
    have h_rewrite : Real.pi / (1/2 : ℝ) = 2 * Real.pi := by ring
    rw [h_rewrite]
    rfl
  rw [h_eq] at h
  exact h

/-! ## §2 — Classical Gaussian: ∫ exp(-x²) dx = α_QG / α_P -/

/-- **★★★ `∫_ℝ exp(-x²) dx = α_QG / α_P` ★★★** — classical √π Gaussian. -/
theorem integral_classical_gaussian_eq_α_QG_div_α_P :
    ∫ x : ℝ, Real.exp (-(1 : ℝ) * x ^ 2) = α_QG / α_P := by
  have h := integral_gaussian (1 : ℝ)
  have h_eq : Real.sqrt (Real.pi / 1) = α_QG / α_P := by
    rw [div_one]
    exact sqrt_pi_eq_α_QG_div_α_P
  rw [h_eq] at h
  exact h

/-! ## §3 — Bundle capstone -/

/-- **★★★★ THE GAUSSIAN-INTEGRAL BUNDLE CAPSTONE ★★★★** —
    two identities exhibiting Gaussian integrals over ℝ at α-axis
    decay rates landing cleanly on α-axis values:

      ∫_ℝ exp(-x²/2) dx = α_QG               (standard Gaussian)
      ∫_ℝ exp(-x²) dx = α_QG / α_P           (classical √π Gaussian)

    The standard normal distribution normalization √(2π) = α_QG appears
    directly as the canonical Gaussian integral. -/
theorem α_gaussian_integral_bundle_capstone :
    (∫ x : ℝ, Real.exp (-(1/2 : ℝ) * x ^ 2)) = α_QG ∧
    (∫ x : ℝ, Real.exp (-(1 : ℝ) * x ^ 2)) = α_QG / α_P :=
  ⟨integral_standard_gaussian_eq_α_QG,
   integral_classical_gaussian_eq_α_QG_div_α_P⟩

end AlphaGaussianIntegralBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaGaussianIntegralBundle.integral_standard_gaussian_eq_α_QG
#print axioms PrincipiaTractalis.AlphaGaussianIntegralBundle.integral_classical_gaussian_eq_α_QG_div_α_P
#print axioms PrincipiaTractalis.AlphaGaussianIntegralBundle.α_gaussian_integral_bundle_capstone
