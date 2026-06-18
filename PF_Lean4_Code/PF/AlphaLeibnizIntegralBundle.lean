/-
# PF.AlphaLeibnizIntegralBundle

★★★★ 2026-06-17 — FUN: the Leibniz integral `∫₀^1 1/(1+x²) dx = π/4`
appears in framework form as `α_BSD / 3`.

## Headline

  ∫₀^1 1/(1 + x²) dx = α_BSD / 3

The canonical Leibniz integral (= arctan 1 = π/4) appears as one-third
of the BSD axis. Equivalently:

  ∫₀^1 1/(1 + x²) dx = α_QG² / α_YM³               (= 2π / 8 = π/4)

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace PrincipiaTractalis
namespace AlphaLeibnizIntegralBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — ∫₀^1 1/(1+x²) dx = α_BSD/3 -/

/-- **★★★ `∫₀^1 1/(1+x²) dx = α_BSD/3` ★★★** — Leibniz integral
    in framework form. -/
theorem integral_inv_one_plus_sq_zero_to_one_eq_α_BSD_div_three :
    ∫ x in (0:ℝ)..(1:ℝ), (1 : ℝ) / (1 + x ^ 2) = α_BSD / 3 := by
  rw [integral_one_div_one_add_sq]
  rw [Real.arctan_one, Real.arctan_zero]
  unfold α_BSD
  ring

/-! ## §2 — ∫₀^1 1/(1+x²) dx = α_QG² / α_YM³ -/

/-- **`∫₀^1 1/(1+x²) dx = α_QG² / α_YM³`** — Leibniz integral via
    α_QG = √(2π) and α_YM³ = 8. -/
theorem integral_inv_one_plus_sq_zero_to_one_eq_α_QG_sq_div_α_YM_cubed :
    ∫ x in (0:ℝ)..(1:ℝ), (1 : ℝ) / (1 + x ^ 2) = α_QG ^ 2 / α_YM ^ 3 := by
  rw [integral_inv_one_plus_sq_zero_to_one_eq_α_BSD_div_three]
  rw [α_QG_sq_eq_two_pi]
  unfold α_BSD α_YM
  ring

/-! ## §3 — Bundle capstone -/

/-- **★★★★ THE LEIBNIZ-INTEGRAL BUNDLE CAPSTONE ★★★★** —
    two identities exhibiting the canonical Leibniz integral
    `∫₀^1 1/(1+x²) dx = π/4` in framework form:

      ∫₀^1 1/(1+x²) dx = α_BSD / 3                     (BSD-axis form)
      ∫₀^1 1/(1+x²) dx = α_QG² / α_YM³                  (α_QG form, = π/4)

    The Leibniz integral that generates the Leibniz series for π
    is anchored to the framework's BSD axis. -/
theorem α_leibniz_integral_bundle_capstone :
    (∫ x in (0:ℝ)..(1:ℝ), (1 : ℝ) / (1 + x ^ 2)) = α_BSD / 3 ∧
    (∫ x in (0:ℝ)..(1:ℝ), (1 : ℝ) / (1 + x ^ 2)) = α_QG ^ 2 / α_YM ^ 3 :=
  ⟨integral_inv_one_plus_sq_zero_to_one_eq_α_BSD_div_three,
   integral_inv_one_plus_sq_zero_to_one_eq_α_QG_sq_div_α_YM_cubed⟩

end AlphaLeibnizIntegralBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaLeibnizIntegralBundle.integral_inv_one_plus_sq_zero_to_one_eq_α_BSD_div_three
#print axioms PrincipiaTractalis.AlphaLeibnizIntegralBundle.integral_inv_one_plus_sq_zero_to_one_eq_α_QG_sq_div_α_YM_cubed
#print axioms PrincipiaTractalis.AlphaLeibnizIntegralBundle.α_leibniz_integral_bundle_capstone
