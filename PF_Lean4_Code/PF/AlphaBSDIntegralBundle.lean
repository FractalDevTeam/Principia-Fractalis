/-
# PF.AlphaBSDIntegralBundle

★★★★ 2026-06-17 — FUN: sin/cos integrals from 0 to α_BSD land on
α-axis combinations involving α_P and the silver ratio.

## Integrals at α_BSD upper limit

  ∫₀^(α_BSD) cos x dx = α_P / α_YM                   (= √2/2 = 1/α_P)
  ∫₀^(α_BSD) sin x dx = α_Poincaré + α_P / α_YM       (= 1 + √2/2)
  ∫₀^(α_BSD) (sin x + cos x) dx = α_Poincaré + α_P    (= 1 + √2, silver ratio)

The sum-of-trig integral over [0, α_BSD] = [0, 3π/4] lands on the
silver ratio α_Poincaré + α_P = 1 + √2.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace PrincipiaTractalis
namespace AlphaBSDIntegralBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — cos(α_BSD) = -α_P / α_YM -/

/-- **`cos(α_BSD) = -α_P / α_YM`** — cos(3π/4) = -√2/2. -/
theorem cos_α_BSD_eq_neg_α_P_div_α_YM :
    Real.cos α_BSD = -α_P / α_YM := by
  unfold α_BSD
  rw [show (3 * Real.pi / 4 : ℝ) = Real.pi - Real.pi / 4 by ring]
  rw [Real.cos_pi_sub, Real.cos_pi_div_four]
  unfold α_P α_YM
  ring

/-! ## §2 — sin(α_BSD) = α_P / α_YM -/

/-- **`sin(α_BSD) = α_P / α_YM`** — sin(3π/4) = √2/2. -/
theorem sin_α_BSD_eq_α_P_div_α_YM :
    Real.sin α_BSD = α_P / α_YM := by
  unfold α_BSD
  rw [show (3 * Real.pi / 4 : ℝ) = Real.pi - Real.pi / 4 by ring]
  rw [Real.sin_pi_sub, Real.sin_pi_div_four]
  unfold α_P α_YM
  ring

/-! ## §3 — ∫₀^(α_BSD) cos x dx = α_P / α_YM -/

/-- **★★★ `∫₀^(α_BSD) cos x dx = α_P / α_YM` ★★★** — cosine integral
    from 0 to α_BSD = 3π/4 equals α_P/α_YM. -/
theorem integral_cos_zero_to_α_BSD_eq_α_P_div_α_YM :
    ∫ x in (0:ℝ)..α_BSD, Real.cos x = α_P / α_YM := by
  rw [integral_cos]
  rw [Real.sin_zero]
  rw [sin_α_BSD_eq_α_P_div_α_YM]
  ring

/-! ## §4 — ∫₀^(α_BSD) sin x dx = α_Poincaré + α_P / α_YM -/

/-- **`∫₀^(α_BSD) sin x dx = α_Poincaré + α_P / α_YM`** — sine integral. -/
theorem integral_sin_zero_to_α_BSD_eq_α_Poincare_plus_α_P_div_α_YM :
    ∫ x in (0:ℝ)..α_BSD, Real.sin x = α_Poincare + α_P / α_YM := by
  rw [integral_sin]
  rw [Real.cos_zero]
  rw [cos_α_BSD_eq_neg_α_P_div_α_YM]
  unfold α_Poincare
  ring

/-! ## §5 — ∫₀^(α_BSD) (sin x + cos x) dx = α_Poincaré + α_P (silver ratio) -/

/-- **★★★ `∫₀^(α_BSD) (sin x + cos x) dx = α_Poincaré + α_P` ★★★** —
    the sum-of-trig integral over [0, α_BSD] = [0, 3π/4] equals the
    silver ratio = 1 + √2. -/
theorem integral_sin_plus_cos_zero_to_α_BSD_eq_silver_ratio :
    ∫ x in (0:ℝ)..α_BSD, (Real.sin x + Real.cos x) = α_Poincare + α_P := by
  rw [intervalIntegral.integral_add (Real.continuous_sin.intervalIntegrable _ _)
        (Real.continuous_cos.intervalIntegrable _ _)]
  rw [integral_sin_zero_to_α_BSD_eq_α_Poincare_plus_α_P_div_α_YM]
  rw [integral_cos_zero_to_α_BSD_eq_α_P_div_α_YM]
  -- α_Poincare + α_P/α_YM + α_P/α_YM = α_Poincare + α_P
  -- since α_YM = 2, we have 2 · α_P / α_YM = α_P
  unfold α_YM
  ring

/-! ## §6 — Bundle capstone -/

/-- **★★★★ THE α_BSD-INTEGRAL BUNDLE CAPSTONE ★★★★** —
    five identities exhibiting sin/cos values and integrals over
    [0, α_BSD] = [0, 3π/4]:

      cos(α_BSD) = -α_P / α_YM                       (cos value)
      sin(α_BSD) = α_P / α_YM                         (sin value)
      ∫₀^(α_BSD) cos x dx = α_P / α_YM                 (cos integral)
      ∫₀^(α_BSD) sin x dx = α_Poincaré + α_P / α_YM    (sin integral)
      ∫₀^(α_BSD) (sin + cos) x dx = α_Poincaré + α_P   (silver ratio!)

    The sum-of-trig integral from 0 to α_BSD equals the silver ratio
    α_Poincaré + α_P = 1 + √2, anchoring it to the BSD axis. -/
theorem α_BSD_integral_bundle_capstone :
    Real.cos α_BSD = -α_P / α_YM ∧
    Real.sin α_BSD = α_P / α_YM ∧
    (∫ x in (0:ℝ)..α_BSD, Real.cos x) = α_P / α_YM ∧
    (∫ x in (0:ℝ)..α_BSD, Real.sin x) = α_Poincare + α_P / α_YM ∧
    (∫ x in (0:ℝ)..α_BSD, (Real.sin x + Real.cos x)) = α_Poincare + α_P :=
  ⟨cos_α_BSD_eq_neg_α_P_div_α_YM,
   sin_α_BSD_eq_α_P_div_α_YM,
   integral_cos_zero_to_α_BSD_eq_α_P_div_α_YM,
   integral_sin_zero_to_α_BSD_eq_α_Poincare_plus_α_P_div_α_YM,
   integral_sin_plus_cos_zero_to_α_BSD_eq_silver_ratio⟩

end AlphaBSDIntegralBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaBSDIntegralBundle.cos_α_BSD_eq_neg_α_P_div_α_YM
#print axioms PrincipiaTractalis.AlphaBSDIntegralBundle.sin_α_BSD_eq_α_P_div_α_YM
#print axioms PrincipiaTractalis.AlphaBSDIntegralBundle.integral_cos_zero_to_α_BSD_eq_α_P_div_α_YM
#print axioms PrincipiaTractalis.AlphaBSDIntegralBundle.integral_sin_zero_to_α_BSD_eq_α_Poincare_plus_α_P_div_α_YM
#print axioms PrincipiaTractalis.AlphaBSDIntegralBundle.integral_sin_plus_cos_zero_to_α_BSD_eq_silver_ratio
#print axioms PrincipiaTractalis.AlphaBSDIntegralBundle.α_BSD_integral_bundle_capstone
