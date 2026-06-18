/-
# PF.AlphaExponentialDecayIntegralBundle

★★★★ 2026-06-17 — FUN: exponential decay integrals at α-axis lower
limits land on α-axis values.

## Integrals

  ∫_(0, ∞) exp(-x) dx = α_Poincaré              (exponential decay normalization)
  ∫_(log α_YM, ∞) exp(-x) dx = α_Poincaré / α_YM (= 1/2)
  ∫_(log α_RH, ∞) exp(-x) dx = α_Poincaré · α_YM / (α_RH · α_YM)    (= 2/3)

The classical exponential decay integrals over `(c, ∞)` evaluate to
exp(-c), which lands on α-axis values when c is a log of an α-axis.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace PrincipiaTractalis
namespace AlphaExponentialDecayIntegralBundle

open Real MeasureTheory
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — ∫_(0, ∞) exp(-x) dx = α_Poincaré -/

/-- **★★★ `∫_(0,∞) exp(-x) dx = α_Poincaré` ★★★** — exponential decay
    normalization in framework form. -/
theorem integral_exp_neg_Ioi_zero_eq_α_Poincare :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x)) = α_Poincare := by
  rw [integral_exp_neg_Ioi]
  simp [α_Poincare]

/-! ## §2 — ∫_(log α_YM, ∞) exp(-x) dx = α_Poincaré/α_YM -/

/-- **`∫_(log α_YM, ∞) exp(-x) dx = α_Poincaré / α_YM`** — exponential
    decay normalized to 1/2 starting at log α_YM. -/
theorem integral_exp_neg_Ioi_log_α_YM_eq_α_Poincare_div_α_YM :
    (∫ x in Set.Ioi (Real.log α_YM), Real.exp (-x)) = α_Poincare / α_YM := by
  rw [integral_exp_neg_Ioi]
  have h_pos : (0 : ℝ) < α_YM := by unfold α_YM; norm_num
  rw [show (-Real.log α_YM : ℝ) = Real.log (α_YM⁻¹) from by
    rw [Real.log_inv]]
  rw [Real.exp_log (by simp [inv_pos]; exact h_pos)]
  unfold α_Poincare
  field_simp

/-! ## §3 — ∫_(log α_RH, ∞) exp(-x) dx = α_Poincaré/α_RH -/

/-- **`∫_(log α_RH, ∞) exp(-x) dx = α_Poincaré / α_RH`** — exponential
    decay normalized to 2/3 starting at log α_RH. -/
theorem integral_exp_neg_Ioi_log_α_RH_eq_α_Poincare_div_α_RH :
    (∫ x in Set.Ioi (Real.log α_RH), Real.exp (-x)) = α_Poincare / α_RH := by
  rw [integral_exp_neg_Ioi]
  have h_pos : (0 : ℝ) < α_RH := by unfold α_RH; norm_num
  rw [show (-Real.log α_RH : ℝ) = Real.log (α_RH⁻¹) from by
    rw [Real.log_inv]]
  rw [Real.exp_log (by simp [inv_pos]; exact h_pos)]
  unfold α_Poincare
  field_simp

/-! ## §4 — Bundle capstone -/

/-- **★★★★ THE α-AXIS EXPONENTIAL-DECAY-INTEGRAL BUNDLE CAPSTONE ★★★★** —
    three identities exhibiting exponential decay integrals over `(c, ∞)`
    at α-axis lower limits c ∈ {0, log α_YM, log α_RH}:

      ∫_(0, ∞) exp(-x) dx = α_Poincaré                  (= 1)
      ∫_(log α_YM, ∞) exp(-x) dx = α_Poincaré / α_YM     (= 1/2)
      ∫_(log α_RH, ∞) exp(-x) dx = α_Poincaré / α_RH     (= 2/3)

    The exponential decay tail integral starting at `log(α)` equals
    `1/α`, so α-axis log-lower-limits give reciprocal-α-axis tail values. -/
theorem α_exponential_decay_integral_bundle_capstone :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x)) = α_Poincare ∧
    (∫ x in Set.Ioi (Real.log α_YM), Real.exp (-x)) = α_Poincare / α_YM ∧
    (∫ x in Set.Ioi (Real.log α_RH), Real.exp (-x)) = α_Poincare / α_RH :=
  ⟨integral_exp_neg_Ioi_zero_eq_α_Poincare,
   integral_exp_neg_Ioi_log_α_YM_eq_α_Poincare_div_α_YM,
   integral_exp_neg_Ioi_log_α_RH_eq_α_Poincare_div_α_RH⟩

end AlphaExponentialDecayIntegralBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaExponentialDecayIntegralBundle.integral_exp_neg_Ioi_zero_eq_α_Poincare
#print axioms PrincipiaTractalis.AlphaExponentialDecayIntegralBundle.integral_exp_neg_Ioi_log_α_YM_eq_α_Poincare_div_α_YM
#print axioms PrincipiaTractalis.AlphaExponentialDecayIntegralBundle.integral_exp_neg_Ioi_log_α_RH_eq_α_Poincare_div_α_RH
#print axioms PrincipiaTractalis.AlphaExponentialDecayIntegralBundle.α_exponential_decay_integral_bundle_capstone
