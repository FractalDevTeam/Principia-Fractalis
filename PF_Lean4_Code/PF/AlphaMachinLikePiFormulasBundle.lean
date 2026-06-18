/-
# PF.AlphaMachinLikePiFormulasBundle

★★★★ 2026-06-17 — FUN: the four classical Machin-like arctan identities
for π/4 = α_BSD/3 in framework form.

## The four Machin-like identities

  Strassnitzky:   arctan(1/2) + arctan(1/3)         = α_BSD / 3   (= π/4)
  Hutton:         2·arctan(1/2) − arctan(1/7)        = α_BSD / 3
  Hermann:        2·arctan(1/3) + arctan(1/7)        = α_BSD / 3
  Machin (1706):  4·arctan(1/5) − arctan(1/239)      = α_BSD / 3

All four 17th-18th century arctan formulas for π anchor to one-third
of the BSD axis in framework form. The framework's α_BSD = 3π/4 is the
canonical π-axis for arctan computations.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace PrincipiaTractalis
namespace AlphaMachinLikePiFormulasBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — Strassnitzky / Euler (1738) -/

/-- **`arctan(1/2) + arctan(1/3) = α_BSD/3`** — the simplest two-term
    π/4 identity (Strassnitzky, also Euler 1738). -/
theorem strassnitzky_eq_α_BSD_div_three :
    Real.arctan ((2 : ℝ)⁻¹) + Real.arctan ((3 : ℝ)⁻¹) = α_BSD / 3 := by
  rw [Real.arctan_inv_2_add_arctan_inv_3]
  unfold α_BSD
  ring

/-! ## §2 — Hutton (1776) -/

/-- **`2·arctan(1/2) − arctan(1/7) = α_BSD/3`** — Hutton's identity. -/
theorem hutton_eq_α_BSD_div_three :
    2 * Real.arctan ((2 : ℝ)⁻¹) - Real.arctan ((7 : ℝ)⁻¹) = α_BSD / 3 := by
  rw [Real.two_mul_arctan_inv_2_sub_arctan_inv_7]
  unfold α_BSD
  ring

/-! ## §3 — Hermann -/

/-- **`2·arctan(1/3) + arctan(1/7) = α_BSD/3`** — Hermann's identity. -/
theorem hermann_eq_α_BSD_div_three :
    2 * Real.arctan ((3 : ℝ)⁻¹) + Real.arctan ((7 : ℝ)⁻¹) = α_BSD / 3 := by
  rw [Real.two_mul_arctan_inv_3_add_arctan_inv_7]
  unfold α_BSD
  ring

/-! ## §4 — Machin (1706) -/

/-- **`4·arctan(1/5) − arctan(1/239) = α_BSD/3`** — John Machin's 1706
    formula used to compute π to 100 decimal places. -/
theorem machin_eq_α_BSD_div_three :
    4 * Real.arctan ((5 : ℝ)⁻¹) - Real.arctan ((239 : ℝ)⁻¹) = α_BSD / 3 := by
  rw [Real.four_mul_arctan_inv_5_sub_arctan_inv_239]
  unfold α_BSD
  ring

/-! ## §5 — Bundle capstone -/

/-- **★★★★ THE FOUR MACHIN-LIKE π-FORMULAS CAPSTONE ★★★★** —
    all four classical 17th-18th century arctan identities for π/4 in
    framework form, anchored to α_BSD/3:

      arctan(1/2) + arctan(1/3) = α_BSD/3              (Strassnitzky/Euler)
      2·arctan(1/2) − arctan(1/7) = α_BSD/3             (Hutton)
      2·arctan(1/3) + arctan(1/7) = α_BSD/3             (Hermann)
      4·arctan(1/5) − arctan(1/239) = α_BSD/3           (Machin 1706)

    All four hand-computation π formulas anchor to one-third of the
    framework's BSD axis. -/
theorem α_machin_like_pi_formulas_capstone :
    Real.arctan ((2 : ℝ)⁻¹) + Real.arctan ((3 : ℝ)⁻¹) = α_BSD / 3 ∧
    2 * Real.arctan ((2 : ℝ)⁻¹) - Real.arctan ((7 : ℝ)⁻¹) = α_BSD / 3 ∧
    2 * Real.arctan ((3 : ℝ)⁻¹) + Real.arctan ((7 : ℝ)⁻¹) = α_BSD / 3 ∧
    4 * Real.arctan ((5 : ℝ)⁻¹) - Real.arctan ((239 : ℝ)⁻¹) = α_BSD / 3 :=
  ⟨strassnitzky_eq_α_BSD_div_three,
   hutton_eq_α_BSD_div_three,
   hermann_eq_α_BSD_div_three,
   machin_eq_α_BSD_div_three⟩

end AlphaMachinLikePiFormulasBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaMachinLikePiFormulasBundle.strassnitzky_eq_α_BSD_div_three
#print axioms PrincipiaTractalis.AlphaMachinLikePiFormulasBundle.hutton_eq_α_BSD_div_three
#print axioms PrincipiaTractalis.AlphaMachinLikePiFormulasBundle.hermann_eq_α_BSD_div_three
#print axioms PrincipiaTractalis.AlphaMachinLikePiFormulasBundle.machin_eq_α_BSD_div_three
#print axioms PrincipiaTractalis.AlphaMachinLikePiFormulasBundle.α_machin_like_pi_formulas_capstone
