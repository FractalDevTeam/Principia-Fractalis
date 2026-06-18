/-
# PF.AlphaMachinFormulaBundle

★★★★ 2026-06-17 — FUN: John Machin's 1706 formula for π in framework form.

## Headline

  4·arctan(1/5) − arctan(1/239) = α_BSD / 3 = π/4

The historical Machin's formula (1706), used by Machin himself to
compute π to 100 decimal places, anchors to α_BSD/3 in framework form.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace PrincipiaTractalis
namespace AlphaMachinFormulaBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — Machin's formula in framework form -/

/-- **★★★ MACHIN'S 1706 FORMULA IN FRAMEWORK FORM ★★★** —
    `4·arctan(1/5) − arctan(1/239) = α_BSD / 3 = π/4`. -/
theorem machin_formula_eq_α_BSD_div_three :
    4 * Real.arctan ((5 : ℝ)⁻¹) - Real.arctan ((239 : ℝ)⁻¹) = α_BSD / 3 := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  unfold α_BSD
  linarith [h]

/-! ## §2 — Bundle capstone -/

/-- **★★★★ THE MACHIN-FORMULA BUNDLE CAPSTONE ★★★★** —
    John Machin's 1706 formula for π in framework form:

      4·arctan(1/5) − arctan(1/239) = α_BSD/3 = π/4

    Machin used this formula to compute π to 100 decimal places —
    the most accurate computation of π for over 200 years. The
    identity anchors to one-third of the BSD axis in framework form. -/
theorem α_machin_formula_bundle_capstone :
    4 * Real.arctan ((5 : ℝ)⁻¹) - Real.arctan ((239 : ℝ)⁻¹) = α_BSD / 3 :=
  machin_formula_eq_α_BSD_div_three

end AlphaMachinFormulaBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaMachinFormulaBundle.machin_formula_eq_α_BSD_div_three
#print axioms PrincipiaTractalis.AlphaMachinFormulaBundle.α_machin_formula_bundle_capstone
