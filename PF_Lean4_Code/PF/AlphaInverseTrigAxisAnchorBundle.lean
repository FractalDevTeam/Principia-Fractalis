/-
# PF.AlphaInverseTrigAxisAnchorBundle

★★★★ 2026-06-17 — FUN: inverse-trig values at α-axis arguments land
on framework axis combinations.

## Inverse-trig at α-axes

  arcsin(α_Poincaré) = α_QG² / α_YM²            (= π/2)
  arccos(α_Poincaré) = 0                          (= 0)
  arccos(-α_Poincaré) = α_QG² / α_YM              (= π)
  arccos(0) = α_QG² / α_YM²                       (= π/2)

The standard arcsin/arccos limits at ±α_Poincaré land cleanly on
α_QG²-based expressions. arcsin(1) and arccos(-1) give the canonical
right angle (α_QG²/α_YM²) and straight angle (α_QG²/α_YM).

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace PrincipiaTractalis
namespace AlphaInverseTrigAxisAnchorBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — arcsin(α_Poincaré) = α_QG² / α_YM² -/

/-- **`arcsin(α_Poincaré) = α_QG² / α_YM²`** — canonical right angle. -/
theorem arcsin_α_Poincare_eq_α_QG_sq_div_α_YM_sq :
    Real.arcsin α_Poincare = α_QG ^ 2 / α_YM ^ 2 := by
  unfold α_Poincare
  rw [Real.arcsin_one]
  rw [α_QG_sq_eq_two_pi]
  unfold α_YM
  ring

/-! ## §2 — arccos(α_Poincaré) = 0 -/

/-- **`arccos(α_Poincaré) = 0`** — angle of (1, 0). -/
theorem arccos_α_Poincare_eq_zero :
    Real.arccos α_Poincare = 0 := by
  unfold α_Poincare
  exact Real.arccos_one

/-! ## §3 — arccos(-α_Poincaré) = α_QG² / α_YM -/

/-- **`arccos(-α_Poincaré) = α_QG² / α_YM`** — canonical straight angle. -/
theorem arccos_neg_α_Poincare_eq_α_QG_sq_div_α_YM :
    Real.arccos (-α_Poincare) = α_QG ^ 2 / α_YM := by
  unfold α_Poincare
  rw [show (-(1 : ℝ)) = -1 from rfl]
  rw [Real.arccos_neg_one]
  rw [α_QG_sq_eq_two_pi]
  unfold α_YM
  ring

/-! ## §4 — arccos(0) = α_QG² / α_YM² -/

/-- **`arccos(0) = α_QG² / α_YM²`** — canonical right angle. -/
theorem arccos_zero_eq_α_QG_sq_div_α_YM_sq :
    Real.arccos 0 = α_QG ^ 2 / α_YM ^ 2 := by
  rw [Real.arccos_zero]
  rw [α_QG_sq_eq_two_pi]
  unfold α_YM
  ring

/-! ## §5 — Bundle capstone -/

/-- **★★★★ THE INVERSE-TRIG α-AXIS-ANCHOR BUNDLE CAPSTONE ★★★★** —
    four identities exhibiting inverse-trig values at α-axis arguments
    landing on α_QG²-based axis combinations:

      arcsin(α_Poincaré) = α_QG² / α_YM²          (= π/2, right angle)
      arccos(α_Poincaré) = 0                       (= 0)
      arccos(-α_Poincaré) = α_QG² / α_YM           (= π, straight angle)
      arccos(0) = α_QG² / α_YM²                    (= π/2, right angle)

    The canonical right angle π/2 = α_QG²/α_YM² and straight angle
    π = α_QG²/α_YM emerge from inverse-trig values at ±α_Poincaré. -/
theorem α_inverse_trig_axis_anchor_bundle_capstone :
    Real.arcsin α_Poincare = α_QG ^ 2 / α_YM ^ 2 ∧
    Real.arccos α_Poincare = 0 ∧
    Real.arccos (-α_Poincare) = α_QG ^ 2 / α_YM ∧
    Real.arccos 0 = α_QG ^ 2 / α_YM ^ 2 :=
  ⟨arcsin_α_Poincare_eq_α_QG_sq_div_α_YM_sq,
   arccos_α_Poincare_eq_zero,
   arccos_neg_α_Poincare_eq_α_QG_sq_div_α_YM,
   arccos_zero_eq_α_QG_sq_div_α_YM_sq⟩

end AlphaInverseTrigAxisAnchorBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaInverseTrigAxisAnchorBundle.arcsin_α_Poincare_eq_α_QG_sq_div_α_YM_sq
#print axioms PrincipiaTractalis.AlphaInverseTrigAxisAnchorBundle.arccos_α_Poincare_eq_zero
#print axioms PrincipiaTractalis.AlphaInverseTrigAxisAnchorBundle.arccos_neg_α_Poincare_eq_α_QG_sq_div_α_YM
#print axioms PrincipiaTractalis.AlphaInverseTrigAxisAnchorBundle.arccos_zero_eq_α_QG_sq_div_α_YM_sq
#print axioms PrincipiaTractalis.AlphaInverseTrigAxisAnchorBundle.α_inverse_trig_axis_anchor_bundle_capstone
