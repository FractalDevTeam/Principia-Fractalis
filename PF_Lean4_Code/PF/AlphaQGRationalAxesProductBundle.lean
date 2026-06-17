/-
# PF.AlphaQGRationalAxesProductBundle

★ 2026-06-17 — α_QG cross-axis products and ratios with the rational
α-axes (α_RH = 3/2, α_YM = 2, α_Poincaré = 1).

## Identities

  (A) α_QG · α_RH = (3/2) · α_QG = 3·α_QG/2
  (B) α_QG · α_YM = 2 · α_QG
  (C) α_QG · α_Poincaré = α_QG
  (D) α_QG / α_RH = (2/3) · α_QG = 2·α_QG/3
  (E) α_QG / α_YM = α_QG / 2

All are immediate from the rational axis values. Numerically:
  α_QG · α_RH ≈ 3.7599
  α_QG · α_YM ≈ 5.0133
  α_QG / α_RH ≈ 1.6711
  α_QG / α_YM ≈ 1.2533

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaQGRationalAxesProductBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — Products -/

/-- **`α_QG · α_RH = (3/2) · α_QG`**. -/
theorem α_QG_mul_α_RH : α_QG * α_RH = (3/2) * α_QG := by
  unfold α_RH
  ring

/-- **`α_QG · α_YM = 2 · α_QG`**. -/
theorem α_QG_mul_α_YM : α_QG * α_YM = 2 * α_QG := by
  unfold α_YM
  ring

/-- **`α_QG · α_Poincaré = α_QG`**. -/
theorem α_QG_mul_α_Poincare : α_QG * α_Poincare = α_QG := by
  unfold α_Poincare
  ring

/-! ## §2 — Ratios -/

/-- **`α_QG / α_RH = (2/3) · α_QG`**. -/
theorem α_QG_div_α_RH : α_QG / α_RH = (2/3) * α_QG := by
  unfold α_RH
  ring

/-- **`α_QG / α_YM = α_QG / 2`**. -/
theorem α_QG_div_α_YM : α_QG / α_YM = α_QG / 2 := by
  unfold α_YM
  ring

/-! ## §3 — α_QG rational-axes product/ratio bundle capstone -/

/-- **★ α_QG rational-axes product/ratio bundle capstone ★** —
    bundles the five clean closed forms between α_QG and the three
    rational Clay α-axes (α_RH, α_YM, α_Poincaré). -/
theorem α_QG_rational_axes_bundle_capstone :
    α_QG * α_RH = (3/2) * α_QG ∧
    α_QG * α_YM = 2 * α_QG ∧
    α_QG * α_Poincare = α_QG ∧
    α_QG / α_RH = (2/3) * α_QG ∧
    α_QG / α_YM = α_QG / 2 :=
  ⟨α_QG_mul_α_RH,
   α_QG_mul_α_YM,
   α_QG_mul_α_Poincare,
   α_QG_div_α_RH,
   α_QG_div_α_YM⟩

end AlphaQGRationalAxesProductBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaQGRationalAxesProductBundle.α_QG_mul_α_RH
#print axioms PrincipiaTractalis.AlphaQGRationalAxesProductBundle.α_QG_mul_α_YM
#print axioms PrincipiaTractalis.AlphaQGRationalAxesProductBundle.α_QG_mul_α_Poincare
#print axioms PrincipiaTractalis.AlphaQGRationalAxesProductBundle.α_QG_div_α_RH
#print axioms PrincipiaTractalis.AlphaQGRationalAxesProductBundle.α_QG_div_α_YM
#print axioms
  PrincipiaTractalis.AlphaQGRationalAxesProductBundle.α_QG_rational_axes_bundle_capstone
