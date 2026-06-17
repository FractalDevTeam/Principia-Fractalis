/-
# PF.AlphaRationalAlgebraicRatiosBundle

★ 2026-06-17 — Six clean closed-form ratios between the rational Clay
α-axes (α_RH = 3/2, α_YM = 2) and the algebraic Clay α-axes
(α_P = √2, α_NP = φ + 1/4, α_Hodge = φ).

## Identities

  α_RH-against-algebraic:
    α_RH / α_P     = 3·α_P / 4         [via 1/√2 = √2/2]
    α_RH / α_Hodge = (3·α_Hodge − 3) / 2  [via 1/φ = φ − 1]
    α_RH / α_NP    = (24·α_Hodge − 30) / 11
                                       [via 1/(4·α_Hodge + 1) = (4·α_Hodge − 5)/11]

  α_YM-against-algebraic:
    α_YM / α_P     = α_P              [direct: 2/√2 = √2]
    α_YM / α_Hodge = 2·α_Hodge − 2
    α_YM / α_NP    = (32·α_Hodge − 40) / 11

All six clean closed forms inside ℚ(√2), ℚ(φ), or ℚ depending on the
algebraic factor.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import PF.TuringEncoding.AlphaCanonical

namespace PrincipiaTractalis
namespace AlphaRationalAlgebraicRatiosBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — α_RH against algebraic axes -/

/-- **`α_RH / α_P = 3·α_P / 4`** — clean ℚ(√2) closed form. -/
theorem α_RH_div_α_P : α_RH / α_P = 3 * α_P / 4 := by
  unfold α_RH α_P
  have h_sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  field_simp
  nlinarith [h_sqrt2_sq, h_sqrt2_pos]

/-- **`α_RH / α_Hodge = (3·α_Hodge − 3) / 2`** — clean ℚ(φ) closed form
    via the golden inverse `1/φ = φ − 1`. -/
theorem α_RH_div_α_Hodge : α_RH / α_Hodge = (3 * α_Hodge - 3) / 2 := by
  unfold α_RH α_Hodge phi
  have h_sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have h_phi_pos : (0 : ℝ) < (1 + Real.sqrt 5) / 2 := by linarith
  field_simp
  nlinarith [h_sqrt5_sq, h_sqrt5_pos]

/-- **`α_RH / α_NP = (24·α_Hodge − 30) / 11`** — clean ℚ(φ) closed form
    via the rationalization `1/(4·α_Hodge + 1) = (4·α_Hodge − 5)/11`. -/
theorem α_RH_div_α_NP : α_RH / α_NP = (24 * α_Hodge - 30) / 11 := by
  unfold α_RH α_NP α_Hodge phi
  have h_sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have h_α_NP_pos : (0 : ℝ) < (1 + Real.sqrt 5) / 2 + 1/4 := by linarith
  field_simp
  nlinarith [h_sqrt5_sq, h_α_NP_pos]

/-! ## §2 — α_YM against algebraic axes -/

/-- **`α_YM / α_P = α_P`** — clean ℚ(√2) identity: 2/√2 = √2. -/
theorem α_YM_div_α_P : α_YM / α_P = α_P := by
  unfold α_YM α_P
  have h_sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  field_simp
  nlinarith [h_sqrt2_sq, h_sqrt2_pos]

/-- **`α_YM / α_Hodge = 2·α_Hodge − 2`** — clean ℚ(φ) closed form. -/
theorem α_YM_div_α_Hodge : α_YM / α_Hodge = 2 * α_Hodge - 2 := by
  unfold α_YM α_Hodge phi
  have h_sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have h_phi_pos : (0 : ℝ) < (1 + Real.sqrt 5) / 2 := by linarith
  field_simp
  nlinarith [h_sqrt5_sq, h_sqrt5_pos]

/-- **`α_YM / α_NP = (32·α_Hodge − 40) / 11`** — clean ℚ(φ) closed form. -/
theorem α_YM_div_α_NP : α_YM / α_NP = (32 * α_Hodge - 40) / 11 := by
  unfold α_YM α_NP α_Hodge phi
  have h_sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have h_α_NP_pos : (0 : ℝ) < (1 + Real.sqrt 5) / 2 + 1/4 := by linarith
  field_simp
  nlinarith [h_sqrt5_sq, h_α_NP_pos]

/-! ## §3 — Bundle capstone -/

/-- **★ Rational/algebraic ratio bundle capstone ★** — six clean closed
    forms relating the rational Clay axes (α_RH, α_YM) to the algebraic
    Clay axes (α_P, α_NP, α_Hodge). -/
theorem α_rational_algebraic_ratios_bundle_capstone :
    α_RH / α_P = 3 * α_P / 4 ∧
    α_RH / α_Hodge = (3 * α_Hodge - 3) / 2 ∧
    α_RH / α_NP = (24 * α_Hodge - 30) / 11 ∧
    α_YM / α_P = α_P ∧
    α_YM / α_Hodge = 2 * α_Hodge - 2 ∧
    α_YM / α_NP = (32 * α_Hodge - 40) / 11 :=
  ⟨α_RH_div_α_P, α_RH_div_α_Hodge, α_RH_div_α_NP,
   α_YM_div_α_P, α_YM_div_α_Hodge, α_YM_div_α_NP⟩

end AlphaRationalAlgebraicRatiosBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaRationalAlgebraicRatiosBundle.α_RH_div_α_P
#print axioms PrincipiaTractalis.AlphaRationalAlgebraicRatiosBundle.α_RH_div_α_Hodge
#print axioms PrincipiaTractalis.AlphaRationalAlgebraicRatiosBundle.α_RH_div_α_NP
#print axioms PrincipiaTractalis.AlphaRationalAlgebraicRatiosBundle.α_YM_div_α_P
#print axioms PrincipiaTractalis.AlphaRationalAlgebraicRatiosBundle.α_YM_div_α_Hodge
#print axioms PrincipiaTractalis.AlphaRationalAlgebraicRatiosBundle.α_YM_div_α_NP
#print axioms
  PrincipiaTractalis.AlphaRationalAlgebraicRatiosBundle.α_rational_algebraic_ratios_bundle_capstone
