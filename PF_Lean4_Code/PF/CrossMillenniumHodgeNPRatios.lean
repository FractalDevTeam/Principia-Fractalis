/-
# PF.CrossMillenniumHodgeNPRatios

★ 2026-06-17 — Two closed-form ratio identities between α_NP = φ + 1/4
and α_Hodge = φ, both of which live in ℚ(φ) = ℚ(√5).

## Identities

  (A) `α_NP / α_Hodge = (α_Hodge + 3) / 4`
      Derivation: α_NP / α_Hodge = (φ + 1/4)/φ = 1 + 1/(4φ)
                = 1 + (φ - 1)/4 [via 1/φ = φ - 1, golden inverse]
                = (3 + φ)/4 = (α_Hodge + 3)/4.

      Numerically (α_Hodge + 3)/4 ≈ 4.618/4 ≈ 1.1545.

  (B) `α_Hodge / α_NP = 4·(4 - α_Hodge) / 11`
      Derivation: α_Hodge/α_NP = 4α_Hodge/(4α_Hodge + 1). Rationalize
      via minimal poly (4α_Hodge)² = 4·(4α_Hodge) + 16:
        1/(4α_Hodge + 1) = (4α_Hodge - 5)/11
      Hence α_Hodge/α_NP = 4α_Hodge·(4α_Hodge - 5)/11
                         = 4·(4α_Hodge² - 5α_Hodge)/11
                         = 4·(4(α_Hodge + 1) - 5α_Hodge)/11
                         = 4·(4 - α_Hodge)/11.

      Numerically 4·(4 - α_Hodge)/11 ≈ 4·2.382/11 ≈ 0.8662.

## Consistency

The product `(α_NP / α_Hodge) · (α_Hodge / α_NP) = 1` factors through
the identity `(α_Hodge + 3)(4 - α_Hodge) = 11` modulo α_Hodge² = α_Hodge + 1.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace CrossMillenniumHodgeNPRatios

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_NP / α_Hodge -/

/-- **`α_NP / α_Hodge = (α_Hodge + 3) / 4`** — clean closed form for
    the NP/Hodge ratio inside ℚ(φ). -/
theorem α_NP_div_α_Hodge :
    α_NP / α_Hodge = (α_Hodge + 3) / 4 := by
  unfold α_NP α_Hodge phi
  have h_sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have h_phi_pos : (0 : ℝ) < (1 + Real.sqrt 5) / 2 := by
    have : (0 : ℝ) < 1 + Real.sqrt 5 := by linarith
    linarith
  field_simp
  nlinarith [h_sqrt5_sq, h_sqrt5_pos]

/-! ## §2 — α_Hodge / α_NP -/

/-- **`α_Hodge / α_NP = 4·(4 - α_Hodge) / 11`** — clean closed form for
    the Hodge/NP ratio inside ℚ(φ). -/
theorem α_Hodge_div_α_NP :
    α_Hodge / α_NP = 4 * (4 - α_Hodge) / 11 := by
  unfold α_NP α_Hodge phi
  have h_sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have h_α_NP_pos : (0 : ℝ) < (1 + Real.sqrt 5) / 2 + 1/4 := by linarith
  field_simp
  nlinarith [h_sqrt5_sq, h_α_NP_pos]

/-! ## §3 — Product consistency -/

/-- **`(α_NP / α_Hodge) · (α_Hodge / α_NP) = 1`** — the two ratio
    closed forms compose to 1, a structural consistency witness
    factoring through `(α_Hodge + 3)·(4 - α_Hodge) = 11` modulo
    `α_Hodge² = α_Hodge + 1`. -/
theorem α_NP_α_Hodge_ratio_product_eq_one :
    (α_NP / α_Hodge) * (α_Hodge / α_NP) = 1 := by
  rw [α_NP_div_α_Hodge, α_Hodge_div_α_NP]
  -- (α_Hodge + 3) * 4 * (4 - α_Hodge) / (4 * 11) = (α_Hodge + 3)(4 - α_Hodge) / 11
  -- (α_Hodge + 3)(4 - α_Hodge) = 4·α_Hodge + 12 - α_Hodge² - 3·α_Hodge
  --                            = α_Hodge - (α_Hodge + 1) + 12 = 11   via α_Hodge² = α_Hodge + 1
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  nlinarith [h_sq]

/-! ## §4 — Ratio bridge capstone -/

/-- **★ NP/Hodge ratio bridge capstone ★** — both ratios are clean
    closed forms in ℚ(φ), and their product is 1. -/
theorem α_NP_α_Hodge_ratio_bridge_capstone :
    α_NP / α_Hodge = (α_Hodge + 3) / 4 ∧
    α_Hodge / α_NP = 4 * (4 - α_Hodge) / 11 ∧
    (α_NP / α_Hodge) * (α_Hodge / α_NP) = 1 :=
  ⟨α_NP_div_α_Hodge,
   α_Hodge_div_α_NP,
   α_NP_α_Hodge_ratio_product_eq_one⟩

end CrossMillenniumHodgeNPRatios
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.CrossMillenniumHodgeNPRatios.α_NP_div_α_Hodge
#print axioms
  PrincipiaTractalis.CrossMillenniumHodgeNPRatios.α_Hodge_div_α_NP
#print axioms
  PrincipiaTractalis.CrossMillenniumHodgeNPRatios.α_NP_α_Hodge_ratio_product_eq_one
#print axioms
  PrincipiaTractalis.CrossMillenniumHodgeNPRatios.α_NP_α_Hodge_ratio_bridge_capstone
