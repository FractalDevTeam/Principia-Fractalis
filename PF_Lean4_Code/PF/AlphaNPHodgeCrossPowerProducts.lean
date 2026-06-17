/-
# PF.AlphaNPHodgeCrossPowerProducts

★ 2026-06-17 — Cross-power products of α_NP and α_Hodge inside ℚ(φ),
extending the rank-1 product `α_Hodge · α_NP = (5/4)·α_Hodge + 1`
in `CrossMillenniumMoreInvariants`.

## Identities

  α_NP · α_Hodge^2 = (9/4)·α_Hodge + 5/4
  α_NP · α_Hodge^3 = (7/2)·α_Hodge + 9/4
  α_NP^2 · α_Hodge = (41/16)·α_Hodge + 3/2
  α_NP^3 · α_Hodge = (301/64)·α_Hodge + 47/16

All four close inside ℚ + ℚ·α_Hodge using α_Hodge² = α_Hodge + 1 and
the existing α_NP^k closed forms.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import PF.TuringEncoding.AlphaCanonical

namespace PrincipiaTractalis
namespace AlphaNPHodgeCrossPowerProducts

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — α_NP × α_Hodge^k -/

/-- **`α_NP · α_Hodge^2 = (9/4)·α_Hodge + 5/4`**. -/
theorem α_NP_mul_α_Hodge_sq :
    α_NP * α_Hodge ^ 2 = (9/4) * α_Hodge + 5/4 := by
  have h_step : α_NP * α_Hodge ^ 2 = (α_Hodge * α_NP) * α_Hodge := by ring
  rw [h_step, α_Hodge_mul_α_NP]
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  nlinarith [h_sq]

/-- **`α_NP · α_Hodge^3 = (7/2)·α_Hodge + 9/4`**. -/
theorem α_NP_mul_α_Hodge_cubed :
    α_NP * α_Hodge ^ 3 = (7/2) * α_Hodge + 9/4 := by
  have h_step : α_NP * α_Hodge ^ 3 = (α_Hodge * α_NP) * α_Hodge ^ 2 := by ring
  rw [h_step, α_Hodge_mul_α_NP]
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  nlinarith [h_sq]

/-! ## §2 — α_NP^k × α_Hodge -/

/-- **`α_NP^2 · α_Hodge = (41/16)·α_Hodge + 3/2`**. -/
theorem α_NP_sq_mul_α_Hodge :
    α_NP ^ 2 * α_Hodge = (41/16) * α_Hodge + 3/2 := by
  rw [α_NP_sq]
  have h_Hodge : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  nlinarith [h_Hodge]

/-- **`α_NP^3 · α_Hodge = (301/64)·α_Hodge + 47/16`**. -/
theorem α_NP_cubed_mul_α_Hodge :
    α_NP ^ 3 * α_Hodge = (301/64) * α_Hodge + 47/16 := by
  rw [α_NP_cubed]
  have h_Hodge : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  nlinarith [h_Hodge]

/-! ## §3 — Cross-power bundle capstone -/

/-- **★ α_NP × α_Hodge cross-power bundle capstone ★** — four clean
    closed forms inside ℚ + ℚ·α_Hodge connecting the NP and Hodge
    Clay axes through their substrate-rigidity relation. -/
theorem α_NP_α_Hodge_cross_power_bundle_capstone :
    α_NP * α_Hodge ^ 2 = (9/4) * α_Hodge + 5/4 ∧
    α_NP * α_Hodge ^ 3 = (7/2) * α_Hodge + 9/4 ∧
    α_NP ^ 2 * α_Hodge = (41/16) * α_Hodge + 3/2 ∧
    α_NP ^ 3 * α_Hodge = (301/64) * α_Hodge + 47/16 :=
  ⟨α_NP_mul_α_Hodge_sq,
   α_NP_mul_α_Hodge_cubed,
   α_NP_sq_mul_α_Hodge,
   α_NP_cubed_mul_α_Hodge⟩

end AlphaNPHodgeCrossPowerProducts
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaNPHodgeCrossPowerProducts.α_NP_mul_α_Hodge_sq
#print axioms PrincipiaTractalis.AlphaNPHodgeCrossPowerProducts.α_NP_mul_α_Hodge_cubed
#print axioms PrincipiaTractalis.AlphaNPHodgeCrossPowerProducts.α_NP_sq_mul_α_Hodge
#print axioms PrincipiaTractalis.AlphaNPHodgeCrossPowerProducts.α_NP_cubed_mul_α_Hodge
#print axioms
  PrincipiaTractalis.AlphaNPHodgeCrossPowerProducts.α_NP_α_Hodge_cross_power_bundle_capstone
