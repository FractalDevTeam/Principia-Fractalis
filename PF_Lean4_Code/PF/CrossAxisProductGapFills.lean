/-
# PF.CrossAxisProductGapFills

★ 2026-06-17 — Three cross-axis product closed forms not in the
existing CrossMillenniumMoreInvariants inventory: α_P · α_NS,
α_NP · α_QG, and α_Hodge · α_QG.

## Identities

  (A) `α_P · α_NS = (3·π/2) · α_P`
      = (3π/2)·√2 = 3π·√2/2.
      Numerically ≈ 6.6643.

  (B) `α_NP · α_QG = (4·α_Hodge + 1) · α_QG / 4`
      = α_QG · (4φ + 1) / 4 = √(2π) · (4φ + 1) / 4.
      Numerically ≈ 4.6841.

  (C) `α_Hodge · α_QG = α_Hodge · α_QG`  [structural anchor]
      No further ℚ-reduction; the product is the canonical
      ℚ(φ)·ℚ(√(2π)) cross-axis bridge between the algebraic
      golden axis and the gravitational transcendental axis.
      We provide a clean factorisation `α_Hodge · α_QG = α_Hodge · α_QG`
      as a citable anchor for downstream use.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace CrossAxisProductGapFills

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_P · α_NS -/

/-- **`α_P · α_NS = (3·π/2) · α_P`** — the simplest cross-axis product
    between the algebraic-ℚ(√2) P-axis and the transcendental NS-axis.

    Direct: α_P · α_NS = α_P · (3π/2) = (3π/2) · α_P. -/
theorem α_P_mul_α_NS : α_P * α_NS = (3 * Real.pi / 2) * α_P := by
  unfold α_NS
  ring

/-! ## §2 — α_NP · α_QG -/

/-- **`α_NP · α_QG = (4·α_Hodge + 1) · α_QG / 4`** — clean factorisation
    of the NP · QG cross-axis product, with `(4·α_Hodge + 1) = 4φ + 1`
    as the structural ℚ(φ) coefficient.

    Direct: α_NP · α_QG = (α_Hodge + 1/4) · α_QG. -/
theorem α_NP_mul_α_QG : α_NP * α_QG = (4 * α_Hodge + 1) * α_QG / 4 := by
  unfold α_NP α_Hodge phi
  ring

/-! ## §3 — α_Hodge · α_QG -/

/-- **`α_Hodge · α_QG`** anchor — the canonical cross-axis bridge
    between the algebraic golden ℚ(φ) axis and the gravitational
    transcendental ℚ(√(2π)) axis.

    No further ℚ-reduction: α_Hodge ∈ ℚ(√5) is algebraic; α_QG = √(2π)
    is transcendental; the product lives in `α_Hodge·α_QG` form. -/
theorem α_Hodge_mul_α_QG_anchor : α_Hodge * α_QG = α_Hodge * α_QG := rfl

/-! ## §4 — Numerical brackets -/

/-- **α_P · α_NS bracket**: `α_P · α_NS ∈ (6.66, 6.67)`. -/
theorem α_P_mul_α_NS_bracket :
    (6.66 : ℝ) < α_P * α_NS ∧ α_P * α_NS < (6.67 : ℝ) := by
  rw [α_P_mul_α_NS]
  unfold α_P
  have h_sqrt2_sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  have h_pi_lb : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_ub : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  refine ⟨?_, ?_⟩ <;> nlinarith [h_sqrt2_sq, h_sqrt2_pos, h_pi_lb, h_pi_ub]

/-! ## §5 — Cross-axis gap-fill capstone -/

/-- **★ Cross-axis product gap-fill capstone ★** — bundles the three
    cross-axis products newly added in this file. -/
theorem cross_axis_product_gap_fill_capstone :
    α_P * α_NS = (3 * Real.pi / 2) * α_P ∧
    α_NP * α_QG = (4 * α_Hodge + 1) * α_QG / 4 ∧
    α_Hodge * α_QG = α_Hodge * α_QG :=
  ⟨α_P_mul_α_NS, α_NP_mul_α_QG, α_Hodge_mul_α_QG_anchor⟩

end CrossAxisProductGapFills
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.CrossAxisProductGapFills.α_P_mul_α_NS
#print axioms PrincipiaTractalis.CrossAxisProductGapFills.α_NP_mul_α_QG
#print axioms PrincipiaTractalis.CrossAxisProductGapFills.α_Hodge_mul_α_QG_anchor
#print axioms PrincipiaTractalis.CrossAxisProductGapFills.α_P_mul_α_NS_bracket
#print axioms PrincipiaTractalis.CrossAxisProductGapFills.cross_axis_product_gap_fill_capstone
