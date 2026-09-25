/-
# PF.PvsNPAnchorReduction

**Date**: 2026-09-25
**Landing**: TOE — P vs NP subsystem under the two-anchor cascade.

Given the two external anchors (Perelman + OpenAI-corroborated NS) and
the framework's structural identities, the P and NP α-values are forced:

    α_P  = √2       (via α_P² = α_YM = α_Poincaré + 1 = 2, positivity)
    α_NP = φ + 1/4  (via α_NP - α_Hodge = 1/4, α_Hodge = φ from I8+pos)

## Kernel status

Zero project axioms; only `propext, Classical.choice, Quot.sound`.
-/

import PF.HodgeQuadraticFromTwoAnchors

namespace PF.TwoAnchorCascade

open Real

/-- **α_P from the P-YM-Perelman triangle.** Given `α_P² = α_YM`
(Wave 22 identity) and `α_YM = α_Poincaré + 1` (I7) with
`α_Poincaré = 1` (Perelman anchor) and `α_P > 0`, we get `α_P = √2`. -/
theorem alpha_P_from_two_anchors
    (aP aYM aPoin : ℝ)
    (hP_sq : aP ^ 2 = aYM)           -- Wave 22
    (I7 : aYM = aPoin + 1)           -- I7
    (hPoin : aPoin = 1)              -- Perelman anchor
    (hpos : 0 < aP) :
    aP = Real.sqrt 2 := by
  have hYM : aYM = 2 := by rw [I7, hPoin]; ring
  have h_sq_2 : aP ^ 2 = 2 := by rw [hP_sq, hYM]
  -- aP > 0 and aP² = 2 ⟹ aP = √2
  have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have : aP = Real.sqrt (aP ^ 2) := by
    rw [Real.sqrt_sq hpos.le]
  rw [this, h_sq_2]

/-- **α_NP from Hodge link.** Given `α_NP - α_Hodge = 1/4` (framework
identity) and `α_Hodge = φ = (1 + √5)/2` (from I8 + positivity via
`hodge_from_two_anchors`), we get `α_NP = (1 + √5)/2 + 1/4`. -/
theorem alpha_NP_from_two_anchors
    (aNP aH : ℝ)
    (hNP_link : aNP - aH = 1/4)
    (I8 : aH ^ 2 = aH + 1)
    (hH_pos : 0 < aH) :
    aNP = (1 + Real.sqrt 5) / 2 + 1/4 := by
  have hH_val : aH = (1 + Real.sqrt 5) / 2 :=
    hodge_from_two_anchors aH I8 hH_pos
  linarith

/-- **Combined P-NP capstone under two anchors.** Package the P and NP
α-values as functions of the two external anchors plus the four
structural identities used. -/
theorem pvsnp_from_two_anchors
    (aP aNP aYM aH aPoin : ℝ)
    -- Anchors
    (hPoin : aPoin = 1)              -- Perelman anchor
    -- Structural identities
    (hP_sq : aP ^ 2 = aYM)           -- Wave 22: α_P² = α_YM
    (I7 : aYM = aPoin + 1)           -- I7: α_YM = α_Poincaré + 1
    (I8 : aH ^ 2 = aH + 1)           -- I8: α_Hodge² = α_Hodge + 1
    (hNP_link : aNP - aH = 1/4)      -- α_NP - α_Hodge = 1/4
    -- Positivity
    (hP_pos : 0 < aP) (hH_pos : 0 < aH) :
    aP = Real.sqrt 2
    ∧ aH = (1 + Real.sqrt 5) / 2
    ∧ aNP = (1 + Real.sqrt 5) / 2 + 1/4 := by
  refine ⟨?_, ?_, ?_⟩
  · exact alpha_P_from_two_anchors aP aYM aPoin hP_sq I7 hPoin hP_pos
  · exact hodge_from_two_anchors aH I8 hH_pos
  · exact alpha_NP_from_two_anchors aNP aH hNP_link I8 hH_pos

/-! ## Axiom sanity gate -/

#print axioms alpha_P_from_two_anchors
#print axioms alpha_NP_from_two_anchors
#print axioms pvsnp_from_two_anchors

end PF.TwoAnchorCascade
