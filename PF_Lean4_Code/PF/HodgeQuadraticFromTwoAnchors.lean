/-
# PF.HodgeQuadraticFromTwoAnchors

**Date**: 2026-09-25
**Landing**: TOE — Hodge extension of two-anchor cascade.

Given the Hodge quadratic identity `α_Hodge² = α_Hodge + 1` (I8) and
positivity `0 < α_Hodge`, the value is uniquely determined:
    α_Hodge = φ = (1 + √5) / 2.

## Kernel status

Zero project axioms; only `propext, Classical.choice, Quot.sound`.
-/

import PF.TwoAnchorCascadeCapstone
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PF.TwoAnchorCascade

open Real

/-- **Hodge value from I8 + positivity.** The φ-quadratic
`aH² = aH + 1` with `aH > 0` has the unique solution
`aH = (1 + √5) / 2 = φ`. -/
theorem hodge_from_two_anchors
    (aH : ℝ) (I8 : aH ^ 2 = aH + 1) (hpos : 0 < aH) :
    aH = (1 + Real.sqrt 5) / 2 := by
  -- √5 · √5 = 5
  have h5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- √5 > 1 (since 1² = 1 < 5)
  have h5_gt_1 : (1 : ℝ) < Real.sqrt 5 := by
    have h : Real.sqrt 1 < Real.sqrt 5 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using h
  -- Set φ = (1+√5)/2, ψ = (1-√5)/2. Then φ+ψ = 1, φ·ψ = -1.
  have hsum : (1 + Real.sqrt 5) / 2 + (1 - Real.sqrt 5) / 2 = 1 := by ring
  have hprod :
      (1 + Real.sqrt 5) / 2 * ((1 - Real.sqrt 5) / 2)
        = -1 := by
    have : (1 + Real.sqrt 5) * (1 - Real.sqrt 5)
             = 1 - Real.sqrt 5 * Real.sqrt 5 := by ring
    calc (1 + Real.sqrt 5) / 2 * ((1 - Real.sqrt 5) / 2)
        = ((1 + Real.sqrt 5) * (1 - Real.sqrt 5)) / 4 := by ring
      _ = (1 - Real.sqrt 5 * Real.sqrt 5) / 4 := by rw [this]
      _ = (1 - 5) / 4 := by rw [h5_sq]
      _ = -1 := by norm_num
  -- Factor: (aH - φ)(aH - ψ) = aH² - aH·(φ+ψ) + φ·ψ = aH² - aH - 1 = 0.
  have hfact :
      (aH - (1 + Real.sqrt 5) / 2) * (aH - (1 - Real.sqrt 5) / 2) = 0 := by
    have expand :
        (aH - (1 + Real.sqrt 5) / 2) * (aH - (1 - Real.sqrt 5) / 2)
          = aH ^ 2 - aH * ((1 + Real.sqrt 5) / 2 + (1 - Real.sqrt 5) / 2)
              + (1 + Real.sqrt 5) / 2 * ((1 - Real.sqrt 5) / 2) := by ring
    rw [expand, hsum, hprod]
    linarith
  -- Root selection by positivity: ψ = (1 - √5)/2 < 0 since √5 > 1.
  rcases mul_eq_zero.mp hfact with h1 | h2
  · linarith
  · exfalso
    have haH_neg : aH = (1 - Real.sqrt 5) / 2 := by linarith
    have hpsi_neg : (1 - Real.sqrt 5) / 2 < 0 := by linarith
    linarith

/-! ## Axiom sanity gate -/

#print axioms hodge_from_two_anchors

end PF.TwoAnchorCascade
