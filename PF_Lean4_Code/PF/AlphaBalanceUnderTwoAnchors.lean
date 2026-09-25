/-
# PF.AlphaBalanceUnderTwoAnchors

**Date**: 2026-09-25
**Landing**: TOE cascade extension — 4-axis Galois balance and NP-conjugate
sum under the two external anchors (Perelman + OpenAI-corroborated NS).

## What this file delivers

Two additional forced identities in the α-substrate, derived from the
already-established two-anchor cascade of `FiveWayFalsifiability`:

1. **Galois balance** — `α_Hodge + α_RH² = α_NP + α_YM`.
   Both sides equal `φ + 9/4` under the two anchors. This is the symmetric
   form of the 4-axis linear identity
   `α_Hodge = α_NP + α_YM − α_RH²`
   from `PF/AlphaFourAxisLinearIdentitiesBundle.lean`.

2. **NP-Galois-conjugate sum** — `α_NP + α_NP_conj = α_RH`, where
   `α_NP_conj = (1 − √5)/2 + 1/4` is the Galois conjugate of `α_NP` in
   `ℚ(√5)`. Vieta's formula on the defining quadratic
   `16·x² − 24·x − 11 = 0` (satisfied by both `α_NP` and `α_NP_conj`).

## Kernel status

Zero project axioms; only `propext, Classical.choice, Quot.sound`.
-/

import PF.FiveWayFalsifiability

namespace PF.TwoAnchorCascade

open Real

/-- The Galois conjugate of `α_NP = φ + 1/4` in `ℚ(√5)` is
`(1 − √5)/2 + 1/4`. -/
noncomputable def alpha_NP_conj : ℝ := (1 - Real.sqrt 5) / 2 + 1/4

/-- **4-axis Galois balance under two anchors.**

    Under the two anchors and the full framework identity set from
    `five_way_falsifiability`, the identity
    `α_Hodge + α_RH² = α_NP + α_YM` holds. Both sides equal `φ + 9/4`.

    This is the symmetric form of the 4-axis linear identity from
    `AlphaFourAxisLinearIdentitiesBundle`. -/
theorem four_axis_galois_balance
    (aPoin aRH aNS aYM aBSD aQG aH aP aNP : ℝ)
    -- Two external anchors
    (hPoin : aPoin = 1)
    (hNS : aNS = 3 * Real.pi / 2)
    -- Structural identities
    (I6 : aNS = 2 * aBSD)
    (I7 : aYM = aPoin + 1)
    (I8 : aH ^ 2 = aH + 1)
    (I9 : aRH * aYM = 3)
    (hQG_sq : aQG ^ 2 = (aPoin + 1) * Real.pi)
    (hP_sq : aP ^ 2 = aYM)
    (hNP_link : aNP - aH = 1/4)
    -- Physical positivity
    (hP_pos : 0 < aP) (hH_pos : 0 < aH) (hQG_pos : 0 < aQG) :
    aH + aRH ^ 2 = aNP + aYM := by
  -- Discharge each α-value via five_way_falsifiability, then compute.
  obtain ⟨hYM, hRH, hBSD, hQG_val, hH_val, hP_val, hNP_val⟩ :=
    five_way_falsifiability aPoin aRH aNS aYM aBSD aQG aH aP aNP
      hPoin hNS I6 I7 I8 I9 hQG_sq hP_sq hNP_link hP_pos hH_pos hQG_pos
  -- Substitute all forced values and verify algebraically.
  rw [hH_val, hRH, hNP_val, hYM]
  ring

/-- **α_NP satisfies the Vieta quadratic `16 x² − 24 x − 11 = 0`.**
Direct algebra: with `α_NP = (1+√5)/2 + 1/4 = (3 + 2√5)/4`,
`16·α_NP² − 24·α_NP − 11 = 0`. -/
lemma alpha_NP_satisfies_quadratic (aH : ℝ) (I8 : aH ^ 2 = aH + 1)
    (hH_pos : 0 < aH) :
    let aNP := aH + (1/4 : ℝ)
    16 * aNP ^ 2 - 24 * aNP - 11 = 0 := by
  simp only
  have hH_val : aH = (1 + Real.sqrt 5) / 2 :=
    hodge_from_two_anchors aH I8 hH_pos
  have h5_sq : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  rw [hH_val]
  -- Expand and use √5·√5 = 5
  have expand : 16 * ((1 + Real.sqrt 5) / 2 + 1/4) ^ 2
                  - 24 * ((1 + Real.sqrt 5) / 2 + 1/4) - 11
                = 4 * Real.sqrt 5 ^ 2 - 20 := by ring
  rw [expand, h5_sq]
  ring

/-- **α_NP-conjugate satisfies the same quadratic.** -/
lemma alpha_NP_conj_satisfies_quadratic :
    16 * alpha_NP_conj ^ 2 - 24 * alpha_NP_conj - 11 = 0 := by
  unfold alpha_NP_conj
  have h5_sq : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have expand : 16 * ((1 - Real.sqrt 5) / 2 + 1/4) ^ 2
                  - 24 * ((1 - Real.sqrt 5) / 2 + 1/4) - 11
                = 4 * Real.sqrt 5 ^ 2 - 20 := by ring
  rw [expand, h5_sq]
  ring

/-- **NP + NP-Galois-conjugate = α_RH.** Vieta's sum-of-roots law on the
NP defining polynomial `16 x² − 24 x − 11 = 0` yields the RH axis
value `3/2` as the sum. -/
theorem alpha_NP_plus_conj_eq_alpha_RH
    (aRH aYM aPoin aH aNP : ℝ)
    (hPoin : aPoin = 1)
    (I7 : aYM = aPoin + 1)
    (I9 : aRH * aYM = 3)
    (I8 : aH ^ 2 = aH + 1)
    (hNP_link : aNP - aH = 1/4)
    (hH_pos : 0 < aH) :
    aNP + alpha_NP_conj = aRH := by
  -- α_RH = 3/2 (from I9 with α_YM = 2)
  have hYM : aYM = 2 := by rw [I7, hPoin]; ring
  have hRH : aRH = 3/2 := by
    have h : aRH * 2 = 3 := hYM ▸ I9
    linarith
  -- α_H = φ = (1+√5)/2
  have hH_val : aH = (1 + Real.sqrt 5) / 2 :=
    hodge_from_two_anchors aH I8 hH_pos
  -- α_NP = φ + 1/4
  have hNP_val : aNP = (1 + Real.sqrt 5) / 2 + 1/4 := by
    rw [← hH_val]; linarith
  -- Sum: [(1+√5)/2 + 1/4] + [(1-√5)/2 + 1/4] = 3/2
  rw [hNP_val, hRH]
  unfold alpha_NP_conj
  ring

/-! ## Axiom sanity gate -/

#print axioms four_axis_galois_balance
#print axioms alpha_NP_satisfies_quadratic
#print axioms alpha_NP_conj_satisfies_quadratic
#print axioms alpha_NP_plus_conj_eq_alpha_RH

end PF.TwoAnchorCascade
