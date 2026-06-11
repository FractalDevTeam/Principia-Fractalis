/-
# PF.Referee.MinimalSubstrateRigidityAnchorNecessity

★★★★ 2026-06-11 — PERELMAN ANCHOR IS STRICTLY NECESSARY ★★★★

The unified minimal substrate-rigidity result requires the Perelman
anchor `a_Poincare = 1` in addition to the 9 minimal cross-Millennium
algebraic invariants and the 3 positivity hypotheses. This file
certifies the anchor is strictly necessary: without it, the
α-skeleton has infinitely many solutions parameterized by
`a_Poincare`.

Counter-example: take any `a_Poincare = c ≠ 1`. The minimal sector-1
invariants then force `a_RH = c + 1/2`, `a_YM = c + 1`, `a_PvNP = c +
1/4`. With `a_BSD = (3/4)·π` (M3) and `a_NS = 2·a_BSD = (3/2)·π`
(M4), all sector-1 invariants hold. Sector-2 invariants require
`a_P² = a_YM = c + 1`, so `a_P = √(c+1)` (positive root). The
α-skeleton is uniquely determined by `c`, but differs from the
framework's whenever `c ≠ 1`.

Combined with:
  * `MinimalSubstrateRigidityUnified.unified_alpha_skeleton_forced_by_minimal_invariants`
    (sufficiency: 9 invariants + anchor + 3 positivities → unique α-skeleton),
  * `MinimalSubstrateRigidityIndependence.minimal_invariants_are_strictly_independent`
    (necessity of each invariant),
  * `MinimalSubstrateRigidityPositivityNecessity.positivity_hypotheses_are_strictly_necessary`
    (necessity of each positivity hypothesis),

the substrate-rigidity result is now COMPLETELY MINIMAL: every one
of the 13 hypotheses (9 invariants + 1 anchor + 3 positivities) is
strictly necessary for uniqueness.

ZERO project axioms. ZERO sorries.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-11.
-/

import PF.Referee.MinimalSubstrateRigidityUnified

namespace PF.Referee.MinimalSubstrateRigidityAnchorNecessity

open PF.Referee.CrossMillenniumCascadeParameterized
open PF.Referee.MinimalSubstrateRigidity
open PF.Referee.MinimalSubstrateRigiditySector2
open PF.Referee.MinimalSubstrateRigidityUnified

/-! ## §1 — Counter-example for the Perelman anchor

Take a_Poincare = 2 (not 1). The minimal invariants then force:
  a_RH = 5/2  (from M1: a_RH = a_Poincare + 1/2)
  a_YM = 3    (from M2: a_YM = a_Poincare + 1)
  a_BSD = (3/4)π (M3, independent of anchor)
  a_NS = (3/2)π  (M4: a_NS = 2·a_BSD)
  a_PvNP = 9/4 (M5: a_PvNP - a_Poincare = 1/4 ⇒ a_PvNP = 9/4)

For sector 2, take a_P = √3 (since a_YM = 3 under M6),
keep a_Hodge = (1+√5)/2 (M7 unchanged), a_NP = (1+√5)/2 + 1/4 (M8),
a_QG = √(2π) (M9). -/

private noncomputable def counter_anchor : UnifiedAlphaAssignment :=
  { sector1 :=
      { a_Poincare := 2
        a_RH       := 5/2
        a_YM       := 3
        a_BSD      := (3/4) * Real.pi
        a_NS       := (3/2) * Real.pi
        a_PvNP     := 9/4 }
    sector2 :=
      { a_P     := Real.sqrt 3
        a_Hodge := (1 + Real.sqrt 5) / 2
        a_NP    := (1 + Real.sqrt 5) / 2 + 1/4
        a_QG    := Real.sqrt (2 * Real.pi) } }

/-! ## §2 — counter_anchor satisfies all 9 minimal invariants -/

theorem counter_anchor_satisfies_M1 :
    counter_anchor.sector1.a_RH = counter_anchor.sector1.a_Poincare + 1/2 := by
  show (5/2 : ℝ) = 2 + 1/2; norm_num

theorem counter_anchor_satisfies_M2 :
    counter_anchor.sector1.a_YM = counter_anchor.sector1.a_Poincare + 1 := by
  show (3:ℝ) = 2 + 1; norm_num

theorem counter_anchor_satisfies_M3 :
    counter_anchor.sector1.a_BSD = (3/4) * Real.pi := rfl

theorem counter_anchor_satisfies_M4 :
    counter_anchor.sector1.a_NS = 2 * counter_anchor.sector1.a_BSD := by
  show (3/2) * Real.pi = 2 * ((3/4) * Real.pi); ring

theorem counter_anchor_satisfies_M5 :
    counter_anchor.sector1.a_PvNP - counter_anchor.sector1.a_Poincare = 1/4 := by
  show (9/4 : ℝ) - 2 = 1/4; norm_num

theorem counter_anchor_satisfies_M6 :
    counter_anchor.sector2.a_P ^ 2 = counter_anchor.sector1.a_YM := by
  show Real.sqrt 3 ^ 2 = 3
  exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)

theorem counter_anchor_satisfies_M7 :
    counter_anchor.sector2.a_Hodge ^ 2 =
      counter_anchor.sector2.a_Hodge + 1 := by
  show ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) / 2 + 1
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith [h5]

theorem counter_anchor_satisfies_M8 :
    counter_anchor.sector2.a_NP - counter_anchor.sector2.a_Hodge = 1/4 := by
  show ((1 + Real.sqrt 5) / 2 + 1/4) - ((1 + Real.sqrt 5) / 2) = 1/4; ring

theorem counter_anchor_satisfies_M9 :
    counter_anchor.sector2.a_QG ^ 2 = 2 * Real.pi := by
  show Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi
  exact Real.sq_sqrt (by positivity)

/-! ## §3 — counter_anchor satisfies positivity on irrational forced values -/

theorem counter_anchor_positivity :
    0 < counter_anchor.sector2.a_P ∧
    0 < counter_anchor.sector2.a_Hodge ∧
    0 < counter_anchor.sector2.a_QG := by
  refine ⟨?_, ?_, ?_⟩
  · show 0 < Real.sqrt 3
    exact Real.sqrt_pos.mpr (by norm_num)
  · show 0 < (1 + Real.sqrt 5) / 2
    have h5 : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    linarith
  · show 0 < Real.sqrt (2 * Real.pi)
    exact Real.sqrt_pos.mpr (by positivity)

/-! ## §4 — counter_anchor violates the Perelman anchor -/

theorem counter_anchor_violates_anchor :
    counter_anchor.sector1.a_Poincare ≠ 1 := by
  show (2 : ℝ) ≠ 1; norm_num

/-! ## §5 — counter_anchor satisfies UnifiedMinimalInvariants -/

theorem counter_anchor_satisfies_minimal_invariants :
    UnifiedMinimalInvariants counter_anchor where
  sector1_minimal :=
    { inv_RH_Poincare   := counter_anchor_satisfies_M1
      inv_YM_Poincare   := counter_anchor_satisfies_M2
      inv_BSD           := counter_anchor_satisfies_M3
      inv_NS_BSD        := counter_anchor_satisfies_M4
      inv_PvNP_Poincare := counter_anchor_satisfies_M5 }
  sector2_minimal :=
    { inv_P_sq_YM         := counter_anchor_satisfies_M6
      inv_Hodge_quad      := counter_anchor_satisfies_M7
      inv_NP_minus_Hodge  := counter_anchor_satisfies_M8
      inv_QG_sq_two_pi    := counter_anchor_satisfies_M9 }

/-! ## §6 — Capstone: the Perelman anchor is strictly necessary -/

/-- **★★★★★ PERELMAN ANCHOR IS STRICTLY NECESSARY ★★★★★** —
    `perelman_anchor_is_strictly_necessary`.

    There exists a unified α-assignment satisfying:
      * all 9 minimal cross-Millennium invariants
        (`UnifiedMinimalInvariants`);
      * positivity on the three irrational forced values
        (`α_P > 0`, `α_Hodge > 0`, `α_QG > 0`);

    but which violates the Perelman anchor `a_Poincare = 1`. Therefore
    the Perelman anchor cannot be dropped from the unified
    minimal substrate-rigidity hypothesis set without losing
    uniqueness of the α-skeleton.

    Together with:
    (a) `unified_alpha_skeleton_forced_by_minimal_invariants`
        (sufficiency: 9 invariants + anchor + 3 positivities force the
        unique α-skeleton);
    (b) `minimal_invariants_are_strictly_independent`
        (necessity of each minimal invariant);
    (c) `positivity_hypotheses_are_strictly_necessary`
        (necessity of each positivity hypothesis);

    this completes the strict-minimality story: every one of the 13
    hypotheses (9 invariants + 1 anchor + 3 positivities) is strictly
    necessary. The substrate-rigidity hypothesis set is COMPLETELY
    MINIMAL. -/
theorem perelman_anchor_is_strictly_necessary :
    ∃ u : UnifiedAlphaAssignment,
      UnifiedMinimalInvariants u ∧
      0 < u.sector2.a_P ∧
      0 < u.sector2.a_Hodge ∧
      0 < u.sector2.a_QG ∧
      u.sector1.a_Poincare ≠ 1 := by
  have ⟨hP, hH, hQG⟩ := counter_anchor_positivity
  exact ⟨counter_anchor,
         counter_anchor_satisfies_minimal_invariants,
         hP, hH, hQG,
         counter_anchor_violates_anchor⟩

end PF.Referee.MinimalSubstrateRigidityAnchorNecessity

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]` for every theorem.

#print axioms
  PF.Referee.MinimalSubstrateRigidityAnchorNecessity.counter_anchor_satisfies_minimal_invariants
#print axioms
  PF.Referee.MinimalSubstrateRigidityAnchorNecessity.counter_anchor_positivity
#print axioms
  PF.Referee.MinimalSubstrateRigidityAnchorNecessity.counter_anchor_violates_anchor
#print axioms
  PF.Referee.MinimalSubstrateRigidityAnchorNecessity.perelman_anchor_is_strictly_necessary
