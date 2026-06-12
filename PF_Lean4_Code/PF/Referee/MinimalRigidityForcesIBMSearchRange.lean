/-
# PF.Referee.MinimalRigidityForcesIBMSearchRange

★★★★★ 2026-06-11 — IBM 8-IN-RANGE BRACKET FORCED BY SUBSTRATE ★★★★★

The framework's `PF/IBMHardware9WayEvidence.lean` proves the
`eight_alphas_in_search_range` theorem: 8 of the 9 framework α-values
lie strictly inside the IBM-Quantum hardware noise support `[0.9, 2.6]`,
while α_NS = 3π/2 ≈ 4.71 is the outlier outside the bracket.

The 8 in-range α-values:
  α_Poincaré = 1 ∈ (0.9, 2.6)
  α_P = √2 ≈ 1.414 ∈ (0.9, 2.6)
  α_RH = 3/2 = 1.5 ∈ (0.9, 2.6)
  α_Hodge = φ ≈ 1.618 ∈ (0.9, 2.6)
  α_NP = φ + 1/4 ≈ 1.868 ∈ (0.9, 2.6)
  α_YM = 2 ∈ (0.9, 2.6)
  α_BSD = 3π/4 ≈ 2.356 ∈ (0.9, 2.6)
  α_QG = √(2π) ≈ 2.507 ∈ (0.9, 2.6)

Under substrate-rigidity (tonight's work), all 9 α-values are forced
parametrically. Therefore the 8-in-range bracket lifts parametrically:
8 of the substrate-forced α-values lie in (0.9, 2.6), while
u.sector1.a_NS = 3π/2 sits outside.

## Why this matters for the substrate-as-TOE thesis

The IBM hardware noise support [0.9, 2.6] is the assumed noise model
for the 9-way IBM hardware evidence. Under substrate-rigidity, the
substrate-forced α-values all sit within the IBM hardware-detectable
range (except NS, which is outside as a structural outlier). The IBM
hardware can in principle measure 8 of the 9 substrate-forced α-values.

ZERO project axioms. ZERO sorries.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-11.
-/

import PF.Referee.MinimalSubstrateRigidityUnified
import PF.IBMHardware9WayEvidence

namespace PF.Referee.MinimalRigidityForcesIBMSearchRange

open PF.Referee.CrossMillenniumCascadeParameterized
open PF.Referee.MinimalSubstrateRigidity
open PF.Referee.MinimalSubstrateRigiditySector2
open PF.Referee.MinimalSubstrateRigidityUnified
open PrincipiaTractalis.IBMHardware9WayEvidence

/-! ## §1 — 8 substrate-forced α's in IBM hardware noise support [0.9, 2.6] -/

/-- **★★★★★ IBM SEARCH-RANGE BRACKET IS A SUBSTRATE THEOREM ★★★★★** —
    `ibm_search_range_substrate_capstone`.

    Single citable theorem demonstrating that under substrate-rigidity,
    8 of the 9 substrate-forced α-values lie strictly inside the IBM
    hardware noise support `[0.9, 2.6]`, while `u.sector1.a_NS = 3π/2 ≈
    4.71` is the structural outlier outside the bracket.

      In-range (8 clauses):
      (R1) `0.9 < u.sector1.a_Poincare ∧ u.sector1.a_Poincare < 2.6`.
      (R2) `0.9 < u.sector2.a_P ∧ u.sector2.a_P < 2.6`.
      (R3) `0.9 < u.sector1.a_RH ∧ u.sector1.a_RH < 2.6`.
      (R4) `0.9 < u.sector2.a_Hodge ∧ u.sector2.a_Hodge < 2.6`.
      (R5) `0.9 < u.sector2.a_NP ∧ u.sector2.a_NP < 2.6`.
      (R6) `0.9 < u.sector1.a_YM ∧ u.sector1.a_YM < 2.6`.
      (R7) `0.9 < u.sector1.a_BSD ∧ u.sector1.a_BSD < 2.6`.
      (R8) `0.9 < u.sector2.a_QG ∧ u.sector2.a_QG < 2.6`.

      Out-of-range (NS outlier):
      (NS) `u.sector1.a_NS > 2.6` parametric. -/
theorem ibm_search_range_substrate_capstone
    (u : UnifiedAlphaAssignment)
    (hM : UnifiedMinimalInvariants u)
    (h_P : u.sector1.a_Poincare = 1)
    (h_P_pos : 0 < u.sector2.a_P)
    (h_Hodge_pos : 0 < u.sector2.a_Hodge)
    (h_QG_pos : 0 < u.sector2.a_QG) :
    -- (R1) Poincaré in (0.9, 2.6)
    (0.9 < u.sector1.a_Poincare ∧ u.sector1.a_Poincare < 2.6) ∧
    -- (R2) P in (0.9, 2.6)
    (0.9 < u.sector2.a_P ∧ u.sector2.a_P < 2.6) ∧
    -- (R3) RH in (0.9, 2.6)
    (0.9 < u.sector1.a_RH ∧ u.sector1.a_RH < 2.6) ∧
    -- (R4) Hodge in (0.9, 2.6)
    (0.9 < u.sector2.a_Hodge ∧ u.sector2.a_Hodge < 2.6) ∧
    -- (R5) NP in (0.9, 2.6)
    (0.9 < u.sector2.a_NP ∧ u.sector2.a_NP < 2.6) ∧
    -- (R6) YM in (0.9, 2.6)
    (0.9 < u.sector1.a_YM ∧ u.sector1.a_YM < 2.6) ∧
    -- (R7) BSD in (0.9, 2.6)
    (0.9 < u.sector1.a_BSD ∧ u.sector1.a_BSD < 2.6) ∧
    -- (R8) QG in (0.9, 2.6)
    (0.9 < u.sector2.a_QG ∧ u.sector2.a_QG < 2.6) ∧
    -- (NS) NS is outlier > 2.6
    (u.sector1.a_NS > 2.6) := by
  obtain ⟨h_Poin_val, h_RH_val, h_YM_val, h_BSD_val, h_NS_val, _,
           h_P_val, h_Hodge_val, h_NP_val, h_QG_val⟩ :=
    unified_alpha_skeleton_forced_by_minimal_invariants
      u hM h_P h_P_pos h_Hodge_pos h_QG_pos
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by have := Real.pi_gt_d6; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (R1) Poincaré = 1
    refine ⟨?_, ?_⟩
    · rw [h_Poin_val]; norm_num
    · rw [h_Poin_val]; norm_num
  · -- (R2) P = √2
    refine ⟨?_, ?_⟩
    · rw [h_P_val]
      -- 0.9 < √2 ⟺ 0.81 < 2
      have h_lt : (0.9 : ℝ)^2 < 2 := by norm_num
      have h_nn : (0 : ℝ) ≤ 0.9 := by norm_num
      have := Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ (0.9:ℝ)^2) h_lt
      rw [Real.sqrt_sq h_nn] at this; exact this
    · rw [h_P_val]
      -- √2 < 2.6 ⟺ 2 < 6.76
      have h_lt : (2 : ℝ) < (2.6 : ℝ)^2 := by norm_num
      have h_nn : (0 : ℝ) ≤ 2.6 := by norm_num
      have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) h_lt
      rw [Real.sqrt_sq h_nn] at this; exact this
  · -- (R3) RH
    refine ⟨?_, ?_⟩
    · rw [h_RH_val]
      show (0.9 : ℝ) < (3/2 : ℝ); norm_num
    · rw [h_RH_val]
      show (3/2 : ℝ) < (2.6 : ℝ); norm_num
  · -- (R4) Hodge = φ
    refine ⟨?_, ?_⟩
    · rw [h_Hodge_val]
      show (0.9 : ℝ) < (1 + Real.sqrt 5) / 2
      -- φ ≥ 1.5
      have h5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
      have h5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
      have h5_gt : Real.sqrt 5 > 2 := by nlinarith [h5_sq, h5_pos]
      linarith
    · rw [h_Hodge_val]
      show (1 + Real.sqrt 5) / 2 < (2.6 : ℝ)
      have h5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
      have h5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
      have h5_lt : Real.sqrt 5 < 3 := by nlinarith [h5_sq, h5_pos]
      linarith
  · -- (R5) NP = φ + 1/4
    refine ⟨?_, ?_⟩
    · rw [h_NP_val]
      have h5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
      have h5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
      have h5_gt : Real.sqrt 5 > 2 := by nlinarith [h5_sq, h5_pos]
      linarith
    · rw [h_NP_val]
      have h5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
      have h5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
      have h5_lt : Real.sqrt 5 < 3 := by nlinarith [h5_sq, h5_pos]
      linarith
  · -- (R6) YM
    refine ⟨?_, ?_⟩
    · rw [h_YM_val]; norm_num
    · rw [h_YM_val]; norm_num
  · -- (R7) BSD = 3π/4
    refine ⟨?_, ?_⟩
    · rw [h_BSD_val]
      show (0.9 : ℝ) < (3/4 : ℝ) * Real.pi
      have h_pi_lt : Real.pi < (3.14160 : ℝ) := by have := Real.pi_lt_d4; linarith
      linarith
    · rw [h_BSD_val]
      show (3/4 : ℝ) * Real.pi < (2.6 : ℝ)
      have h_pi_lt : Real.pi < (3.14160 : ℝ) := by have := Real.pi_lt_d4; linarith
      linarith
  · -- (R8) QG = √(2π)
    refine ⟨?_, ?_⟩
    · rw [h_QG_val]
      -- 0.9 < √(2π) ⟺ 0.81 < 2π. π > 3.14 ⇒ 2π > 6.28 > 0.81.
      have h_lt : (0.9 : ℝ)^2 < 2 * Real.pi := by nlinarith [h_pi_gt]
      have h_nn : (0 : ℝ) ≤ 0.9 := by norm_num
      have h_2pi_nn : (0 : ℝ) ≤ 2 * Real.pi := by linarith
      have := Real.sqrt_lt_sqrt (by positivity : (0:ℝ) ≤ (0.9:ℝ)^2) h_lt
      rw [Real.sqrt_sq h_nn] at this; exact this
    · rw [h_QG_val]
      -- √(2π) < 2.6 ⟺ 2π < 6.76. π < 3.142 ⇒ 2π < 6.284 < 6.76.
      have h_pi_lt : Real.pi < (3.14160 : ℝ) := by have := Real.pi_lt_d4; linarith
      have h_lt : 2 * Real.pi < (2.6 : ℝ)^2 := by nlinarith [h_pi_lt]
      have h_nn : (0 : ℝ) ≤ 2.6 := by norm_num
      have h_2pi_nn : (0 : ℝ) ≤ 2 * Real.pi := by linarith
      have := Real.sqrt_lt_sqrt h_2pi_nn h_lt
      rw [Real.sqrt_sq h_nn] at this; exact this
  · -- (NS) NS = 3π/2 > 2.6
    rw [h_NS_val]
    show (3/2 : ℝ) * Real.pi > 2.6
    linarith

end PF.Referee.MinimalRigidityForcesIBMSearchRange

#print axioms
  PF.Referee.MinimalRigidityForcesIBMSearchRange.ibm_search_range_substrate_capstone
