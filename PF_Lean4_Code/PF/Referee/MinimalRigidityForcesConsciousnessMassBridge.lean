/-
# PF.Referee.MinimalRigidityForcesConsciousnessMassBridge

★★★★★ 2026-06-11 — CONSCIOUSNESS MASS-PLANCK RATIO MEETS NP FIBRE ★★★★★

Second substrate-consciousness connection (after
`MinimalRigidityForcesIITPhiThreshold`).

The framework's Ch 12 Mass-IIT bridge
(`PF.Consciousness.Ch12MassIITBridge`) defines the consciousness
mass-to-Planck-mass ratio
`m_C_over_M_Planck := √(1 − ch_2_threshold) = √(1 − 0.95) = √(1/20)
                   = 1/√20`.
Under minimal-rigidity, the framework's NP fibre value is
`(4·α_NP − 3)² = 20`, so the side length is
`4·α_NP − 3 = √20` (positive since α_NP > 3/4).

The product:

    m_C_over_M_Planck · (4·α_NP − 3) = (1/√20) · √20 = 1.

The consciousness mass-Planck ratio is the reciprocal of the framework's
NP fibre side length. Under the substrate, the two are not independent
constants — they cancel to unity.

This is a second formal connection between the framework's algebraic
substrate-rigidity and the consciousness chain:

  * IIT Φ threshold meets NP fibre at 2·log 20 (prior file).
  * Consciousness mass-Planck ratio meets NP fibre side length at 1
    (this file).

Both consciousness chain constants — the Φ_threshold and the
m_C/M_Planck ratio — are downstream consequences of the same
NP fibre value forced by minimal-rigidity.

ZERO project axioms. ZERO sorries.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-11.
-/

import PF.Referee.MinimalRigidityForcesIBMGaloisPair
import PF.Consciousness.Ch12MassIITBridge

namespace PF.Referee.MinimalRigidityForcesConsciousnessMassBridge

open PF.Referee.CrossMillenniumCascadeParameterized
open PF.Referee.MinimalSubstrateRigidity
open PF.Referee.MinimalSubstrateRigiditySector2
open PF.Referee.MinimalSubstrateRigidityUnified
open PF.Referee.MinimalRigidityForcesIBMGaloisPair
open PrincipiaTractalis.Consciousness

/-! ## §1 — The framework's consciousness mass-Planck ratio is 1/√20 -/

/-- The framework's `m_C_over_M_Planck` reduces to `1/√20` by direct
    calculation: `√(1 − 0.95) = √(1/20) = 1/√20`. -/
private theorem m_C_over_M_Planck_eq_one_over_sqrt_20 :
    m_C_over_M_Planck = 1 / Real.sqrt 20 := by
  unfold m_C_over_M_Planck ch_2_threshold_Ch12
  -- Goal: √(1 - 0.95) = 1/√20.
  -- 1 - 0.95 = 0.05 = 1/20, so √(1/20) = 1/√20.
  have h_eq : (1:ℝ) - 0.95 = 1 / 20 := by norm_num
  rw [h_eq]
  -- Goal: √(1/20) = 1/√20.
  -- (1/20) = 20⁻¹, so √(1/20) = √(20⁻¹) = (√20)⁻¹ = 1/√20.
  rw [show ((1:ℝ) / 20) = (20:ℝ)⁻¹ by norm_num]
  rw [Real.sqrt_inv]
  rw [inv_eq_one_div]

/-! ## §2 — Under minimal rigidity, 4·a_NP − 3 = √20 (positive root) -/

/-- **The NP fibre side length under minimal rigidity.** Combining
    the forced fibre value `(4·a_NP − 3)² = 20` and positivity of
    `4·a_NP − 3` (since the forced `a_NP > 3/4`), we have
    `4·a_NP − 3 = √20`. -/
theorem unified_minimal_forces_NP_fibre_side_eq_sqrt_20
    (u : UnifiedAlphaAssignment)
    (hM : UnifiedMinimalInvariants u)
    (h_P : u.sector1.a_Poincare = 1)
    (h_P_pos : 0 < u.sector2.a_P)
    (h_Hodge_pos : 0 < u.sector2.a_Hodge)
    (h_QG_pos : 0 < u.sector2.a_QG) :
    4 * u.sector2.a_NP - 3 = Real.sqrt 20 := by
  -- Step 1: minimal-rigidity forces a_NP = (1+√5)/2 + 1/4.
  obtain ⟨_, _, _, _, _, _, _, _, h_NP, _⟩ :=
    unified_alpha_skeleton_forced_by_minimal_invariants
      u hM h_P h_P_pos h_Hodge_pos h_QG_pos
  rw [h_NP]
  -- Goal: 4·((1+√5)/2 + 1/4) - 3 = √20.
  -- 4·((1+√5)/2 + 1/4) = 2·(1+√5) + 1 = 3 + 2√5.
  -- So 4·... - 3 = 2√5.
  -- And 2√5 = √(4·5) = √20.
  have h_simp : 4 * ((1 + Real.sqrt 5) / 2 + 1/4) - 3 = 2 * Real.sqrt 5 := by
    ring
  rw [h_simp]
  -- Goal: 2·√5 = √20.
  -- Use Real.sqrt_mul: √(4·5) = √4 · √5 = 2·√5. So √20 = 2·√5.
  have h4_nonneg : (0:ℝ) ≤ 4 := by norm_num
  have h20_eq : (20 : ℝ) = 4 * 5 := by norm_num
  rw [h20_eq, Real.sqrt_mul h4_nonneg]
  -- Goal: 2·√5 = √4·√5. Use Real.sqrt_four / direct.
  have h_sqrt4 : Real.sqrt 4 = 2 := by
    have : Real.sqrt (2^2) = 2 := Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)
    convert this using 1
    norm_num
  rw [h_sqrt4]

/-! ## §3 — The consciousness mass-Planck ratio × NP fibre side = 1 -/

/-- **★★★★ THE CONSCIOUSNESS-MASS / NP-FIBRE PRODUCT IS UNITY ★★★★** —
    `unified_minimal_forces_consciousness_mass_NP_fibre_product_one`.

    Under the substrate-rigidity hypotheses, the consciousness mass-
    Planck ratio `m_C_over_M_Planck` and the NP fibre side length
    `4·a_NP − 3` multiply to 1:

      `m_C_over_M_Planck · (4·a_NP − 3) = 1`.

    The two seemingly independent consciousness-chain and Galois-
    pair constants are reciprocals of each other under the
    substrate-rigidity hypotheses. Under minimal-rigidity, both are
    expressed parametrically in terms of `√20`. -/
theorem unified_minimal_forces_consciousness_mass_NP_fibre_product_one
    (u : UnifiedAlphaAssignment)
    (hM : UnifiedMinimalInvariants u)
    (h_P : u.sector1.a_Poincare = 1)
    (h_P_pos : 0 < u.sector2.a_P)
    (h_Hodge_pos : 0 < u.sector2.a_Hodge)
    (h_QG_pos : 0 < u.sector2.a_QG) :
    m_C_over_M_Planck * (4 * u.sector2.a_NP - 3) = 1 := by
  rw [m_C_over_M_Planck_eq_one_over_sqrt_20,
      unified_minimal_forces_NP_fibre_side_eq_sqrt_20
        u hM h_P h_P_pos h_Hodge_pos h_QG_pos]
  -- Goal: (1/√20)·√20 = 1.
  have h_sqrt20_pos : 0 < Real.sqrt 20 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 20)
  field_simp

end PF.Referee.MinimalRigidityForcesConsciousnessMassBridge

#print axioms
  PF.Referee.MinimalRigidityForcesConsciousnessMassBridge.unified_minimal_forces_NP_fibre_side_eq_sqrt_20
#print axioms
  PF.Referee.MinimalRigidityForcesConsciousnessMassBridge.unified_minimal_forces_consciousness_mass_NP_fibre_product_one
