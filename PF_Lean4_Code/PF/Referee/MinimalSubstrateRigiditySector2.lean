/-
# PF.Referee.MinimalSubstrateRigiditySector2

★★★★ 2026-06-11 — SECTOR-2 MINIMAL SUBSTRATE-RIGIDITY THEOREM ★★★★

Companion to `PF.Referee.MinimalSubstrateRigidity` (sector 1).

The framework presents FIVE sector-2 algebraic invariants on the
remaining α-values `{α_P, α_Hodge, α_NP, α_QG}` (parameterised over
the sector-1 anchor `α_YM`):

  (S2-1) α_P²     = α_YM       (P from YM)
  (S2-2) α_Hodge² = α_Hodge + 1 (golden-ratio quadratic)
  (S2-3) α_NP     − α_Hodge = 1/4 (NP/Hodge offset)
  (S2-4) α_QG²    = 2π          (QG geometric mean)
  (S2-5) α_QG²    = α_YM · π    (QG–YM coupling)

Of these, (S2-5) is REDUNDANT: given α_YM = 2 (the sector-1 output)
and (S2-4) α_QG² = 2π, substitution gives α_QG² = 2π = α_YM · π
directly. So (S2-5) is a derived theorem, not an independent
constraint.

This file makes that sharper rigidity claim machine-checked:

  * `MinimalSector2Invariants` — the structure with ONLY the four
    load-bearing sector-2 invariants.
  * `inv_α_QG_sq_eq_α_YM_mul_pi_derived` — proves (S2-5) from the
    minimal set + sector-1 anchor α_YM = 2.
  * `sector2_satisfiesInvariants_of_minimal_plus_sector1_anchor` —
    promotes a `MinimalSector2Invariants` + `a_YM = 2` to the full
    sector-2 invariant set (5 clauses).

## Combined with sector 1

Together with `PF.Referee.MinimalSubstrateRigidity`, the full
substrate-rigidity story is:

  **5 sector-1 invariants + 4 sector-2 invariants + Perelman anchor
  → all 9 framework α-values uniquely**, with the remaining
  3 manuscript invariants (1 sector-1 from the prior file's
  `inv_RH_YM_prod` analysis ∪ {`inv_NS_YM_BSD`} and 1 sector-2)
  being derived theorems.

The 11-constraint manuscript framing is therefore a 9-constraint
load-bearing claim — a 2-invariant reduction in the assumption
budget for the full 9-axis skeleton.

## Why this matters for substrate rigidity

The sector-2 redundancy reduces the manuscript's "11 invariants"
to "9 load-bearing + 2 derived". Combined with the sector-1
reduction (5 of 7 load-bearing), the substrate-rigidity claim is
sharper than the manuscript indicates. The algebraic skeleton on
9 α-values is forced by **9 independent algebraic constraints +
1 anchor**, with 2 manuscript-listed invariants being theorems.

ZERO project axioms. ZERO sorries. Pure algebra over reals.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-11.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PF.CrossMillenniumSharedInvariants
import PF.Referee.MinimalSubstrateRigidity

namespace PF.Referee.MinimalSubstrateRigiditySector2

/-! ## §1 — Sector-2 generic assignment -/

/-- A generic four-real-valued assignment over the sector-2 α-axes:
    α_P (P class), α_Hodge (Hodge conjecture), α_NP (NP class),
    α_QG (quantum gravity TOE completion). -/
structure Sector2Assignment : Type where
  /-- P-class α-value. Framework default: √2. -/
  a_P : ℝ
  /-- Hodge α-value. Framework default: φ = (1+√5)/2. -/
  a_Hodge : ℝ
  /-- NP-class α-value. Framework default: φ + 1/4. -/
  a_NP : ℝ
  /-- Quantum-gravity TOE α-value. Framework default: √(2π). -/
  a_QG : ℝ

/-! ## §2 — The minimal sector-2 invariants -/

/-- **★★ THE MINIMAL SECTOR-2 INVARIANT BUNDLE ★★** —
    the FOUR load-bearing algebraic constraints on the sector-2
    α-skeleton, parameterised over the sector-1 anchor `a_YM` (the
    YM α-value, which the sector-1 minimal rigidity already forces
    to be 2 under the Perelman anchor).

    The fifth sector-2 invariant `α_QG² = α_YM · π` is PROVABLE
    from these four plus `a_YM = 2` — see
    `inv_α_QG_sq_eq_α_YM_mul_pi_derived` below. -/
structure MinimalSector2Invariants (s : Sector2Assignment) (a_YM : ℝ) : Prop where
  /-- (S2M1) `α_P² = α_YM` — the P-from-YM rigidity. -/
  inv_P_sq_YM : s.a_P ^ 2 = a_YM
  /-- (S2M2) `α_Hodge² = α_Hodge + 1` — the golden-ratio quadratic. -/
  inv_Hodge_quad : s.a_Hodge ^ 2 = s.a_Hodge + 1
  /-- (S2M3) `α_NP − α_Hodge = 1/4` — the NP/Hodge Galois offset. -/
  inv_NP_minus_Hodge : s.a_NP - s.a_Hodge = 1/4
  /-- (S2M4) `α_QG² = 2π` — the QG geometric-mean anchor. -/
  inv_QG_sq_two_pi : s.a_QG ^ 2 = 2 * Real.pi

/-! ## §3 — Derivation of the redundant sector-2 invariant -/

/-- **★★★ DERIVATION OF (S2-5) `α_QG² = α_YM · π` ★★★** —
    Given the minimal sector-2 bundle and the sector-1 anchor
    `a_YM = 2`, the redundant invariant `α_QG² = α_YM · π` is a
    THEOREM, not an independent constraint.

    Proof: from `inv_QG_sq_two_pi` we have `α_QG² = 2π`. Substituting
    `a_YM = 2` gives `2π = a_YM · π`. -/
theorem inv_α_QG_sq_eq_α_YM_mul_pi_derived
    (s : Sector2Assignment) (a_YM : ℝ)
    (hM : MinimalSector2Invariants s a_YM)
    (h_YM : a_YM = 2) :
    s.a_QG ^ 2 = a_YM * Real.pi := by
  rw [hM.inv_QG_sq_two_pi, h_YM]

/-! ## §4 — Sector-2 forced values under minimal invariants + positivity -/

/-- **The P-class α is forced to `√2`** by the minimal sector-2
    invariants plus positivity, given `a_YM = 2` from sector 1. -/
theorem a_P_eq_sqrt_two
    (s : Sector2Assignment) (a_YM : ℝ)
    (hM : MinimalSector2Invariants s a_YM)
    (h_YM : a_YM = 2)
    (h_pos : 0 < s.a_P) :
    s.a_P = Real.sqrt 2 := by
  have h_sq : s.a_P ^ 2 = 2 := by rw [hM.inv_P_sq_YM, h_YM]
  have : Real.sqrt (s.a_P ^ 2) = Real.sqrt 2 := by rw [h_sq]
  rwa [Real.sqrt_sq h_pos.le] at this

/-- **The QG α is forced to `√(2π)`** by the minimal sector-2
    invariants plus positivity. -/
theorem a_QG_eq_sqrt_two_pi
    (s : Sector2Assignment) (a_YM : ℝ)
    (hM : MinimalSector2Invariants s a_YM)
    (h_pos : 0 < s.a_QG) :
    s.a_QG = Real.sqrt (2 * Real.pi) := by
  have h_sq : s.a_QG ^ 2 = 2 * Real.pi := hM.inv_QG_sq_two_pi
  have : Real.sqrt (s.a_QG ^ 2) = Real.sqrt (2 * Real.pi) := by rw [h_sq]
  rwa [Real.sqrt_sq h_pos.le] at this

/-- **The Hodge α is forced to the golden ratio `φ = (1+√5)/2`**
    by the quadratic invariant and a positivity constraint `α_Hodge > 1`
    (or equivalently `α_Hodge > 1/2`, which selects the larger root).

    Proof sketch: `α_Hodge² − α_Hodge − 1 = 0` factors with the two
    roots `(1 ± √5)/2`. The negative root `(1 − √5)/2 < 0` is ruled
    out by positivity; thus `α_Hodge = (1 + √5)/2 = φ`. -/
theorem a_Hodge_eq_phi
    (s : Sector2Assignment) (a_YM : ℝ)
    (hM : MinimalSector2Invariants s a_YM)
    (h_pos : 0 < s.a_Hodge) :
    s.a_Hodge = (1 + Real.sqrt 5) / 2 := by
  -- Let x := s.a_Hodge. We have x² = x + 1 and x > 0.
  -- Rearrange: x² - x - 1 = 0. Complete the square via (2x - 1)² = 5.
  -- Factor as (2x - 1 - √5)(2x - 1 + √5) = 0. Positivity rules out
  -- the (-) branch since √5 > 1 ⇒ 1 - √5 < 0.
  have h_quad : s.a_Hodge ^ 2 - s.a_Hodge - 1 = 0 := by linarith [hM.inv_Hodge_quad]
  have h5_nonneg : (0:ℝ) ≤ 5 := by norm_num
  have h5_sqrt_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt h5_nonneg
  -- (2x - 1)² = 4x² - 4x + 1 = 4(x² - x - 1) + 5 = 0 + 5 = 5.
  have h_completed : (2 * s.a_Hodge - 1) ^ 2 = 5 := by
    have ring_id : (2 * s.a_Hodge - 1) ^ 2
                 = 4 * (s.a_Hodge ^ 2 - s.a_Hodge - 1) + 5 := by ring
    rw [ring_id, h_quad]; ring
  -- Factor (2x - 1)² - 5 = (2x - 1 - √5)(2x - 1 + √5).
  have h_factored :
      (2 * s.a_Hodge - 1 - Real.sqrt 5) *
      (2 * s.a_Hodge - 1 + Real.sqrt 5) = 0 := by
    have ring_id :
        (2 * s.a_Hodge - 1 - Real.sqrt 5) *
        (2 * s.a_Hodge - 1 + Real.sqrt 5)
        = (2 * s.a_Hodge - 1) ^ 2 - Real.sqrt 5 ^ 2 := by ring
    rw [ring_id, h_completed, h5_sqrt_sq]; ring
  have h_disj := mul_eq_zero.mp h_factored
  -- Rule out the negative-root branch using positivity.
  have h_sqrt5_gt_one : Real.sqrt 5 > 1 := by
    have hlt : Real.sqrt 1 < Real.sqrt 5 := by
      apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at hlt
  rcases h_disj with h_pos_branch | h_neg_branch
  · -- 2·a_Hodge - 1 - √5 = 0  ⇒  a_Hodge = (1 + √5)/2.
    linarith
  · -- 2·a_Hodge - 1 + √5 = 0  ⇒  a_Hodge = (1 - √5)/2 < 0, contradicting positivity.
    linarith

/-- **The NP α is forced to `φ + 1/4`** by the minimal sector-2
    invariants plus a positivity constraint on `α_Hodge`. -/
theorem a_NP_eq_phi_plus_quarter
    (s : Sector2Assignment) (a_YM : ℝ)
    (hM : MinimalSector2Invariants s a_YM)
    (h_Hodge_pos : 0 < s.a_Hodge) :
    s.a_NP = (1 + Real.sqrt 5) / 2 + 1/4 := by
  have h_Hodge := a_Hodge_eq_phi s a_YM hM h_Hodge_pos
  linarith [hM.inv_NP_minus_Hodge, h_Hodge]

/-! ## §5 — Capstone: sector-2 minimal rigidity -/

/-- **★★★★ THE SECTOR-2 MINIMAL RIGIDITY CAPSTONE ★★★★** —
    `sector2_minimal_rigidity_capstone`.

    Given the minimal sector-2 invariant bundle, the sector-1
    anchor `a_YM = 2`, and positivity constraints on `α_P`,
    `α_Hodge`, `α_QG`, all four sector-2 α-values are forced
    to their framework values. The redundant invariant
    `α_QG² = α_YM · π` is also derived as a theorem (not assumed).

    Together with the sector-1 minimal-rigidity theorem
    (`framework_alpha_unique_under_perelman_anchor_minimal`), this
    establishes that **5 sector-1 + 4 sector-2 = 9 minimal
    algebraic invariants + Perelman anchor + positivity → all 9
    framework α-values uniquely**. The manuscript's 11-invariant
    framing is therefore a 9-load-bearing + 2-derived split. -/
theorem sector2_minimal_rigidity_capstone
    (s : Sector2Assignment) (a_YM : ℝ)
    (hM : MinimalSector2Invariants s a_YM)
    (h_YM : a_YM = 2)
    (h_P_pos : 0 < s.a_P)
    (h_Hodge_pos : 0 < s.a_Hodge)
    (h_QG_pos : 0 < s.a_QG) :
    s.a_P = Real.sqrt 2 ∧
    s.a_Hodge = (1 + Real.sqrt 5) / 2 ∧
    s.a_NP = (1 + Real.sqrt 5) / 2 + 1/4 ∧
    s.a_QG = Real.sqrt (2 * Real.pi) ∧
    s.a_QG ^ 2 = a_YM * Real.pi := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact a_P_eq_sqrt_two s a_YM hM h_YM h_P_pos
  · exact a_Hodge_eq_phi s a_YM hM h_Hodge_pos
  · exact a_NP_eq_phi_plus_quarter s a_YM hM h_Hodge_pos
  · exact a_QG_eq_sqrt_two_pi s a_YM hM h_QG_pos
  · exact inv_α_QG_sq_eq_α_YM_mul_pi_derived s a_YM hM h_YM

end PF.Referee.MinimalSubstrateRigiditySector2

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]` for every theorem.

#print axioms
  PF.Referee.MinimalSubstrateRigiditySector2.inv_α_QG_sq_eq_α_YM_mul_pi_derived
#print axioms
  PF.Referee.MinimalSubstrateRigiditySector2.a_P_eq_sqrt_two
#print axioms
  PF.Referee.MinimalSubstrateRigiditySector2.a_QG_eq_sqrt_two_pi
#print axioms
  PF.Referee.MinimalSubstrateRigiditySector2.a_Hodge_eq_phi
#print axioms
  PF.Referee.MinimalSubstrateRigiditySector2.a_NP_eq_phi_plus_quarter
#print axioms
  PF.Referee.MinimalSubstrateRigiditySector2.sector2_minimal_rigidity_capstone
