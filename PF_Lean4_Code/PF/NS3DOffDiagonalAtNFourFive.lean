/-
# NS3DOffDiagonalAtNFourFive: extend the OFF-DIAGONAL vortex-stretching
#   bound of Wave 25 (NS3DOffDiagonalAtNTwoThree, n ∈ {0,1,2,3}) to
#   n ∈ {4, 5}, and bundle the combined diagonal + off-diagonal capstone.

## Honest scope (READ FIRST)

This file is a Wave 26 follow-on to `NS3DOffDiagonalAtNTwoThree`.
Wave 25 (commit `bf796f3`) discharged the off-diagonal vortex-stretching
bound `‖VortexStretching3DOffDiagonal ω o‖ ≤ K_T · ‖ω‖ · ‖o‖` for the
Galerkin truncations `n ∈ {0, 1, 2, 3}` with `K_off = 2`.

This file:
  (1) Reuses the same `OffDiagonalGradient3DState` 6-tuple type and the
      same `VortexStretching3DOffDiagonal` operator from Wave 24 — only
      the Galerkin index changes (`n = 4`, then `n = 5`).
  (2) Extends the reusable single-component off-diagonal bound to `n = 4`
      and `n = 5` via the Hadamard bounds `hadamard_norm_le_n4`
      (4D Cauchy-Schwarz) and `hadamard_norm_le_n5` (5D Cauchy-Schwarz),
      both from `NS3DLocalRegularityAtNEqFourFive.lean`.
  (3) Proves `local_vortex_stretching_bound_off_diagonal_at_n_eq_four`
      and `local_vortex_stretching_bound_off_diagonal_at_n_eq_five`
      axiom-free with `K_off = 2`.
  (4) Bundles the combined diagonal + off-diagonal capstone
      `local_vortex_stretching_bound_off_diagonal_at_n_le_five` covering
      off-diagonal at `n ∈ {0, 1, 2, 3, 4, 5}` and diagonal at
      `n ∈ {0, 1, 2, 3, 4, 5}`.

## What this does NOT do

This is STILL the local-in-time (Leray-Hopf 1934) Galerkin shadow. It is
NOT a Clay Millennium discharge. The bound holds at FIXED truncation
indices `n ∈ {0, 1, 2, 3, 4, 5}` with `K_off = 2` independent of `T` but
the operator is the truncated Galerkin shadow, not the full PDE-level
`(ω·∇)u`. The Clay openness lives in
`VortexStretchingBoundedHypothesis`.

What this DOES do: closes the gap between off-diagonal (Wave 25, n ≤ 3)
and diagonal (Wave 23, n ≤ 5) coverage on the Galerkin shadow.

ZERO project axioms. ZERO `sorry`s.

Author: Pablo Cohen (formalization, Wave 26 off-diagonal extension to n∈{4,5})
Date: 2026-05-25
-/

import PF.NS3DOffDiagonalAtNTwoThree
import PF.NS3DLocalRegularityAtNEqFourFive
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin

namespace PrincipiaTractalis.NS3DOffDiagonalAtNFourFive

open PrincipiaTractalis.NS3DVortexStretchingObstruction
open PrincipiaTractalis.NS3DLocalRegularityViaBKM
open PrincipiaTractalis.NS3DLocalRegularityAtNGeqOneRetry
open PrincipiaTractalis.NS3DLocalRegularityAtNEqThree
open PrincipiaTractalis.NS3DLocalRegularityAtNEqFourFive
open PrincipiaTractalis.NS3DOffDiagonalVortexStretching
open PrincipiaTractalis.NS3DOffDiagonalAtNTwoThree
open Real

/-! ## §1 — Reusable single-component off-diagonal bound at `n = 4` and `n = 5`

These mirror `offdiag_one_component_bound_n3` from Wave 25 but use the
n=4 and n=5 Hadamard bounds (4D and 5D Cauchy-Schwarz). -/

/-- Reusable single-component off-diagonal bound at `n = 4`. -/
lemma offdiag_one_component_bound_n4
    (a b c d : EuclideanSpace ℝ (Fin 4)) :
    ‖hadamardSum a b c d‖ ≤ ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ := by
  refine le_trans (norm_hadamard_sum_le a b c d) ?_
  exact add_le_add (hadamard_norm_le_n4 _ _) (hadamard_norm_le_n4 _ _)

/-- Reusable single-component off-diagonal bound at `n = 5`. -/
lemma offdiag_one_component_bound_n5
    (a b c d : EuclideanSpace ℝ (Fin 5)) :
    ‖hadamardSum a b c d‖ ≤ ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ := by
  refine le_trans (norm_hadamard_sum_le a b c d) ?_
  exact add_le_add (hadamard_norm_le_n5 _ _) (hadamard_norm_le_n5 _ _)

/-! ## §2 — Two-slot sum bound at `n = 4` and `n = 5` -/

/-- For two component slots from `(ω, o)` at `n = 4`, the off-diagonal sum
    bound `‖hadamardSum ωₐ oₐ ωᵦ oᵦ‖ ≤ 2·‖ω‖·‖o‖`. -/
lemma offdiag_sum_bound_n4
    (ω : Vorticity3DState 4) (o : OffDiagonalGradient3DState 4)
    (ωa ωb : EuclideanSpace ℝ (Fin 4))
    (oa ob : EuclideanSpace ℝ (Fin 4))
    (hωa : ‖ωa‖ ≤ ‖ω‖) (hωb : ‖ωb‖ ≤ ‖ω‖)
    (hoa : ‖oa‖ ≤ ‖o‖) (hob : ‖ob‖ ≤ ‖o‖) :
    ‖hadamardSum ωa oa ωb ob‖ ≤ 2 * ‖ω‖ * ‖o‖ := by
  have nω : 0 ≤ ‖ω‖ := norm_nonneg _
  have key := offdiag_one_component_bound_n4 ωa oa ωb ob
  have c1 : ‖ωa‖ * ‖oa‖ ≤ ‖ω‖ * ‖o‖ :=
    mul_le_mul hωa hoa (norm_nonneg _) nω
  have c2 : ‖ωb‖ * ‖ob‖ ≤ ‖ω‖ * ‖o‖ :=
    mul_le_mul hωb hob (norm_nonneg _) nω
  linarith [key, c1, c2]

/-- For two component slots from `(ω, o)` at `n = 5`, the off-diagonal sum
    bound `‖hadamardSum ωₐ oₐ ωᵦ oᵦ‖ ≤ 2·‖ω‖·‖o‖`. -/
lemma offdiag_sum_bound_n5
    (ω : Vorticity3DState 5) (o : OffDiagonalGradient3DState 5)
    (ωa ωb : EuclideanSpace ℝ (Fin 5))
    (oa ob : EuclideanSpace ℝ (Fin 5))
    (hωa : ‖ωa‖ ≤ ‖ω‖) (hωb : ‖ωb‖ ≤ ‖ω‖)
    (hoa : ‖oa‖ ≤ ‖o‖) (hob : ‖ob‖ ≤ ‖o‖) :
    ‖hadamardSum ωa oa ωb ob‖ ≤ 2 * ‖ω‖ * ‖o‖ := by
  have nω : 0 ≤ ‖ω‖ := norm_nonneg _
  have key := offdiag_one_component_bound_n5 ωa oa ωb ob
  have c1 : ‖ωa‖ * ‖oa‖ ≤ ‖ω‖ * ‖o‖ :=
    mul_le_mul hωa hoa (norm_nonneg _) nω
  have c2 : ‖ωb‖ * ‖ob‖ ≤ ‖ω‖ * ‖o‖ :=
    mul_le_mul hωb hob (norm_nonneg _) nω
  linarith [key, c1, c2]

/-! ## §3 — Off-diagonal bound at `n = 4` and `n = 5` (axiom-free) -/

/-- **At `n = 4`, the off-diagonal bound with `K_T = 2`** (axiom-free).
    Each of the three triple components is a `hadamardSum` of two products;
    triangle inequality + Hadamard bound at `n=4` (4D Cauchy-Schwarz)
    gives the factor `2`. -/
theorem local_vortex_stretching_bound_off_diagonal_at_n_eq_four
    (T : ℝ) (_hT : 0 < T) :
    LocalVortexStretchingBoundOffDiagonal T 4 := by
  refine ⟨2, by norm_num, ?_⟩
  intro ω o
  unfold VortexStretching3DOffDiagonal; simp only
  rw [prod_triple_norm_eq]
  obtain ⟨hω0, hω1, hω2⟩ := three_tuple_components_le ω
  obtain ⟨ho01, ho02, ho10, ho12, ho20, ho21⟩ := six_tuple_components_le o
  -- Component i = 0: hadamardSum ω.2.1 o.2.2.1 ω.2.2 o.2.2.2.2.1
  have b0 := offdiag_sum_bound_n4 ω o ω.2.1 ω.2.2 o.2.2.1 o.2.2.2.2.1
    hω1 hω2 ho10 ho20
  -- Component i = 1: hadamardSum ω.1 o.1 ω.2.2 o.2.2.2.2.2
  have b1 := offdiag_sum_bound_n4 ω o ω.1 ω.2.2 o.1 o.2.2.2.2.2
    hω0 hω2 ho01 ho21
  -- Component i = 2: hadamardSum ω.1 o.2.1 ω.2.1 o.2.2.2.1
  have b2 := offdiag_sum_bound_n4 ω o ω.1 ω.2.1 o.2.1 o.2.2.2.1
    hω0 hω1 ho02 ho12
  exact max_le b0 (max_le b1 b2)

/-- **At `n = 5`, the off-diagonal bound with `K_T = 2`** (axiom-free).
    Same structure as `_at_n_eq_four`, using `hadamard_norm_le_n5`
    (5D Cauchy-Schwarz). -/
theorem local_vortex_stretching_bound_off_diagonal_at_n_eq_five
    (T : ℝ) (_hT : 0 < T) :
    LocalVortexStretchingBoundOffDiagonal T 5 := by
  refine ⟨2, by norm_num, ?_⟩
  intro ω o
  unfold VortexStretching3DOffDiagonal; simp only
  rw [prod_triple_norm_eq]
  obtain ⟨hω0, hω1, hω2⟩ := three_tuple_components_le ω
  obtain ⟨ho01, ho02, ho10, ho12, ho20, ho21⟩ := six_tuple_components_le o
  have b0 := offdiag_sum_bound_n5 ω o ω.2.1 ω.2.2 o.2.2.1 o.2.2.2.2.1
    hω1 hω2 ho10 ho20
  have b1 := offdiag_sum_bound_n5 ω o ω.1 ω.2.2 o.1 o.2.2.2.2.2
    hω0 hω2 ho01 ho21
  have b2 := offdiag_sum_bound_n5 ω o ω.1 ω.2.1 o.2.1 o.2.2.2.1
    hω0 hω1 ho02 ho12
  exact max_le b0 (max_le b1 b2)

/-! ## §4 — Combined capstone at `n ≤ 5`

Extends Wave 25's `_at_n_le_three` by adding the off-diagonal coverage at
`n ∈ {4, 5}` and the diagonal coverage at `n ∈ {4, 5}` from Wave 23. -/

/-- **★★ CAPSTONE — Combined off-diagonal vortex-stretching bound at
    `n ∈ {0, 1, 2, 3, 4, 5}`** (axiom-free).

    For every `T > 0`:
      (a) the off-diagonal bound holds at every `n ∈ {0, 1, 2, 3, 4, 5}`,
      (b) the diagonal bound holds at every `n ∈ {0, 1, 2, 3, 4, 5}`
          (Waves 21–23),
      (c) the combined operator inequality
            ∀ ω g o, ‖VS_diag ω g‖ + ‖VS_off ω o‖
                      ≤ 1·‖ω‖·‖g‖ + 2·‖ω‖·‖o‖
          holds at `n = 1` (inherited from Wave 24's `_at_n_le_three`).

    HONEST: this is the LOCAL-in-time Leray-Hopf 1934 shadow on the
    diagonal + off-diagonal Galerkin model. It is NOT the Clay Millennium
    bound. -/
theorem local_vortex_stretching_bound_off_diagonal_at_n_le_five
    (T : ℝ) (hT : 0 < T) :
    -- (a) Off-diagonal bound at n ∈ {0, 1, 2, 3, 4, 5}
    LocalVortexStretchingBoundOffDiagonal T 0 ∧
    LocalVortexStretchingBoundOffDiagonal T 1 ∧
    LocalVortexStretchingBoundOffDiagonal T 2 ∧
    LocalVortexStretchingBoundOffDiagonal T 3 ∧
    LocalVortexStretchingBoundOffDiagonal T 4 ∧
    LocalVortexStretchingBoundOffDiagonal T 5 ∧
    -- (b) Diagonal bound at n ∈ {0, 1, 2, 3, 4, 5} (Waves 21–23)
    LocalVortexStretchingBound T 0 ∧
    LocalVortexStretchingBound T 1 ∧
    LocalVortexStretchingBound T 2 ∧
    LocalVortexStretchingBound T 3 ∧
    LocalVortexStretchingBound T 4 ∧
    LocalVortexStretchingBound T 5 ∧
    -- (c) Combined operator inequality at n = 1 (Wave 24)
    (∀ (ω : Vorticity3DState 1) (g : VelocityGradient3DState 1)
       (o : OffDiagonalGradient3DState 1),
       ‖VortexStretching3D ω g‖ + ‖VortexStretching3DOffDiagonal ω o‖
         ≤ 1 * ‖ω‖ * ‖g‖ + 2 * ‖ω‖ * ‖o‖) := by
  -- Re-use the Wave 25 capstone for n ∈ {0,1,2,3} (off-diag), n ∈ {0,1,2,3}
  -- (diag), and the combined (c) clause.
  obtain ⟨h0off, h1off, h2off, h3off, h0diag, h1diag, h2diag, h3diag,
          hcombined⟩ :=
    PrincipiaTractalis.NS3DOffDiagonalAtNTwoThree.local_vortex_stretching_bound_off_diagonal_at_n_le_three T hT
  exact ⟨h0off, h1off, h2off, h3off,
         local_vortex_stretching_bound_off_diagonal_at_n_eq_four T hT,
         local_vortex_stretching_bound_off_diagonal_at_n_eq_five T hT,
         h0diag, h1diag, h2diag, h3diag,
         local_vortex_stretching_bound_at_n_eq_four T hT,
         local_vortex_stretching_bound_at_n_eq_five T hT,
         hcombined⟩

end PrincipiaTractalis.NS3DOffDiagonalAtNFourFive
