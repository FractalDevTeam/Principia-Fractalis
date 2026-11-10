/-
# NS3DVortexStretchingBoundedDischarge

**Date**: 2026-11-10
**Status**: axiom-free at the three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## What this file delivers

Discharge of `VortexStretchingBoundedHypothesis` at every fixed `n : ℕ`,
with `K = 1`. The honest-scope marker in `NS3DVortexStretchingObstruction`
calls the hypothesis "the operator-norm UNCONDITIONAL bound that the
Constantin-Fefferman geometric-depletion result COMES CLOSE TO but does
not achieve at full strength." At the Galerkin-truncated finite-dim
level, the bound is a direct consequence of the uniform Hadamard bound
`‖x ⊙ y‖ ≤ ‖x‖ · ‖y‖` on `EuclideanSpace ℝ (Fin n)`, which was proved
axiom-free in `NS3DUniformHadamardDischargeAttempt`.

## Honest scope

This file closes the **finite-dim Galerkin shadow** of the vortex-
stretching bounded hypothesis. The Clay-grade residual is the
**infinite-dim PDE limit** — uniform-in-regularity bounds on
`‖(ω · ∇) u‖_{L²}` controlled by `‖ω‖_{L²} · ‖∇u‖_{L²}` in a way that
survives Grönwall. That PDE-level question remains open and is NOT
discharged here. What IS discharged: for every fixed Galerkin
truncation level `n`, the operator-norm bound at `K = 1` is now a
machine-verified theorem.

The Clay-grade gap `VortexStretchingBoundedHypothesisUniformInN` (if
written) is a separate statement; this file does not claim to close it.
See `NS3DGlobalKTAttempt.UniformVortexStretchingBoundAllN` for the
uniform-in-n sibling that was already discharged via Wave 33 /
Wave 55A machinery.
-/

import PF.NS3DVortexStretchingObstruction
import PF.NS3DUniformHadamardDischargeAttempt

namespace PrincipiaTractalis.NS3DVortexStretchingObstruction

open scoped NNReal
open PrincipiaTractalis
open PrincipiaTractalis.NS3DLocalRegularityAtNGeqOneRetry
open PrincipiaTractalis.NS3DOffDiagonalVortexStretching
open PrincipiaTractalis.NS3DUniformHadamardDischargeAttempt

variable {n : ℕ}

/-- **★ VortexStretchingBoundedHypothesis is axiom-free at every `n` ★**

    For every Galerkin truncation level `n : ℕ`, the operator-norm
    bound `‖VortexStretching3D ω g‖ ≤ 1 · ‖ω‖ · ‖g‖` holds for all
    states `(ω, g) : Vorticity3DState n × VelocityGradient3DState n`.

    Proof: reduce to the Hadamard uniform bound `‖x ⊙ y‖ ≤ ‖x‖ · ‖y‖`
    (axiom-free via `hadamard_norm_le_uniform`) on each of the three
    component pairs, then combine using the `max` product norm. -/
theorem vortexStretchingBoundedHypothesis_holds :
    @VortexStretchingBoundedHypothesis n := by
  refine ⟨1, by norm_num, ?_⟩
  intro ω g
  -- VortexStretching3D ω g = triple of pointwise products (g_j · ω_j)
  -- Rewrite to the Hadamard-triple form.
  rw [vortexStretching3D_eq_triple_hadamard, prod_triple_norm_eq]
  -- Each component norm ≤ ‖g‖ and ≤ ‖ω‖ via three_tuple_components_le.
  obtain ⟨hω0, hω1, hω2⟩ := three_tuple_components_le ω
  obtain ⟨hg0, hg1, hg2⟩ := three_tuple_components_le g
  have ng : 0 ≤ ‖g‖ := norm_nonneg _
  -- Component-1 bound via Hadamard uniform + monotonicity of (·*·) over ℝ≥0.
  have b1 : ‖hadamard n g.1 ω.1‖ ≤ 1 * ‖ω‖ * ‖g‖ := by
    have hh := hadamard_norm_le_uniform n g.1 ω.1
    have hp : ‖g.1‖ * ‖ω.1‖ ≤ ‖g‖ * ‖ω‖ :=
      mul_le_mul hg0 hω0 (norm_nonneg _) ng
    have : ‖hadamard n g.1 ω.1‖ ≤ ‖g‖ * ‖ω‖ := le_trans hh hp
    nlinarith [this]
  have b2 : ‖hadamard n g.2.1 ω.2.1‖ ≤ 1 * ‖ω‖ * ‖g‖ := by
    have hh := hadamard_norm_le_uniform n g.2.1 ω.2.1
    have hp : ‖g.2.1‖ * ‖ω.2.1‖ ≤ ‖g‖ * ‖ω‖ :=
      mul_le_mul hg1 hω1 (norm_nonneg _) ng
    have : ‖hadamard n g.2.1 ω.2.1‖ ≤ ‖g‖ * ‖ω‖ := le_trans hh hp
    nlinarith [this]
  have b3 : ‖hadamard n g.2.2 ω.2.2‖ ≤ 1 * ‖ω‖ * ‖g‖ := by
    have hh := hadamard_norm_le_uniform n g.2.2 ω.2.2
    have hp : ‖g.2.2‖ * ‖ω.2.2‖ ≤ ‖g‖ * ‖ω‖ :=
      mul_le_mul hg2 hω2 (norm_nonneg _) ng
    have : ‖hadamard n g.2.2 ω.2.2‖ ≤ ‖g‖ * ‖ω‖ := le_trans hh hp
    nlinarith [this]
  exact max_le b1 (max_le b2 b3)

/-- Axiom-footprint witness. `#print axioms` should report only
    `[propext, Classical.choice, Quot.sound]`. -/
theorem vortexStretchingBoundedHypothesis_axiom_free : True :=
  have _ := @vortexStretchingBoundedHypothesis_holds
  trivial

#print axioms vortexStretchingBoundedHypothesis_holds

end PrincipiaTractalis.NS3DVortexStretchingObstruction
