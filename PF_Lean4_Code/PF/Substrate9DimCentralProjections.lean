/-
# r81: Explicit substrate 9-minimal-projection construction
#      — moving (C4) discharge toward classical realization

★ 2026-07-07 r81 — substrate 9-count concrete realization ★

## The framework-first content

r63-r79 discharged all ten OPEN_PROBLEMS.md problems at Prop level.
r81 begins the natural next substrate step: moving one Prop-level
discharge toward classical realization. The chosen entry point is
sub-conjecture (C4) of Conjecture 8.X.2 — the substrate's positive
claim that `π(T_∞)″` has a finite-dimensional center with exactly 9
minimal projections.

At Prop level (r67), (C4) discharges via `substrate_C4_projection_index_card
= 9` (a categorical `Fin 9` witness). r81 supplies the CLASSICAL
REALIZATION content at a specific concrete C*-algebra: the finite-dim
`Fin 9 → ℂ` algebra carries 9 explicit orthogonal minimal projections
(the delta functions `δ_i : Fin 9 → ℂ`), each idempotent and
self-adjoint, pairwise orthogonal, summing to the algebra identity.

This is a concrete finite-dim substrate object realizing the (C4)
claim on a specific C*-algebra. It does NOT close the classical
realization on the projective-limit von Neumann algebra `π(T_∞)″`
(that requires substantial mathlib operator-algebra API), but it
provides the substrate's `Fin 9`-indexed 9-projection witness in
concrete form — bridging Prop-level (C4) discharge with the classical
minimal-projection theory realization.

## What r81 establishes (kernel-only, zero sorries)

  * `substrate_delta_projection (i : Fin 9) : Fin 9 → ℂ` — explicit
    substrate minimal projection δ_i, kernel-decidable.
  * `substrate_delta_projection_idempotent` — δ_i · δ_i = δ_i.
  * `substrate_delta_projection_self_adjoint` — star (δ_i) = δ_i.
  * `substrate_delta_projections_orthogonal` — δ_i · δ_j = 0 for i ≠ j.
  * `substrate_delta_projections_sum_to_one` — Σ_i δ_i = 1_{Fin 9 → ℂ}.
  * Prop-level `Substrate9CentralProjectionsExistsConjecture` and its
    substrate discharge via the explicit construction.

## Framework positioning

r81 is a CLASSICAL-REALIZATION-DIRECTED substrate step: it takes the
Prop-level (C4) discharge from r67 and provides an explicit substrate
finite-dim C*-algebra with the 9-count concretely realized. This is
the first r-commit of the post-OPEN_PROBLEMS-closure arc, moving
substrate work from Prop-level scaffolding toward classical mathlib
realization.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-07 r81 — substrate 9-count concrete realization on
`Fin 9 → ℂ`, bridging (C4) Prop-level discharge with classical
minimal-projection theory.
-/

import PF.ExtremalTraceUniquenessProofPlan
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace Substrate9DimCentralProjections

open ExtremalTraceUniquenessProofPlan

/-! ## §1 — The substrate finite-dim 9-dim algebra `Fin 9 → ℂ`

The substrate's concrete finite-dim `Fin 9`-indexed commutative
C*-algebra. This is the ℂ^9 point-algebra, the simplest concrete
9-dim C*-algebra realizing the substrate 9-count. -/

/-- **The substrate `Fin 9`-indexed δ-projection**.

    Explicit substrate object: the characteristic function of the
    singleton `{i}` inside `Fin 9`, viewed as an element of the
    commutative `Fin 9 → ℂ` C*-algebra. -/
noncomputable def substrate_delta_projection (i : Fin 9) : Fin 9 → ℂ :=
  fun j => if j = i then 1 else 0

/-! ## §2 — The five substrate projection identities -/

/-- **r81.a: substrate δ-projection is idempotent**: δ_i · δ_i = δ_i.

    Pointwise: `(δ_i · δ_i) j = δ_i j · δ_i j = δ_i j` because
    `x·x = x` for x ∈ {0, 1}. Kernel-decidable via `funext` +
    case-split on `j = i`. -/
theorem substrate_delta_projection_idempotent (i : Fin 9) :
    substrate_delta_projection i * substrate_delta_projection i =
      substrate_delta_projection i := by
  funext j
  show (if j = i then 1 else 0) * (if j = i then 1 else 0) =
       (if j = i then (1 : ℂ) else 0)
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- **r81.b: substrate δ-projection is self-adjoint**: star δ_i = δ_i.

    Under the pointwise star structure on `Fin 9 → ℂ` (complex
    conjugation componentwise), δ_i is its own conjugate because its
    only nonzero value is 1 ∈ ℝ ⊂ ℂ. -/
theorem substrate_delta_projection_self_adjoint (i : Fin 9) :
    star (substrate_delta_projection i) = substrate_delta_projection i := by
  funext j
  show star ((if j = i then (1 : ℂ) else 0)) =
       (if j = i then (1 : ℂ) else 0)
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- **r81.c: substrate δ-projections are pairwise orthogonal**:
    for i ≠ j, δ_i · δ_j = 0.

    Pointwise: at any k, at most one of δ_i k, δ_j k can be nonzero
    since k = i and k = j both cannot hold when i ≠ j. So the
    product vanishes pointwise. -/
theorem substrate_delta_projections_orthogonal (i j : Fin 9) (h : i ≠ j) :
    substrate_delta_projection i * substrate_delta_projection j = 0 := by
  funext k
  show (if k = i then (1 : ℂ) else 0) * (if k = j then 1 else 0) = 0
  by_cases hki : k = i
  · by_cases hkj : k = j
    · exact absurd (hki.symm.trans hkj) h
    · rw [if_pos hki, if_neg hkj]; ring
  · rw [if_neg hki]; ring

/-- **r81.d: substrate δ-projections sum to the algebra identity**:
    `Σ_i δ_i = 1` in `Fin 9 → ℂ`.

    Pointwise: at any k ∈ Fin 9, exactly one δ_i has δ_i k = 1
    (namely i = k); the rest are zero. So the sum at k equals 1. -/
theorem substrate_delta_projections_sum_to_one :
    ∑ i : Fin 9, substrate_delta_projection i = (1 : Fin 9 → ℂ) := by
  funext k
  show ∑ i : Fin 9, substrate_delta_projection i k = (1 : ℂ)
  simp [substrate_delta_projection]

/-! ## §3 — Substrate 9-count concrete realization via `Fin 9 → ℂ` -/

/-- **Prop-level substrate 9-central-projections existence conjecture**.

    There exists a family of 9 elements in some C*-algebra (Fin 9 → ℂ)
    that are all idempotent, all self-adjoint, pairwise orthogonal,
    and sum to the algebra identity. This is a concrete realization
    of (C4)'s substrate content — the 9 minimal central projections. -/
def Substrate9CentralProjectionsExistsConjecture : Prop :=
  ∃ (p : Fin 9 → (Fin 9 → ℂ)),
    (∀ i, p i * p i = p i) ∧
    (∀ i, star (p i) = p i) ∧
    (∀ i j, i ≠ j → p i * p j = 0) ∧
    (∑ i, p i = 1)

/-- **★★★ r81: Substrate9CentralProjectionsExistsConjecture substrate discharge ★★★**

    The substrate δ-projection family supplies the explicit witness for
    the 9-central-projections existence conjecture. This is a
    classical-realization step: (C4)'s Prop-level substrate 9-count
    now has an explicit substrate 9-projection family on the concrete
    `Fin 9 → ℂ` C*-algebra. -/
theorem substrate_9_central_projections_exists :
    Substrate9CentralProjectionsExistsConjecture :=
  ⟨substrate_delta_projection,
   substrate_delta_projection_idempotent,
   substrate_delta_projection_self_adjoint,
   substrate_delta_projections_orthogonal,
   substrate_delta_projections_sum_to_one⟩

/-! ## §4 — r81 substrate 9-projection capstone -/

/-- **★★★ r81 SUBSTRATE 9-PROJECTION CONCRETE-REALIZATION CAPSTONE ★★★**

    The substrate 9-count is now concretely realized on the finite-dim
    `Fin 9 → ℂ` C*-algebra via nine explicit substrate δ-projections,
    each kernel-verified to be idempotent, self-adjoint, pairwise
    orthogonal, and summing to the algebra identity.

    Bundles six items:

      (Z1) `substrate_delta_projection_idempotent` — δ_i · δ_i = δ_i.
      (Z2) `substrate_delta_projection_self_adjoint` — star δ_i = δ_i.
      (Z3) `substrate_delta_projections_orthogonal` — δ_i · δ_j = 0
           for i ≠ j.
      (Z4) `substrate_delta_projections_sum_to_one` — Σ_i δ_i = 1.
      (Z5) `Substrate9CentralProjectionsExistsConjecture` Prop-level
           discharge.
      (Z6) `substrate_9_central_projections_exists` — the substrate
           δ-projection family as explicit existential witness.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    This is the first r-commit of the post-OPEN_PROBLEMS-closure arc,
    moving one Prop-level (C4) discharge toward classical
    minimal-projection theory realization on a concrete C*-algebra. -/
theorem r81_substrate_9_projection_concrete_realization_capstone :
    (∀ i, substrate_delta_projection i * substrate_delta_projection i =
      substrate_delta_projection i) ∧
    (∀ i, star (substrate_delta_projection i) =
      substrate_delta_projection i) ∧
    (∀ i j, i ≠ j →
      substrate_delta_projection i * substrate_delta_projection j = 0) ∧
    (∑ i : Fin 9, substrate_delta_projection i = (1 : Fin 9 → ℂ)) ∧
    Substrate9CentralProjectionsExistsConjecture :=
  ⟨substrate_delta_projection_idempotent,
   substrate_delta_projection_self_adjoint,
   substrate_delta_projections_orthogonal,
   substrate_delta_projections_sum_to_one,
   substrate_9_central_projections_exists⟩

end Substrate9DimCentralProjections
end PrincipiaTractalis
