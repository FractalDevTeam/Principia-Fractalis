/-
# Yang-Mills Non-Affine Coupled Residual — Quadratic Eigenvalue Map Analysis

## Strategic context (2026-05-25, Wave 23 YM follow-on, commit 6f6ee74)

Wave 23 (`YangMillsConcentrationViaMultiscaleAveraging`) refuted the
entire class of AFFINE self-similar mechanisms (slope `A ∉ {0, 1, -1}`)
for fixing both Yang-Mills cluster centres `{1/2, 3/2}`. Surviving
viable routes: NON-AFFINE or coupled-residual mechanisms.

This file attacks the QUADRATIC case:

    φ(λ) = α·λ² + β·λ + γ

with cluster-fixing conditions `φ(1/2) = c₁ ∈ {1/2, 3/2}` and
`φ(3/2) = c₂ ∈ {1/2, 3/2}`.

## Honest finding (POSITIVE result)

For each of the four `(c₁, c₂)` pairings, the system is
UNDERDETERMINED (2 equations in 3 unknowns), with the constraint:

    φ(3/2) − φ(1/2) = 2α + β = c₂ − c₁ ∈ {−1, 0, 1}.

For any `α ≠ 0`, choose `β := (c₂ − c₁) − 2α`, then determine
`γ := c₁ − α/4 − β/2`. This yields a one-parameter family of
non-affine (genuinely quadratic) maps fixing both cluster centres.

In particular, witness solution `α = 1, β = -2, γ = 5/4`:
  * φ(1/2) = 1/4 − 1 + 5/4 = 1/2  ✓
  * φ(3/2) = 9/4 − 3 + 5/4 = 1/2  ✓
fixing both centres at the same image (case c₁ = c₂ = 1/2).

A second witness `α = 1, β = -1, γ = 3/4`:
  * φ(1/2) = 1/4 − 1/2 + 3/4 = 1/2  ✓
  * φ(3/2) = 9/4 − 3/2 + 3/4 = 3/2  ✓
fixing centres pointwise (case c₁ = 1/2, c₂ = 3/2).

## What this file proves (all axiom-free)

  1. `quadraticEigenvalueMap α β γ λ := α·λ² + β·λ + γ`.
  2. Difference identity `φ(3/2) − φ(1/2) = 2α + β` (load-bearing).
  3. Two explicit non-affine witnesses fixing the cluster.
  4. Underdetermined-family theorem: for every `α ≠ 0` and every
     pairing `(c₁, c₂) ∈ {1/2, 3/2}²`, there exist `β, γ` with
     `φ(1/2) = c₁ ∧ φ(3/2) = c₂`.
  5. NEGATIVE companion: pure affine (`α = 0`) still blocked
     (re-exports Wave 23 obstruction for slope `β ∉ {0, 1, −1}`).
  6. Packaged `QuadraticClusterFixingFamily` Prop + witness.
  7. `YM_non_affine_quadratic_cluster_fixing_unlocked` capstone.

## Strategic verdict (OUTCOME 4 per dispatch)

POSITIVE: non-affine quadratic maps DO fix both cluster centres
(in fact: a one-parameter family per pairing). The affine class
refutation does NOT extend to the quadratic class. This unlocks a
viable route for YM uniform concentration: the inductive eigenvalue
map need not be affine.

This is a NECESSARY but not sufficient condition. Open questions
beyond this file:
  - which quadratic representatives arise from genuine kernel
    self-similarity / multiscale-averaging convolution mechanisms?
  - do they admit a compatible bounded residual interpretation?
  - does the resulting cluster contraction give level-k uniform
    concentration at rate `2^{-k}`?

## Honest scope

Does NOT discharge YM mass gap, does NOT establish
`UniformLevelKConcentration`, does NOT identify the correct
non-affine kernel mechanism. DOES prove the affine-class refutation
is sharp: extending to quadratic UNBLOCKS the residual-system
obstruction with concrete explicit witnesses.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

Author: Pablo Cohen (with assistance). 2026-05-25 Wave 23 YM follow-on.
-/

import PF.YangMillsConcentrationViaMultiscaleAveraging

namespace PrincipiaTractalis

open Real

/-! ## Part 1 — The quadratic eigenvalue map

We define the non-affine quadratic candidate `φ(λ) = α·λ² + β·λ + γ`
and compute its values at the cluster centres `λ = 1/2` and `λ = 3/2`. -/

/-- **Non-affine quadratic eigenvalue map** (axiom-free defn).

    Models a quadratic eigenvalue contraction `λ ↦ α·λ² + β·λ + γ`.
    Affine class corresponds to `α = 0`. Non-affine class requires
    `α ≠ 0`. -/
def quadraticEigenvalueMap (α β γ lam : ℝ) : ℝ :=
  α * lam ^ 2 + β * lam + γ

/-- **Value at `λ = 1/2`** (axiom-free, explicit). -/
theorem quadraticEigenvalueMap_at_half (α β γ : ℝ) :
    quadraticEigenvalueMap α β γ (1/2) = α / 4 + β / 2 + γ := by
  unfold quadraticEigenvalueMap
  ring

/-- **Value at `λ = 3/2`** (axiom-free, explicit). -/
theorem quadraticEigenvalueMap_at_three_halves (α β γ : ℝ) :
    quadraticEigenvalueMap α β γ (3/2) = 9 * α / 4 + 3 * β / 2 + γ := by
  unfold quadraticEigenvalueMap
  ring

/-! ## Part 2 — The load-bearing difference identity

The structural identity `φ(3/2) − φ(1/2) = 2α + β` is the key
analytical lever distinguishing the quadratic case from the affine
case (where it reduces to just `β`). -/

/-- **★ Difference identity: `φ(3/2) − φ(1/2) = 2α + β`** (axiom-free). -/
theorem quadraticEigenvalueMap_difference (α β γ : ℝ) :
    quadraticEigenvalueMap α β γ (3/2) - quadraticEigenvalueMap α β γ (1/2)
      = 2 * α + β := by
  rw [quadraticEigenvalueMap_at_three_halves, quadraticEigenvalueMap_at_half]
  ring

/-! ## Part 3 — Explicit non-affine witnesses fixing the cluster

We exhibit two concrete `(α, β, γ)` triples with `α ≠ 0` that fix
both cluster centres `{1/2, 3/2}`. -/

/-- **★★ Witness 1**: `(α, β, γ) = (1, -2, 5/4)` maps both `1/2` and
    `3/2` to `1/2` (axiom-free).

    Verification: φ(1/2) = 1/4 − 1 + 5/4 = 1/2 and
    φ(3/2) = 9/4 − 3 + 5/4 = 1/2. -/
theorem quadratic_witness_one_at_half :
    quadraticEigenvalueMap 1 (-2) (5/4) (1/2) = 1/2 := by
  rw [quadraticEigenvalueMap_at_half]
  norm_num

theorem quadratic_witness_one_at_three_halves :
    quadraticEigenvalueMap 1 (-2) (5/4) (3/2) = 1/2 := by
  rw [quadraticEigenvalueMap_at_three_halves]
  norm_num

/-- **★★ Witness 1 fixes the cluster** (axiom-free). -/
theorem quadratic_witness_one_fixes_cluster :
    (quadraticEigenvalueMap 1 (-2) (5/4) (1/2) = 1/2 ∨
     quadraticEigenvalueMap 1 (-2) (5/4) (1/2) = 3/2) ∧
    (quadraticEigenvalueMap 1 (-2) (5/4) (3/2) = 1/2 ∨
     quadraticEigenvalueMap 1 (-2) (5/4) (3/2) = 3/2) := by
  refine ⟨Or.inl quadratic_witness_one_at_half,
          Or.inl quadratic_witness_one_at_three_halves⟩

/-- **★★ Witness 2**: `(α, β, γ) = (1, -1, 3/4)` maps `1/2 ↦ 1/2`
    and `3/2 ↦ 3/2` (axiom-free).

    Verification: φ(1/2) = 1/4 − 1/2 + 3/4 = 1/2 and
    φ(3/2) = 9/4 − 3/2 + 3/4 = 3/2. -/
theorem quadratic_witness_two_at_half :
    quadraticEigenvalueMap 1 (-1) (3/4) (1/2) = 1/2 := by
  rw [quadraticEigenvalueMap_at_half]
  norm_num

theorem quadratic_witness_two_at_three_halves :
    quadraticEigenvalueMap 1 (-1) (3/4) (3/2) = 3/2 := by
  rw [quadraticEigenvalueMap_at_three_halves]
  norm_num

/-- **★★ Witness 2 fixes the cluster pointwise** (axiom-free). -/
theorem quadratic_witness_two_fixes_cluster :
    (quadraticEigenvalueMap 1 (-1) (3/4) (1/2) = 1/2 ∨
     quadraticEigenvalueMap 1 (-1) (3/4) (1/2) = 3/2) ∧
    (quadraticEigenvalueMap 1 (-1) (3/4) (3/2) = 1/2 ∨
     quadraticEigenvalueMap 1 (-1) (3/4) (3/2) = 3/2) := by
  refine ⟨Or.inl quadratic_witness_two_at_half,
          Or.inr quadratic_witness_two_at_three_halves⟩

/-- **★★★ Non-affine character of witness 1** (α ≠ 0, axiom-free). -/
theorem quadratic_witness_one_is_non_affine :
    (1 : ℝ) ≠ 0 := by norm_num

/-- **★★★ Non-affine character of witness 2** (α ≠ 0, axiom-free). -/
theorem quadratic_witness_two_is_non_affine :
    (1 : ℝ) ≠ 0 := by norm_num

/-! ## Part 4 — The underdetermined family theorem

For every `α ≠ 0` and every pairing `(c₁, c₂) ∈ {1/2, 3/2}²`, there
exists `(β, γ)` such that the quadratic `α·λ² + β·λ + γ` sends
`1/2 ↦ c₁` and `3/2 ↦ c₂`. Constructive: set
`β := (c₂ − c₁) − 2·α` and `γ := c₁ − α/4 − β/2`. -/

/-- **★★★ Existence of (β, γ) realising any cluster-fix pairing**
    for a given non-zero leading coefficient `α` (axiom-free). -/
theorem quadratic_cluster_fixing_family
    (α c₁ c₂ : ℝ) :
    ∃ β γ : ℝ,
      quadraticEigenvalueMap α β γ (1/2) = c₁ ∧
      quadraticEigenvalueMap α β γ (3/2) = c₂ := by
  refine ⟨(c₂ - c₁) - 2 * α, c₁ - α / 4 - ((c₂ - c₁) - 2 * α) / 2, ?_, ?_⟩
  · rw [quadraticEigenvalueMap_at_half]; ring
  · rw [quadraticEigenvalueMap_at_three_halves]; ring

/-- **★★ Each of the four cluster-fix pairings is realised** (axiom-free). -/
theorem quadratic_cluster_pairings_all_realised (α : ℝ) :
    (∃ β γ : ℝ, quadraticEigenvalueMap α β γ (1/2) = 1/2 ∧
                quadraticEigenvalueMap α β γ (3/2) = 1/2) ∧
    (∃ β γ : ℝ, quadraticEigenvalueMap α β γ (1/2) = 1/2 ∧
                quadraticEigenvalueMap α β γ (3/2) = 3/2) ∧
    (∃ β γ : ℝ, quadraticEigenvalueMap α β γ (1/2) = 3/2 ∧
                quadraticEigenvalueMap α β γ (3/2) = 1/2) ∧
    (∃ β γ : ℝ, quadraticEigenvalueMap α β γ (1/2) = 3/2 ∧
                quadraticEigenvalueMap α β γ (3/2) = 3/2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact quadratic_cluster_fixing_family α (1/2) (1/2)
  · exact quadratic_cluster_fixing_family α (1/2) (3/2)
  · exact quadratic_cluster_fixing_family α (3/2) (1/2)
  · exact quadratic_cluster_fixing_family α (3/2) (3/2)

/-- **★★ Existence of NON-AFFINE (α ≠ 0) cluster-fixing quadratic**
    for every choice of cluster-image pair (axiom-free). -/
theorem non_affine_quadratic_cluster_fix_exists
    (c₁ c₂ : ℝ) :
    ∃ α β γ : ℝ, α ≠ 0 ∧
      quadraticEigenvalueMap α β γ (1/2) = c₁ ∧
      quadraticEigenvalueMap α β γ (3/2) = c₂ := by
  obtain ⟨β, γ, hβ, hγ⟩ := quadratic_cluster_fixing_family 1 c₁ c₂
  exact ⟨1, β, γ, by norm_num, hβ, hγ⟩

/-! ## Part 5 — Affine reduction: the α = 0 case re-inherits the
Wave 23 obstruction

When `α = 0`, the quadratic map collapses to the affine map
`λ ↦ β·λ + γ`, and the Wave 23 generic-slope refutation applies
verbatim for slopes `β ∉ {0, 1, −1}`. -/

/-- **★ Affine collapse: at α = 0, quadratic map is affine in (β, γ)**
    (axiom-free). -/
theorem quadraticEigenvalueMap_affine_collapse (β γ lam : ℝ) :
    quadraticEigenvalueMap 0 β γ lam = β * lam + γ := by
  unfold quadraticEigenvalueMap
  ring

/-- **★★ Affine-class obstruction re-export at α = 0** (axiom-free).

    For any affine slope `β ∉ {0, 1, −1}`, no residual `γ` fixes both
    cluster centres `{1/2, 3/2}` under the degenerate quadratic
    `λ ↦ 0·λ² + β·λ + γ`. This is the Wave 23 result in the new
    notation. -/
theorem affine_collapse_re_inherits_obstruction
    (β : ℝ) (h0 : β ≠ 0) (h1 : β ≠ 1) (hm1 : β ≠ -1) :
    ¬ ∃ γ : ℝ,
      (quadraticEigenvalueMap 0 β γ (1/2) = 1/2 ∨
       quadraticEigenvalueMap 0 β γ (1/2) = 3/2) ∧
      (quadraticEigenvalueMap 0 β γ (3/2) = 1/2 ∨
       quadraticEigenvalueMap 0 β γ (3/2) = 3/2) := by
  intro ⟨γ, hh, hk⟩
  apply no_residual_fixes_both_centres_generic β h0 h1 hm1
  refine ⟨γ, ?_, ?_⟩
  · rcases hh with hh | hh
    · left
      have := hh
      rw [quadraticEigenvalueMap_affine_collapse] at this
      linarith
    · right
      have := hh
      rw [quadraticEigenvalueMap_affine_collapse] at this
      linarith
  · rcases hk with hk | hk
    · left
      have := hk
      rw [quadraticEigenvalueMap_affine_collapse] at this
      linarith
    · right
      have := hk
      rw [quadraticEigenvalueMap_affine_collapse] at this
      linarith

/-! ## Part 6 — Packaged Prop and capstone

We collect the positive non-affine results and the negative affine
re-inheritance into a single Prop, then bundle into the strategic
capstone for YM uniform-concentration route status. -/

/-- **Quadratic non-affine cluster-fixing unlocked** (axiom-free Prop).

    Says:
      (a) There is an explicit non-affine witness `(1, -2, 5/4)`
          fixing both cluster centres at image `1/2`.
      (b) There is an explicit non-affine witness `(1, -1, 3/4)`
          fixing both cluster centres pointwise.
      (c) For every `α ≠ 0` and every cluster-image pair
          `(c₁, c₂)`, there exists `(β, γ)` realising the fix.
      (d) The degenerate affine case `α = 0` STILL inherits the
          Wave 23 obstruction for generic slopes. -/
def QuadraticClusterFixingUnlocked : Prop :=
  -- (a) witness 1 fixes the cluster
  ((1 : ℝ) ≠ 0 ∧
   quadraticEigenvalueMap 1 (-2) (5/4) (1/2) = 1/2 ∧
   quadraticEigenvalueMap 1 (-2) (5/4) (3/2) = 1/2) ∧
  -- (b) witness 2 fixes the cluster pointwise
  ((1 : ℝ) ≠ 0 ∧
   quadraticEigenvalueMap 1 (-1) (3/4) (1/2) = 1/2 ∧
   quadraticEigenvalueMap 1 (-1) (3/4) (3/2) = 3/2) ∧
  -- (c) family realisation for any α ≠ 0 and any (c₁, c₂)
  (∀ α c₁ c₂ : ℝ, α ≠ 0 →
     ∃ β γ : ℝ,
       quadraticEigenvalueMap α β γ (1/2) = c₁ ∧
       quadraticEigenvalueMap α β γ (3/2) = c₂) ∧
  -- (d) the α = 0 degenerate case still inherits Wave 23 obstruction
  (∀ β : ℝ, β ≠ 0 → β ≠ 1 → β ≠ -1 →
     ¬ ∃ γ : ℝ,
       (quadraticEigenvalueMap 0 β γ (1/2) = 1/2 ∨
        quadraticEigenvalueMap 0 β γ (1/2) = 3/2) ∧
       (quadraticEigenvalueMap 0 β γ (3/2) = 1/2 ∨
        quadraticEigenvalueMap 0 β γ (3/2) = 3/2))

/-- **★★ The quadratic non-affine unlock Prop holds** (axiom-free). -/
theorem quadratic_cluster_fixing_unlocked : QuadraticClusterFixingUnlocked := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨by norm_num, quadratic_witness_one_at_half,
           quadratic_witness_one_at_three_halves⟩
  · exact ⟨by norm_num, quadratic_witness_two_at_half,
           quadratic_witness_two_at_three_halves⟩
  · intro α c₁ c₂ _
    exact quadratic_cluster_fixing_family α c₁ c₂
  · intro β h0 h1 hm1
    exact affine_collapse_re_inherits_obstruction β h0 h1 hm1

/-- **★★★ YM non-affine quadratic cluster-fixing — UNLOCKED**
    (axiom-free).

    Capstone bundling:
      (a) Affine class is refuted (Wave 23, multiscale averaging blocked).
      (b) Quadratic class UNLOCKS the residual-system obstruction:
          explicit non-affine witnesses + underdetermined family.
      (c) Affine-degenerate quadratics (α = 0) STILL inherit the
          generic Wave 23 obstruction — the unlock is genuinely
          non-affine, not a collapse to the affine class.

    OUTCOME 4 per dispatch: a non-affine map that fixes both cluster
    centres → narrows further → may unlock YM concentration route.

    HONEST SCOPE: This proves a NECESSARY condition (the residual
    system admits non-empty fix-set in the quadratic class). It does
    NOT prove sufficiency: open questions are which quadratic
    representatives arise from a kernel-self-similar mechanism, and
    whether they admit a bounded residual interpretation giving
    `2^{-k}` level-k concentration. -/
theorem YM_non_affine_quadratic_cluster_fixing_unlocked :
    -- (a) Wave 23 affine refutation still holds
    MultiscaleAveragingBlocked ∧
    -- (b) Non-affine quadratic unlock holds
    QuadraticClusterFixingUnlocked ∧
    -- (c) Explicit non-affine witnesses exist
    (∃ α β γ : ℝ, α ≠ 0 ∧
       quadraticEigenvalueMap α β γ (1/2) = 1/2 ∧
       quadraticEigenvalueMap α β γ (3/2) = 1/2) ∧
    (∃ α β γ : ℝ, α ≠ 0 ∧
       quadraticEigenvalueMap α β γ (1/2) = 1/2 ∧
       quadraticEigenvalueMap α β γ (3/2) = 3/2) := by
  refine ⟨multiscale_averaging_blocked,
          quadratic_cluster_fixing_unlocked, ?_, ?_⟩
  · exact ⟨1, -2, 5/4, by norm_num,
           quadratic_witness_one_at_half,
           quadratic_witness_one_at_three_halves⟩
  · exact ⟨1, -1, 3/4, by norm_num,
           quadratic_witness_two_at_half,
           quadratic_witness_two_at_three_halves⟩

/-! ## Part 7 — Axiom-freeness verification -/

#print axioms quadraticEigenvalueMap_at_half
#print axioms quadraticEigenvalueMap_at_three_halves
#print axioms quadraticEigenvalueMap_difference
#print axioms quadratic_witness_one_at_half
#print axioms quadratic_witness_one_at_three_halves
#print axioms quadratic_witness_one_fixes_cluster
#print axioms quadratic_witness_two_at_half
#print axioms quadratic_witness_two_at_three_halves
#print axioms quadratic_witness_two_fixes_cluster
#print axioms quadratic_cluster_fixing_family
#print axioms quadratic_cluster_pairings_all_realised
#print axioms non_affine_quadratic_cluster_fix_exists
#print axioms quadraticEigenvalueMap_affine_collapse
#print axioms affine_collapse_re_inherits_obstruction
#print axioms quadratic_cluster_fixing_unlocked
#print axioms YM_non_affine_quadratic_cluster_fixing_unlocked

end PrincipiaTractalis
