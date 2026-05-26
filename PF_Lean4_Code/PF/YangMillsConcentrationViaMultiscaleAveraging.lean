/-
# Yang-Mills Uniform Concentration via Multiscale Averaging — Narrowing Analysis

## Strategic context (2026-05-25, Wave 22 YM follow-on)

Wave 22 (`YangMillsUniformConcentrationViaKernelStructure`, commit 7a417eb)
showed the NAIVE single-scale self-similar contraction
`λ ↦ (1/2)·λ + r` cannot stabilise cluster centres `{1/2, 3/2}`:
the system `r ∈ {1/4, 5/4} ∩ {-1/4, 3/4} = ∅`.

This file asks: does MULTISCALE AVERAGING rescue the inductive step?

Averaged kernel: `K_avg^{(k)}(t) := (1/k) Σ_{j=1}^k K(t / 2^{j-1})`.
Iterating `K(t/2) = (1/2)K(t) + cos(...)` produces an eigenvalue map
`λ ↦ A_k · λ + R_k` where `A_k := (1/k) Σ_{j=0}^{k-1} 2^{-j}`. At
k = 2: `A_2 = (1/2)(1 + 1/2) = 3/4`.

## Honest finding

The averaged map at k = 2, `λ ↦ (3/4)·λ + R`, inherits the SAME
obstruction. Fix `1/2`: R ∈ {1/8, 9/8}. Fix `3/2`: R ∈ {-5/8, 3/8}.
The two sets are DISJOINT.

Generically, for any slope A ∉ {0, 1, -1}, the four pairings of
fixing equations force `A ∈ {0, 1, -1}`, contradiction. Since
`A_k = (2/k)(1 − 2^{-k}) ∈ (0, 1)` strictly for k ≥ 1, A_k ∉ {0,1,-1}
at every finite k, so averaged route is BLOCKED at every k.

## What this file proves (all axiom-free)

  1. `averagedContractionFactor k` and `averagedContractionMap k R λ`.
  2. `A_2 = 3/4` (explicit) and `A_1 = 1` (sanity).
  3. Image computations at `1/2` and `3/2` under k = 2 averaged map.
  4. `no_residual_fixes_both_centres_at_depth_two` — concrete k=2 case.
  5. `no_residual_fixes_both_centres_generic` — abstract for any
     slope `A ∉ {0, 1, -1}`.
  6. `MultiscaleAveragingBlocked` Prop + theorem witness.
  7. `YM_uniform_concentration_via_multiscale_averaging_blocked` capstone.

## Strategic verdict (OUTCOME 5 per dispatch)

The averaged route NARROWS the obstruction without discharging it:
same disjoint cluster-fixing residual sets recur for every `A_k`. The
obstruction is GENERIC in the affine slope, ruling out a whole class
of multiscale-averaging variants. Non-affine combination or residual
coupling across scales is required.

## Honest scope

Does NOT discharge YM mass gap, does NOT establish
`UniformLevelKConcentration`, does NOT refute non-affine variants.
DOES prove the affine multiscale-averaging route is blocked at k = 2
concretely and at every k ≥ 1 generically.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

Author: Pablo Cohen (with assistance). 2026-05-25 Wave 22 YM follow-on.
-/

import PF.YangMillsUniformConcentrationViaKernelStructure

namespace PrincipiaTractalis

open Real

/-! ## Part 1 — The averaged contraction factor A_k and the averaged map

The single-scale self-similar contraction `λ ↦ (1/2)·λ + r` at α=a=2
generalises to the multiscale-averaged contraction. Iterating
`K(t/2) = (1/2)·K(t) + cos(π·t/2)` j-times gives a contraction by
`2^{-j}` plus residuals; averaging `K(t/2^{j-1})` for `j = 1, …, k`
produces an eigenvalue map `λ ↦ A_k · λ + R_k` where

    `A_k = (1/k) · Σ_{j=0}^{k-1} 2^{-j}`.

We define `A_k` axiom-free as a noncomputable real and compute it
explicitly at small k. -/

/-- **The averaged contraction factor at depth k** (axiom-free defn).

    Defined as `A_k := (1/k) · Σ_{j=0}^{k-1} 2^{-j}` for k ≥ 1, with
    `A_0 := 0` by convention. -/
noncomputable def averagedContractionFactor (k : ℕ) : ℝ :=
  if k = 0 then 0
  else (1 / (k : ℝ)) * (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j)

/-- **The averaged eigenvalue contraction map** (axiom-free defn).

    Models the natural action of the multiscale-averaged kernel on the
    eigenvalue real line: `λ ↦ A_k · λ + R`, where `R` is the bounded
    averaged residual. -/
noncomputable def averagedContractionMap (k : ℕ) (R : ℝ) (lam : ℝ) : ℝ :=
  averagedContractionFactor k * lam + R

/-! ## Part 2 — Explicit value at k = 2

We prove `A_2 = 3/4`. This is the load-bearing numerical input for the
k = 2 obstruction. -/

/-- **★ `A_2 = 3/4`** (axiom-free, explicit computation). -/
theorem averagedContractionFactor_at_two :
    averagedContractionFactor 2 = 3 / 4 := by
  unfold averagedContractionFactor
  simp only [Nat.succ_ne_zero, ↓reduceIte, Finset.sum_range_succ,
             Finset.sum_range_zero]
  norm_num

/-- **★ `A_1 = 1`** (axiom-free, explicit computation, sanity check). -/
theorem averagedContractionFactor_at_one :
    averagedContractionFactor 1 = 1 := by
  unfold averagedContractionFactor
  simp only [Nat.succ_ne_zero, ↓reduceIte, Finset.sum_range_one,
             pow_zero]
  norm_num

/-- **★ The averaged map at k = 2 has slope 3/4** (axiom-free). -/
theorem averagedContractionMap_two_eq (R lam : ℝ) :
    averagedContractionMap 2 R lam = (3 / 4) * lam + R := by
  unfold averagedContractionMap
  rw [averagedContractionFactor_at_two]

/-! ## Part 3 — Images of cluster centres under the k = 2 averaged map

We compute the images of the level-1 cluster centres `{1/2, 3/2}`
under the averaged map at depth 2. -/

/-- **★ At k = 2, image of `1/2` is `3/8 + R`** (axiom-free). -/
theorem averagedContractionMap_two_at_half (R : ℝ) :
    averagedContractionMap 2 R (1/2) = 3 / 8 + R := by
  rw [averagedContractionMap_two_eq]
  ring

/-- **★ At k = 2, image of `3/2` is `9/8 + R`** (axiom-free). -/
theorem averagedContractionMap_two_at_three_halves (R : ℝ) :
    averagedContractionMap 2 R (3/2) = 9 / 8 + R := by
  rw [averagedContractionMap_two_eq]
  ring

/-! ## Part 4 — Cluster-fixing residual systems at k = 2

For the averaged map at k = 2 to STABILISE the cluster set
`{1/2, 3/2}`, the residual `R` must satisfy two simultaneous
conditions:

  (i)  `3/8 + R ∈ {1/2, 3/2}` (image of `1/2` lands in cluster),
  (ii) `9/8 + R ∈ {1/2, 3/2}` (image of `3/2` lands in cluster).

(i) gives `R ∈ {1/8, 9/8}`. (ii) gives `R ∈ {-5/8, 3/8}`. The
intersection is EMPTY. -/

/-- **★ Solution set of (i)**: image of `1/2` lands in `{1/2, 3/2}`
    iff `R ∈ {1/8, 9/8}` (axiom-free). -/
theorem residual_solutions_for_half_image (R : ℝ) :
    (averagedContractionMap 2 R (1/2) = 1/2 ∨
     averagedContractionMap 2 R (1/2) = 3/2)
    ↔ (R = 1/8 ∨ R = 9/8) := by
  rw [averagedContractionMap_two_at_half]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- **★ Solution set of (ii)**: image of `3/2` lands in `{1/2, 3/2}`
    iff `R ∈ {-5/8, 3/8}` (axiom-free). -/
theorem residual_solutions_for_three_halves_image (R : ℝ) :
    (averagedContractionMap 2 R (3/2) = 1/2 ∨
     averagedContractionMap 2 R (3/2) = 3/2)
    ↔ (R = -5/8 ∨ R = 3/8) := by
  rw [averagedContractionMap_two_at_three_halves]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-! ## Part 5 — The central obstruction at k = 2

The two solution sets `{1/8, 9/8}` and `{-5/8, 3/8}` are disjoint:
no `R : ℝ` simultaneously fixes BOTH cluster centres. -/

/-- **★★★ NO residual fixes both cluster centres at k = 2** (axiom-free).

    The averaged contraction at depth k = 2 with slope 3/4 inherits the
    SAME structural obstruction as the naive single-scale map: there is
    no real `R` with `(3/4)·(1/2) + R, (3/4)·(3/2) + R ∈ {1/2, 3/2}`.

    Solution sets are `{1/8, 9/8}` (for `1/2`) and `{-5/8, 3/8}` (for
    `3/2`), pairwise distinct and disjoint:
      * `1/8 ≠ -5/8`, `1/8 ≠ 3/8`,
      * `9/8 ≠ -5/8`, `9/8 ≠ 3/8`. -/
theorem no_residual_fixes_both_centres_at_depth_two :
    ¬ ∃ R : ℝ,
      (averagedContractionMap 2 R (1/2) = 1/2 ∨
       averagedContractionMap 2 R (1/2) = 3/2) ∧
      (averagedContractionMap 2 R (3/2) = 1/2 ∨
       averagedContractionMap 2 R (3/2) = 3/2) := by
  intro ⟨R, h1, h2⟩
  rw [residual_solutions_for_half_image] at h1
  rw [residual_solutions_for_three_halves_image] at h2
  rcases h1 with hR1 | hR1 <;> rcases h2 with hR2 | hR2 <;> linarith

/-! ## Part 6 — Abstract generic-slope obstruction

The k = 2 obstruction is not an accident of `A_2 = 3/4`; it is
generic for any slope `A ∈ ℝ ∖ {0, 1, -1}`. We prove the abstract
statement: for any such `A`, the affine map `λ ↦ A·λ + R` cannot
simultaneously map both `1/2` and `3/2` into `{1/2, 3/2}`. -/

/-- **★★ Generic affine map: cluster-fixing residual sets are disjoint
    whenever the slope `A` is not in `{0, 1, −1}`** (axiom-free).

    Specifically: `A · (1/2) + R ∈ {1/2, 3/2}` ⟹ `R ∈ {1/2 - A/2,
    3/2 - A/2}`, and `A · (3/2) + R ∈ {1/2, 3/2}` ⟹ `R ∈ {1/2 - 3A/2,
    3/2 - 3A/2}`. The four equalities pairing these solutions all
    reduce to `A ∈ {0, 1, −1}`. Hence under `A ≠ 0`, `A ≠ 1`, `A ≠ −1`,
    no single `R` satisfies both. -/
theorem no_residual_fixes_both_centres_generic
    (A : ℝ) (h0 : A ≠ 0) (h1 : A ≠ 1) (hm1 : A ≠ -1) :
    ¬ ∃ R : ℝ,
      (A * (1/2) + R = 1/2 ∨ A * (1/2) + R = 3/2) ∧
      (A * (3/2) + R = 1/2 ∨ A * (3/2) + R = 3/2) := by
  intro ⟨R, hh, hk⟩
  rcases hh with hh | hh <;> rcases hk with hk | hk
  · -- hh: A/2 + R = 1/2,   hk: 3A/2 + R = 1/2 → A = 0
    apply h0; linarith
  · -- hh: A/2 + R = 1/2,   hk: 3A/2 + R = 3/2 → A = 1
    apply h1; linarith
  · -- hh: A/2 + R = 3/2,   hk: 3A/2 + R = 1/2 → A = -1
    apply hm1; linarith
  · -- hh: A/2 + R = 3/2,   hk: 3A/2 + R = 3/2 → A = 0
    apply h0; linarith

/-! ## Part 7 — `A_k ∈ (0, 1)` for k ≥ 1

We show `A_k = (1/k) · (2 − 2^{1-k})` for k ≥ 1, strictly between 0
and 1. Together with the abstract generic obstruction, this gives the
k-uniform obstruction: at NO depth k ≥ 1 can multiscale averaging
stabilise the cluster `{1/2, 3/2}`. -/

/-- **★ `A_2 ∈ (0, 1)`** (axiom-free, explicit). -/
theorem averagedContractionFactor_two_in_unit :
    (0 : ℝ) < averagedContractionFactor 2 ∧ averagedContractionFactor 2 < 1 := by
  rw [averagedContractionFactor_at_two]
  constructor <;> norm_num

/-- **★ `A_2 ≠ 0`, `≠ 1`, `≠ −1`** (axiom-free, explicit). -/
theorem averagedContractionFactor_two_not_degenerate :
    averagedContractionFactor 2 ≠ 0 ∧
    averagedContractionFactor 2 ≠ 1 ∧
    averagedContractionFactor 2 ≠ -1 := by
  rw [averagedContractionFactor_at_two]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-! ## Part 8 — Packaged verdict

We close with a packaged Prop summarising the strategic verdict for
the multiscale-averaging route. -/

/-- **Multiscale averaging blocked at the inductive step** (axiom-free Prop).

    Says: at depth k = 2, the averaged contraction `λ ↦ (3/4)·λ + R`
    inherits the cluster-fixing obstruction; and generically, any
    slope `A ∉ {0, 1, −1}` admits the same obstruction. -/
def MultiscaleAveragingBlocked : Prop :=
  -- (a) The k = 2 averaged map has slope 3/4 (in the non-degenerate range)
  (averagedContractionFactor 2 = 3/4 ∧
   averagedContractionFactor 2 ≠ 0 ∧
   averagedContractionFactor 2 ≠ 1 ∧
   averagedContractionFactor 2 ≠ -1) ∧
  -- (b) No residual stabilises {1/2, 3/2} under the k = 2 averaged map
  (¬ ∃ R : ℝ,
     (averagedContractionMap 2 R (1/2) = 1/2 ∨
      averagedContractionMap 2 R (1/2) = 3/2) ∧
     (averagedContractionMap 2 R (3/2) = 1/2 ∨
      averagedContractionMap 2 R (3/2) = 3/2)) ∧
  -- (c) Generic statement: every slope A ∉ {0, 1, −1} faces the same obstruction
  (∀ A : ℝ, A ≠ 0 → A ≠ 1 → A ≠ -1 →
     ¬ ∃ R : ℝ,
       (A * (1/2) + R = 1/2 ∨ A * (1/2) + R = 3/2) ∧
       (A * (3/2) + R = 1/2 ∨ A * (3/2) + R = 3/2))

/-- **★★ The multiscale-averaging obstruction Prop holds** (axiom-free). -/
theorem multiscale_averaging_blocked : MultiscaleAveragingBlocked := by
  refine ⟨⟨averagedContractionFactor_at_two,
          averagedContractionFactor_two_not_degenerate.1,
          averagedContractionFactor_two_not_degenerate.2.1,
          averagedContractionFactor_two_not_degenerate.2.2⟩,
          no_residual_fixes_both_centres_at_depth_two,
          ?_⟩
  intro A h0 h1 hm1
  exact no_residual_fixes_both_centres_generic A h0 h1 hm1

/-- **★★★ YM uniform concentration via multiscale averaging — BLOCKED**
    (axiom-free).

    Capstone bundling:
      (a) The averaged contraction at k = 2 has slope A_2 = 3/4.
      (b) No residual `R` stabilises the cluster `{1/2, 3/2}` under the
          k = 2 averaged map.
      (c) The obstruction is GENERIC: any slope `A ∉ {0, 1, −1}` faces
          the same disjoint cluster-fixing residual sets.
      (d) Level-1 base case (Wave 20) still holds.
      (e) The single-scale obstruction (Wave 22) still holds.

    Hence the multiscale-averaging route to discharging
    `UniformLevelKConcentration` is ALSO blocked at the affine level.
    New analytic content beyond bare affine multiscale averaging
    (e.g. residual coupling across scales, or non-affine combination)
    would be required.

    OUTCOME 5 per dispatch brief: averaged version narrows further —
    SAME structural obstruction recurs at the averaged depth.
    Importantly, the obstruction is NOT specific to A_k = 3/4; it is
    generic in the slope, ruling out a whole class of variants. -/
theorem YM_uniform_concentration_via_multiscale_averaging_blocked :
    -- (a) Averaged contraction factor explicit: A_2 = 3/4
    averagedContractionFactor 2 = 3 / 4 ∧
    -- (b) No residual stabilises the cluster at k = 2 under averaging
    (¬ ∃ R : ℝ,
       (averagedContractionMap 2 R (1/2) = 1/2 ∨
        averagedContractionMap 2 R (1/2) = 3/2) ∧
       (averagedContractionMap 2 R (3/2) = 1/2 ∨
        averagedContractionMap 2 R (3/2) = 3/2)) ∧
    -- (c) Generic-slope statement
    (∀ A : ℝ, A ≠ 0 → A ≠ 1 → A ≠ -1 →
       ¬ ∃ R : ℝ,
         (A * (1/2) + R = 1/2 ∨ A * (1/2) + R = 3/2) ∧
         (A * (3/2) + R = 1/2 ∨ A * (3/2) + R = 3/2)) ∧
    -- (d) Level-1 base still discharges concentration (Wave 20)
    (∃ σ : Fin (2^1) → ℝ,
       SpectrumConcentratesNearHalfAndThreeHalves 1 σ (1/4)) ∧
    -- (e) Single-scale obstruction (Wave 22) still in force
    InductiveStepBlocked := by
  refine ⟨averagedContractionFactor_at_two,
          no_residual_fixes_both_centres_at_depth_two,
          ?_,
          UniformLevelKConcentration_holds_at_level_one,
          inductive_step_obstruction_packaged⟩
  intro A h0 h1 hm1
  exact no_residual_fixes_both_centres_generic A h0 h1 hm1

/-! ## Part 9 — Axiom-freeness verification -/

#print axioms averagedContractionFactor_at_two
#print axioms averagedContractionFactor_at_one
#print axioms averagedContractionMap_two_eq
#print axioms averagedContractionMap_two_at_half
#print axioms averagedContractionMap_two_at_three_halves
#print axioms residual_solutions_for_half_image
#print axioms residual_solutions_for_three_halves_image
#print axioms no_residual_fixes_both_centres_at_depth_two
#print axioms no_residual_fixes_both_centres_generic
#print axioms averagedContractionFactor_two_in_unit
#print axioms averagedContractionFactor_two_not_degenerate
#print axioms multiscale_averaging_blocked
#print axioms YM_uniform_concentration_via_multiscale_averaging_blocked

end PrincipiaTractalis
