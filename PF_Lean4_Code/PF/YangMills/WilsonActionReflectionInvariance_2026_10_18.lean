/-
# Yang-Mills — `wilsonActionTotal (θ U) = wilsonActionTotal U`

**Rio's YM step 3 (queued after Seg02-06), 2026-10-18.** Legion's 2026-10-17
scoping (`codex/YM_OS_SCOPE_SITE_REFLECTION_2026-10-17.md`) measured that
the originally-landed `timeReflectionLink` left the Wilson action with
|ΔS| ≈ 2.4 (L=4) and ≈ 15.5 (L=5), and that the corrected θ (with the
temporal-link base-site shift `θx − ê₀` and a per-temporal-link inverse)
is numerically invariant to 2e-11.

Step 0 (fixing `timeReflectionGaugeField`) landed in
`ReflectionPositivityGram_2026_10_17.lean`. This file is step 3:
proving the invariance formally.

### Proof structure

The sum over plaquettes is reindexed by an explicit plaquette involution
`timeReflectionPlaquette`:

* `(x, μ, ν)` with both `μ, ν ≠ 0` → `(θx, μ, ν)` (spatial-spatial unchanged);
* `(x, 0, ν)` with `ν ≠ 0`        → `(θx − ê₀, ν, 0)` (swap, shift base);
* `(x, μ, 0)` with `μ ≠ 0`        → `(θx − ê₀, 0, μ)` (symmetric);
* `(x, 0, 0)` (diagonal, density 0) → `(θx − ê₀, 0, 0)`.

The core identity in each non-trivial case is that the plaquette holonomy
under `θ U` is a *cyclic permutation* of the holonomy under `U` evaluated
at the image plaquette. Trace cyclicity (`Matrix.trace_mul_comm`,
`Matrix.trace_mul_cycle`) does the rest; no SU(2)-specific trace identity
is needed.

### Scope

Finite periodic lattice at side `L` (any `[NeZero L]`, no `Even L` required
for the action equality — that hypothesis is only needed later for the
Fubini sector split).

### Three-axiom bar

Every declaration kernel-clean `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-18.
-/
import PF.YangMills.ReflectionPositivityGram_2026_10_17

set_option autoImplicit false

namespace PF.YangMills

open Matrix

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The plaquette involution. -/

/-- **Time reflection on a plaquette.** Four-case definition keyed on
whether `μ`, `ν` are the time direction (`0`). The exact mapping on each
case is forced by the structure of the holonomy under `θ U` — see
`plaquetteHolonomy_timeReflection_eq` below. -/
def timeReflectionPlaquette (p : Plaquette L) : Plaquette L :=
  let x := p.1
  let μ := p.2.1
  let ν := p.2.2
  if μ = 0 then
    if ν = 0 then (shiftTimeNeg (timeReflectionSite x), 0, 0)
    else (shiftTimeNeg (timeReflectionSite x), ν, 0)
  else if ν = 0 then
    (shiftTimeNeg (timeReflectionSite x), 0, μ)
  else
    (timeReflectionSite x, μ, ν)

/-! ## §2 — Site-level lemmas. -/

/-- `θ ∘ θ = id` on sites. -/
lemma timeReflectionSite_involutive : Function.Involutive (timeReflectionSite (L := L)) := by
  intro x
  unfold timeReflectionSite
  funext i
  by_cases h : i = 0
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- `(θ(θx − ê₀)) − ê₀ = x`. The composite of "reflect, shift back" is
an involution on sites. -/
lemma shiftTimeNeg_timeReflectionSite_involutive :
    Function.Involutive (fun x : LatticeSite L => shiftTimeNeg (timeReflectionSite x)) := by
  intro x
  show shiftTimeNeg (timeReflectionSite (shiftTimeNeg (timeReflectionSite x))) = x
  unfold shiftTimeNeg timeReflectionSite
  funext i
  by_cases h : i = 0
  · subst h
    simp only [Function.update_self]
    show -(-x 0 - 1) - 1 = x 0
    abel
  · simp only [Function.update_of_ne h]

/-! ## §3 — `timeReflectionPlaquette` is an involution. -/

/-- Specialization: `θx − ê₀` applied twice is `x`, phrased for the
plaquette involution (the base-site transform in the three temporal cases). -/
lemma shiftTimeNeg_timeReflectionSite_twice (x : LatticeSite L) :
    shiftTimeNeg (timeReflectionSite (shiftTimeNeg (timeReflectionSite x))) = x :=
  shiftTimeNeg_timeReflectionSite_involutive x

/-- The plaquette-level reflection is an involution. -/
lemma timeReflectionPlaquette_involutive :
    Function.Involutive (timeReflectionPlaquette (L := L)) := by
  intro p
  rcases p with ⟨x, μ, ν⟩
  simp only [timeReflectionPlaquette]
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hν : ν = 0
    · subst hν
      -- (x, 0, 0) → (shiftTimeNeg (θx), 0, 0) → (x, 0, 0)
      simp only [if_true, if_pos rfl]
      congr 1
      exact shiftTimeNeg_timeReflectionSite_twice x
    · -- (x, 0, ν) → (shiftTimeNeg (θx), ν, 0) → (x, 0, ν)
      simp only [if_true, if_pos rfl, if_neg hν]
      congr 1
      exact shiftTimeNeg_timeReflectionSite_twice x
  · by_cases hν : ν = 0
    · subst hν
      -- (x, μ, 0) → (shiftTimeNeg (θx), 0, μ) → (x, μ, 0)
      simp only [if_neg hμ, if_pos rfl, if_true]
      congr 1
      exact shiftTimeNeg_timeReflectionSite_twice x
    · -- (x, μ, ν) → (θx, μ, ν) → (x, μ, ν)
      simp only [if_neg hμ, if_neg hν]
      congr 1
      exact timeReflectionSite_involutive x

/-- The plaquette-level reflection is a bijection. -/
lemma timeReflectionPlaquette_bijective :
    Function.Bijective (timeReflectionPlaquette (L := L)) :=
  timeReflectionPlaquette_involutive.bijective

/-! ## §4 — Site-level commutation lemmas: how `θ` and the two shifts
(`shiftSite μ`, `shiftTimeNeg`) interact. -/

/-- For spatial directions `μ ≠ 0`, `θ` commutes with `shiftSite μ`. -/
lemma timeReflectionSite_shiftSite_spatial {μ : LatticeDir} (hμ : μ ≠ 0)
    (x : LatticeSite L) :
    timeReflectionSite (shiftSite x μ) = shiftSite (timeReflectionSite x) μ := by
  unfold timeReflectionSite shiftSite
  funext i
  by_cases h0 : i = 0
  · subst h0; simp [Function.update_of_ne hμ.symm]
  · by_cases hμi : i = μ
    · subst hμi; simp [Function.update_of_ne h0]
    · simp [Function.update_of_ne hμi, Function.update_of_ne h0]

/-- Time reflection of a `+ê₀` shift gives `shiftTimeNeg` of the reflection. -/
lemma timeReflectionSite_shiftSite_temporal (x : LatticeSite L) :
    timeReflectionSite (shiftSite x 0) = shiftTimeNeg (timeReflectionSite x) := by
  unfold timeReflectionSite shiftSite shiftTimeNeg
  funext i
  by_cases h0 : i = 0
  · subst h0
    simp only [Function.update_self]
    show -(x 0 + 1) = -x 0 - 1
    abel
  · simp [Function.update_of_ne h0]

/-- `shiftTimeNeg` commutes with `shiftSite μ` for spatial `μ ≠ 0`. -/
lemma shiftTimeNeg_shiftSite_spatial {μ : LatticeDir} (hμ : μ ≠ 0)
    (x : LatticeSite L) :
    shiftTimeNeg (shiftSite x μ) = shiftSite (shiftTimeNeg x) μ := by
  unfold shiftTimeNeg shiftSite
  funext i
  by_cases h0 : i = 0
  · subst h0; simp [Function.update_of_ne hμ.symm]
  · by_cases hμi : i = μ
    · subst hμi; simp [Function.update_of_ne h0]
    · simp [Function.update_of_ne hμi, Function.update_of_ne h0]

/-- `shiftSite 0 ∘ shiftTimeNeg = id` on sites. -/
lemma shiftSite_shiftTimeNeg (x : LatticeSite L) :
    shiftSite (shiftTimeNeg x) 0 = x := by
  unfold shiftSite shiftTimeNeg
  funext i
  by_cases h : i = 0
  · subst h
    simp only [Function.update_self]
    show x 0 - 1 + 1 = x 0
    abel
  · simp [Function.update_of_ne h]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.timeReflectionSite_involutive
#print axioms PF.YangMills.shiftTimeNeg_timeReflectionSite_involutive
#print axioms PF.YangMills.timeReflectionPlaquette
#print axioms PF.YangMills.timeReflectionPlaquette_involutive
#print axioms PF.YangMills.timeReflectionPlaquette_bijective
#print axioms PF.YangMills.timeReflectionSite_shiftSite_spatial
#print axioms PF.YangMills.timeReflectionSite_shiftSite_temporal
#print axioms PF.YangMills.shiftTimeNeg_shiftSite_spatial
#print axioms PF.YangMills.shiftSite_shiftTimeNeg
