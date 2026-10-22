/-
# Yang-Mills — 3-way plaquette sector refinement (zero sector = θ-fixed FF boundary)

**Rio's §2 ACER directive, 2026-10-21.** Route (a) of the Step-6 Fubini
discharge issue: the existing binary `plaquetteSector ∈ {plus, minus}`
lumps **boundary FF plaquettes** (μ ≠ 0, ν ≠ 0, μ ≠ ν, base-time ∈ {0, L/2})
asymmetrically, breaking the pointwise reflection identity
`wilsonActionMinus (θU) = wilsonActionPlus U`. This file introduces a
3-way refinement with an explicit **zero** sector for the θ-fixed
boundary plaquettes, giving the textbook OS reflection structure.

### Scope of this landing

Introduces the predicates and the refined sector; downstream reflection
identities (`plaquetteSectorRefined (θ_p p) = (plaquetteSectorRefined p).reflect`
and `wilsonActionMinusR (θU) = wilsonActionPlusR U`) and the three-way
decomposition `S_W = S_+' + S_0 + S_-'` are landed in follow-up files
once the four plaquette-case analyses are discharged.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonSectorAction_2026_10_19

set_option autoImplicit false

namespace PF.YangMills

open Finset

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The `isZeroPlaquette` predicate. -/

/-- **Boundary FF plaquette predicate.** A plaquette is in the "zero"
sector if it is purely spatial (`μ ≠ 0, ν ≠ 0, μ ≠ ν`) and its base-time
is at the boundary (`0` or `L/2`). These are precisely the plaquettes
fixed by `timeReflectionPlaquette`. -/
def isZeroPlaquette (p : Plaquette L) : Prop :=
  p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.1 ≠ p.2.2 ∧
    ((p.1 0).val = 0 ∨ (p.1 0).val = L / 2)

instance isZeroPlaquette_decidable (p : Plaquette L) : Decidable (isZeroPlaquette p) := by
  unfold isZeroPlaquette; infer_instance

/-! ## §2 — The refined 3-way sector. -/

/-- **Refined plaquette sector (3-way).** Returns `zero` for boundary FF
plaquettes (`isZeroPlaquette`); otherwise falls back on the binary
`plaquetteSector`. -/
def plaquetteSectorRefined (p : Plaquette L) : LinkSector :=
  if isZeroPlaquette p then LinkSector.zero else plaquetteSector p

/-! ## §3 — Basic equivalences. -/

/-- `plaquetteSectorRefined = zero ↔ isZeroPlaquette`. -/
lemma plaquetteSectorRefined_eq_zero_iff (p : Plaquette L) :
    plaquetteSectorRefined p = LinkSector.zero ↔ isZeroPlaquette p := by
  unfold plaquetteSectorRefined
  by_cases h : isZeroPlaquette p
  · simp [h]
  · simp only [if_neg h]
    constructor
    · intro h_binary
      -- `plaquetteSector p = zero` but binary sector is only plus or minus; contradiction.
      exact absurd h_binary (by
        unfold plaquetteSector
        by_cases h' : (p.1 0).val < L / 2 <;> simp [h'])
    · intro; exact absurd ‹_› h

/-- `plaquetteSectorRefined = plus ↔ (binary plaquetteSector = plus) ∧ ¬ isZeroPlaquette`. -/
lemma plaquetteSectorRefined_eq_plus_iff (p : Plaquette L) :
    plaquetteSectorRefined p = LinkSector.plus
      ↔ plaquetteSector p = LinkSector.plus ∧ ¬ isZeroPlaquette p := by
  unfold plaquetteSectorRefined
  by_cases h : isZeroPlaquette p
  · simp [h]
  · simp only [if_neg h, and_true, iff_self_and]
    exact fun _ => h

/-- `plaquetteSectorRefined = minus ↔ (binary plaquetteSector = minus) ∧ ¬ isZeroPlaquette`. -/
lemma plaquetteSectorRefined_eq_minus_iff (p : Plaquette L) :
    plaquetteSectorRefined p = LinkSector.minus
      ↔ plaquetteSector p = LinkSector.minus ∧ ¬ isZeroPlaquette p := by
  unfold plaquetteSectorRefined
  by_cases h : isZeroPlaquette p
  · simp [h]
  · simp only [if_neg h, and_true, iff_self_and]
    exact fun _ => h

/-! ## §4 — The three refined sector actions. -/

/-- Refined plus-sector action: sum of densities over `plaquetteSectorRefined = plus`. -/
noncomputable def wilsonActionPlusR (U : GaugeField L) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Plaquette L)).filter
          (fun p => plaquetteSectorRefined p = LinkSector.plus),
    wilsonActionDensity U p

/-- Refined zero-sector action: sum of densities over `plaquetteSectorRefined = zero`
(boundary FF plaquettes only). -/
noncomputable def wilsonActionZero (U : GaugeField L) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Plaquette L)).filter
          (fun p => plaquetteSectorRefined p = LinkSector.zero),
    wilsonActionDensity U p

/-- Refined minus-sector action: sum of densities over `plaquetteSectorRefined = minus`. -/
noncomputable def wilsonActionMinusR (U : GaugeField L) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Plaquette L)).filter
          (fun p => plaquetteSectorRefined p = LinkSector.minus),
    wilsonActionDensity U p

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.isZeroPlaquette
#print axioms PF.YangMills.plaquetteSectorRefined
#print axioms PF.YangMills.plaquetteSectorRefined_eq_zero_iff
#print axioms PF.YangMills.plaquetteSectorRefined_eq_plus_iff
#print axioms PF.YangMills.plaquetteSectorRefined_eq_minus_iff
#print axioms PF.YangMills.wilsonActionPlusR
#print axioms PF.YangMills.wilsonActionZero
#print axioms PF.YangMills.wilsonActionMinusR
