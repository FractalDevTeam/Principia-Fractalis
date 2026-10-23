/-
# Yang-Mills — Per-link conditional inversion on Λ_-

**Rio's §P3 ACER directive, 2026-10-23.** Piece 2 of the Λ_- measure-
preserving restriction: per-link conditional inversion on the Λ_-
subtype (inversion on temporal Λ_- links, identity on spatial Λ_-
links), measure-preserving on the Λ_- Pi Haar.

Mirrors the full-field `condInvAt` + `gaugeFieldCondInv_measurePreserving`
(`WilsonReflectionMeasurePreservingApply_2026_10_21.lean`), restricted
to the Λ_- subtype.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-23.
-/
import PF.YangMills.WilsonSectorMeasureSplit_2026_10_20
import PF.YangMills.WilsonReflectionMeasurePreserving_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- Per-link conditional inversion on a Λ_- link: `Inv.inv` on temporal,
`id` on spatial. -/
def condInvAtMinus (ℓ : Subtype (isMinusLink : LatticeLink L → Prop)) :
    SU2 → SU2 :=
  if ℓ.val.2 = 0 then Inv.inv else id

/-- Per-link `condInvAtMinus ℓ` preserves `SU2_haar`. -/
lemma condInvAtMinus_measurePreserving
    (ℓ : Subtype (isMinusLink : LatticeLink L → Prop)) :
    MeasurePreserving (condInvAtMinus ℓ) SU2_haar SU2_haar := by
  unfold condInvAtMinus
  by_cases hd : ℓ.val.2 = 0
  · simp [hd]; exact SU2_measurePreserving_inv
  · simp [hd]; exact MeasurePreserving.id SU2_haar

/-- **Λ_- conditional-inversion map.** -/
def minusCondInv
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2) :
    Subtype (isMinusLink : LatticeLink L → Prop) → SU2 :=
  fun ℓ => condInvAtMinus ℓ (X ℓ)

/-- **`minusCondInv` preserves the Λ_- Pi Haar.** Direct via
`measurePreserving_pi` + per-link measure preservation. -/
theorem minusCondInv_measurePreserving :
    MeasurePreserving
      (minusCondInv :
        (Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
          → (Subtype (isMinusLink : LatticeLink L → Prop) → SU2))
      (Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) => SU2_haar))
      (Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) => SU2_haar)) :=
  measurePreserving_pi
    (μ := fun _ : Subtype (isMinusLink : LatticeLink L → Prop) => SU2_haar)
    (ν := fun _ : Subtype (isMinusLink : LatticeLink L → Prop) => SU2_haar)
    (f := condInvAtMinus)
    (fun ℓ => condInvAtMinus_measurePreserving ℓ)

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.condInvAtMinus
#print axioms PF.YangMills.condInvAtMinus_measurePreserving
#print axioms PF.YangMills.minusCondInv
#print axioms PF.YangMills.minusCondInv_measurePreserving
