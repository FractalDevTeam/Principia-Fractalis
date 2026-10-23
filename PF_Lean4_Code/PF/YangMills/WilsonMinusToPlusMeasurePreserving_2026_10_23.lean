/-
# Yang-Mills — Λ_- → Λ_+ measure-preserving map (step 6)

**Rio's §P3 ACER directive, 2026-10-23.** Compose
`minusCondInv` + `piCongrLeft(sectorSwap)` to get the full
measure-preserving map

  `minusToPlus : (Λ_- → SU2) → (Λ_+ → SU2)`
  `minusToPlus X ℓ_plus = (X (linkTheta ℓ_plus))⁻¹`  on temporal `ℓ_plus`
  `minusToPlus X ℓ_plus = X (linkTheta ℓ_plus)`      on spatial `ℓ_plus`

This is the restriction of the full-field `timeReflectionGaugeField`
to the sector-swap bijection between the Λ_- and Λ_+ half-fields.
Mirrors `WilsonReflectionMeasurePreservingApply` §4-§7, restricted.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-23.
-/
import PF.YangMills.WilsonMinusCondInv_2026_10_23
import PF.YangMills.WilsonSectorSwapMeasurePreserving_2026_10_23

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **The full Λ_- → Λ_+ map: conditional-invert, then relabel via sector-swap.** -/
noncomputable def minusToPlus (hL : Even L)
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2) :
    Subtype (isPlusLink : LatticeLink L → Prop) → SU2 :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : Subtype (isPlusLink : LatticeLink L → Prop) => SU2)
    (sectorSwapEquiv hL)) (minusCondInv X)

/-- **`minusToPlus` is measure-preserving on the Pi Haar.** -/
theorem minusToPlus_measurePreserving (hL : Even L) :
    MeasurePreserving (minusToPlus hL)
      (Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) => SU2_haar))
      (Measure.pi (fun _ : Subtype (isPlusLink : LatticeLink L → Prop) => SU2_haar)) := by
  unfold minusToPlus
  exact (sectorSwap_measurePreserving hL).comp minusCondInv_measurePreserving

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.minusToPlus
#print axioms PF.YangMills.minusToPlus_measurePreserving
