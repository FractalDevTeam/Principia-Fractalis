/-
# Yang-Mills — Sector-swap Pi Haar measure-preserving

**Rio's §P3 ACER directive, 2026-10-23.** The `sectorSwapEquiv`
(`e028c251`) lifts to a measure-preserving map between the Λ_- and
Λ_+ Pi Haar measures via `measurePreserving_piCongrLeft`.

This is piece 1 of the Λ_- measure-preserving restriction needed for
the Fubini apply. Piece 2 is the per-link conditional inversion (on
temporal Λ_- links) — composed with this, it mirrors the full-field
`timeReflectionGaugeField_measurePreserving`.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-23.
-/
import PF.YangMills.WilsonSectorSwapBijection_2026_10_22
import PF.YangMills.SU2HaarUnimodular_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **Sector-swap Pi Haar measure-preserving.**

The `sectorSwapEquiv : {isMinusLink} ≃ {isPlusLink}` lifts to a
measure-preserving map from the Λ_- Pi Haar to the Λ_+ Pi Haar via
`MeasurableEquiv.piCongrLeft`. All links carry the same `SU2_haar`,
so the relabeling preserves the product measure. -/
theorem sectorSwap_measurePreserving (hL : Even L) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Subtype (isPlusLink : LatticeLink L → Prop) => SU2)
        (sectorSwapEquiv hL))
      (Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) => SU2_haar))
      (Measure.pi (fun _ : Subtype (isPlusLink : LatticeLink L → Prop) => SU2_haar)) :=
  measurePreserving_piCongrLeft
    (μ := fun _ : Subtype (isPlusLink : LatticeLink L → Prop) => SU2_haar)
    (sectorSwapEquiv hL)

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.sectorSwap_measurePreserving
