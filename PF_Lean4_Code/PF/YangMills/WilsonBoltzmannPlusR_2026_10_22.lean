/-
# Yang-Mills — Refined Boltzmann plus-factor: congruence + supportedOnPlusZero

**Rio's §2 ACER directive, 2026-10-22.** Refined analogs of
`wilsonBoltzmann_plus_congr` + `wilsonBoltzmann_plus_supportedOnPlusZero`
(`WilsonFubiniFactorization_2026_10_20.lean` `f852724c` /
`WilsonSectorGlueAction_2026_10_21.lean` `4e5bbb10`).

### What this file provides

* **`wilsonBoltzmann_plusR_congr` (Even L)** — refined Boltzmann
  plus-factor is X-independent on non-minus agreement.
* **`wilsonBoltzmann_plusR_supportedOnPlusZero` (Even L)** — complex
  lift is `supportedOnPlusZero`.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-22.
-/
import PF.YangMills.WilsonSectorRefinedGaugeDependence_2026_10_22
import PF.YangMills.WilsonReflectionPositivity_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **Refined Boltzmann plus-factor congruence on non-minus agreement.** -/
theorem wilsonBoltzmann_plusR_congr (hL : Even L) (β : ℝ) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.minus → U₁ ℓ = U₂ ℓ) :
    Real.exp (-β * wilsonActionPlusR U₁) = Real.exp (-β * wilsonActionPlusR U₂) := by
  rw [wilsonActionPlusR_congr hL U₁ U₂ hAgree]

/-- **Complex lift of refined Boltzmann plus-factor is `supportedOnPlusZero`.** -/
theorem wilsonBoltzmann_plusR_supportedOnPlusZero (hL : Even L) (β : ℝ) :
    supportedOnPlusZero
      (fun U : GaugeField L => (Real.exp (-β * wilsonActionPlusR U) : ℂ)) := by
  intro U₁ U₂ hAgree
  show (Real.exp (-β * wilsonActionPlusR U₁) : ℂ)
      = (Real.exp (-β * wilsonActionPlusR U₂) : ℂ)
  rw [wilsonActionPlusR_congr hL U₁ U₂ hAgree]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonBoltzmann_plusR_congr
#print axioms PF.YangMills.wilsonBoltzmann_plusR_supportedOnPlusZero
