/-
# Yang-Mills — Refined Boltzmann plus-R: X-independence on the Λ_- glue

**Rio's §P3 ACER directive, 2026-10-23.** The refined counterpart to
`wilsonBoltzmann_plus_glue_eq_of_W` and `wilsonBoltzmann_plus_glue_factor_eq`
(`WilsonSectorGlueAction_2026_10_21.lean`, `4e5bbb10`).

### What this file provides

* `wilsonActionPlusR_glue_eq_of_W` (Even L): `S_+R(glue X_1 W) = S_+R(glue X_2 W)`.
* `wilsonBoltzmann_plusR_glue_eq_of_W` (Even L): the Boltzmann version.
* `wilsonBoltzmann_plusR_glue_factor_eq` (Even L): factor-through form via
  `supportedOnPlusZero_factor_eq`.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-23.
-/
import PF.YangMills.WilsonBoltzmannPlusR_2026_10_22
import PF.YangMills.WilsonSectorGlue_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **`S_+R(glue X W)` depends only on `W`.** -/
theorem wilsonActionPlusR_glue_eq_of_W (hL : Even L)
    (X₁ X₂ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    wilsonActionPlusR (gaugeFieldGlue X₁ W) = wilsonActionPlusR (gaugeFieldGlue X₂ W) := by
  apply wilsonActionPlusR_congr hL
  intro ℓ h_ne_minus
  have h_not_minus : ¬ isMinusLink ℓ := h_ne_minus
  rw [gaugeFieldGlue_apply_mnot X₁ W h_not_minus,
      gaugeFieldGlue_apply_mnot X₂ W h_not_minus]

/-- **`exp(-β S_+R(glue X W))` depends only on `W`.** -/
theorem wilsonBoltzmann_plusR_glue_eq_of_W (hL : Even L) (β : ℝ)
    (X₁ X₂ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    Real.exp (-β * wilsonActionPlusR (gaugeFieldGlue X₁ W))
      = Real.exp (-β * wilsonActionPlusR (gaugeFieldGlue X₂ W)) := by
  rw [wilsonActionPlusR_glue_eq_of_W hL X₁ X₂ W]

/-- **Refined Boltzmann plus-factor factors through `W` on the glue.** -/
theorem wilsonBoltzmann_plusR_glue_factor_eq (hL : Even L) (β : ℝ)
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    (Real.exp (-β * wilsonActionPlusR (gaugeFieldGlue X W)) : ℂ)
      = supportedOnPlusZero_factor
          (fun U => (Real.exp (-β * wilsonActionPlusR U) : ℂ)) W :=
  supportedOnPlusZero_factor_eq _
    (wilsonBoltzmann_plusR_supportedOnPlusZero hL β) X W

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonActionPlusR_glue_eq_of_W
#print axioms PF.YangMills.wilsonBoltzmann_plusR_glue_eq_of_W
#print axioms PF.YangMills.wilsonBoltzmann_plusR_glue_factor_eq
