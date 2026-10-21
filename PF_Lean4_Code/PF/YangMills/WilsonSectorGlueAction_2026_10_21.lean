/-
# Yang-Mills — Action + Boltzmann symmetries on glued sector configs

**Rio's §2 ACER directive, 2026-10-21.** Step 3 of the Fubini discharge
memo: how the sector action pieces `S_+`, `S_-` and the corresponding
Boltzmann factors behave under the glue parametrisation
`gaugeFieldGlue : (Λ_- → SU2) × (Λ_mnot → SU2) → GaugeField L`.

### What this file provides

* **`wilsonActionPlus_glue_eq_of_W`** — `S_+(glue X₁ W) = S_+(glue X₂ W)`
  for all `X₁ X₂`. Pure consequence of `wilsonActionPlus_congr` + the
  glue restriction identity on non-minus links.
* **`wilsonBoltzmann_plus_glue_eq_of_W`** — the Boltzmann plus-factor
  `exp(-β S_+(glue X W))` is `X`-independent.
* **`wilsonBoltzmann_plus_supportedOnPlusZero`** — the complex-valued
  lift of `exp(-β S_+)` is `supportedOnPlusZero`, i.e. it depends only on
  `Λ_+ ∪ Λ_0`.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonSectorGlue_2026_10_21
import PF.YangMills.WilsonFubiniFactorization_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — `wilsonActionPlus (gaugeFieldGlue X W)` is X-independent. -/

/-- **`S_+(glue X W)` depends only on `W`.** For any two Λ_- configs
`X₁, X₂` and any `W`, `wilsonActionPlus (gaugeFieldGlue X₁ W)
= wilsonActionPlus (gaugeFieldGlue X₂ W)`.

Proof: both glued fields agree on every non-minus link (= every link in
`Λ_+ ∪ Λ_0`), where they both read from `W`. Then
`wilsonActionPlus_congr` applies. -/
theorem wilsonActionPlus_glue_eq_of_W (hL : Even L)
    (X₁ X₂ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    wilsonActionPlus (gaugeFieldGlue X₁ W) = wilsonActionPlus (gaugeFieldGlue X₂ W) := by
  apply wilsonActionPlus_congr hL
  intro ℓ h_ne_minus
  have h_not_minus : ¬ isMinusLink ℓ := h_ne_minus
  rw [gaugeFieldGlue_apply_mnot X₁ W h_not_minus,
      gaugeFieldGlue_apply_mnot X₂ W h_not_minus]

/-! ## §2 — Boltzmann plus-factor on glued configs. -/

/-- **`exp(-β S_+(glue X W))` depends only on `W`.** -/
theorem wilsonBoltzmann_plus_glue_eq_of_W (hL : Even L) (β : ℝ)
    (X₁ X₂ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    Real.exp (-β * wilsonActionPlus (gaugeFieldGlue X₁ W))
      = Real.exp (-β * wilsonActionPlus (gaugeFieldGlue X₂ W)) := by
  rw [wilsonActionPlus_glue_eq_of_W hL X₁ X₂ W]

/-! ## §3 — The complex-valued Boltzmann plus-factor is `supportedOnPlusZero`. -/

/-- **`exp(-β S_+) : GaugeField L → ℂ` is `supportedOnPlusZero`.**

The complex lift of the Boltzmann plus-factor depends only on non-minus
links. Direct corollary of `wilsonActionPlus_congr`. This is the input
the Fubini factorization expects. -/
theorem wilsonBoltzmann_plus_supportedOnPlusZero (hL : Even L) (β : ℝ) :
    supportedOnPlusZero
      (fun U : GaugeField L => (Real.exp (-β * wilsonActionPlus U) : ℂ)) := by
  intro U₁ U₂ hAgree
  show (Real.exp (-β * wilsonActionPlus U₁) : ℂ)
      = (Real.exp (-β * wilsonActionPlus U₂) : ℂ)
  rw [wilsonActionPlus_congr hL U₁ U₂ hAgree]

/-! ## §4 — `exp(-β S_+)` factors through the Λ_mnot component on glue. -/

/-- **Boltzmann plus-factor factors through `W`.** Applying
`supportedOnPlusZero_factor_eq` to the (`supportedOnPlusZero`) Boltzmann
plus-factor: `exp(-β S_+(glue X W))` equals the factor-through value at `W`. -/
theorem wilsonBoltzmann_plus_glue_factor_eq (hL : Even L) (β : ℝ)
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    (Real.exp (-β * wilsonActionPlus (gaugeFieldGlue X W)) : ℂ)
      = supportedOnPlusZero_factor
          (fun U => (Real.exp (-β * wilsonActionPlus U) : ℂ)) W :=
  supportedOnPlusZero_factor_eq _
    (wilsonBoltzmann_plus_supportedOnPlusZero hL β) X W

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonActionPlus_glue_eq_of_W
#print axioms PF.YangMills.wilsonBoltzmann_plus_glue_eq_of_W
#print axioms PF.YangMills.wilsonBoltzmann_plus_supportedOnPlusZero
#print axioms PF.YangMills.wilsonBoltzmann_plus_glue_factor_eq
