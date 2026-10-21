/-
# Yang-Mills — Sector glue map + F-image under θ

**Rio's §2 ACER directive, 2026-10-21.** The next unlanded steps of the
sector-split Fubini chain (steps 2 and 4 of the Fubini discharge memo).

### What this file provides

* **Step 2 (glue map).** `gaugeFieldGlue : (Λ_minus → SU2) → (Λ_mnot → SU2)
   → GaugeField L`. The inverse of `piEquivPiSubtypeProd` on the sector
   split. Restriction identities on each sector.
* **Step 4 (F-image via support).** For `F` supportedOnPlusZero,
  `F (gaugeFieldGlue X W)` depends only on `W`, not `X`. The sector
  support hypothesis directly specializes to the glue parametrisation.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonFubiniApply_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The gauge-field glue map. -/

/-- **Glue a `Λ_-` config and a `Λ_mnot` config into a full gauge field.**
This is the inverse of the sector-split equivalence
`piEquivPiSubtypeProd` applied with the `isMinusLink` predicate. -/
noncomputable def gaugeFieldGlue
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    GaugeField L :=
  (MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : LatticeLink L => SU2)
    (isMinusLink : LatticeLink L → Prop)).symm (X, W)

/-- At a link `ℓ` with `isMinusLink ℓ` (in Λ_-), the glued field reads
from the `X` component. -/
lemma gaugeFieldGlue_apply_minus
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2)
    {ℓ : LatticeLink L} (h : isMinusLink ℓ) :
    gaugeFieldGlue X W ℓ = X ⟨ℓ, h⟩ := by
  simp [gaugeFieldGlue, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd_symm_apply, h]

/-- At a link `ℓ` with `¬ isMinusLink ℓ` (in Λ_+ ∪ Λ_0), the glued field
reads from the `W` component. -/
lemma gaugeFieldGlue_apply_mnot
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2)
    {ℓ : LatticeLink L} (h : ¬ isMinusLink ℓ) :
    gaugeFieldGlue X W ℓ = W ⟨ℓ, h⟩ := by
  simp [gaugeFieldGlue, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd_symm_apply, h]

/-! ## §2 — Measurability of the glue map. -/

/-- `gaugeFieldGlue` is measurable as a map from the product measurable
space to the gauge-field measurable space. -/
lemma gaugeFieldGlue_measurable :
    Measurable (fun p : _ × _ =>
      gaugeFieldGlue (L := L) p.1 p.2) := by
  unfold gaugeFieldGlue
  exact (MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : LatticeLink L => SU2)
    (isMinusLink : LatticeLink L → Prop)).symm.measurable

/-! ## §3 — F-image under glue + support. -/

/-- **Step 4: F-image via `supportedOnPlusZero`.** If `F` is supported on
`Λ_+ ∪ Λ_0`, then `F (gaugeFieldGlue X W)` is independent of the Λ_-
component `X`, depending only on `W`.

Formal statement: for any two Λ_- configurations `X₁, X₂`,
`F (gaugeFieldGlue X₁ W) = F (gaugeFieldGlue X₂ W)`.

Proof: `supportedOnPlusZero` requires agreement on all non-`minus`
links; both glued fields agree on `W` (= all non-`minus` links). -/
theorem supportedOnPlusZero_glue
    (F : GaugeField L → ℂ) (hF : supportedOnPlusZero F)
    (X₁ X₂ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    F (gaugeFieldGlue X₁ W) = F (gaugeFieldGlue X₂ W) := by
  apply hF
  intro ℓ h_ne_minus
  -- `h_ne_minus : linkSector ℓ ≠ LinkSector.minus`
  -- Equivalently: `¬ isMinusLink ℓ`.
  have h_not_minus : ¬ isMinusLink ℓ := h_ne_minus
  rw [gaugeFieldGlue_apply_mnot X₁ W h_not_minus,
      gaugeFieldGlue_apply_mnot X₂ W h_not_minus]

/-- **F supportedOnPlusZero factors through the Λ_mnot component.** For
each such `F`, there is a function `F' : (Λ_mnot → SU2) → ℂ` such that
`F (gaugeFieldGlue X W) = F' W` for all `X, W`. (The classical choice
pins the function by evaluation at an arbitrary Λ_- config.) -/
noncomputable def supportedOnPlusZero_factor
    (F : GaugeField L → ℂ) :
    (Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) → ℂ :=
  fun W =>
    -- Evaluate F at a glued field with an arbitrary Λ_- config.
    -- By `supportedOnPlusZero`, the specific choice doesn't matter;
    -- we use the arbitrary-choice-via-classical constant.
    F (gaugeFieldGlue (fun _ => (1 : SU2)) W)

/-- The factorization is exact: `F (gaugeFieldGlue X W) = (factor F) W`. -/
theorem supportedOnPlusZero_factor_eq
    (F : GaugeField L → ℂ) (hF : supportedOnPlusZero F)
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    F (gaugeFieldGlue X W) = supportedOnPlusZero_factor F W := by
  unfold supportedOnPlusZero_factor
  exact supportedOnPlusZero_glue F hF X _ W

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.gaugeFieldGlue
#print axioms PF.YangMills.gaugeFieldGlue_apply_minus
#print axioms PF.YangMills.gaugeFieldGlue_apply_mnot
#print axioms PF.YangMills.gaugeFieldGlue_measurable
#print axioms PF.YangMills.supportedOnPlusZero_glue
#print axioms PF.YangMills.supportedOnPlusZero_factor
#print axioms PF.YangMills.supportedOnPlusZero_factor_eq
