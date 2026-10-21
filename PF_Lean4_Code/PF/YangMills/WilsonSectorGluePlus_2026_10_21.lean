/-
# Yang-Mills — Λ_+ side glue (parallel to Λ_- side glue)

**Rio's §2 ACER directive, 2026-10-21.** Step 5 scaffold: the Fubini
discharge of `wilson_reflection_positivity` constructs `Φ_i : GaugeField L → ℂ`
as a partial integral over the Λ_+ component. To express that integral
cleanly, we need a glue map on the Λ_+ side analogous to the Λ_- side
glue (`gaugeFieldGlue` at `c5080d4b`).

### What this file provides

* **`isPlusLink`** — decidable predicate `linkSector ℓ = LinkSector.plus`.
* **`gaugeFieldGluePlus`** — glue
  `(Λ_+ → SU2) → (Λ_pnot → SU2) → GaugeField L`
  via `MeasurableEquiv.piEquivPiSubtypeProd` with `isPlusLink`.
* **`gaugeFieldGluePlus_apply_plus`** / **`_apply_pnot`** — restriction
  identities.
* **`gaugeFieldGluePlus_measurable`** — product-measurability.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonSectorGlue_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The `linkSector = plus` predicate. -/

/-- `isPlusLink ℓ`: the link `ℓ` lies in `Λ_+`. -/
def isPlusLink (ℓ : LatticeLink L) : Prop := linkSector ℓ = LinkSector.plus

instance isPlusLink_decidable (ℓ : LatticeLink L) : Decidable (isPlusLink ℓ) := by
  unfold isPlusLink; infer_instance

/-! ## §2 — The Λ_+ side glue. -/

/-- **Glue a `Λ_+` config and a `Λ_pnot` config into a full gauge field.**
Analogue of `gaugeFieldGlue` with `isPlusLink` instead of `isMinusLink`. -/
noncomputable def gaugeFieldGluePlus
    (V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2) :
    GaugeField L :=
  (MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : LatticeLink L => SU2)
    (isPlusLink : LatticeLink L → Prop)).symm (V, W)

/-- At a link `ℓ` with `isPlusLink ℓ`, the glued field reads from `V`. -/
lemma gaugeFieldGluePlus_apply_plus
    (V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2)
    {ℓ : LatticeLink L} (h : isPlusLink ℓ) :
    gaugeFieldGluePlus V W ℓ = V ⟨ℓ, h⟩ := by
  simp [gaugeFieldGluePlus, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd_symm_apply, h]

/-- At a link `ℓ` with `¬ isPlusLink ℓ`, the glued field reads from `W`. -/
lemma gaugeFieldGluePlus_apply_pnot
    (V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2)
    {ℓ : LatticeLink L} (h : ¬ isPlusLink ℓ) :
    gaugeFieldGluePlus V W ℓ = W ⟨ℓ, h⟩ := by
  simp [gaugeFieldGluePlus, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd_symm_apply, h]

/-! ## §3 — Measurability of the Λ_+ glue. -/

/-- `gaugeFieldGluePlus` is measurable on the product space. -/
lemma gaugeFieldGluePlus_measurable :
    Measurable (fun p : _ × _ =>
      gaugeFieldGluePlus (L := L) p.1 p.2) := by
  unfold gaugeFieldGluePlus
  exact (MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : LatticeLink L => SU2)
    (isPlusLink : LatticeLink L → Prop)).symm.measurable

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.isPlusLink
#print axioms PF.YangMills.gaugeFieldGluePlus
#print axioms PF.YangMills.gaugeFieldGluePlus_apply_plus
#print axioms PF.YangMills.gaugeFieldGluePlus_apply_pnot
#print axioms PF.YangMills.gaugeFieldGluePlus_measurable
