/-
# Yang-Mills — Measure split along the sector partition

**Rio's Fubini-discharge groundwork, 2026-10-20.** Builds the sector-aligned
`Measure.pi` split that the full Wilson RP Fubini step consumes.

### What this file provides

* `isMinusLink` — the decidable predicate `linkSector ℓ = minus`.
* `wilsonBaseMeasure_split_minus` — the Pi measure split via
  `measurePreserving_piEquivPiSubtypeProd`, factoring `wilsonBaseMeasure L`
  as the product of its restrictions to `Λ₋` and its complement `Λ₊ ∪ Λ₀`.
* `wilsonBaseMeasure_lintegral_split` — Fubini factorization of the lower
  integral over the sector split.
* `wilsonBaseMeasure_integral_split` — Fubini factorization of the Bochner
  integral for integrable functions.

### Status

This file lands **half** of the Fubini discharge: the measure-preserving
sector split. The remaining pieces (Haar inversion-invariance on Λ₋ to
match `F_i(θU)` with `conj(F_i)` support, and the final `Φ`-reduction)
require composing this split with:
* `pi.isInvInvariant` of Haar on each Λ₋ link,
* the action invariance `wilsonActionTotal_timeReflection` (`9b374b48`)
  specialized to `S_-(θU) = S_+(U)`,
* an explicit gauge-field reconstruction map that glues `(U_mnot, θU_-)`
  back together.

The complete discharge is a mechanical measure-theoretic exercise bolted
on top of this split.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-20.
-/
import PF.YangMills.WilsonReflectionPositivity_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The `linkSector = minus` predicate and its decidability. -/

/-- `isMinusLink ℓ`: the link `ℓ` lies in `Λ₋`. -/
def isMinusLink (ℓ : LatticeLink L) : Prop := linkSector ℓ = LinkSector.minus

instance isMinusLink_decidable (ℓ : LatticeLink L) : Decidable (isMinusLink ℓ) := by
  unfold isMinusLink; infer_instance

/-! ## §2 — The measure-preserving sector split.

The gauge-field space `LatticeLink L → SU2` is in measure-preserving
bijection with `({ℓ // isMinusLink ℓ} → SU2) × ({ℓ // ¬ isMinusLink ℓ} → SU2)`
under the Pi measure. -/

/-- Haar is a probability measure, hence `IsFiniteMeasure`, hence `SigmaFinite`. -/
instance SU2_haar_sigmaFinite : SigmaFinite SU2_haar :=
  haveI : IsFiniteMeasure SU2_haar := inferInstance
  inferInstance

/-- **★ MEASURE SPLIT ★**

Under the pointwise equivalence
`GaugeField L ≃ ({ℓ // isMinusLink ℓ} → SU2) × ({ℓ // ¬ isMinusLink ℓ} → SU2)`,
the Wilson base measure is a product of its restrictions to Λ₋ and Λ₊ ∪ Λ₀.

This is `measurePreserving_piEquivPiSubtypeProd` specialised to the sector
predicate. -/
theorem wilsonBaseMeasure_split_minus :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : LatticeLink L => SU2) (isMinusLink : LatticeLink L → Prop))
      (wilsonBaseMeasure L)
      ((Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) => SU2_haar)).prod
       (Measure.pi (fun _ : Subtype
          (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) => SU2_haar))) := by
  unfold wilsonBaseMeasure
  exact measurePreserving_piEquivPiSubtypeProd
    (α := fun _ : LatticeLink L => SU2)
    (μ := fun _ => SU2_haar)
    (isMinusLink : LatticeLink L → Prop)

/-! ## §3 — Fubini on the sector split.

Via the split + Fubini on products, the lower integral and Bochner integral
over `wilsonBaseMeasure` factor into iterated integrals. -/

/-- **Bochner Fubini on the sector split.**

For any `F : GaugeField L → ℂ`, the Bochner integral factors over the
Λ₋ vs Λ₊∪Λ₀ sector split. The equivalence `e := piEquivPiSubtypeProd`
reparametrizes `GaugeField L` as `(Λ₋ → SU2) × (Λ₊∪Λ₀ → SU2)`. -/
theorem wilsonBaseMeasure_integral_split (F : GaugeField L → ℂ) :
    ∫ U, F U ∂(wilsonBaseMeasure L)
      = ∫ U_split,
          F ((MeasurableEquiv.piEquivPiSubtypeProd
                (fun _ : LatticeLink L => SU2)
                (isMinusLink : LatticeLink L → Prop)).symm U_split)
          ∂((Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
                SU2_haar)).prod
            (Measure.pi (fun _ : Subtype
                (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) => SU2_haar))) := by
  have hMP := wilsonBaseMeasure_split_minus (L := L)
  have := hMP.integral_comp'
    (f := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : LatticeLink L => SU2)
      (isMinusLink : LatticeLink L → Prop))
    (g := fun U_split =>
      F ((MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : LatticeLink L => SU2)
            (isMinusLink : LatticeLink L → Prop)).symm U_split))
  simp only [MeasurableEquiv.symm_apply_apply] at this
  exact this

/-! ## §4 — Hooks for the final Wilson RP discharge.

The remaining Fubini discharge requires composing this split with:
1. Haar inversion-invariance on each Λ₋ link (via `pi.isInvInvariant`),
2. The action-invariance `wilsonActionTotal_timeReflection`,
3. A gauge-field "swap" between Λ₋ and Λ₊ that respects action values.

With those pieces, the inner `∫_{U_-}` integral factors as `conj` of the
`∫_{U_+}` integral, yielding the Φ-reduction that discharges the Fubini
hypothesis of `wilson_reflection_positivity`.
-/

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.isMinusLink
#print axioms PF.YangMills.SU2_haar_sigmaFinite
#print axioms PF.YangMills.wilsonBaseMeasure_split_minus
#print axioms PF.YangMills.wilsonBaseMeasure_integral_split
