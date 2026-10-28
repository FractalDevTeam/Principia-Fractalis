/-
# r362: the Λ_+ base-measure split, in iterated form

★ 2026-10-28 r362 — the `Λ_+` counterpart of the `Λ_-` split, taken to the
iterated integral ★

## What exists already, and what this adds

`WilsonSectorMeasureSplit_2026_10_20.lean:104` already proves
`wilsonBaseMeasure_integral_split`: for the **`isMinusLink`** partition, the
base integral equals an integral against the **product measure**, through the
`piEquivPiSubtypeProd` reparametrisation. Its own §4 note lists what the
remaining discharge still needs.

Two gaps this file closes, and they are the two the `Λ_+` route needs:

1. **The partition is `isMinusLink`, not `isPlusLink`.** `wilsonReducedPhiR`
   integrates over the `Λ_+` component (`WilsonReducedPhiR_2026_10_23.lean:53`),
   so the `Λ_+` instance is the one that can meet it.
2. **It stops at the product measure.** Fubini proper — the *iterated* integral
   `∫ V ∫ W` — is what lets the inner integral be recognised as `Φ`. That step
   needs integrability, which is where r361 comes in: continuity of the
   integrand gives it on the compact `GaugeField L`.

The measure-preserving lemma is proved here for an **arbitrary** decidable
predicate, so it covers both partitions and subsumes
`wilsonBaseMeasure_split_minus` as the `isMinusLink` instance.

## A correction to the roadmap in `WilsonRPFubiniApply_2026_10_21`

That file's step 4 note says "the sector action reflection identity is not yet
landed". **That is stale.** It was written 2026-10-21 and the identity landed
the same day:

    wilsonActionMinusR_timeReflection (hL : Even L) (U : GaugeField L) :
      wilsonActionMinusR (timeReflectionGaugeField U) = wilsonActionPlusR U

(`WilsonSectorRefinedSumIdentity_2026_10_21.lean:56`, verified present at this
pin). Step 4's ingredient exists; so do steps 1 and 3. Note that it carries
`Even L`, as does `minusToPlus_measurePreserving` — so the assembled `hFubini`
will carry `Even L` too, and that is a real hypothesis, not a formality.

## What is NOT claimed

**This does not discharge `hFubini`.** It supplies the `Λ_+` iterated split.
The assembly of steps 1–4 remains, and it is the step where the `Λ_-` integral
must be turned into `star Φ_i` by the inversion-invariance change of variable —
the one piece of the chain that is genuinely more than bookkeeping.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.YangMills.WilsonReducedPhiRIntegrable_r361
import PF.YangMills.WilsonSectorMeasureSplit_2026_10_20
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The glue is jointly continuous

r361 proved continuity in each variable separately, which is what
`continuous_of_dominated` consumed there. Product-measure Fubini needs the
joint statement. Proved through the existing `apply` lemmas, coordinate by
coordinate, rather than by unfolding the equivalence. -/

lemma gaugeFieldGluePlus_continuous :
    Continuous (fun z : (Subtype (isPlusLink : LatticeLink L → Prop) → SU2) ×
        (Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2) =>
      gaugeFieldGluePlus z.1 z.2) := by
  refine continuous_pi fun ℓ => ?_
  by_cases h : isPlusLink ℓ
  · simp only [gaugeFieldGluePlus_apply_plus _ _ h]
    exact (continuous_apply (⟨ℓ, h⟩ : Subtype (isPlusLink : LatticeLink L → Prop))).comp
      continuous_fst
  · simp only [gaugeFieldGluePlus_apply_pnot _ _ h]
    exact (continuous_apply (⟨ℓ, h⟩ : Subtype (fun ℓ : LatticeLink L =>
      ¬ isPlusLink ℓ))).comp continuous_snd

/-! ## §2 — The base measure is the product of the two sub-products

For an arbitrary decidable predicate. `wilsonBaseMeasure_split_minus` is the
`isMinusLink` instance of this. -/

lemma wilsonBase_measurePreserving_split
    (p : LatticeLink L → Prop) [DecidablePred p] :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : LatticeLink L => SU2) p)
      (wilsonBaseMeasure L)
      ((Measure.pi fun _ : Subtype p => SU2_haar).prod
        (Measure.pi fun _ : Subtype (fun ℓ => ¬ p ℓ) => SU2_haar)) :=
  measurePreserving_piEquivPiSubtypeProd (fun _ : LatticeLink L => SU2_haar) p

/-! ## §3 — The `Λ_+` split against the product measure

The `isPlusLink` counterpart of `wilsonBaseMeasure_integral_split`, written
through `gaugeFieldGluePlus` — which **is** the inverse of the partition
equivalence at `isPlusLink`, definitionally. Same proof shape as the `Λ_-`
version. -/

theorem wilsonBasePlus_integral_split_prod (F : GaugeField L → ℂ) :
    ∫ U, F U ∂(wilsonBaseMeasure L)
      = ∫ z, F (gaugeFieldGluePlus z.1 z.2)
          ∂((Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
                SU2_haar).prod
            (Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
                ¬ isPlusLink ℓ) => SU2_haar)) := by
  have hMP := wilsonBase_measurePreserving_split
    (isPlusLink : LatticeLink L → Prop) (L := L)
  have h := hMP.integral_comp'
    (g := fun z => F (gaugeFieldGluePlus z.1 z.2))
  simpa [gaugeFieldGluePlus, MeasurableEquiv.symm_apply_apply] using h

/-! ## §4 — The iterated form

This is the step the `Λ_-` version does not take. Integrability comes from
continuity on the compact product space, exactly as in r361. -/

/-- **★★★ r362: the `Λ_+` base integral as an iterated integral ★★★**

The inner integral is over the `Λ_+` component with the rest held fixed — the
shape `wilsonReducedPhiR` is defined by. -/
theorem wilsonBasePlus_integral_split_iterated
    (F : GaugeField L → ℂ) (hF : Continuous F) :
    ∫ U, F U ∂(wilsonBaseMeasure L)
      = ∫ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
          ∫ W : Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2,
            F (gaugeFieldGluePlus V W)
          ∂(Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
              ¬ isPlusLink ℓ) => SU2_haar)
        ∂(Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
            SU2_haar) := by
  have hcomp : Continuous (fun z : (Subtype (isPlusLink : LatticeLink L → Prop) → SU2) ×
      (Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2) =>
      F (gaugeFieldGluePlus z.1 z.2)) :=
    hF.comp gaugeFieldGluePlus_continuous
  have hint : Integrable (fun z => F (gaugeFieldGluePlus z.1 z.2))
      ((Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
          SU2_haar).prod
        (Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
            ¬ isPlusLink ℓ) => SU2_haar)) :=
    hcomp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [wilsonBasePlus_integral_split_prod F, integral_prod _ hint]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.gaugeFieldGluePlus_continuous
#print axioms PF.YangMills.wilsonBase_measurePreserving_split
#print axioms PF.YangMills.wilsonBasePlus_integral_split_prod
#print axioms PF.YangMills.wilsonBasePlus_integral_split_iterated
