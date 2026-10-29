/-
# r382: the `W`-side ingredients — a documented-but-absent lemma, supplied

★ 2026-10-29 r382 — `wilsonActionZero_congr`, the refined factorisation, and the
`Λ_-` iterated split ★

## A header that promised a lemma the tree does not contain

`WilsonSectorRefinedGaugeDependence_2026_10_22.lean`'s own header lists three
results:

> * `wilsonActionPlusR_congr` (Even L) …
> * `wilsonActionMinusR_congr` (Even L): symmetric, S_-R depends only on …
> * `wilsonActionZero_congr` (Even L): S_0 depends only on `Λ_0`.

The first two are declared in that file. **The third is declared nowhere in the
repository** — searched by both `theorem` and `lemma` across the whole tree. It
is needed by the `W`-side of the `hFubini` assembly, because the refined
factorisation produces an `exp(-β S_0)` factor that has to be pulled out of the
`Λ_-` inner integral, and that needs `S_0` to be blind to the `Λ_-` links.

So it is supplied here. The statement proved is the one the assembly needs,
which is slightly stronger in form than the header's phrasing: `S_0` depends
only on the **non-minus** links. (Blindness to `Λ_-` is what gets used; the
header's "depends only on `Λ_0`" is also true and follows, since the proof shows
every link of a zero-plaquette is itself in `Λ_0`.)

**It needs no `Even L`.** The header attributes `Even L` to it; the proof does
not use it. `isZeroPlaquette` already pins the base time to `0` or `L/2`
explicitly, so no parity argument is required.

## Why it is true

`isZeroPlaquette p` says `p` is purely spatial (`μ ≠ 0`, `ν ≠ 0`, `μ ≠ ν`) with
base time `0` or `L/2`. All four of its links are therefore spatial, and all sit
at the *same* time as the base, because shifting a site in a spatial direction
does not move coordinate `0` (`shiftSite_spatial_time_val`). And `linkSector`
sends a spatial link at time `0` or `L/2` to `zero`. So every link of a
zero-plaquette is in `Λ_0`, hence not in `Λ_-`.

The one place this could have failed is the `L/2` boundary: a plaquette based at
time `L/2` has binary `plaquetteSector = minus`, so `no_straddling` alone would
only say its links are `minus` or `zero` — not enough. The direct computation
avoids `no_straddling` entirely and gets `zero` outright, which is why the
spatiality clause of `isZeroPlaquette` is load-bearing rather than decorative.

## What is proved

* **`wilsonActionZero_congr`** — the absent lemma;
* `wilsonActionZero_glue_eq_of_W`, `wilsonBoltzmann_zero_glue_eq_of_W` — its glue
  corollaries, matching the shape of `WilsonBoltzmannPlusRGlue_2026_10_23`;
* `wilsonBoltzmann_factorize_refined` — `exp(-β S) = exp(-β S_+R) · exp(-β S_0) ·
  exp(-β S_-R)`, the refined counterpart of the landed binary factorisation.
  The binary one cannot serve the `Φ_R` route, since `Φ_R` is built on `S_+R`;
* `gaugeFieldGlue_continuous` — the `Λ_-` counterpart of r362's
  `gaugeFieldGluePlus_continuous`;
* **`wilsonBaseMinus_integral_split_iterated`** — the base integral as an
  iterated integral with the `Λ_-` component **inner**, which is the order step 4
  consumes. r362 supplied the `Λ_+` instance with the other nesting; this is
  `integral_prod_symm` rather than `integral_prod`.

## What is NOT claimed

This file is ingredients, not the assembly. `hFubini` is not discharged here and
neither is any further step of its chain; step 4 is r381's and remains the only
step of the four that is closed. No mass-gap claim and no Clay claim.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.YangMills.WilsonFubiniStep4_r381
import PF.YangMills.WilsonSectorRefinedGaugeDependence_2026_10_22
import PF.YangMills.WilsonActionSectorDecomp3Way_2026_10_22
import PF.YangMills.WilsonFubiniFactorization_2026_10_20
import PF.YangMills.WilsonBaseMeasureSplit_r362
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — `wilsonActionZero_congr`: the documented-but-absent lemma

Every link of a zero-plaquette is itself in `Λ_0`. Proved by direct computation
rather than through `no_straddling`, which is too weak at the `L/2` boundary —
see the header. -/

omit [NeZero L] in
/-- A spatial link at boundary time lies in `Λ_0`. -/
lemma linkSector_spatial_boundary {x : LatticeSite L} {d : LatticeDir}
    (hd : d ≠ 0) (ht : (x 0).val = 0 ∨ (x 0).val = L / 2) :
    linkSector ((x, d) : LatticeLink L) = LinkSector.zero := by
  simp only [linkSector, hd, if_false]
  exact if_pos ht

/-- **`S_0` depends only on the non-minus links.**

Supplies the lemma named in `WilsonSectorRefinedGaugeDependence_2026_10_22`'s
header and absent from the tree. No `Even L` is needed: `isZeroPlaquette`
pins the base time explicitly. -/
theorem wilsonActionZero_congr (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L,
      linkSector ℓ ≠ LinkSector.minus → U₁ ℓ = U₂ ℓ) :
    wilsonActionZero U₁ = wilsonActionZero U₂ := by
  unfold wilsonActionZero
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hμ, hν, _hμν, ht⟩ := (plaquetteSectorRefined_eq_zero_iff p).mp hp
  rcases p with ⟨x, μ, ν⟩
  simp only at hμ hν ht
  refine wilsonActionDensity_congr _ _ _ ?_ ?_ ?_ ?_
  · exact hAgree _ (by rw [linkSector_spatial_boundary hμ ht]; decide)
  · refine hAgree _ (by
      rw [linkSector_spatial_boundary hν
        (by rwa [shiftSite_spatial_time_val hμ])]
      decide)
  · refine hAgree _ (by
      rw [linkSector_spatial_boundary hμ
        (by rwa [shiftSite_spatial_time_val hν])]
      decide)
  · exact hAgree _ (by rw [linkSector_spatial_boundary hν ht]; decide)

/-- **`S_0 (glue X W)` depends only on `W`.** -/
theorem wilsonActionZero_glue_eq_of_W
    (X₁ X₂ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    wilsonActionZero (gaugeFieldGlue X₁ W)
      = wilsonActionZero (gaugeFieldGlue X₂ W) := by
  refine wilsonActionZero_congr _ _ fun ℓ h_ne_minus => ?_
  have h_not_minus : ¬ isMinusLink ℓ := h_ne_minus
  rw [gaugeFieldGlue_apply_mnot X₁ W h_not_minus,
    gaugeFieldGlue_apply_mnot X₂ W h_not_minus]

/-- **`exp(-β S_0 (glue X W))` depends only on `W`.** -/
theorem wilsonBoltzmann_zero_glue_eq_of_W (β : ℝ)
    (X₁ X₂ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    Real.exp (-β * wilsonActionZero (gaugeFieldGlue X₁ W))
      = Real.exp (-β * wilsonActionZero (gaugeFieldGlue X₂ W)) := by
  rw [wilsonActionZero_glue_eq_of_W X₁ X₂ W]

/-! ## §2 — The refined Boltzmann factorisation

The landed factorisation (`wilsonBoltzmann_factorize_real`) is binary,
`exp(-β S_+) · exp(-β S_-)`. `Φ_R` is built on the *refined* `S_+R`, so the
three-factor form is what the `Φ_R` route consumes. -/

/-- **`exp(-β S) = exp(-β S_+R) · exp(-β S_0) · exp(-β S_-R)`.** -/
theorem wilsonBoltzmann_factorize_refined (β : ℝ) (U : GaugeField L) :
    Real.exp (-β * wilsonActionTotal U)
      = Real.exp (-β * wilsonActionPlusR U)
        * Real.exp (-β * wilsonActionZero U)
        * Real.exp (-β * wilsonActionMinusR U) := by
  rw [wilsonActionTotal_sector_decomposition_refined, mul_add, mul_add,
    Real.exp_add, Real.exp_add]

/-! ## §3 — The `Λ_-` iterated split, with `Λ_-` inner

r362 gave the `Λ_+` instance with the `Λ_+` component **outer**. Step 4 reads an
integral whose `Λ_-` component is **inner**, so the nesting here is the other
way round: `integral_prod_symm` in place of `integral_prod`. -/

/-- The `Λ_-` glue is jointly continuous. The `Λ_-` counterpart of r362's
`gaugeFieldGluePlus_continuous`, same proof shape. -/
lemma gaugeFieldGlue_continuous :
    Continuous (fun z : (Subtype (isMinusLink : LatticeLink L → Prop) → SU2) ×
        (Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) =>
      gaugeFieldGlue z.1 z.2) := by
  refine continuous_pi fun ℓ => ?_
  by_cases h : isMinusLink ℓ
  · simp only [gaugeFieldGlue_apply_minus _ _ h]
    exact (continuous_apply
      (⟨ℓ, h⟩ : Subtype (isMinusLink : LatticeLink L → Prop))).comp continuous_fst
  · simp only [gaugeFieldGlue_apply_mnot _ _ h]
    exact (continuous_apply
      (⟨ℓ, h⟩ : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ))).comp
      continuous_snd

/-- **★ r382: the base integral with the `Λ_-` component inner ★** -/
theorem wilsonBaseMinus_integral_split_iterated
    (F : GaugeField L → ℂ) (hF : Continuous F) :
    ∫ U, F U ∂(wilsonBaseMeasure L)
      = ∫ W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2,
          ∫ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
            F (gaugeFieldGlue X W)
          ∂(Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
              SU2_haar)
        ∂(Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
            ¬ isMinusLink ℓ) => SU2_haar) := by
  have hMP := wilsonBase_measurePreserving_split
    (isMinusLink : LatticeLink L → Prop) (L := L)
  have hsplit : ∫ U, F U ∂(wilsonBaseMeasure L)
      = ∫ z, F (gaugeFieldGlue z.1 z.2)
        ∂((Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
              SU2_haar).prod
          (Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
              ¬ isMinusLink ℓ) => SU2_haar)) := by
    simpa [gaugeFieldGlue, MeasurableEquiv.symm_apply_apply] using
      hMP.integral_comp' (g := fun z => F (gaugeFieldGlue z.1 z.2))
  have hcomp : Continuous
      (fun z : (Subtype (isMinusLink : LatticeLink L → Prop) → SU2) ×
          (Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) =>
        F (gaugeFieldGlue z.1 z.2)) := hF.comp gaugeFieldGlue_continuous
  have hint : Integrable (fun z => F (gaugeFieldGlue z.1 z.2))
      ((Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
          SU2_haar).prod
        (Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
            ¬ isMinusLink ℓ) => SU2_haar)) :=
    hcomp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hsplit, integral_prod_symm _ hint]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.linkSector_spatial_boundary
#print axioms PF.YangMills.wilsonActionZero_congr
#print axioms PF.YangMills.wilsonActionZero_glue_eq_of_W
#print axioms PF.YangMills.wilsonBoltzmann_zero_glue_eq_of_W
#print axioms PF.YangMills.wilsonBoltzmann_factorize_refined
#print axioms PF.YangMills.gaugeFieldGlue_continuous
#print axioms PF.YangMills.wilsonBaseMinus_integral_split_iterated
