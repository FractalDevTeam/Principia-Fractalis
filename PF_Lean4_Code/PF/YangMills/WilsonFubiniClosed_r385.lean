/-
# r385: `hFubini` discharged with the corrected `Φ`, and Wilson RP made unconditional

★ 2026-10-29 r385 — the boundary weight placed, and the lane's headline closed ★

## What this file does

r383 reduced `hFubini`'s left side; r384 showed θ is the identity on `Λ_0` and
`Φ_R` is θ-invariant, isolating the discrepancy to a factor `exp(-β S_0)`. This
file closes the accounting as a machine-checked identity, places the boundary
weight where it belongs, and discharges `hFubini` — which makes
`wilson_reflection_positivity` **unconditional** for continuous test functions
supported on `Λ_+ ∪ Λ_0`, over an even lattice.

    ∫ U, star (F_i (θ U)) · F_j U  ∂μ_Gibbs
      = ∫ U, exp(-β S_0 U) · star (Φ_R β F_i U) · Φ_R β F_j U  ∂μ_base

and with `Φ_i := exp(-β S_0 / 2) · Φ_R β F_i` that is exactly `hFubini`'s shape,
because the two half-weights multiply back to `exp(-β S_0)`.

**So the `exp(-β S_0)` discrepancy was real, and it was a defect in the
*placement* of the boundary weight, not in the mathematics.** The repair is
additive: `Φ_R` keeps every theorem it had, and the corrected `Φ` is a new
definition on top of it.

## The nested split turned out to be avoidable

r383 and r384 both recorded the remaining obstacle as a
`¬Λ_- ≃ Λ_+ × Λ_0` sub-split — a nested-subtype construction. **It is not
needed**, and saying why is the one idea in this file.

An integral over the `¬Λ_-` component of a function that is *blind* to `Λ_-`
equals the integral of that function over the whole base measure: split the base
over `Λ_-`, and the inner integral is a constant against a probability measure.
That converts a subtype integral back into a full base integral, where the
*already landed* `Λ_+` split applies directly. So the two splits are composed
through the full space instead of being nested inside one another, and no
subtype-of-subtype equivalence is ever formed.

The route is: `¬Λ_-` integral → base integral (`Λ_-`-blind) → `Λ_+` split →
recognise `Φ_R` → base integral (`Λ_+`-blind). Each arrow is one lemma below.

## `Even L`, and what the headline costs

`Even L` is carried throughout, inherited from `sectorSwapEquiv` (via r380) and
`linkSector_linkTheta`. It is a genuine restriction on the lattice and the
headline states it. Also stated: continuity of the test functions, and their
support in `Λ_+ ∪ Λ_0`, which is reflection positivity's own premise rather than
a gap. There is no remaining hypothesis of Fubini or integrability type.

## What is NOT claimed

Not a mass gap, and not any Clay statement. This is reflection positivity for
the Wilson action on a finite even periodic lattice — one input to a
constructive programme whose later steps (transfer matrix, thermodynamic limit,
spectral gap) are separately scoped and untouched here.

Nothing previously deployed is weakened. `wilson_reflection_positivity` and
`wilsonReducedPhiR` are used exactly as they stand. The specialisation
`wilson_reflection_positivity_withReducedPhiR` is **not** touched: its `Φ`
carries no boundary weight, and whether to restate it is the author's call, not
this file's.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.YangMills.WilsonPhiThetaInvariant_r384
import PF.YangMills.WilsonSectorActionBounded_r360
import PF.YangMills.WilsonReflectionPositivity_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory
open scoped ComplexOrder

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — `S_0` reads only `Λ_0`

r382 proved blindness to `Λ_-`, which is what its own assembly needed. The
`Λ_+`-blindness used here needs the sharper form: agreement on `Λ_0` alone. Same
proof — every link of a zero-plaquette is itself in `Λ_0`, so the four side
conditions are discharged by `linkSector_spatial_boundary` outright instead of
being weakened to `≠ minus` first. -/

/-- **`S_0` depends only on the `Λ_0` links.** -/
theorem wilsonActionZero_congr_of_zero (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L,
      linkSector ℓ = LinkSector.zero → U₁ ℓ = U₂ ℓ) :
    wilsonActionZero U₁ = wilsonActionZero U₂ := by
  unfold wilsonActionZero
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hμ, hν, _hμν, ht⟩ := (plaquetteSectorRefined_eq_zero_iff p).mp hp
  rcases p with ⟨x, μ, ν⟩
  simp only at hμ hν ht
  refine wilsonActionDensity_congr _ _ _ ?_ ?_ ?_ ?_
  · exact hAgree _ (linkSector_spatial_boundary hμ ht)
  · exact hAgree _ (linkSector_spatial_boundary hν
      (by rwa [shiftSite_spatial_time_val hμ]))
  · exact hAgree _ (linkSector_spatial_boundary hμ
      (by rwa [shiftSite_spatial_time_val hν]))
  · exact hAgree _ (linkSector_spatial_boundary hν ht)

/-! ## §2 — Blindness collapses a sector integral into a base integral

The two arrows that make the nested split unnecessary, plus the `Λ_+` split in
the nesting this file consumes. -/

/-- `restrictNonPlus` of a `Λ_+` glue is its `W` component. The plus-side
counterpart of r383's `restrictNonMinus_gaugeFieldGlue`; neither this nor its
mirror was in the tree. -/
lemma restrictNonPlus_gaugeFieldGluePlus
    (V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2) :
    restrictNonPlus (gaugeFieldGluePlus V W) = W := by
  funext ℓ
  exact gaugeFieldGluePlus_apply_pnot V W ℓ.property

/-- `star` fixes a real coercion. Stated so that rewriting never has to leave
the goal stranded between `star` and `starRingEnd`. -/
lemma star_ofReal_complex (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The base integral with the `Λ_+` component **inner**. Mirror of r382's
minus-side lemma. -/
theorem wilsonBasePlus_integral_split_iterated_symm
    (K : GaugeField L → ℂ) (hK : Continuous K) :
    ∫ U, K U ∂(wilsonBaseMeasure L)
      = ∫ W : Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2,
          ∫ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
            K (gaugeFieldGluePlus V W)
          ∂(Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
              SU2_haar)
        ∂(Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
            ¬ isPlusLink ℓ) => SU2_haar) := by
  have hMP := wilsonBase_measurePreserving_split
    (isPlusLink : LatticeLink L → Prop) (L := L)
  have hsplit : ∫ U, K U ∂(wilsonBaseMeasure L)
      = ∫ z, K (gaugeFieldGluePlus z.1 z.2)
        ∂((Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
              SU2_haar).prod
          (Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
              ¬ isPlusLink ℓ) => SU2_haar)) := by
    simpa [gaugeFieldGluePlus, MeasurableEquiv.symm_apply_apply] using
      hMP.integral_comp' (g := fun z => K (gaugeFieldGluePlus z.1 z.2))
  have hcomp : Continuous
      (fun z : (Subtype (isPlusLink : LatticeLink L → Prop) → SU2) ×
          (Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2) =>
        K (gaugeFieldGluePlus z.1 z.2)) := hK.comp gaugeFieldGluePlus_continuous
  have hint : Integrable (fun z => K (gaugeFieldGluePlus z.1 z.2))
      ((Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
          SU2_haar).prod
        (Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
            ¬ isPlusLink ℓ) => SU2_haar)) :=
    hcomp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hsplit, integral_prod_symm _ hint]

/-- **A `Λ_-`-blind integrand: the `¬Λ_-` integral is the base integral.** -/
theorem integral_nonMinus_eq_base (H : GaugeField L → ℂ) (hH : Continuous H)
    (hblind : ∀ U₁ U₂ : GaugeField L,
      (∀ ℓ : LatticeLink L, ¬ isMinusLink ℓ → U₁ ℓ = U₂ ℓ) → H U₁ = H U₂)
    (X₁ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2) :
    ∫ W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2,
        H (gaugeFieldGlue X₁ W)
      ∂(Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
          ¬ isMinusLink ℓ) => SU2_haar)
      = ∫ U, H U ∂(wilsonBaseMeasure L) := by
  rw [wilsonBaseMinus_integral_split_iterated H hH]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  simp only []
  have hconst : ∀ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
      H (gaugeFieldGlue X W) = H (gaugeFieldGlue X₁ W) := by
    intro X
    refine hblind _ _ fun ℓ hnm => ?_
    rw [gaugeFieldGlue_apply_mnot X W hnm, gaugeFieldGlue_apply_mnot X₁ W hnm]
  rw [show (∫ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
        H (gaugeFieldGlue X W)
      ∂(Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
          SU2_haar))
      = ∫ _X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
          H (gaugeFieldGlue X₁ W)
        ∂(Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
            SU2_haar) from
      integral_congr_ae (Filter.Eventually.of_forall hconst)]
  simp

/-- **A `Λ_+`-blind integrand: the `¬Λ_+` integral is the base integral.** -/
theorem integral_nonPlus_eq_base (K : GaugeField L → ℂ) (hK : Continuous K)
    (hblind : ∀ U₁ U₂ : GaugeField L,
      (∀ ℓ : LatticeLink L, ¬ isPlusLink ℓ → U₁ ℓ = U₂ ℓ) → K U₁ = K U₂)
    (V₁ : Subtype (isPlusLink : LatticeLink L → Prop) → SU2) :
    ∫ W : Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2,
        K (gaugeFieldGluePlus V₁ W)
      ∂(Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
          ¬ isPlusLink ℓ) => SU2_haar)
      = ∫ U, K U ∂(wilsonBaseMeasure L) := by
  rw [wilsonBasePlus_integral_split_iterated_symm K hK]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  simp only []
  have hconst : ∀ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
      K (gaugeFieldGluePlus V W) = K (gaugeFieldGluePlus V₁ W) := by
    intro V
    refine hblind _ _ fun ℓ hnp => ?_
    rw [gaugeFieldGluePlus_apply_pnot V W hnp,
      gaugeFieldGluePlus_apply_pnot V₁ W hnp]
  rw [show (∫ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
        K (gaugeFieldGluePlus V W)
      ∂(Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
          SU2_haar))
      = ∫ _V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
          K (gaugeFieldGluePlus V₁ W)
        ∂(Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
            SU2_haar) from
      integral_congr_ae (Filter.Eventually.of_forall hconst)]
  simp

/-! ## §3 — The corrected identity

The chain, left to right: r384's θ-free reduction; `Λ_-`-blindness to return to
the base measure; the `Λ_+` split; pull out the `Λ_+`-blind factors and
recognise what is left as `Φ_R β F_j`; `Λ_+`-blindness to return to the base
measure again. -/

/-- **★★★ r385: the Gibbs cross-θ integral, exactly ★★★**

The boundary weight `exp(-β S_0)` sits on the right-hand side, which is what
r383's accounting predicted and what `wilsonReducedPhiR` alone does not carry. -/
theorem wilsonGibbs_crossTheta_eq_corrected (hL : Even L) (β : ℝ)
    (Fi Fj : GaugeField L → ℂ) (hFi : Continuous Fi) (hFj : Continuous Fj)
    (hFisup : supportedOnPlusZero Fi) (hFjsup : supportedOnPlusZero Fj) :
    ∫ U, star (Fi (timeReflectionGaugeField U)) * Fj U
        ∂(wilsonGibbsMeasure L β)
      = ∫ U, (Real.exp (-β * wilsonActionZero U) : ℂ)
            * (star (wilsonReducedPhiR β Fi U) * wilsonReducedPhiR β Fj U)
        ∂(wilsonBaseMeasure L) := by
  have hPhiI : Continuous (wilsonReducedPhiR β Fi) :=
    wilsonReducedPhiR_continuous β Fi hFi
  have hPhiJ : Continuous (wilsonReducedPhiR β Fj) :=
    wilsonReducedPhiR_continuous β Fj hFj
  -- the integrand after r384, as a function on the whole space
  have hGcont : Continuous (fun U : GaugeField L =>
      ((Real.exp (-β * wilsonActionPlusR U) : ℂ)
          * (Real.exp (-β * wilsonActionZero U) : ℂ) * Fj U)
        * star (wilsonReducedPhiR β Fi U)) := by
    refine Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) hFj)
      (continuous_star.comp hPhiI)
    · exact Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul wilsonActionPlusR_continuous))
    · exact Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul wilsonActionZero_continuous))
  have hGblind : ∀ U₁ U₂ : GaugeField L,
      (∀ ℓ : LatticeLink L, ¬ isMinusLink ℓ → U₁ ℓ = U₂ ℓ) →
      ((Real.exp (-β * wilsonActionPlusR U₁) : ℂ)
          * (Real.exp (-β * wilsonActionZero U₁) : ℂ) * Fj U₁)
        * star (wilsonReducedPhiR β Fi U₁)
      = ((Real.exp (-β * wilsonActionPlusR U₂) : ℂ)
          * (Real.exp (-β * wilsonActionZero U₂) : ℂ) * Fj U₂)
        * star (wilsonReducedPhiR β Fi U₂) := by
    intro U₁ U₂ hag
    have hne : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.minus → U₁ ℓ = U₂ ℓ :=
      fun ℓ h => hag ℓ h
    have hz : ∀ ℓ : LatticeLink L, linkSector ℓ = LinkSector.zero → U₁ ℓ = U₂ ℓ := by
      intro ℓ h
      exact hag ℓ (by rw [isMinusLink, h]; decide)
    rw [wilsonActionPlusR_congr hL U₁ U₂ hne, wilsonActionZero_congr U₁ U₂ hne,
      hFjsup U₁ U₂ hne, wilsonReducedPhiR_congr_zero hL β Fi hFisup U₁ U₂ hz]
  -- step 1+2: r384, then back to the base measure
  rw [wilsonGibbs_crossTheta_eq_W_integral_noTheta hL β Fi Fj hFi hFj hFisup hFjsup
      (fun _ => 1),
    integral_nonMinus_eq_base _ hGcont hGblind (fun _ => 1),
    -- step 3: the `Λ_+` split, `Λ_+` inner
    wilsonBasePlus_integral_split_iterated_symm _ hGcont]
  -- step 4+5: pull out the `Λ_+`-blind factors; what remains is `Φ_R β Fj`
  have hinner : ∀ W : Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2,
      (∫ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
          ((Real.exp (-β * wilsonActionPlusR (gaugeFieldGluePlus V W)) : ℂ)
              * (Real.exp (-β * wilsonActionZero (gaugeFieldGluePlus V W)) : ℂ)
              * Fj (gaugeFieldGluePlus V W))
            * star (wilsonReducedPhiR β Fi (gaugeFieldGluePlus V W))
          ∂(Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
              SU2_haar))
      = (Real.exp (-β * wilsonActionZero (gaugeFieldGluePlus (fun _ => 1) W)) : ℂ)
        * (star (wilsonReducedPhiR β Fi (gaugeFieldGluePlus (fun _ => 1) W))
            * wilsonReducedPhiR β Fj (gaugeFieldGluePlus (fun _ => 1) W)) := by
    intro W
    -- the two `Λ_+`-blind factors agree with their values at the reference `V`
    have hzW : ∀ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
        ∀ ℓ : LatticeLink L, linkSector ℓ = LinkSector.zero →
          gaugeFieldGluePlus V W ℓ
            = gaugeFieldGluePlus (fun _ => (1 : SU2)) W ℓ := by
      intro V ℓ h
      have hnp : ¬ isPlusLink ℓ := by rw [isPlusLink, h]; decide
      rw [gaugeFieldGluePlus_apply_pnot V W hnp,
        gaugeFieldGluePlus_apply_pnot (fun _ => (1 : SU2)) W hnp]
    have hpt : ∀ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
        ((Real.exp (-β * wilsonActionPlusR (gaugeFieldGluePlus V W)) : ℂ)
            * (Real.exp (-β * wilsonActionZero (gaugeFieldGluePlus V W)) : ℂ)
            * Fj (gaugeFieldGluePlus V W))
          * star (wilsonReducedPhiR β Fi (gaugeFieldGluePlus V W))
        = ((Real.exp (-β * wilsonActionZero
              (gaugeFieldGluePlus (fun _ => 1) W)) : ℂ)
            * star (wilsonReducedPhiR β Fi
                (gaugeFieldGluePlus (fun _ => 1) W)))
          * (Fj (gaugeFieldGluePlus V W)
              * (Real.exp (-β * wilsonActionPlusR
                  (gaugeFieldGluePlus V W)) : ℂ)) := by
      intro V
      rw [wilsonActionZero_congr_of_zero _ _ (hzW V),
        wilsonReducedPhiR_congr_zero hL β Fi hFisup _ _ (hzW V)]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      mul_assoc]
    congr 1
    congr 1
    -- what is left is `Φ_R β Fj`, by definition and the `Λ_+` round trip
    unfold wilsonReducedPhiR
    rw [restrictNonPlus_gaugeFieldGluePlus]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  -- step 6: `Λ_+`-blind again, so back to the base measure
  have hKcont : Continuous (fun U : GaugeField L =>
      (Real.exp (-β * wilsonActionZero U) : ℂ)
        * (star (wilsonReducedPhiR β Fi U) * wilsonReducedPhiR β Fj U)) := by
    refine Continuous.mul ?_ ((continuous_star.comp hPhiI).mul hPhiJ)
    exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul wilsonActionZero_continuous))
  have hKblind : ∀ U₁ U₂ : GaugeField L,
      (∀ ℓ : LatticeLink L, ¬ isPlusLink ℓ → U₁ ℓ = U₂ ℓ) →
      (Real.exp (-β * wilsonActionZero U₁) : ℂ)
          * (star (wilsonReducedPhiR β Fi U₁) * wilsonReducedPhiR β Fj U₁)
        = (Real.exp (-β * wilsonActionZero U₂) : ℂ)
          * (star (wilsonReducedPhiR β Fi U₂) * wilsonReducedPhiR β Fj U₂) := by
    intro U₁ U₂ hag
    have hz : ∀ ℓ : LatticeLink L, linkSector ℓ = LinkSector.zero → U₁ ℓ = U₂ ℓ := by
      intro ℓ h
      exact hag ℓ (by rw [isPlusLink, h]; decide)
    rw [wilsonActionZero_congr_of_zero U₁ U₂ hz,
      wilsonReducedPhiR_congr_zero hL β Fi hFisup U₁ U₂ hz,
      wilsonReducedPhiR_congr_zero hL β Fj hFjsup U₁ U₂ hz]
  exact integral_nonPlus_eq_base _ hKcont hKblind (fun _ => 1)

/-! ## §4 — The corrected `Φ`, and the headline

`Φ_R` carries no boundary weight, so the weight is attached here, split in half
so that `star (Φ i) * Φ j` reassembles `exp(-β S_0)`. This is additive: `Φ_R`
keeps every theorem it had. -/

/-- **The corrected `Φ`**: `Φ_R` with half the boundary weight. -/
def wilsonReducedPhiRCorrected (β : ℝ) (F : GaugeField L → ℂ) :
    GaugeField L → ℂ :=
  fun U => (Real.exp (-β * wilsonActionZero U / 2) : ℂ) * wilsonReducedPhiR β F U

lemma wilsonReducedPhiRCorrected_continuous (β : ℝ) (F : GaugeField L → ℂ)
    (hF : Continuous F) :
    Continuous (wilsonReducedPhiRCorrected β F) := by
  unfold wilsonReducedPhiRCorrected
  refine Continuous.mul ?_ (wilsonReducedPhiR_continuous β F hF)
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      ((continuous_const.mul wilsonActionZero_continuous).div_const 2))

/-- The two half-weights reassemble `exp(-β S_0)`. -/
lemma star_corrected_mul_corrected (β : ℝ) (Fi Fj : GaugeField L → ℂ)
    (U : GaugeField L) :
    star (wilsonReducedPhiRCorrected β Fi U) * wilsonReducedPhiRCorrected β Fj U
      = (Real.exp (-β * wilsonActionZero U) : ℂ)
        * (star (wilsonReducedPhiR β Fi U) * wilsonReducedPhiR β Fj U) := by
  unfold wilsonReducedPhiRCorrected
  have hhalf : (Real.exp (-β * wilsonActionZero U / 2) : ℂ)
      * (Real.exp (-β * wilsonActionZero U / 2) : ℂ)
      = (Real.exp (-β * wilsonActionZero U) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    norm_num
  rw [star_mul', star_ofReal_complex, ← hhalf]
  ring

/-- **★ r385: `hFubini` discharged, for the corrected `Φ` ★** -/
theorem wilsonFubini_corrected (hL : Even L) (β : ℝ)
    (Fi Fj : GaugeField L → ℂ) (hFi : Continuous Fi) (hFj : Continuous Fj)
    (hFisup : supportedOnPlusZero Fi) (hFjsup : supportedOnPlusZero Fj) :
    ∫ U, star (Fi (timeReflectionGaugeField U)) * Fj U
        ∂(wilsonGibbsMeasure L β)
      = ∫ U, star (wilsonReducedPhiRCorrected β Fi U)
            * wilsonReducedPhiRCorrected β Fj U
        ∂(wilsonBaseMeasure L) := by
  rw [wilsonGibbs_crossTheta_eq_corrected hL β Fi Fj hFi hFj hFisup hFjsup]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only []
  rw [star_corrected_mul_corrected]

/-- **★★★ r385: WILSON REFLECTION POSITIVITY, free of Fubini ★★★**

**No Fubini hypothesis and no integrability hypothesis remains.** What does
remain, stated precisely so the name cannot be read as more than it is:
`Even L`; continuity of the test functions; and their support in `Λ_+ ∪ Λ_0`.
The support condition is reflection positivity's own premise rather than a gap —
the statement is false without it. `Even L` is a genuine restriction on the
lattice, inherited from `sectorSwapEquiv`.

So this does **not** meet the scoping document's "empty hypothesis list"
phrasing, and is not claimed to. What it closes is the analytic debt: the two
hypotheses that stood in for unfinished work are gone.

Not a mass gap and not a Clay statement: this is reflection positivity for the
Wilson action on a finite even periodic lattice. -/
theorem wilson_reflection_positivity_of_continuous (hL : Even L) {K : ℕ} (β : ℝ)
    (F : Fin K → GaugeField L → ℂ)
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (hF_cont : ∀ i : Fin K, Continuous (F i)) :
    (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).PosSemidef := by
  refine wilson_reflection_positivity β F hF_support
    (fun i => wilsonReducedPhiRCorrected β (F i)) (fun i j => ?_) (fun i j => ?_)
  · exact ((continuous_star.comp
      (wilsonReducedPhiRCorrected_continuous β (F i) (hF_cont i))).mul
      (wilsonReducedPhiRCorrected_continuous β (F j) (hF_cont j))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact wilsonFubini_corrected hL β (F i) (F j) (hF_cont i) (hF_cont j)
      (hF_support i) (hF_support j)

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonActionZero_congr_of_zero
#print axioms PF.YangMills.restrictNonPlus_gaugeFieldGluePlus
#print axioms PF.YangMills.star_ofReal_complex
#print axioms PF.YangMills.wilsonBasePlus_integral_split_iterated_symm
#print axioms PF.YangMills.integral_nonMinus_eq_base
#print axioms PF.YangMills.integral_nonPlus_eq_base
#print axioms PF.YangMills.wilsonGibbs_crossTheta_eq_corrected
#print axioms PF.YangMills.wilsonReducedPhiRCorrected
#print axioms PF.YangMills.star_corrected_mul_corrected
#print axioms PF.YangMills.wilsonFubini_corrected
#print axioms PF.YangMills.wilson_reflection_positivity_of_continuous

-- Axiom-check coverage completed 2026-10-30 (declarations the in-file check had omitted)
#print axioms PF.YangMills.wilsonReducedPhiRCorrected_continuous
