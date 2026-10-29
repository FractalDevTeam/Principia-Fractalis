/-
# r384: θ is the identity on `Λ_0`, and `Φ_R` is θ-invariant

★ 2026-10-29 r384 — r383's prose analysis, converted to theorems ★

## Why this file exists

r383 reduced `hFubini`'s left-hand side to a single `¬Λ_-` integral, and its
header then carried an **analysis** — explicitly labelled as not-yet-Lean —
arguing that the two sides of `hFubini` differ by a factor `exp(-β S_0)`. That
argument rested on two claims. Both are now theorems.

1. **θ is the identity on `Λ_0`.** `Λ_0` links are spatial at time `0` or `L/2`;
   `timeReflectionSite` negates the time coordinate; and in `Fin L` with `L = 2M`
   both `-0 = 0` and `-M = M`. So `linkTheta` fixes every `Λ_0` link, and since
   those links are spatial, θ applies no inverse to them either. No reflection of
   the boundary data occurs at all.

2. **`Φ_R β F` reads only the `Λ_0` data**, when `F` is `supportedOnPlusZero`.
   `Φ_R` integrates the `Λ_+` component out, and both `F` and `S_+R` are blind to
   `Λ_-`; what is left is the `Λ_0` data. Note this is *sharper* than blindness
   to `Λ_-` alone, and the sharper form is what is needed: `Φ_R` must be shown
   insensitive to the `Λ_+` data too, since θ moves that.

Together: **`Φ_R β F (θ U) = Φ_R β F U`.** So the θ in r383's right-hand side
can be deleted, which is done here, and the discrepancy between the two sides of
`hFubini` is isolated to the `exp(-β S_0)` factor exactly as the analysis said.

## What this settles about `hFubini`, and what it does not

Settled: the θ-side of the accounting. The factor `exp(-β S_0)` is the *only*
difference the analysis attributed to the boundary, and the other candidate —
that θ scrambles the `Λ_0` data and so `Φ_R(θ·)` differs from `Φ_R(·)` — is now
ruled out by theorem rather than by argument.

**Not settled, and still not claimed:** that `hFubini` with `Φ := Φ_R` is false.
That would need its own theorem, and the project's standing rule is that an
impossibility is never inferred from a construction's failure to deliver. What
remains to close the accounting in Lean is the identification

    ∫ over Λ_+ of  F_j · exp(-β S_+R)   =   Φ_R β F_j

which is true by `Φ_R`'s definition but needs the `¬Λ_- ≃ Λ_+ × Λ_0` sub-split
to state against r383's reduction — a nested-subtype split, and the one piece of
real index work left. Until that lands, the `exp(-β S_0)` discrepancy is
established by analysis plus these two theorems, not by a single machine-checked
identity.

The candidate repair stands as r383 recorded it: `Φ_i := exp(-β S_0 / 2) · Φ_R`.
The headline `wilson_reflection_positivity` is untouched either way, since it
quantifies over `Φ` and `gramMatrix_bochner_posSemidef` takes an arbitrary
measure. Whether to restate the specialisation
`wilson_reflection_positivity_withReducedPhiR` is Pablo's call.

No mass-gap claim and no Clay claim.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.YangMills.WilsonFubiniLHSReduction_r383
import PF.YangMills.WilsonSectorPlaquetteZeroReflection_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Reading `Λ_0` membership backwards

`linkSector` returns `zero` only through its spatial branch, and only on the
boundary times. Both facts are needed and neither was recorded. -/

omit [NeZero L] in
/-- A `Λ_0` link is spatial. -/
lemma spatial_of_zeroSector {ℓ : LatticeLink L}
    (h : linkSector ℓ = LinkSector.zero) : ℓ.2 ≠ 0 := by
  intro hd
  simp only [linkSector, hd, if_true] at h
  by_cases ht : (ℓ.1 0).val < L / 2
  · rw [if_pos ht] at h; exact absurd h (by decide)
  · rw [if_neg ht] at h; exact absurd h (by decide)

omit [NeZero L] in
/-- A `Λ_0` link sits at a boundary time. -/
lemma boundary_of_zeroSector {ℓ : LatticeLink L}
    (h : linkSector ℓ = LinkSector.zero) :
    (ℓ.1 0).val = 0 ∨ (ℓ.1 0).val = L / 2 := by
  by_contra hc
  simp only [linkSector, if_neg (spatial_of_zeroSector h), if_neg hc] at h
  by_cases ht : (ℓ.1 0).val < L / 2
  · rw [if_pos ht] at h; exact absurd h (by decide)
  · rw [if_neg ht] at h; exact absurd h (by decide)

/-! ## §2 — θ fixes the boundary

The two `val`-level lemmas are landed
(`WilsonSectorPlaquetteZeroReflection_2026_10_21`). What was missing is that the
*site* is fixed, not only its time coordinate — which follows, because
`timeReflectionSite` is a `Function.update` at coordinate `0` and nothing else. -/

/-- **`timeReflectionSite` fixes a boundary-time site outright.** -/
lemma timeReflectionSite_eq_self_of_boundary (hL : Even L) (x : LatticeSite L)
    (h : (x 0).val = 0 ∨ (x 0).val = L / 2) :
    timeReflectionSite x = x := by
  have hupd : (timeReflectionSite x) 0 = -(x 0) := by
    unfold timeReflectionSite; rw [Function.update_self]
  have hval : ((timeReflectionSite x) 0).val = (x 0).val := by
    rcases h with h | h
    · rw [timeReflectionSite_val_fixed_zero x h, h]
    · rw [timeReflectionSite_val_fixed_half hL x h, h]
  have hneg : -(x 0) = x 0 := by
    apply Fin.ext
    rw [← hupd]; exact hval
  unfold timeReflectionSite
  rw [hneg]
  exact Function.update_eq_self 0 x

/-- **`linkTheta` fixes every `Λ_0` link.** -/
lemma linkTheta_eq_self_of_zeroSector (hL : Even L) {ℓ : LatticeLink L}
    (h : linkSector ℓ = LinkSector.zero) : linkTheta ℓ = ℓ := by
  unfold linkTheta
  rw [if_neg (spatial_of_zeroSector h),
    timeReflectionSite_eq_self_of_boundary hL ℓ.1 (boundary_of_zeroSector h)]

/-- **★ r384: θ is the identity on `Λ_0` ★**

No relabelling, because `linkTheta` fixes the link; and no inverse, because the
link is spatial. The boundary data is untouched by the time reflection. -/
theorem timeReflectionGaugeField_eq_on_zeroSector (hL : Even L) (U : GaugeField L)
    {ℓ : LatticeLink L} (h : linkSector ℓ = LinkSector.zero) :
    timeReflectionGaugeField U ℓ = U ℓ := by
  rw [timeReflectionGaugeField_apply_eq, if_neg (spatial_of_zeroSector h),
    linkTheta_eq_self_of_zeroSector hL h]

/-! ## §3 — `Φ_R` reads only the `Λ_0` data -/

/-- **`Φ_R β F` depends on `U` only through its `Λ_0` component.**

Sharper than blindness to `Λ_-`, and the sharper form is the one needed: the
`Λ_+` data is integrated out by `Φ_R` itself, so agreement on `Λ_0` alone
suffices. -/
theorem wilsonReducedPhiR_congr_zero (hL : Even L) (β : ℝ)
    (F : GaugeField L → ℂ) (hF : supportedOnPlusZero F) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L,
      linkSector ℓ = LinkSector.zero → U₁ ℓ = U₂ ℓ) :
    wilsonReducedPhiR β F U₁ = wilsonReducedPhiR β F U₂ := by
  unfold wilsonReducedPhiR
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only []
  have hglue : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.minus →
      gaugeFieldGluePlus V (restrictNonPlus U₁) ℓ
        = gaugeFieldGluePlus V (restrictNonPlus U₂) ℓ := by
    intro ℓ hne
    by_cases hp : isPlusLink ℓ
    · rw [gaugeFieldGluePlus_apply_plus _ _ hp,
        gaugeFieldGluePlus_apply_plus _ _ hp]
    · rw [gaugeFieldGluePlus_apply_pnot _ _ hp,
        gaugeFieldGluePlus_apply_pnot _ _ hp]
      refine hAgree ℓ ?_
      cases hs : linkSector ℓ with
      | plus => exact absurd hs hp
      | zero => rfl
      | minus => exact absurd hs hne
  rw [hF _ _ hglue, wilsonActionPlusR_congr hL _ _ hglue]

/-- **★★★ r384: `Φ_R` is θ-invariant ★★★**

`Φ_R` reads only `Λ_0`, and θ is the identity there. -/
theorem wilsonReducedPhiR_timeReflection (hL : Even L) (β : ℝ)
    (F : GaugeField L → ℂ) (hF : supportedOnPlusZero F) (U : GaugeField L) :
    wilsonReducedPhiR β F (timeReflectionGaugeField U)
      = wilsonReducedPhiR β F U :=
  wilsonReducedPhiR_congr_zero hL β F hF _ _ fun _ hz =>
    timeReflectionGaugeField_eq_on_zeroSector hL U hz

/-! ## §4 — r383's reduction, with the θ deleted -/

/-- **★ r384: the Gibbs cross-θ integral with no θ left in it ★**

r383's reduction, composed with the θ-invariance of `Φ_R`. -/
theorem wilsonGibbs_crossTheta_eq_W_integral_noTheta (hL : Even L) (β : ℝ)
    (Fi Fj : GaugeField L → ℂ) (hFi : Continuous Fi) (hFj : Continuous Fj)
    (hFisup : supportedOnPlusZero Fi) (hFjsup : supportedOnPlusZero Fj)
    (X₁ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2) :
    ∫ U, star (Fi (timeReflectionGaugeField U)) * Fj U
        ∂(wilsonGibbsMeasure L β)
      = ∫ W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2,
          ((Real.exp (-β * wilsonActionPlusR (gaugeFieldGlue X₁ W)) : ℂ)
            * (Real.exp (-β * wilsonActionZero (gaugeFieldGlue X₁ W)) : ℂ)
            * Fj (gaugeFieldGlue X₁ W))
          * star (wilsonReducedPhiR β Fi (gaugeFieldGlue X₁ W))
        ∂(Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
            ¬ isMinusLink ℓ) => SU2_haar) := by
  rw [wilsonGibbs_crossTheta_eq_W_integral hL β Fi Fj hFi hFj hFjsup X₁]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  simp only []
  rw [wilsonReducedPhiR_timeReflection hL β Fi hFisup]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.spatial_of_zeroSector
#print axioms PF.YangMills.boundary_of_zeroSector
#print axioms PF.YangMills.timeReflectionSite_eq_self_of_boundary
#print axioms PF.YangMills.linkTheta_eq_self_of_zeroSector
#print axioms PF.YangMills.timeReflectionGaugeField_eq_on_zeroSector
#print axioms PF.YangMills.wilsonReducedPhiR_congr_zero
#print axioms PF.YangMills.wilsonReducedPhiR_timeReflection
#print axioms PF.YangMills.wilsonGibbs_crossTheta_eq_W_integral_noTheta
