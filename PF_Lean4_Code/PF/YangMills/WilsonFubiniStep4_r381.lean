/-
# r381: step 4 of the `hFubini` chain, discharged — the `Λ_-` inner integral IS `star Φ`

★ 2026-10-29 r381 — `∫_{Λ_-} star F(θ·) · exp(-β S_-R) = star Φ(θU)` ★

## What this closes

`WilsonRPFubiniApply_2026_10_21` sets out the `hFubini` chain in four steps and
names step 4 as "the remaining structural payload":

> the `X`-integrand `star F_i(θU) · exp(-β S_-)` becomes `star Φ_i(W)` under
> change of variable `X ↦ θ_Λ⁻ V` using `Λ_-` Pi inv-invariance + sector action
> reflection.

r380 supplied the missing bridge (`minusToPlus` *is* θ on the `Λ_-` data) and the
change of variable it powers. This file is the step itself:

    ∫ X, star (F (θ (glue X (U ∣ ¬Λ_-)))) · exp(-β · S_-R (glue X (U ∣ ¬Λ_-)))
      = star (Φ_R β F (θ U))

**Step 4 is done.** What remains of `hFubini` is the `W`-side assembly of steps
1–3, which is bookkeeping.

## The hypothesis list, which is shorter than expected

Only `Even L`. In particular **no support hypothesis on `F` and no continuity**,
even though the roadmap's step-4 sketch invokes `F`'s support. The reason is that
the proof never needs to know which links `F` reads: the chain

* `restrictPlus (θ U') = minusToPlus hL (restrictMinus U')` (r380's bridge),
* `gaugeFieldGluePlus (restrictPlus V) (restrictNonPlus V) = V` (round trip),
* `restrictNonPlus (θ (glue X W))` is independent of `X`,

rewrites `θ U'` *exactly* as `gluePlus (minusToPlus hL X) N` with `N` fixed. The
integrand is then literally a function of `minusToPlus hL X`, so r380's change of
variable applies on the nose. Support would be needed to show the *other* factors
(`F_j`, `exp(-β S_+R)`, `exp(-β S_0)`) are `X`-independent — that is steps 1–3's
business, on the `W` side, not step 4's.

`Even L` is genuine and traced: it enters through `sectorSwapEquiv` (hence every
mention of `minusToPlus`) and through `linkSector_linkTheta`, used here to show
that θ carries non-`Λ_+` links to non-`Λ_-` links. The assembled `hFubini` and
the eventual headline must both state it.

## The `X`-independence, which is the one real observation

`restrictNonPlus (θ (glue X W))` must not depend on `X`, or the integrand is not
a function of `minusToPlus hL X` alone and the change of variable is unavailable.
It does not, and the reason is a sector fact: for `ℓ ∉ Λ_+`, `linkTheta ℓ ∉ Λ_-`,
because `linkSector (linkTheta ℓ) = (linkSector ℓ).reflect` and `reflect s` is
`minus` exactly when `s` is `plus`. So θ at a non-`Λ_+` link reads the glue at a
non-`Λ_-` link, where the glue reads `W`. The `X` component is never consulted.

## What is proved

* `gaugeFieldGlue_restrict`, `restrictMinus_gaugeFieldGlue`,
  `gaugeFieldGluePlus_restrict` — the two split round trips;
* `not_isMinusLink_linkTheta_of_not_isPlusLink` — the sector fact above;
* `restrictNonPlus_timeReflection_glue_congr` — the `X`-independence;
* `wilsonActionMinusR_eq_plusR_timeReflection` — `S_-R U = S_+R (θ U)`, the
  landed identity read through θ's involutivity;
* `star_integral_complex`, `star_mul_ofReal` — two `star` bookkeeping lemmas,
  stated explicitly because `simp` rewrites `↑(Real.exp x)` into `Complex.exp ↑x`
  and then can no longer see that the factor is real;
* **`integral_minus_eq_star_reducedPhiR`** — step 4.

## What is NOT claimed

**This does not discharge `hFubini`.** It discharges step 4 of four. The
remaining work is the `W`-side assembly: factor the Gibbs weight by the *refined*
3-way decomposition (step 1 as landed is binary, `S_+ + S_-`, while `Φ_R` is
built on `S_+R`, so the refined factorisation is a small new lemma), pull the
`X`-independent factors out through the `Λ_-` split, then match against `Φ_j`.

No mass-gap claim and no Clay claim. The lane's acceptance criterion is an
unconditional lattice reflection positivity; this is one step of one hypothesis
inside it.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.YangMills.WilsonThetaIsMinusToPlus_r380
import PF.YangMills.WilsonReducedPhiRIntegrable_r361
import PF.YangMills.WilsonSectorRefinedSumIdentity_2026_10_21
import PF.YangMills.WilsonSectorGlue_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Restrictions and the two round trips -/

/-- The `Λ_+` component of a gauge field. -/
def restrictPlus (U : GaugeField L) :
    Subtype (isPlusLink : LatticeLink L → Prop) → SU2 :=
  fun ℓ => U ℓ.val

/-- The non-`Λ_-` component of a gauge field. -/
def restrictNonMinus (U : GaugeField L) :
    Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2 :=
  fun ℓ => U ℓ.val

lemma restrictMinus_gaugeFieldGlue
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    restrictMinus (gaugeFieldGlue X W) = X := by
  funext ℓ
  exact gaugeFieldGlue_apply_minus X W ℓ.property

lemma gaugeFieldGlue_restrict (U : GaugeField L) :
    gaugeFieldGlue (restrictMinus U) (restrictNonMinus U) = U := by
  funext ℓ
  by_cases h : isMinusLink ℓ
  · rw [gaugeFieldGlue_apply_minus _ _ h]; rfl
  · rw [gaugeFieldGlue_apply_mnot _ _ h]; rfl

lemma gaugeFieldGluePlus_restrict (U : GaugeField L) :
    gaugeFieldGluePlus (restrictPlus U) (restrictNonPlus U) = U := by
  funext ℓ
  by_cases h : isPlusLink ℓ
  · rw [gaugeFieldGluePlus_apply_plus _ _ h]; rfl
  · rw [gaugeFieldGluePlus_apply_pnot _ _ h]; rfl

/-! ## §2 — θ carries non-`Λ_+` links to non-`Λ_-` links

This is what makes `restrictNonPlus (θ (glue X W))` blind to `X`: at a non-`Λ_+`
link, θ reads the glue at a non-`Λ_-` link, where the glue reads `W`. -/

lemma not_isMinusLink_linkTheta_of_not_isPlusLink (hL : Even L)
    {ℓ : LatticeLink L} (h : ¬ isPlusLink ℓ) : ¬ isMinusLink (linkTheta ℓ) := by
  unfold isMinusLink
  rw [linkSector_linkTheta hL]
  unfold isPlusLink at h
  cases hs : linkSector ℓ with
  | plus => exact absurd hs h
  | zero => decide
  | minus => decide

/-- **The `X`-independence.** `θ (glue X W)` restricted to the non-`Λ_+` links
does not see `X` at all. -/
lemma restrictNonPlus_timeReflection_glue_congr (hL : Even L)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2)
    (X₁ X₂ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2) :
    restrictNonPlus (timeReflectionGaugeField (gaugeFieldGlue X₁ W))
      = restrictNonPlus (timeReflectionGaugeField (gaugeFieldGlue X₂ W)) := by
  funext ℓ
  have hθ := not_isMinusLink_linkTheta_of_not_isPlusLink hL ℓ.property
  show timeReflectionGaugeField (gaugeFieldGlue X₁ W) ℓ.val
      = timeReflectionGaugeField (gaugeFieldGlue X₂ W) ℓ.val
  rw [timeReflectionGaugeField_apply_eq, timeReflectionGaugeField_apply_eq,
    gaugeFieldGlue_apply_mnot _ _ hθ, gaugeFieldGlue_apply_mnot _ _ hθ]

/-! ## §3 — The refined minus action, read through θ

`wilsonActionMinusR_timeReflection` says `S_-R (θ U) = S_+R U`. Applying it at
`θ U` and using θ's involutivity turns it around into the form step 4 needs. -/

lemma wilsonActionMinusR_eq_plusR_timeReflection (hL : Even L) (U : GaugeField L) :
    wilsonActionMinusR U
      = wilsonActionPlusR (timeReflectionGaugeField U) := by
  have h := wilsonActionMinusR_timeReflection hL (timeReflectionGaugeField U)
  rwa [timeReflectionGaugeField_involutive U] at h

/-! ## §4 — Step 4 -/

/-- `star` passes through a complex Bochner integral. Stated explicitly rather
than left to `simp`, which has to reconcile `star` with `starRingEnd`. -/
lemma star_integral_complex {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℂ) :
    star (∫ x, f x ∂μ) = ∫ x, star (f x) ∂μ := by
  simpa only [starRingEnd_apply] using (integral_conj (μ := μ) (f := f)).symm

/-- `star` of a product with a real scalar. Stated explicitly because `simp`
rewrites `↑(Real.exp x)` into `Complex.exp ↑x` and then can no longer see that
the factor is real. -/
lemma star_mul_ofReal (z : ℂ) (r : ℝ) : star z * (r : ℂ) = star (z * (r : ℂ)) := by
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]

/-- **★★★ r381: step 4 of the `hFubini` chain ★★★**

The `Λ_-` inner integral of `star F(θ ·) · exp(-β S_-R)` is exactly
`star (Φ_R β F (θ U))`.

Only `Even L` is assumed: no support condition on `F`, no continuity. See the
header for why step 4 does not need them — the rewriting of `θ (glue X W)` as
`gluePlus (minusToPlus hL X) N` is exact. -/
theorem integral_minus_eq_star_reducedPhiR (hL : Even L) (β : ℝ)
    (F : GaugeField L → ℂ) (U : GaugeField L) :
    ∫ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
        star (F (timeReflectionGaugeField
              (gaugeFieldGlue X (restrictNonMinus U))))
          * (Real.exp (-β * wilsonActionMinusR
              (gaugeFieldGlue X (restrictNonMinus U))) : ℂ)
        ∂(Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
            SU2_haar)
      = star (wilsonReducedPhiR β F (timeReflectionGaugeField U)) := by
  -- θ of the glue, written exactly through the `Λ_+` glue.
  have key : ∀ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
      timeReflectionGaugeField (gaugeFieldGlue X (restrictNonMinus U))
        = gaugeFieldGluePlus (minusToPlus hL X)
            (restrictNonPlus (timeReflectionGaugeField U)) := by
    intro X
    have hplus : restrictPlus (timeReflectionGaugeField
        (gaugeFieldGlue X (restrictNonMinus U))) = minusToPlus hL X := by
      have h := minusToPlus_restrictMinus hL
        (gaugeFieldGlue X (restrictNonMinus U))
      rw [restrictMinus_gaugeFieldGlue] at h
      exact h.symm
    have hnon : restrictNonPlus (timeReflectionGaugeField
        (gaugeFieldGlue X (restrictNonMinus U)))
          = restrictNonPlus (timeReflectionGaugeField U) := by
      conv_rhs => rw [← gaugeFieldGlue_restrict U]
      exact restrictNonPlus_timeReflection_glue_congr hL
        (restrictNonMinus U) X (restrictMinus U)
    conv_lhs => rw [← gaugeFieldGluePlus_restrict (timeReflectionGaugeField
      (gaugeFieldGlue X (restrictNonMinus U)))]
    rw [hplus, hnon]
  -- The integrand is literally a function of `minusToPlus hL X`.
  have hEq : ∀ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
      star (F (timeReflectionGaugeField
            (gaugeFieldGlue X (restrictNonMinus U))))
        * (Real.exp (-β * wilsonActionMinusR
            (gaugeFieldGlue X (restrictNonMinus U))) : ℂ)
      = (fun V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2 =>
          star (F (gaugeFieldGluePlus V
                (restrictNonPlus (timeReflectionGaugeField U))))
            * (Real.exp (-β * wilsonActionPlusR (gaugeFieldGluePlus V
                (restrictNonPlus (timeReflectionGaugeField U)))) : ℂ))
        (minusToPlus hL X) := by
    intro X
    rw [wilsonActionMinusR_eq_plusR_timeReflection hL, key X]
  have h1 : ∫ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
        star (F (timeReflectionGaugeField
              (gaugeFieldGlue X (restrictNonMinus U))))
          * (Real.exp (-β * wilsonActionMinusR
              (gaugeFieldGlue X (restrictNonMinus U))) : ℂ)
        ∂(Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
            SU2_haar)
      = ∫ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
          (fun V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2 =>
            star (F (gaugeFieldGluePlus V
                  (restrictNonPlus (timeReflectionGaugeField U))))
              * (Real.exp (-β * wilsonActionPlusR (gaugeFieldGluePlus V
                  (restrictNonPlus (timeReflectionGaugeField U)))) : ℂ))
          (minusToPlus hL X)
        ∂(Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
            SU2_haar) :=
    integral_congr_ae (Filter.Eventually.of_forall hEq)
  rw [h1, integral_minusToPlus hL (E := ℂ)
    (fun V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2 =>
      star (F (gaugeFieldGluePlus V
            (restrictNonPlus (timeReflectionGaugeField U))))
        * (Real.exp (-β * wilsonActionPlusR (gaugeFieldGluePlus V
            (restrictNonPlus (timeReflectionGaugeField U)))) : ℂ))]
  unfold wilsonReducedPhiR
  rw [star_integral_complex]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  exact star_mul_ofReal _ _

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.restrictMinus_gaugeFieldGlue
#print axioms PF.YangMills.gaugeFieldGlue_restrict
#print axioms PF.YangMills.gaugeFieldGluePlus_restrict
#print axioms PF.YangMills.not_isMinusLink_linkTheta_of_not_isPlusLink
#print axioms PF.YangMills.restrictNonPlus_timeReflection_glue_congr
#print axioms PF.YangMills.wilsonActionMinusR_eq_plusR_timeReflection
#print axioms PF.YangMills.star_integral_complex
#print axioms PF.YangMills.star_mul_ofReal
#print axioms PF.YangMills.integral_minus_eq_star_reducedPhiR

-- Axiom-check coverage completed 2026-10-30 (declarations the in-file check had omitted)
#print axioms PF.YangMills.restrictPlus
#print axioms PF.YangMills.restrictNonMinus
