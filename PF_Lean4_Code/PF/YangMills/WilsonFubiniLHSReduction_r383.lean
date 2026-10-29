/-
# r383: the Gibbs cross-θ integral collapses to a single positive-time-half integral

★ 2026-10-29 r383 — steps 1–3 assembled onto r381's step 4 ★

## What this does

`hFubini`'s left-hand side is a Gibbs integral over the whole configuration
space. This file reduces it to a single integral over the `Λ_+ ∪ Λ_0` component,
with `Φ_R` already present in the integrand:

    ∫ U, star (F_i (θ U)) · F_j U  ∂μ_Gibbs
      = ∫ W, (exp(-β S_+R) · exp(-β S_0) · F_j) · star (Φ_R β F_i (θ ·))  ∂π_{¬Λ_-}

The four steps of `WilsonRPFubiniApply_2026_10_21`'s chain all appear:

* step 1 — `wilsonGibbs_integral_eq_base_integral` and r382's **refined**
  factorisation (the landed factorisation is binary and cannot serve `Φ_R`);
* step 2 — r382's `wilsonBaseMinus_integral_split_iterated`;
* step 3 — the `X`-independence of `exp(-β S_+R)`, `exp(-β S_0)` and `F_j`,
  from the landed glue lemmas plus r382's zero-sector one;
* step 4 — r381, which turns the inner `Λ_-` integral into `star Φ_R`.

## The `X₁` parameter is not a defect

The statement is quantified over an arbitrary `X₁ : Λ_- → SU2`, which appears on
the right-hand side. That is deliberate: every factor it appears in is provably
blind to its argument, so the right-hand side has the same value for every `X₁`.
Fixing a canonical one (say `fun _ => 1`) would hide a real fact rather than
state it, and a caller who wants a specific one can instantiate.

## What this does NOT do, and the discrepancy it exposes

**`hFubini` is not discharged, and this file is evidence that — as stated with
`Φ := wilsonReducedPhiR` — it may not be dischargeable.** The reduction above is
machine-checked; the accounting that follows is **ANALYSIS, not yet Lean**, and
is flagged as such.

Carry the reduction one step further, splitting `W` over `Λ_+ × Λ_0`. Three
facts, each already in the tree:

* `Φ_R β F` is blind to the `Λ_-` links whenever `F` is `supportedOnPlusZero`,
  since both `F` and `S_+R` are; so `Φ_R` reads only the `Λ_0` data.
* θ is the **identity** on `Λ_0`. `Λ_0` links are spatial at time `0` or `L/2`
  (`linkSector`), `timeReflectionSite` negates the time coordinate, and in
  `Fin L` with `L = 2M` both `-0 = 0` and `-M = M`. So no reflection of the
  boundary data occurs — `linkTheta` fixes every `Λ_0` link.
* `∫ over Λ_+ of F_j · exp(-β S_+R)` is, by definition, `Φ_R β F_j`.

Those give, writing `W_0` for the `Λ_0` data:

    LHS  =  ∫ W_0,  exp(-β S_0 (W_0)) · star (Φ_R β F_i) · (Φ_R β F_j)
    RHS  =  ∫ W_0,                      star (Φ_R β F_i) · (Φ_R β F_j)

**The two differ by exactly `exp(-β S_0)`.** The Gibbs weight carries three
refined factors, `e_+R · e_0 · e_-R`; `e_-R(U) = e_+R(θU)` supplies the second
`e_+R`, so each side accounts for `e_+R` twice — and `e_0` appears on the left
and nowhere on the right, because `wilsonReducedPhiR` is built on `S_+R` alone.

The zero sector is **not** empty, so this is not a vacuous difference:
`isZeroPlaquette` asks for a purely spatial plaquette (`μ ≠ 0`, `ν ≠ 0`,
`μ ≠ ν`) at base time `0` or `L/2`, and `LatticeDir = Fin 4` supplies three
spatial directions.

### The repair, and why the headline survives

Not claimed: that `hFubini` is false. It quantifies over `Φ`, so it is a
question about which `Φ` can satisfy it, and the natural candidate is

    Φ_i  :=  exp(-β S_0 / 2) · Φ_R β F_i

for which `star (Φ_i) · Φ_j = exp(-β S_0) · star (Φ_R F_i) · (Φ_R F_j)`,
matching the left side. `S_0` is real and depends only on the shared `Λ_0` data,
so the same positive factor multiplies every entry of the Gram matrix — and
`gramMatrix_bochner_posSemidef` takes an **arbitrary** measure, so the headline
`wilson_reflection_positivity` is untouched by the correction. What the
correction does hit is the specialisation
`wilson_reflection_positivity_withReducedPhiR`, whose `Φ` is `Φ_R` with no
boundary weight.

Per the project's standing rule on impossibility versus absence, no impossibility
is asserted here: what is established is the reduction, and what is offered is an
accounting plus a candidate repair, both to be checked in Lean before any
statement in the tree is changed. `WilsonReducedPhiR_2026_10_23`'s header says
its refined action has "no boundary residuals", which is true of `S_+R` itself
and is exactly why the `e_0` weight has to live somewhere else.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.YangMills.WilsonFubiniWSide_r382
import PF.YangMills.WilsonBoltzmannPlusRGlue_2026_10_23
import PF.YangMills.WilsonActionContinuity_2026_10_20
import PF.YangMills.SpecialUnitaryGroupTopology_2026_10_17

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Two missing pieces of plumbing -/

lemma restrictNonMinus_gaugeFieldGlue
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
    (W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2) :
    restrictNonMinus (gaugeFieldGlue X W) = W := by
  funext ℓ
  exact gaugeFieldGlue_apply_mnot X W ℓ.property

/-- θ is continuous. Immediate from r380's factorisation of θ through
`linkTheta`, plus `ContinuousInv` on `SU(2)`. -/
lemma timeReflectionGaugeField_continuous :
    Continuous (timeReflectionGaugeField : GaugeField L → GaugeField L) := by
  refine continuous_pi fun ℓ => ?_
  by_cases hd : ℓ.2 = 0
  · simp only [timeReflectionGaugeField_apply_eq, hd, if_true]
    exact continuous_inv.comp (continuous_apply (linkTheta ℓ))
  · simp only [timeReflectionGaugeField_apply_eq, hd, if_false]
    exact continuous_apply (linkTheta ℓ)

/-! ## §2 — The reduction -/

/-- **★★★ r383: the Gibbs cross-θ integral as a single `¬Λ_-` integral ★★★** -/
theorem wilsonGibbs_crossTheta_eq_W_integral (hL : Even L) (β : ℝ)
    (Fi Fj : GaugeField L → ℂ) (hFi : Continuous Fi) (hFj : Continuous Fj)
    (hFjsup : supportedOnPlusZero Fj)
    (X₁ : Subtype (isMinusLink : LatticeLink L → Prop) → SU2) :
    ∫ U, star (Fi (timeReflectionGaugeField U)) * Fj U
        ∂(wilsonGibbsMeasure L β)
      = ∫ W : Subtype (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) → SU2,
          ((Real.exp (-β * wilsonActionPlusR (gaugeFieldGlue X₁ W)) : ℂ)
            * (Real.exp (-β * wilsonActionZero (gaugeFieldGlue X₁ W)) : ℂ)
            * Fj (gaugeFieldGlue X₁ W))
          * star (wilsonReducedPhiR β Fi
              (timeReflectionGaugeField (gaugeFieldGlue X₁ W)))
        ∂(Measure.pi fun _ : Subtype (fun ℓ : LatticeLink L =>
            ¬ isMinusLink ℓ) => SU2_haar) := by
  have hcont : Continuous (fun U : GaugeField L =>
      Real.exp (-β * wilsonActionTotal U)
        • (star (Fi (timeReflectionGaugeField U)) * Fj U)) := by
    refine Continuous.smul
      (Real.continuous_exp.comp (continuous_const.mul wilsonActionTotal_continuous))
      ?_
    exact (continuous_star.comp (hFi.comp timeReflectionGaugeField_continuous)).mul hFj
  rw [wilsonGibbs_integral_eq_base_integral,
    wilsonBaseMinus_integral_split_iterated _ hcont]
  refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
  simp only []
  -- the three `X`-independent factors, pulled to the reference `X₁`
  have hFjX : ∀ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
      Fj (gaugeFieldGlue X W) = Fj (gaugeFieldGlue X₁ W) := by
    intro X
    refine hFjsup _ _ fun ℓ h_ne_minus => ?_
    have h_not_minus : ¬ isMinusLink ℓ := h_ne_minus
    rw [gaugeFieldGlue_apply_mnot X W h_not_minus,
      gaugeFieldGlue_apply_mnot X₁ W h_not_minus]
  have hpt : ∀ X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2,
      Real.exp (-β * wilsonActionTotal (gaugeFieldGlue X W))
          • (star (Fi (timeReflectionGaugeField (gaugeFieldGlue X W)))
              * Fj (gaugeFieldGlue X W))
        = ((Real.exp (-β * wilsonActionPlusR (gaugeFieldGlue X₁ W)) : ℂ)
            * (Real.exp (-β * wilsonActionZero (gaugeFieldGlue X₁ W)) : ℂ)
            * Fj (gaugeFieldGlue X₁ W))
          * (star (Fi (timeReflectionGaugeField (gaugeFieldGlue X W)))
              * (Real.exp (-β * wilsonActionMinusR
                  (gaugeFieldGlue X W)) : ℂ)) := by
    intro X
    rw [Complex.real_smul, wilsonBoltzmann_factorize_refined,
      wilsonBoltzmann_plusR_glue_eq_of_W hL β X X₁ W,
      wilsonBoltzmann_zero_glue_eq_of_W β X X₁ W, hFjX X]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  congr 1
  have h4 := integral_minus_eq_star_reducedPhiR hL β Fi (gaugeFieldGlue X₁ W)
  rwa [restrictNonMinus_gaugeFieldGlue] at h4

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.restrictNonMinus_gaugeFieldGlue
#print axioms PF.YangMills.timeReflectionGaugeField_continuous
#print axioms PF.YangMills.wilsonGibbs_crossTheta_eq_W_integral
