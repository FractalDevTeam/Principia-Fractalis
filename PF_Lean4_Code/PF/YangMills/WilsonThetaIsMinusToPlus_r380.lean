/-
# r380: θ restricted to `Λ_+` **is** `minusToPlus` — the bridge step 4 was missing

★ 2026-10-29 r380 — the structural payload of the `hFubini` chain's step 4 ★

## What was missing, measured

`hFubini` is the single remaining undischarged hypothesis of
`wilson_reflection_positivity` (`_hF_support` is the statement's own premise;
`hΦ_integrable` was discharged by r361). Its four-step chain is set out in
`WilsonRPFubiniApply_2026_10_21`. Steps 1–3 are landed. Step 4 reads:

> the `X`-integrand `star F_i(θU) · exp(-β S_-)` becomes `star Φ_i(W)` under
> change of variable `X ↦ θ_Λ⁻ V` using `Λ_-` Pi inv-invariance + sector action
> reflection.

Both named ingredients exist: `minusToPlus_measurePreserving` (10-23) and
`wilsonActionMinusR_timeReflection` (10-21). What did **not** exist, and what a
sweep of every file mentioning both θ and the glue confirms is absent, is the
lemma that makes the change of variable the *right* one: that `minusToPlus` is
not merely *a* measure-preserving map `Λ_- → Λ_+`, but is exactly **θ's own
action on the `Λ_-` data**. Without it the change of variable moves the integral
to the `Λ_+` Pi Haar and leaves the integrand still referring to θ, which is no
progress.

## Why it is true, and why it was findable

`timeReflectionGaugeField` composes a base-site reflection with an SU(2) inverse
on temporal links. `linkTheta` was introduced for sector counting as the
base-site half, its docstring saying it "forgets the inverse". Comparing the two
definitions, the forgotten inverse is *exactly* the per-link conditional
inversion `condInvAtMinus`, and the base-site halves agree on the nose, temporal
`-ê₀` shift included:

    timeReflectionGaugeField U ℓ
      = if ℓ.2 = 0 then (U (linkTheta ℓ))⁻¹ else U (linkTheta ℓ)

So θ factors as *conditional inverse* after *relabel by `linkTheta`* — and that
is the definition of `minusToPlus`, which is `minusCondInv` followed by
`piCongrLeft (sectorSwapEquiv)`, with `sectorSwapEquiv` being `linkTheta`. The
three pieces were built separately, for separate purposes, and are the same map.
This file proves that.

## What is proved

* `linkTheta_snd` — `linkTheta` preserves the direction coordinate, so
  "temporal" is a `linkTheta`-invariant notion;
* `timeReflectionGaugeField_apply_eq` — **θ factors through `linkTheta`**;
* **`minusToPlus_restrictMinus`** — the bridge: for every `U`,
  `minusToPlus hL (U ∣ Λ_-) = (θ U) ∣ Λ_+`;
* `minusCondInv_involutive`, `minusToPlusMeasurableEquiv` — `minusToPlus` as a
  `MeasurableEquiv`, which is what mathlib's `integral_comp'` consumes;
* **`integral_minusToPlus`** — the change of variable itself, for any
  Bochner integral into a normed space.

Together the last two are step 4's engine: an integral over the `Λ_-` Pi Haar of
a function of θ's `Λ_+` data equals the plain `Λ_+` Pi Haar integral of that
function of raw data. That is the move that turns the `Λ_-` inner integral
into `Φ`.

## What is NOT claimed

**This does not discharge `hFubini`.** It supplies step 4's missing identity and
its change of variable. The assembly — gluing this to steps 1–3 through
`gaugeFieldGluePlus`, and carrying the `exp(-β S_-) ↦ exp(-β S_+)` rewrite
through `wilsonActionMinusR_timeReflection` — remains, and it is bookkeeping of
a real but ordinary kind.

Note the hypothesis: `Even L`, inherited from `sectorSwapEquiv` and so carried by
every statement here that mentions `minusToPlus`. The assembled `hFubini` will
carry it, and the eventual headline must state it. It is a genuine restriction on
the lattice, not a formality.

Nothing here is a mass-gap statement or any Clay statement. The lane's acceptance
criterion is an unconditional lattice reflection positivity, and this is one
lemma inside it.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.YangMills.WilsonMinusToPlusMeasurePreserving_2026_10_23
import PF.YangMills.ReflectionPositivityGram_2026_10_17

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — `linkTheta` preserves the direction coordinate

`linkTheta` reflects the base site and, on temporal links, additionally shifts by
`-ê₀`. Neither move touches the direction, so "temporal" survives it. This is
what lets the conditional inversion be stated indifferently on either side. -/

@[simp] lemma linkTheta_snd (ℓ : LatticeLink L) : (linkTheta ℓ).2 = ℓ.2 := by
  unfold linkTheta
  by_cases hd : ℓ.2 = 0
  · simp [hd]
  · simp [hd]

/-! ## §2 — θ factors through `linkTheta`

`linkTheta`'s docstring says it is the base-site half of
`timeReflectionGaugeField`, "forgetting the inverse". This makes that precise:
the forgotten part is exactly a conditional inversion on temporal links. -/

/-- **θ factors through `linkTheta`.** The gauge-field time reflection is the
`linkTheta` relabelling followed by inversion on temporal links. -/
theorem timeReflectionGaugeField_apply_eq (U : GaugeField L) (ℓ : LatticeLink L) :
    timeReflectionGaugeField U ℓ
      = if ℓ.2 = 0 then (U (linkTheta ℓ))⁻¹ else U (linkTheta ℓ) := by
  unfold timeReflectionGaugeField linkTheta
  by_cases hd : ℓ.2 = 0
  · simp [hd]
  · simp [hd]

/-! ## §3 — The bridge -/

/-- The `Λ_-` component of a gauge field. -/
def restrictMinus (U : GaugeField L) :
    Subtype (isMinusLink : LatticeLink L → Prop) → SU2 :=
  fun ℓ => U ℓ.val

/-- **★★★ r380: `minusToPlus` IS θ on the `Λ_-` data ★★★**

The measure-preserving map `minusToPlus`, built for the change of variable out of
`minusCondInv` and the sector swap, applied to the `Λ_-` component of `U`,
returns exactly the `Λ_+` component of `θ U`. This is what makes step 4's change
of variable the correct one rather than merely a measure-preserving one. -/
theorem minusToPlus_restrictMinus (hL : Even L) (U : GaugeField L) :
    minusToPlus hL (restrictMinus U)
      = fun ℓ : Subtype (isPlusLink : LatticeLink L → Prop) =>
          timeReflectionGaugeField U ℓ.val := by
  funext lplus
  obtain ⟨i, hi⟩ : ∃ i, sectorSwapEquiv hL i = lplus :=
    ⟨(sectorSwapEquiv hL).symm lplus, Equiv.apply_symm_apply _ _⟩
  subst hi
  show MeasurableEquiv.piCongrLeft
      (fun _ : Subtype (isPlusLink : LatticeLink L → Prop) => SU2)
      (sectorSwapEquiv hL) (minusCondInv (restrictMinus U))
      (sectorSwapEquiv hL i) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  show condInvAtMinus i (U i.val)
      = timeReflectionGaugeField U (linkTheta i.val)
  rw [timeReflectionGaugeField_apply_eq, linkTheta_snd,
    linkTheta_involutive i.val]
  unfold condInvAtMinus
  by_cases hd : i.val.2 = 0
  · simp [hd]
  · simp [hd]

/-! ## §4 — `minusToPlus` as a `MeasurableEquiv`, and the change of variable

`minusToPlus_measurePreserving` is stated for the bare function. Mathlib's
`MeasurePreserving.integral_comp'` consumes a `MeasurableEquiv`, so the equiv
structure is supplied here. Both factors are invertible: `minusCondInv` is an
involution, and the relabelling is already an equiv. -/

omit [NeZero L] in
lemma minusCondInv_involutive :
    Function.Involutive (minusCondInv (L := L)) := by
  intro X
  funext ℓ
  unfold minusCondInv condInvAtMinus
  by_cases hd : ℓ.val.2 = 0
  · simp [hd]
  · simp [hd]

omit [NeZero L] in
lemma minusCondInv_measurable :
    Measurable (minusCondInv (L := L)) := by
  refine measurable_pi_lambda _ fun ℓ => ?_
  unfold minusCondInv condInvAtMinus
  by_cases hd : ℓ.val.2 = 0
  · have h1 : Measurable
        (fun X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2 => (X ℓ)⁻¹) :=
      SU2_measurePreserving_inv.measurable.comp (measurable_pi_apply ℓ)
    simpa [hd] using h1
  · simpa [hd] using measurable_pi_apply ℓ

/-- `minusCondInv` as a `MeasurableEquiv`, via its involutivity. -/
def minusCondInvMeasurableEquiv :
    (Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
      ≃ᵐ (Subtype (isMinusLink : LatticeLink L → Prop) → SU2) where
  toFun := minusCondInv
  invFun := minusCondInv
  left_inv := minusCondInv_involutive
  right_inv := minusCondInv_involutive
  measurable_toFun := minusCondInv_measurable
  measurable_invFun := minusCondInv_measurable

/-- `minusToPlus` as a `MeasurableEquiv`. -/
def minusToPlusMeasurableEquiv (hL : Even L) :
    (Subtype (isMinusLink : LatticeLink L → Prop) → SU2)
      ≃ᵐ (Subtype (isPlusLink : LatticeLink L → Prop) → SU2) :=
  minusCondInvMeasurableEquiv.trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : Subtype (isPlusLink : LatticeLink L → Prop) => SU2)
      (sectorSwapEquiv hL))

@[simp] lemma minusToPlusMeasurableEquiv_apply (hL : Even L)
    (X : Subtype (isMinusLink : LatticeLink L → Prop) → SU2) :
    minusToPlusMeasurableEquiv hL X = minusToPlus hL X := rfl

/-- **★ r380: step 4's change of variable ★**

An integral over the `Λ_-` Pi Haar of a function of `minusToPlus` equals the
plain `Λ_+` Pi Haar integral. Combined with `minusToPlus_restrictMinus`, this is
the move that carries the `Λ_-` inner integral onto the `Λ_+` component, where
`Φ` is defined. -/
theorem integral_minusToPlus (hL : Even L)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : (Subtype (isPlusLink : LatticeLink L → Prop) → SU2) → E) :
    ∫ X, G (minusToPlus hL X)
        ∂(Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
            SU2_haar)
      = ∫ V, G V
        ∂(Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
            SU2_haar) := by
  have hMP : MeasurePreserving (minusToPlusMeasurableEquiv hL)
      (Measure.pi fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
        SU2_haar)
      (Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
        SU2_haar) := minusToPlus_measurePreserving hL
  exact hMP.integral_comp' G

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.linkTheta_snd
#print axioms PF.YangMills.timeReflectionGaugeField_apply_eq
#print axioms PF.YangMills.minusToPlus_restrictMinus
#print axioms PF.YangMills.minusCondInv_involutive
#print axioms PF.YangMills.minusToPlusMeasurableEquiv
#print axioms PF.YangMills.integral_minusToPlus

-- Axiom-check coverage completed 2026-10-30 (declarations the in-file check had omitted)
#print axioms PF.YangMills.restrictMinus
#print axioms PF.YangMills.minusCondInv_measurable
#print axioms PF.YangMills.minusCondInvMeasurableEquiv
#print axioms PF.YangMills.minusToPlusMeasurableEquiv_apply
