/-
# Yang-Mills — `timeReflectionGaugeField` is measure-preserving

**Rio's push-through on the Fubini discharge, 2026-10-21.** Builds on
the involutive property (`5ad9b21a`) + inv-invariance of `wilsonBaseMeasure`
to prove `θ̂ : GaugeField L → GaugeField L` is measure-preserving.

### Strategy

Observe `(θ̂U)(ℓ) = Inv.inv (U (linkTheta ℓ))` on **temporal** links,
and `(θ̂U)(ℓ) = U (linkTheta ℓ)` on **spatial** links. Both are
measure-preserving pieces:
* `U ↦ U ∘ linkTheta` is measure-preserving (relabel via a bijection on
  a product measure, since Haar is the same on every link).
* Pointwise inversion on temporal links preserves `SU2_haar`
  (via `IsInvInvariant`); identity preserves trivially.
* Combined on the Pi structure.

### What this delivers

`MeasurePreserving θ̂ wilsonBaseMeasure wilsonBaseMeasure`, which unlocks
change of variable `U → θ̂U` in any Bochner integral against the base
measure. Combined with the Boltzmann factorization (`f852724c`), this
reduces the "`F_i(θU)` under exp(-βS_W)" integrand to one that can be
Fubini-split along the Λ₊/Λ₋ partition.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonReflectionMeasurePreserving_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory MeasureTheory.Measure

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The link-level `linkTheta` as a `MeasurableEquiv`. -/

/-- `linkTheta` promoted to a `MeasurableEquiv` via its involutive-bijection
property. -/
def linkThetaMeasurableEquiv : LatticeLink L ≃ᵐ LatticeLink L where
  toFun := linkTheta
  invFun := linkTheta
  left_inv := linkTheta_involutive
  right_inv := linkTheta_involutive
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

/-- `linkTheta` as an `Equiv` (via its involutive-bijection property). -/
def linkThetaEquiv : LatticeLink L ≃ LatticeLink L :=
  Equiv.ofBijective linkTheta linkTheta_bijective

@[simp] lemma linkThetaEquiv_apply (ℓ : LatticeLink L) :
    linkThetaEquiv ℓ = linkTheta ℓ := rfl

@[simp] lemma linkThetaEquiv_symm_apply (ℓ : LatticeLink L) :
    linkThetaEquiv.symm ℓ = linkTheta ℓ := by
  rw [Equiv.symm_apply_eq]
  exact (linkTheta_involutive ℓ).symm

/-! ## §2 — Pointwise map on gauge fields with conditional inversion. -/

/-- The conditional inversion map: temporal links get inverted, spatial
links are left alone. -/
def gaugeFieldCondInv (U : GaugeField L) : GaugeField L :=
  fun ℓ => if ℓ.2 = 0 then (U ℓ)⁻¹ else U ℓ

/-- `gaugeFieldCondInv` is involutive (double inverse / double identity). -/
lemma gaugeFieldCondInv_involutive :
    Function.Involutive (gaugeFieldCondInv : GaugeField L → GaugeField L) := by
  intro U
  funext ℓ
  unfold gaugeFieldCondInv
  by_cases hd : ℓ.2 = 0
  · simp [hd, inv_inv]
  · simp [hd]

/-! ## §3 — Factorization: `θ̂ = gaugeFieldCondInv ∘ (U ↦ U ∘ linkTheta)`. -/

/-- The gauge-field reflection factors as per-link conditional inversion
composed with link-level relabeling via `linkTheta`. -/
theorem timeReflectionGaugeField_factorization (U : GaugeField L) :
    timeReflectionGaugeField U = gaugeFieldCondInv (fun ℓ => U (linkTheta ℓ)) := by
  funext ℓ
  unfold timeReflectionGaugeField gaugeFieldCondInv linkTheta
  by_cases hd : ℓ.2 = 0
  · simp [hd]
  · simp [hd]

-- piCongrLeft identification deferred — needs explicit cast-handling for the
-- constant-family case which is tangential to the main deliverable here.

/-! ## §4 — Measurability + measure-preservation of the two factors. -/

/-- The relabeling `U ↦ U ∘ linkTheta` is measurable (projection + continuous
pre-composition). -/
lemma relabel_linkTheta_measurable :
    Measurable (fun U : GaugeField L => (fun ℓ => U (linkTheta ℓ))) := by
  apply measurable_pi_lambda
  intro ℓ
  exact measurable_pi_apply _

/-- `gaugeFieldCondInv` is measurable: a Pi of per-link measurable
cond-inv (either `Inv.inv` or `id` on SU2, both measurable). -/
lemma gaugeFieldCondInv_measurable :
    Measurable (gaugeFieldCondInv : GaugeField L → GaugeField L) := by
  apply measurable_pi_lambda
  intro ℓ
  by_cases hd : ℓ.2 = 0
  · -- Temporal: `U ↦ (U ℓ)⁻¹`
    show Measurable (fun U : GaugeField L => if ℓ.2 = 0 then (U ℓ)⁻¹ else U ℓ)
    simp only [if_pos hd]
    exact (measurable_inv).comp (measurable_pi_apply ℓ)
  · -- Spatial: `U ↦ U ℓ`
    show Measurable (fun U : GaugeField L => if ℓ.2 = 0 then (U ℓ)⁻¹ else U ℓ)
    simp only [if_neg hd]
    exact measurable_pi_apply ℓ

/-- `timeReflectionGaugeField` is measurable. -/
theorem timeReflectionGaugeField_measurable :
    Measurable (timeReflectionGaugeField : GaugeField L → GaugeField L) := by
  have h_eq : (timeReflectionGaugeField : GaugeField L → GaugeField L) =
              gaugeFieldCondInv ∘ (fun U => fun ℓ => U (linkTheta ℓ)) := by
    funext U
    exact timeReflectionGaugeField_factorization U
  rw [h_eq]
  exact gaugeFieldCondInv_measurable.comp relabel_linkTheta_measurable

/-! ## §5 — Per-link measure preservation for `gaugeFieldCondInv`. -/

/-- Per-link function in `gaugeFieldCondInv`: `Inv.inv` on temporal, `id`
on spatial. -/
def condInvAt (ℓ : LatticeLink L) : SU2 → SU2 :=
  if ℓ.2 = 0 then Inv.inv else id

/-- `gaugeFieldCondInv U ℓ = condInvAt ℓ (U ℓ)` — unfolds `gaugeFieldCondInv`
into a per-link function application. -/
lemma gaugeFieldCondInv_eq_pi (U : GaugeField L) :
    gaugeFieldCondInv U = fun ℓ => condInvAt ℓ (U ℓ) := by
  funext ℓ
  unfold gaugeFieldCondInv condInvAt
  by_cases hd : ℓ.2 = 0
  · simp [hd]
  · simp [hd]

/-- Per-link `condInvAt ℓ` preserves `SU2_haar`. -/
lemma condInvAt_measurePreserving (ℓ : LatticeLink L) :
    MeasurePreserving (condInvAt ℓ) SU2_haar SU2_haar := by
  unfold condInvAt
  by_cases hd : ℓ.2 = 0
  · simp [hd]; exact SU2_measurePreserving_inv
  · simp [hd]; exact MeasurePreserving.id SU2_haar

/-! ## §6 — `gaugeFieldCondInv` preserves `wilsonBaseMeasure`. -/

/-- **`gaugeFieldCondInv` preserves `wilsonBaseMeasure`.** Pi of per-link
measure-preserving `condInvAt` via `measurePreserving_pi`. -/
theorem gaugeFieldCondInv_measurePreserving :
    MeasurePreserving (gaugeFieldCondInv : GaugeField L → GaugeField L)
      (wilsonBaseMeasure L) (wilsonBaseMeasure L) := by
  have h_eq : (gaugeFieldCondInv : GaugeField L → GaugeField L)
              = fun U ℓ => condInvAt ℓ (U ℓ) := by
    funext U
    exact gaugeFieldCondInv_eq_pi U
  rw [h_eq]
  unfold wilsonBaseMeasure
  exact measurePreserving_pi
    (μ := fun _ : LatticeLink L => SU2_haar)
    (ν := fun _ : LatticeLink L => SU2_haar)
    (f := condInvAt)
    (fun ℓ => condInvAt_measurePreserving ℓ)

/-! ## §7 — The link-relabel preserves `wilsonBaseMeasure`.

Via `measurePreserving_piCongrLeft`: since all links carry the same
`SU2_haar`, relabeling by a bijection is measure-preserving. -/

/-- **The link-relabel preserves `wilsonBaseMeasure`.** -/
theorem relabel_linkTheta_measurePreserving :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : LatticeLink L => SU2) linkThetaEquiv)
      (wilsonBaseMeasure L) (wilsonBaseMeasure L) := by
  unfold wilsonBaseMeasure
  -- `measurePreserving_piCongrLeft` gives us
  --   MeasurePreserving (piCongrLeft ...) (Pi fun i' => μ (f i')) (Pi μ)
  -- For μ constant (= SU2_haar), both Pi measures coincide.
  exact measurePreserving_piCongrLeft
    (μ := fun _ : LatticeLink L => SU2_haar) linkThetaEquiv

/-! ## §8 — Reconcile the two forms of the link-relabel. -/

/-- The `piCongrLeft linkThetaEquiv` acting on a constant-family gauge field
agrees pointwise with the explicit `fun ℓ => U (linkTheta ℓ)` form. -/
lemma piCongrLeft_linkThetaEquiv_eq (U : GaugeField L) :
    (MeasurableEquiv.piCongrLeft (fun _ : LatticeLink L => SU2) linkThetaEquiv) U
      = fun ℓ => U (linkTheta ℓ) := by
  funext ℓ
  -- Apply `piCongrLeft_apply_apply` at `a := linkTheta ℓ`:
  --   (piCongrLeft ... U) (linkThetaEquiv (linkTheta ℓ)) = U (linkTheta ℓ)
  -- Since linkThetaEquiv (linkTheta ℓ) = linkTheta (linkTheta ℓ) = ℓ:
  have h_apply :
      (Equiv.piCongrLeft (fun _ : LatticeLink L => SU2) linkThetaEquiv) U
          (linkThetaEquiv (linkTheta ℓ))
        = U (linkTheta ℓ) :=
    Equiv.piCongrLeft_apply_apply (fun _ => SU2) linkThetaEquiv U (linkTheta ℓ)
  have h_fix : linkThetaEquiv (linkTheta ℓ) = ℓ := by
    show linkTheta (linkTheta ℓ) = ℓ
    exact linkTheta_involutive ℓ
  rw [h_fix] at h_apply
  exact h_apply

/-! ## §9 — `θ̂` is measure-preserving. -/

/-- **★ θ̂ IS MEASURE-PRESERVING ★**

`MeasurePreserving timeReflectionGaugeField wilsonBaseMeasure wilsonBaseMeasure`.

Composition of the relabeling (`relabel_linkTheta_measurePreserving`) and
the conditional inversion (`gaugeFieldCondInv_measurePreserving`), both
measure-preserving on `wilsonBaseMeasure`. -/
theorem timeReflectionGaugeField_measurePreserving :
    MeasurePreserving (timeReflectionGaugeField : GaugeField L → GaugeField L)
      (wilsonBaseMeasure L) (wilsonBaseMeasure L) := by
  have h_eq : (timeReflectionGaugeField : GaugeField L → GaugeField L) =
              gaugeFieldCondInv ∘
                (MeasurableEquiv.piCongrLeft (fun _ : LatticeLink L => SU2)
                  linkThetaEquiv) := by
    funext U
    show timeReflectionGaugeField U
         = gaugeFieldCondInv
             ((MeasurableEquiv.piCongrLeft (fun _ : LatticeLink L => SU2)
                linkThetaEquiv) U)
    rw [piCongrLeft_linkThetaEquiv_eq]
    exact timeReflectionGaugeField_factorization U
  rw [h_eq]
  exact gaugeFieldCondInv_measurePreserving.comp relabel_linkTheta_measurePreserving

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.linkThetaMeasurableEquiv
#print axioms PF.YangMills.linkThetaEquiv
#print axioms PF.YangMills.gaugeFieldCondInv
#print axioms PF.YangMills.gaugeFieldCondInv_involutive
#print axioms PF.YangMills.timeReflectionGaugeField_factorization
#print axioms PF.YangMills.relabel_linkTheta_measurable
#print axioms PF.YangMills.gaugeFieldCondInv_measurable
#print axioms PF.YangMills.timeReflectionGaugeField_measurable
#print axioms PF.YangMills.condInvAt_measurePreserving
#print axioms PF.YangMills.gaugeFieldCondInv_measurePreserving
#print axioms PF.YangMills.relabel_linkTheta_measurePreserving
#print axioms PF.YangMills.piCongrLeft_linkThetaEquiv_eq
#print axioms PF.YangMills.timeReflectionGaugeField_measurePreserving
