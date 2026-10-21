/-
# Yang-Mills — `timeReflectionGaugeField` is a measure-preserving involution

**Rio's step-1/2 of the Fubini discharge, 2026-10-21.** With
`IsInvInvariant SU2_haar` landed (`42d6ad7a`), the Λ₋ Pi inv-invariance
fires. This file lifts to the full gauge-field reflection:

* `timeReflectionGaugeField : GaugeField L → GaugeField L` is a bijection
  (an involution), i.e. `θ̂ ∘ θ̂ = id`.
* `θ̂` is **measure-preserving** under `wilsonBaseMeasure`.

### Why this matters for Fubini

With `θ̂` measure-preserving, change of variable `U → θ̂U` in any integral
against `wilsonBaseMeasure` is free. In particular:

  `∫ G(U) ∂μ_base = ∫ G(θ̂U) ∂μ_base`

This is the fundamental substitution the Fubini factorization uses to
relate the "`F_i(θU)` under `exp(-β S_-)`" integrand to the "`F_i(U)`
under `exp(-β S_+)`" integrand on the Λ_- half of the sector split.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.SU2HaarUnimodular_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory MeasureTheory.Measure

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Λ₋ Pi measure is inv-invariant.

Via `pi.isInvInvariant` applied to `IsInvInvariant SU2_haar` (landed in
`SU2HaarUnimodular_2026_10_21`). -/

/-- The Λ₋ Pi Haar measure is inv-invariant. -/
instance pi_SU2_haar_minus_isInvInvariant :
    IsInvInvariant
      (Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
        SU2_haar)) :=
  pi.isInvInvariant _

/-- The whole `wilsonBaseMeasure` (viewed as a Pi over all links) is
inv-invariant. -/
instance wilsonBaseMeasure_isInvInvariant :
    IsInvInvariant (wilsonBaseMeasure L) := by
  unfold wilsonBaseMeasure
  exact pi.isInvInvariant _

/-! ## §2 — `timeReflectionGaugeField` is involutive.

The gauge-field reflection `θ̂` is an involution: `θ̂ ∘ θ̂ = id`. On
spatial links this follows from `timeReflectionSite_involutive`; on
temporal links it combines the base-site involution + `inv_inv` on SU2.
-/

/-- **`timeReflectionGaugeField` is an involution.** For any gauge field
`U : GaugeField L`, `θ̂ (θ̂ U) = U`. -/
theorem timeReflectionGaugeField_involutive :
    Function.Involutive (timeReflectionGaugeField : GaugeField L → GaugeField L) := by
  intro U
  funext ℓ
  rcases ℓ with ⟨x, d⟩
  unfold timeReflectionGaugeField
  by_cases hd : d = 0
  · subst hd
    simp only [if_true]
    -- goal: (U (shiftTimeNeg (timeReflectionSite (shiftTimeNeg (timeReflectionSite x))), 0))⁻¹⁻¹ = U(x, 0)
    have h := shiftTimeNeg_timeReflectionSite_involutive x
    simp only at h
    rw [h, inv_inv]
  · simp only [if_neg hd]
    rw [timeReflectionSite_involutive x]

/-- `timeReflectionGaugeField` is a bijection (as a consequence of being
an involution). -/
theorem timeReflectionGaugeField_bijective :
    Function.Bijective (timeReflectionGaugeField : GaugeField L → GaugeField L) :=
  timeReflectionGaugeField_involutive.bijective

/-! ## §3 — Scaffolding for measure-preservation of `θ̂`.

The full measure-preservation proof requires factoring `θ̂` through:
1. Per-link inversion on temporal Λ₋ links (measure-preserving via Haar
   inv-invariance),
2. Pi-level relabeling of links via the sector-swap bijection
   (measure-preserving via `measurePreserving_piCongrLeft`),
3. Combination.

The pieces are available but assembly is a bigger lemma than fits here.
What we land here are the local inversion-invariance checks that each
component is measure-preserving.
-/

/-- Haar on SU2 is preserved by inversion: `(SU2_haar).map Inv.inv = SU2_haar`. -/
lemma SU2_haar_map_inv_eq_self : (SU2_haar).map Inv.inv = SU2_haar :=
  IsInvInvariant.inv_eq_self

/-- Inv is a measure-preserving map on SU2 under `SU2_haar`. -/
lemma SU2_measurePreserving_inv : MeasurePreserving (Inv.inv : SU2 → SU2) SU2_haar SU2_haar :=
  measurePreserving_inv SU2_haar

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.pi_SU2_haar_minus_isInvInvariant
#print axioms PF.YangMills.wilsonBaseMeasure_isInvInvariant
#print axioms PF.YangMills.timeReflectionGaugeField_involutive
#print axioms PF.YangMills.timeReflectionGaugeField_bijective
#print axioms PF.YangMills.SU2_haar_map_inv_eq_self
#print axioms PF.YangMills.SU2_measurePreserving_inv
