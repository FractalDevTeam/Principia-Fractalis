/-
# Yang-Mills — Sum-level refined sector reflection `S_-R(θU) = S_+R(U)`

**Rio's §2 ACER directive, 2026-10-21.** Sum-level identity combining
the pointwise non-diag reflection with `timeReflectionPlaquette_bijective`
and diagonal density zero.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-22.
-/
import PF.YangMills.WilsonSectorRefinedActionReflection_2026_10_21
import PF.YangMills.WilsonSectorPlaquetteZeroActionReflection_2026_10_21
import PF.YangMills.WilsonSectorGaugeDependence_2026_10_20
import PF.YangMills.WilsonReflectionMeasurePreserving_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open Finset

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — `timeReflectionPlaquette` preserves diagonality. -/

/-- Diagonality is `timeReflectionPlaquette`-invariant. -/
lemma timeReflectionPlaquette_diag_iff (p : Plaquette L) :
    (timeReflectionPlaquette p).2.1 = (timeReflectionPlaquette p).2.2
      ↔ p.2.1 = p.2.2 := by
  rw [← not_iff_not]
  exact timeReflectionPlaquette_nondiag_iff p

/-! ## §2 — Density is zero on diagonal plaquettes. -/

/-- Density of a diagonal plaquette is 0 (triple form). -/
lemma wilsonActionDensity_diag_pair_eq_zero (U : GaugeField L)
    (p : Plaquette L) (hdiag : p.2.1 = p.2.2) :
    wilsonActionDensity U p = 0 := by
  rcases p with ⟨x, μ, ν⟩
  simp only at hdiag
  subst hdiag
  exact wilsonActionDensity_diag_eq_zero U x μ

/-! ## §3 — Sum-level `S_-R(θU) = S_+R(U)`. -/

/-- **★ REFINED SECTOR ACTION REFLECTION ★**

`wilsonActionMinusR (θU) = wilsonActionPlusR U`. -/
theorem wilsonActionMinusR_timeReflection (hL : Even L) (U : GaugeField L) :
    wilsonActionMinusR (timeReflectionGaugeField U) = wilsonActionPlusR U := by
  unfold wilsonActionMinusR wilsonActionPlusR
  simp_rw [wilsonActionDensity_timeReflection]
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  rw [← timeReflectionPlaquette_bijective.sum_comp
       (fun q : Plaquette L =>
         if plaquetteSectorRefined q = LinkSector.plus then
           wilsonActionDensity U q
         else 0)]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hnd : p.2.1 = p.2.2
  · -- Diagonal: density(U, θ_p p) = 0 since θ_p p is also diagonal
    have hdiag_θ : (timeReflectionPlaquette p).2.1 = (timeReflectionPlaquette p).2.2 :=
      (timeReflectionPlaquette_diag_iff p).mpr hnd
    have hdensity_θ : wilsonActionDensity U (timeReflectionPlaquette p) = 0 :=
      wilsonActionDensity_diag_pair_eq_zero U _ hdiag_θ
    rw [hdensity_θ]
    simp
  · -- Non-diagonal: refined sector reflects pointwise
    have hreflect := plaquetteSectorRefined_timeReflection_of_nondiag hL p hnd
    rw [hreflect]
    -- Case split on plaquetteSectorRefined p
    by_cases hplus : plaquetteSectorRefined p = LinkSector.plus
    · rw [hplus]
      simp [LinkSector.reflect]
    · by_cases hminus : plaquetteSectorRefined p = LinkSector.minus
      · rw [hminus]
        simp [LinkSector.reflect]
      · -- Must be zero
        have hzero : plaquetteSectorRefined p = LinkSector.zero := by
          match h : plaquetteSectorRefined p with
          | LinkSector.plus => exact absurd h hplus
          | LinkSector.zero => rfl
          | LinkSector.minus => exact absurd h hminus
        rw [hzero]
        simp [LinkSector.reflect]

/-- **Companion: `wilsonActionPlusR (θU) = wilsonActionMinusR U`.** -/
theorem wilsonActionPlusR_timeReflection (hL : Even L) (U : GaugeField L) :
    wilsonActionPlusR (timeReflectionGaugeField U) = wilsonActionMinusR U := by
  have h := wilsonActionMinusR_timeReflection hL (timeReflectionGaugeField U)
  rw [timeReflectionGaugeField_involutive U] at h
  exact h.symm

/-! ## §4 — Zero sector is θ-invariant. -/

/-- **`wilsonActionZero (θU) = wilsonActionZero U`.** -/
theorem wilsonActionZero_timeReflection (hL : Even L) (U : GaugeField L) :
    wilsonActionZero (timeReflectionGaugeField U) = wilsonActionZero U := by
  unfold wilsonActionZero
  simp_rw [wilsonActionDensity_timeReflection]
  rw [Finset.sum_filter, Finset.sum_filter]
  symm
  rw [← timeReflectionPlaquette_bijective.sum_comp
       (fun q : Plaquette L =>
         if plaquetteSectorRefined q = LinkSector.zero then
           wilsonActionDensity U q
         else 0)]
  apply Finset.sum_congr rfl
  intro p _
  have hzero_iff :
      plaquetteSectorRefined (timeReflectionPlaquette p) = LinkSector.zero
        ↔ plaquetteSectorRefined p = LinkSector.zero := by
    rw [plaquetteSectorRefined_eq_zero_iff, plaquetteSectorRefined_eq_zero_iff]
    exact isZeroPlaquette_timeReflection_iff hL p
  by_cases hzero : plaquetteSectorRefined p = LinkSector.zero
  · rw [if_pos hzero, if_pos (hzero_iff.mpr hzero)]
  · rw [if_neg hzero, if_neg (fun h => hzero (hzero_iff.mp h))]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.timeReflectionPlaquette_diag_iff
#print axioms PF.YangMills.wilsonActionDensity_diag_pair_eq_zero
#print axioms PF.YangMills.wilsonActionMinusR_timeReflection
#print axioms PF.YangMills.wilsonActionPlusR_timeReflection
#print axioms PF.YangMills.wilsonActionZero_timeReflection
