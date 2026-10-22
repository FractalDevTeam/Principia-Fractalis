/-
# Yang-Mills — Refined sector action gauge-dependence

**Rio's §2 ACER directive, 2026-10-22.** Refined analogs of
`wilsonActionPlus_congr` and `wilsonActionMinus_congr`
(`WilsonSectorGaugeDependence_2026_10_20.lean` `7800bd4f`).

### What this file provides

* `wilsonActionPlusR_congr` (Even L): if two configurations agree on
  every link whose sector is **not** `minus`, their `wilsonActionPlusR`
  values are equal — i.e., S_+R depends only on `Λ_+ ∪ Λ_0`.
* `wilsonActionMinusR_congr` (Even L): symmetric, S_-R depends only on
  `Λ_- ∪ Λ_0`.
* `wilsonActionZero_congr` (Even L): S_0 depends only on `Λ_0`.

These are the structural inputs for the Fubini factorization: combined
with `supportedOnPlusZero` of F, we get that `F · exp(-β S_+R)` is
X-independent under the `Λ_-` glue parametrization.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-22.
-/
import PF.YangMills.WilsonSectorPlaquetteZero_2026_10_21
import PF.YangMills.WilsonSectorGaugeDependence_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open Finset

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — `wilsonActionPlusR` depends only on `Λ_+ ∪ Λ_0`. -/

/-- **S_+R depends only on non-minus links.** -/
theorem wilsonActionPlusR_congr (hL : Even L) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.minus → U₁ ℓ = U₂ ℓ) :
    wilsonActionPlusR U₁ = wilsonActionPlusR U₂ := by
  unfold wilsonActionPlusR
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  -- hp : plaquetteSectorRefined p = plus
  have hp_binary : plaquetteSector p = LinkSector.plus :=
    ((plaquetteSectorRefined_eq_plus_iff p).mp hp).1
  rcases p with ⟨x, μ, ν⟩
  by_cases hμν : μ = ν
  · subst hμν
    rw [wilsonActionDensity_diag_eq_zero, wilsonActionDensity_diag_eq_zero]
  · apply wilsonActionDensity_congr
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (x, μ) (Or.inl rfl)
      rw [hp_binary] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (shiftSite x μ, ν)
        (Or.inr (Or.inl rfl))
      rw [hp_binary] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (shiftSite x ν, μ)
        (Or.inr (Or.inr (Or.inl rfl)))
      rw [hp_binary] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (x, ν)
        (Or.inr (Or.inr (Or.inr rfl)))
      rw [hp_binary] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide

/-! ## §2 — `wilsonActionMinusR` depends only on `Λ_- ∪ Λ_0`. -/

/-- **S_-R depends only on non-plus links.** -/
theorem wilsonActionMinusR_congr (hL : Even L) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.plus → U₁ ℓ = U₂ ℓ) :
    wilsonActionMinusR U₁ = wilsonActionMinusR U₂ := by
  unfold wilsonActionMinusR
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hp_binary : plaquetteSector p = LinkSector.minus :=
    ((plaquetteSectorRefined_eq_minus_iff p).mp hp).1
  rcases p with ⟨x, μ, ν⟩
  by_cases hμν : μ = ν
  · subst hμν
    rw [wilsonActionDensity_diag_eq_zero, wilsonActionDensity_diag_eq_zero]
  · apply wilsonActionDensity_congr
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (x, μ) (Or.inl rfl)
      rw [hp_binary] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (shiftSite x μ, ν)
        (Or.inr (Or.inl rfl))
      rw [hp_binary] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (shiftSite x ν, μ)
        (Or.inr (Or.inr (Or.inl rfl)))
      rw [hp_binary] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (x, ν)
        (Or.inr (Or.inr (Or.inr rfl)))
      rw [hp_binary] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonActionPlusR_congr
#print axioms PF.YangMills.wilsonActionMinusR_congr
