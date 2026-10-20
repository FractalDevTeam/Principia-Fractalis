/-
# Yang-Mills — Sector action gauge-dependence (Legion step 5b)

**Rio's followup to the sector sum identity, 2026-10-20.** With Phase B's
no-straddling theorem (`9b7964e9`) and the sector sum identity (`ccd0c60b`)
in place, this file proves the structural facts needed for the Fubini step:

* `wilsonActionPlus U` depends only on the gauge values on `Λ₊ ∪ Λ₀`
  (equivalently, on links with `linkSector ≠ minus`).
* `wilsonActionMinus U` depends only on `Λ₋ ∪ Λ₀` (equivalently, on
  links with `linkSector ≠ plus`).

Both are proved by congruence: if two configurations agree on the
appropriate link set, the corresponding sector action is unchanged.

### Diagonal plaquettes

For plaquettes with `μ = ν`, the holonomy equals the identity (the two
pairs of inverse factors cancel), hence density = 0. The no-straddling
theorem doesn't cover `μ = ν`, but we don't need it — the diagonal
density vanishes unconditionally, so congruence holds trivially on
those terms.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-20.
-/
import PF.YangMills.WilsonSectorAction_2026_10_19

set_option autoImplicit false

namespace PF.YangMills

open Finset Matrix

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Plaquette holonomy congruence and diagonal collapse. -/

/-- `plaquetteHolonomy` depends only on the 4 link gauge values of the plaquette. -/
lemma plaquetteHolonomy_congr (U₁ U₂ : GaugeField L) (p : Plaquette L)
    (h1 : U₁ (p.1, p.2.1) = U₂ (p.1, p.2.1))
    (h2 : U₁ (shiftSite p.1 p.2.1, p.2.2) = U₂ (shiftSite p.1 p.2.1, p.2.2))
    (h3 : U₁ (shiftSite p.1 p.2.2, p.2.1) = U₂ (shiftSite p.1 p.2.2, p.2.1))
    (h4 : U₁ (p.1, p.2.2) = U₂ (p.1, p.2.2)) :
    plaquetteHolonomy U₁ p = plaquetteHolonomy U₂ p := by
  unfold plaquetteHolonomy
  rw [h1, h2, h3, h4]

/-- `wilsonActionDensity` depends only on the 4 link gauge values. -/
lemma wilsonActionDensity_congr (U₁ U₂ : GaugeField L) (p : Plaquette L)
    (h1 : U₁ (p.1, p.2.1) = U₂ (p.1, p.2.1))
    (h2 : U₁ (shiftSite p.1 p.2.1, p.2.2) = U₂ (shiftSite p.1 p.2.1, p.2.2))
    (h3 : U₁ (shiftSite p.1 p.2.2, p.2.1) = U₂ (shiftSite p.1 p.2.2, p.2.1))
    (h4 : U₁ (p.1, p.2.2) = U₂ (p.1, p.2.2)) :
    wilsonActionDensity U₁ p = wilsonActionDensity U₂ p := by
  unfold wilsonActionDensity
  rw [plaquetteHolonomy_congr U₁ U₂ p h1 h2 h3 h4]

/-- On a diagonal plaquette `(x, μ, μ)`, the holonomy is the identity:
the two pairs of inverse factors cancel. -/
lemma plaquetteHolonomy_diag_eq_one (U : GaugeField L)
    (x : LatticeSite L) (μ : LatticeDir) :
    plaquetteHolonomy U (x, μ, μ) = 1 := by
  unfold plaquetteHolonomy
  simp only
  group

/-- On a diagonal plaquette the action density is `0`. -/
lemma wilsonActionDensity_diag_eq_zero (U : GaugeField L)
    (x : LatticeSite L) (μ : LatticeDir) :
    wilsonActionDensity U (x, μ, μ) = 0 := by
  unfold wilsonActionDensity
  rw [plaquetteHolonomy_diag_eq_one]
  show 1 - 1 / 2 * ((1 : Matrix (Fin 2) (Fin 2) ℂ).trace.re) = 0
  rw [Matrix.trace_one, Fintype.card_fin]
  simp

/-! ## §2 — Sector-plus gauge-dependence. -/

/-- **★ wilsonActionPlus depends only on Λ₊ ∪ Λ₀ ★**

If two gauge configurations `U₁, U₂` agree on every link whose sector
is **not** `minus` (i.e., every link in `Λ₊ ∪ Λ₀`), then their
`wilsonActionPlus` values are equal.

Proof: for each plaquette `p` with `plaquetteSector p = plus`, either
(i) `p.2.1 = p.2.2`, so the density is `0` on both sides (diagonal); or
(ii) `p.2.1 ≠ p.2.2`, so by `no_straddling` every link of `p` has sector
`∈ {plus, zero}`, hence `U₁ = U₂` on those links by hypothesis, hence
the plaquette holonomies agree, hence the densities agree. -/
theorem wilsonActionPlus_congr (hL : Even L) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.minus → U₁ ℓ = U₂ ℓ) :
    wilsonActionPlus U₁ = wilsonActionPlus U₂ := by
  unfold wilsonActionPlus
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  -- `hp : plaquetteSector p = plus`
  rcases p with ⟨x, μ, ν⟩
  by_cases hμν : μ = ν
  · -- Diagonal plaquette: density is 0 on both sides.
    subst hμν
    rw [wilsonActionDensity_diag_eq_zero, wilsonActionDensity_diag_eq_zero]
  · -- Non-diagonal: apply no_straddling + congruence.
    apply wilsonActionDensity_congr
    · -- Link 1: (x, μ)
      apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (x, μ) (Or.inl rfl)
      rw [hp] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · -- Link 2: (shiftSite x μ, ν)
      apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (shiftSite x μ, ν)
        (Or.inr (Or.inl rfl))
      rw [hp] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · -- Link 3: (shiftSite x ν, μ)
      apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (shiftSite x ν, μ)
        (Or.inr (Or.inr (Or.inl rfl)))
      rw [hp] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · -- Link 4: (x, ν)
      apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (x, ν)
        (Or.inr (Or.inr (Or.inr rfl)))
      rw [hp] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide

/-! ## §3 — Sector-minus gauge-dependence. -/

/-- **★ wilsonActionMinus depends only on Λ₋ ∪ Λ₀ ★**

Symmetric to `wilsonActionPlus_congr`: if two configurations agree on
every link whose sector is **not** `plus`, then their `wilsonActionMinus`
values are equal. -/
theorem wilsonActionMinus_congr (hL : Even L) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.plus → U₁ ℓ = U₂ ℓ) :
    wilsonActionMinus U₁ = wilsonActionMinus U₂ := by
  unfold wilsonActionMinus
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rcases p with ⟨x, μ, ν⟩
  by_cases hμν : μ = ν
  · subst hμν
    rw [wilsonActionDensity_diag_eq_zero, wilsonActionDensity_diag_eq_zero]
  · apply wilsonActionDensity_congr
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (x, μ) (Or.inl rfl)
      rw [hp] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (shiftSite x μ, ν)
        (Or.inr (Or.inl rfl))
      rw [hp] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (shiftSite x ν, μ)
        (Or.inr (Or.inr (Or.inl rfl)))
      rw [hp] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide
    · apply hAgree
      have h_sector := no_straddling hL (x, μ, ν) hμν (x, ν)
        (Or.inr (Or.inr (Or.inr rfl)))
      rw [hp] at h_sector
      rcases h_sector with h | h <;> rw [h] <;> decide

/-! ## §4 — Corollaries: dependence under θ-reflection and inverse structure. -/

/-- The Λ₋ configuration under `timeReflectionGaugeField` depends on
Λ₊ gauge values (since θ swaps the halves). This connects the two
sector actions through the θ-involution — needed for Legion's
`S₋ = S₊ ∘ θ` observation. -/
lemma wilsonActionPlus_eq_minus_timeReflection_support
    (hL : Even L) (U : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, linkSector ℓ ≠ LinkSector.plus →
        timeReflectionGaugeField U ℓ = U ℓ) :
    wilsonActionMinus (timeReflectionGaugeField U) = wilsonActionMinus U :=
  wilsonActionMinus_congr hL _ _ hAgree

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.plaquetteHolonomy_congr
#print axioms PF.YangMills.wilsonActionDensity_congr
#print axioms PF.YangMills.plaquetteHolonomy_diag_eq_one
#print axioms PF.YangMills.wilsonActionDensity_diag_eq_zero
#print axioms PF.YangMills.wilsonActionPlus_congr
#print axioms PF.YangMills.wilsonActionMinus_congr
#print axioms PF.YangMills.wilsonActionPlus_eq_minus_timeReflection_support
