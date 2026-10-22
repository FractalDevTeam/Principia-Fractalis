/-
# Yang-Mills — Sector-swap bijection `{isMinusLink} ≃ {isPlusLink}`

**Rio's §2 ACER directive, 2026-10-22.** Step 6 subcomponent: the
sector-swap bijection between `Λ_-` and `Λ_+` subtypes, induced by
`linkTheta` + `linkSector_linkTheta` (= `.reflect`).

Needed for the Λ_- measure-preserving restriction: via
`measurePreserving_piCongrLeft`, this equivalence lifts to a measure-
preserving map between `Λ_-` Pi Haar and `Λ_+` Pi Haar — the first
piece of the Fubini-apply change of variable.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-22.
-/
import PF.YangMills.WilsonSectorGluePlus_2026_10_21
import PF.YangMills.WilsonSectorMeasureSplit_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — `linkTheta` sends `isMinusLink` to `isPlusLink` and vice versa. -/

/-- For Even L, `linkTheta` restricted to Λ_- lands in Λ_+. -/
lemma isPlusLink_linkTheta_of_isMinusLink (hL : Even L) {ℓ : LatticeLink L}
    (h : isMinusLink ℓ) : isPlusLink (linkTheta ℓ) := by
  unfold isPlusLink
  rw [linkSector_linkTheta hL]
  unfold isMinusLink at h
  rw [h]
  rfl

/-- For Even L, `linkTheta` restricted to Λ_+ lands in Λ_-. -/
lemma isMinusLink_linkTheta_of_isPlusLink (hL : Even L) {ℓ : LatticeLink L}
    (h : isPlusLink ℓ) : isMinusLink (linkTheta ℓ) := by
  unfold isMinusLink
  rw [linkSector_linkTheta hL]
  unfold isPlusLink at h
  rw [h]
  rfl

/-! ## §2 — The sector-swap equivalence. -/

/-- **`linkTheta`-induced sector-swap bijection `{isMinusLink} ≃ {isPlusLink}`
for Even L.** -/
def sectorSwapEquiv (hL : Even L) :
    Subtype (isMinusLink : LatticeLink L → Prop)
      ≃ Subtype (isPlusLink : LatticeLink L → Prop) where
  toFun ℓ := ⟨linkTheta ℓ.val, isPlusLink_linkTheta_of_isMinusLink hL ℓ.property⟩
  invFun ℓ := ⟨linkTheta ℓ.val, isMinusLink_linkTheta_of_isPlusLink hL ℓ.property⟩
  left_inv := by
    intro ℓ
    apply Subtype.ext
    show linkTheta (linkTheta ℓ.val) = ℓ.val
    exact linkTheta_involutive ℓ.val
  right_inv := by
    intro ℓ
    apply Subtype.ext
    show linkTheta (linkTheta ℓ.val) = ℓ.val
    exact linkTheta_involutive ℓ.val

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.isPlusLink_linkTheta_of_isMinusLink
#print axioms PF.YangMills.isMinusLink_linkTheta_of_isPlusLink
#print axioms PF.YangMills.sectorSwapEquiv
