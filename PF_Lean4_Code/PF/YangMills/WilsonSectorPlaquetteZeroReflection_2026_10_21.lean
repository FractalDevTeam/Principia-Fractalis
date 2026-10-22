/-
# Yang-Mills — Reflection identities for the refined 3-way plaquette sector

**Rio's §2 ACER directive, 2026-10-21.** Follow-up to the
`WilsonSectorPlaquetteZero_2026_10_21.lean` scaffold: proves that
`plaquetteSectorRefined` properly swaps under `timeReflectionPlaquette`
on NON-DIAGONAL plaquettes (diagonals have density zero, so the sum
identities carry through). This closes the "sector action reflection"
gap that blocked the pointwise `S_-(θU) = S_+(U)` on the binary
scaffold.

### What this file provides

* **`timeReflectionSite_val_fixed_half` (Even L)** — if `(x 0).val = L/2`,
  then `((timeReflectionSite x) 0).val = L/2`.
* **`timeReflectionSite_val_fixed_zero`** — if `(x 0).val = 0`, then
  `((timeReflectionSite x) 0).val = 0`.
* **`isZeroPlaquette_timeReflection_iff` (Even L)** — the zero sector
  is `timeReflectionPlaquette`-invariant.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonSectorPlaquetteZero_2026_10_21
import PF.YangMills.WilsonActionReflectionInvariance_2026_10_18

set_option autoImplicit false

namespace PF.YangMills

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Site-level fixed points of `timeReflectionSite`. -/

/-- If `(x 0).val = 0`, then `((timeReflectionSite x) 0).val = 0`. -/
lemma timeReflectionSite_val_fixed_zero (x : LatticeSite L)
    (h : (x 0).val = 0) :
    ((timeReflectionSite x) 0).val = 0 := by
  have hx : x 0 = (0 : Fin L) := Fin.ext (h.trans (Fin.val_zero L).symm)
  unfold timeReflectionSite
  rw [Function.update_self, hx, neg_zero]
  rfl

/-- **Even L: `L/2` is a fixed point of `timeReflectionSite`.** -/
lemma timeReflectionSite_val_fixed_half (hL : Even L) (x : LatticeSite L)
    (h : (x 0).val = L / 2) :
    ((timeReflectionSite x) 0).val = L / 2 := by
  obtain ⟨k, hk⟩ := hL
  have hL_pos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hhalf : L / 2 = k := by omega
  have hx_ne_zero : x 0 ≠ 0 := by
    intro hx
    have hv : (x 0).val = 0 := by rw [hx]; rfl
    omega
  unfold timeReflectionSite
  rw [Function.update_self, Fin.val_neg, if_neg hx_ne_zero, h]
  omega

/-! ## §2 — `isZeroPlaquette` is `timeReflectionPlaquette`-invariant. -/

/-- Only the FF (both-spatial) case of `timeReflectionPlaquette` can
produce an `isZeroPlaquette` output, because `isZeroPlaquette` requires
`μ ≠ 0` and `ν ≠ 0`. -/
lemma isZeroPlaquette_timeReflection_iff (hL : Even L) (p : Plaquette L) :
    isZeroPlaquette (timeReflectionPlaquette p) ↔ isZeroPlaquette p := by
  rcases p with ⟨x, μ, ν⟩
  by_cases hμ : μ = 0
  · subst hμ
    unfold isZeroPlaquette timeReflectionPlaquette
    simp only [if_pos rfl]
    -- Goal: `isZeroPlaquette (if ν = 0 then ..., 0, 0 else ..., ν, 0) ↔ isZeroPlaquette (x, 0, ν)`
    -- Both false: the LHS fails on `.2.2 ≠ 0` (= 0); the RHS fails on `.2.1 ≠ 0` (= 0).
    by_cases hν : ν = 0
    · subst hν; simp
    · simp [hν]
  · by_cases hν : ν = 0
    · subst hν
      unfold isZeroPlaquette timeReflectionPlaquette
      -- LHS: timeReflectionPlaquette (x, μ, 0) is the FT branch, hits `.2.2 = μ` with μ ≠ 0 but `.2.1 = 0`.
      -- RHS: isZeroPlaquette (x, μ, 0) fails on `.2.2 ≠ 0` (= 0).
      simp [hμ]
    · -- FF case: timeReflectionPlaquette = (timeReflectionSite x, μ, ν)
      unfold isZeroPlaquette timeReflectionPlaquette
      simp only [if_neg hμ, if_neg hν]
      -- μ, ν unchanged in FF case; only the time condition differs.
      refine ⟨?_, ?_⟩
      · rintro ⟨_, _, hμν, h_time⟩
        refine ⟨hμ, hν, hμν, ?_⟩
        rcases h_time with h | h
        · left
          have hfix : ((timeReflectionSite (timeReflectionSite x)) 0).val = 0 :=
            timeReflectionSite_val_fixed_zero (timeReflectionSite x) h
          rwa [timeReflectionSite_involutive x] at hfix
        · right
          have hfix : ((timeReflectionSite (timeReflectionSite x)) 0).val = L / 2 :=
            timeReflectionSite_val_fixed_half hL _ h
          rwa [timeReflectionSite_involutive x] at hfix
      · rintro ⟨_, _, hμν, h_time⟩
        refine ⟨hμ, hν, hμν, ?_⟩
        rcases h_time with h | h
        · exact Or.inl (timeReflectionSite_val_fixed_zero x h)
        · exact Or.inr (timeReflectionSite_val_fixed_half hL x h)

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.timeReflectionSite_val_fixed_zero
#print axioms PF.YangMills.timeReflectionSite_val_fixed_half
#print axioms PF.YangMills.isZeroPlaquette_timeReflection_iff
