/-
# Yang-Mills — Pointwise refined-sector reflection on non-diagonal plaquettes

**Rio's §2 ACER directive, 2026-10-21.** Pointwise plaquette-sector
reflection on non-diagonal plaquettes — the ingredient the sum-level
`S_-R(θU) = S_+R(U)` identity consumes. Full sum identity in a
follow-up (needs `Finset.sum_bij` on non-diagonal + density-zero on
diagonal).

### What this file provides

* **`plaquetteSector_timeReflection_of_nondiag_nonZero`** — binary
  `plaquetteSector` reflects pointwise on non-diagonal non-zero
  plaquettes. Case analysis on `timeReflectionPlaquette`'s four
  branches.
* **`plaquetteSectorRefined_timeReflection_of_nondiag`** — the refined
  sector reflects pointwise on non-diagonal plaquettes (combines the
  above with the zero-sector θ-invariance).

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonSectorPlaquetteSectorReflection_2026_10_21
import PF.YangMills.WilsonSectorPlaquetteZeroActionReflection_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Binary-sector pointwise reflection on non-diagonal non-zero plaquettes. -/

/-- **Binary `plaquetteSector` reflects pointwise on non-diagonal
non-zero plaquettes.** -/
lemma plaquetteSector_timeReflection_of_nondiag_nonZero (hL : Even L)
    (p : Plaquette L) (hnd : p.2.1 ≠ p.2.2) (hnz : ¬ isZeroPlaquette p) :
    plaquetteSector (timeReflectionPlaquette p)
      = (plaquetteSector p).reflect := by
  rcases p with ⟨x, μ, ν⟩
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hν : ν = 0
    · exact absurd hν (fun h => hnd (by simp [h]))
    · -- TF
      have heq : timeReflectionPlaquette (x, (0 : LatticeDir), ν)
               = (shiftTimeNeg (timeReflectionSite x), ν, 0) := by
        unfold timeReflectionPlaquette; simp [hν]
      rw [heq]
      unfold plaquetteSector
      by_cases hs : ((shiftTimeNeg (timeReflectionSite x)) 0).val < L / 2
      · rw [if_pos hs]
        have hs' : L / 2 ≤ (x 0).val :=
          (shiftTimeNeg_timeReflectionSite_sector hL x).mp hs
        rw [if_neg (not_lt.mpr hs')]
        rfl
      · rw [if_neg hs]
        have hs' : ¬ L / 2 ≤ (x 0).val :=
          fun hle => hs ((shiftTimeNeg_timeReflectionSite_sector hL x).mpr hle)
        rw [if_pos (lt_of_not_ge hs')]
        rfl
  · by_cases hν : ν = 0
    · subst hν
      -- FT
      have heq : timeReflectionPlaquette (x, μ, (0 : LatticeDir))
               = (shiftTimeNeg (timeReflectionSite x), 0, μ) := by
        unfold timeReflectionPlaquette; simp [hμ]
      rw [heq]
      unfold plaquetteSector
      by_cases hs : ((shiftTimeNeg (timeReflectionSite x)) 0).val < L / 2
      · rw [if_pos hs]
        have hs' : L / 2 ≤ (x 0).val :=
          (shiftTimeNeg_timeReflectionSite_sector hL x).mp hs
        rw [if_neg (not_lt.mpr hs')]
        rfl
      · rw [if_neg hs]
        have hs' : ¬ L / 2 ≤ (x 0).val :=
          fun hle => hs ((shiftTimeNeg_timeReflectionSite_sector hL x).mpr hle)
        rw [if_pos (lt_of_not_ge hs')]
        rfl
    · -- FF
      have heq : timeReflectionPlaquette (x, μ, ν)
               = (timeReflectionSite x, μ, ν) := by
        unfold timeReflectionPlaquette; simp [hμ, hν]
      rw [heq]
      unfold plaquetteSector
      have h_nonbdry : (x 0).val ≠ 0 ∧ (x 0).val ≠ L / 2 := by
        unfold isZeroPlaquette at hnz
        push_neg at hnz
        exact hnz hμ hν hnd
      by_cases hs : ((timeReflectionSite x) 0).val < L / 2
      · rw [if_pos hs]
        have hs' : L / 2 ≤ (x 0).val :=
          (timeReflectionSite_sector_nonboundary hL x h_nonbdry).mp hs
        rw [if_neg (not_lt.mpr hs')]
        rfl
      · rw [if_neg hs]
        have hs' : ¬ L / 2 ≤ (x 0).val :=
          fun hle => hs ((timeReflectionSite_sector_nonboundary hL x h_nonbdry).mpr hle)
        rw [if_pos (lt_of_not_ge hs')]
        rfl

/-! ## §2 — Refined-sector reflection combining binary + zero. -/

/-- **`plaquetteSectorRefined` reflects pointwise on non-diagonal plaquettes.**

Zero-sector case: both sides are `zero` (fixed under reflect by definition).
Non-zero case: reduce to the binary pointwise lemma. -/
lemma plaquetteSectorRefined_timeReflection_of_nondiag (hL : Even L) (p : Plaquette L)
    (hnd : p.2.1 ≠ p.2.2) :
    plaquetteSectorRefined (timeReflectionPlaquette p)
      = (plaquetteSectorRefined p).reflect := by
  by_cases hzero : isZeroPlaquette p
  · have h1 : plaquetteSectorRefined p = LinkSector.zero :=
      (plaquetteSectorRefined_eq_zero_iff p).mpr hzero
    have h2 : plaquetteSectorRefined (timeReflectionPlaquette p) = LinkSector.zero :=
      (plaquetteSectorRefined_eq_zero_iff _).mpr
        ((isZeroPlaquette_timeReflection_iff hL p).mpr hzero)
    rw [h1, h2]
    rfl
  · unfold plaquetteSectorRefined
    have hzero_θ : ¬ isZeroPlaquette (timeReflectionPlaquette p) :=
      fun h => hzero ((isZeroPlaquette_timeReflection_iff hL p).mp h)
    rw [if_neg hzero, if_neg hzero_θ]
    exact plaquetteSector_timeReflection_of_nondiag_nonZero hL p hnd hzero

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.plaquetteSector_timeReflection_of_nondiag_nonZero
#print axioms PF.YangMills.plaquetteSectorRefined_timeReflection_of_nondiag
