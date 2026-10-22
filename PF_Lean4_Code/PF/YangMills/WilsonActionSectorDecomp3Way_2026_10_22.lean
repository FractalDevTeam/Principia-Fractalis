/-
# Yang-Mills — Three-way sector action decomposition `S_W = S_+R + S_0 + S_-R`

**Rio's §2 ACER directive, 2026-10-22.** The 3-way counterpart to the
binary `wilsonActionTotal_sector_decomposition` (`ccd0c60b`), using
`plaquetteSectorRefined` (3-valued) instead of `plaquetteSector` (2-valued).

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-22.
-/
import PF.YangMills.WilsonSectorPlaquetteZero_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open Finset

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **★ THREE-WAY SECTOR DECOMPOSITION ★**

`wilsonActionTotal U = wilsonActionPlusR U + wilsonActionZero U + wilsonActionMinusR U`.

Proof: iterate `Finset.sum_filter_add_sum_filter_not` twice. First split
`univ` into `{refined-plus}` and its complement; then split the complement
into `{refined-zero}` and its complement (which equals `{refined-minus}`
since the refined sector is 3-valued and we've peeled off plus). -/
theorem wilsonActionTotal_sector_decomposition_refined (U : GaugeField L) :
    wilsonActionTotal U
      = wilsonActionPlusR U + wilsonActionZero U + wilsonActionMinusR U := by
  unfold wilsonActionTotal wilsonActionPlusR wilsonActionZero wilsonActionMinusR
  -- Step 1: ∑ p ∈ univ = ∑ p ∈ (plus-filter) + ∑ p ∈ (plus-complement)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Plaquette L))
       (fun p => plaquetteSectorRefined p = LinkSector.plus)]
  -- Step 2: ∑ p ∈ (plus-complement) = ∑ p ∈ (zero-filter) + ∑ p ∈ (zero-plus-complement)
  -- But: filter_not (plus) ∩ filter (zero) = filter (zero).
  -- And filter_not (plus) ∩ filter_not (zero) = filter (minus).
  have h_plus_complement :
      (Finset.univ : Finset (Plaquette L)).filter
        (fun p => ¬ plaquetteSectorRefined p = LinkSector.plus)
      = (Finset.univ.filter (fun p => plaquetteSectorRefined p = LinkSector.zero))
      ∪ (Finset.univ.filter (fun p => plaquetteSectorRefined p = LinkSector.minus)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    constructor
    · intro h_not_plus
      by_cases hz : plaquetteSectorRefined p = LinkSector.zero
      · exact Or.inl hz
      · right
        -- plaquetteSectorRefined ≠ plus, ≠ zero → must be minus
        match h : plaquetteSectorRefined p with
        | LinkSector.plus => exact absurd h h_not_plus
        | LinkSector.zero => exact absurd h hz
        | LinkSector.minus => rfl
    · rintro (h_zero | h_minus)
      · rw [h_zero]; decide
      · rw [h_minus]; decide
  rw [h_plus_complement, Finset.sum_union]
  · -- Now goal: `plus-sum + (zero-sum + minus-sum) = plus-sum + zero-sum + minus-sum`
    ring
  · -- Disjointness: zero-filter and minus-filter are disjoint
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    rw [hp] at hp'
    exact LinkSector.noConfusion hp'

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonActionTotal_sector_decomposition_refined
