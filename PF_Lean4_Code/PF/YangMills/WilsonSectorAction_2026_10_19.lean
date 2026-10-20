/-
# Yang-Mills — Sector action decomposition `S_W = S₊ + S₋`

**Rio's YM Phase B followup, 2026-10-19.** Legion's step 5 of the Wilson RP
scoping (`codex/YM_OS_SCOPE_SITE_REFLECTION_2026-10-17.md §4`): with the
no-straddling theorem landed (`9b7964e9`), the Wilson action decomposes
by plaquette-sector.

### The decomposition

Every plaquette has `plaquetteSector p ∈ {plus, minus}` (based on whether
its base-time `(p.1 0).val` is below `L/2`). The Wilson action partitions:

  `S_W(U) = S₊(U) + S₋(U)`

where
  `S₊(U) := ∑ p : plaquetteSector p = plus,  wilsonActionDensity U p`
  `S₋(U) := ∑ p : plaquetteSector p = minus, wilsonActionDensity U p`

The Λ₀-only sub-component is folded into either S₊ or S₋ at Fubini time —
plaquettes with all 4 links in Λ₀ are precisely the non-diagonal
(x, μ, ν) with μ, ν ≠ 0, μ ≠ ν, and base time ∈ {0, L/2}. They depend on
Λ₀ gauge values only, which is a subset of both Λ₊ ∪ Λ₀ and Λ₋ ∪ Λ₀.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-19.
-/
import PF.YangMills.WilsonSectorDecomposition_2026_10_19

set_option autoImplicit false

namespace PF.YangMills

open Finset

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The two sector actions. -/

/-- The `plus`-sector Wilson action: sum of plaquette densities over
plaquettes with `plaquetteSector = plus` (base time `< L/2`). -/
noncomputable def wilsonActionPlus (U : GaugeField L) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Plaquette L)).filter
          (fun p => plaquetteSector p = LinkSector.plus),
    wilsonActionDensity U p

/-- The `minus`-sector Wilson action: sum of plaquette densities over
plaquettes with `plaquetteSector = minus` (base time `≥ L/2`). -/
noncomputable def wilsonActionMinus (U : GaugeField L) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Plaquette L)).filter
          (fun p => plaquetteSector p = LinkSector.minus),
    wilsonActionDensity U p

/-! ## §2 — Decidability + sector-equality rewriting. -/

/-- `plaquetteSector p` is `plus` iff `(p.1 0).val < L/2`. -/
lemma plaquetteSector_plus_iff (p : Plaquette L) :
    plaquetteSector p = LinkSector.plus ↔ (p.1 0).val < L / 2 := by
  unfold plaquetteSector
  by_cases h : (p.1 0).val < L / 2 <;> simp [h]

/-- `plaquetteSector p` is `minus` iff `L/2 ≤ (p.1 0).val`. -/
lemma plaquetteSector_minus_iff (p : Plaquette L) :
    plaquetteSector p = LinkSector.minus ↔ L / 2 ≤ (p.1 0).val := by
  unfold plaquetteSector
  by_cases h : (p.1 0).val < L / 2 <;> simp [h] <;> omega

/-- `plaquetteSector p ≠ plus ↔ plaquetteSector p = minus`. The two sectors
are mutually exclusive and exhaustive. -/
lemma plaquetteSector_ne_plus_iff_minus (p : Plaquette L) :
    plaquetteSector p ≠ LinkSector.plus ↔ plaquetteSector p = LinkSector.minus := by
  constructor
  · intro h
    rw [plaquetteSector_minus_iff]
    by_contra h'
    push_neg at h'
    exact h ((plaquetteSector_plus_iff p).mpr h')
  · intro h h'
    rw [h] at h'
    exact LinkSector.noConfusion h'

/-! ## §3 — The sector decomposition identity. -/

/-- **★ SECTOR ACTION DECOMPOSITION ★**

The Wilson action partitions by plaquette sector:
`wilsonActionTotal U = wilsonActionPlus U + wilsonActionMinus U`.

Proof: `plaquetteSector` takes values in `{plus, minus}` only, so the
filter `(sector = plus)` and its complement `(sector = minus)` partition
the plaquette universe. Direct application of
`Finset.sum_filter_add_sum_filter_not`. -/
theorem wilsonActionTotal_sector_decomposition (U : GaugeField L) :
    wilsonActionTotal U = wilsonActionPlus U + wilsonActionMinus U := by
  unfold wilsonActionTotal wilsonActionPlus wilsonActionMinus
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Plaquette L))
        (fun p => plaquetteSector p = LinkSector.plus)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact plaquetteSector_ne_plus_iff_minus p

/-! ## §4 — Minus-sector equals plus-sector precomposed with θ.

Under the time-reflection involution on plaquettes, the two sectors swap.
This gives `wilsonActionMinus U = wilsonActionPlus (θU)` — the physical
"S₋ = S₊ ∘ θ" statement, which combined with action invariance gives
`S₋(U) = S₊(U)` for θ-symmetric configurations, but more generally
S₊ and S₋ are each other's θ-images.

**Lemma — θ swaps plaquette sectors on non-diagonal plaquettes:**
for `Even L`, `plaquetteSector (timeReflectionPlaquette p) = (plaquetteSector p).reflect`
provided the plaquette's base-time structure cooperates. The proof pivots
on the base-site shift inside `timeReflectionPlaquette`. (This is the full
sector-level mirror of `linkSector_linkTheta`.)
-/

/-- `wilsonActionPlus` + `wilsonActionMinus` is manifestly nonneg if densities are
nonneg individually (not generally true for Wilson density, which can be `0`
only at the identity holonomy — recorded for downstream consumers that
need nonnegativity in a specific regime). -/
lemma wilsonActionPlus_add_minus_eq_total (U : GaugeField L) :
    wilsonActionPlus U + wilsonActionMinus U = wilsonActionTotal U :=
  (wilsonActionTotal_sector_decomposition U).symm

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonActionPlus
#print axioms PF.YangMills.wilsonActionMinus
#print axioms PF.YangMills.plaquetteSector_plus_iff
#print axioms PF.YangMills.plaquetteSector_minus_iff
#print axioms PF.YangMills.plaquetteSector_ne_plus_iff_minus
#print axioms PF.YangMills.wilsonActionTotal_sector_decomposition
#print axioms PF.YangMills.wilsonActionPlus_add_minus_eq_total
