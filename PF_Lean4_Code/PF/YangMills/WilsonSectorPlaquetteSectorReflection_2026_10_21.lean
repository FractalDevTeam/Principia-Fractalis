/-
# Yang-Mills — Pointwise plaquette-sector reflection: time-arithmetic layer

**Rio's §2 ACER directive, 2026-10-21.** Proves that the base-time
transformations inside `timeReflectionPlaquette`'s four branches
reflect the plus/minus sector (where the sector depends only on
`time < L/2`). Combined with `isZeroPlaquette_timeReflection_iff`
(zero-sector fixed) and the pointwise plaquette-sector lemma, this
feeds the sum-level `wilsonActionMinusR (θU) = wilsonActionPlusR U`
identity in the next file.

### What this file provides

* **`shiftTimeNeg_timeReflectionSite_sector` (Even L)** — the time
  of `shiftTimeNeg (timeReflectionSite x)` is in `[0, L/2)` iff the
  time of `x` is in `[L/2, L)`. Used in the TT/TF/FT branches.
* **`timeReflectionSite_sector_nonboundary` (Even L)** — the time
  of `timeReflectionSite x` is in `[0, L/2)` iff the time of `x` is
  in `[L/2, L)`, assuming `(x 0).val ∉ {0, L/2}`. Used in the FF
  branch (which only applies to non-zero plaquettes, i.e. non-boundary
  times by `isZeroPlaquette`).

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-22.
-/
import PF.YangMills.WilsonSectorPlaquetteZeroReflection_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Time of `shiftTimeNeg ∘ timeReflectionSite` reflects strictly. -/

/-- **For any `x`: the time of `shiftTimeNeg(timeReflectionSite x)`
reflects the plus/minus sector strictly.**

Base-time transformation: `t ↦ (L - 1 - t) mod L` on the time
coordinate (where `t = (x 0).val`). For Even L, this maps `[0, L/2)`
bijectively to `[L/2, L)` and vice versa — i.e., swaps `plus ↔ minus`. -/
lemma shiftTimeNeg_timeReflectionSite_sector (hL : Even L) (x : LatticeSite L) :
    ((shiftTimeNeg (timeReflectionSite x)) 0).val < L / 2
      ↔ L / 2 ≤ (x 0).val := by
  obtain ⟨k, hk⟩ := hL
  have hhalf : L / 2 = k := by omega
  have hL_pos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hx_lt : (x 0).val < L := (x 0).isLt
  unfold shiftTimeNeg timeReflectionSite
  simp only [Function.update_self]
  -- Compute val: `(-x 0 - 1 : Fin L).val`
  rw [Fin.sub_def, Fin.val_neg, Fin.val_one']
  have h1_mod : (1 : ℕ) % L = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1_mod]
  simp only [Fin.val_mk]
  by_cases hx0 : x 0 = 0
  · rw [if_pos hx0]
    have hval0 : (x 0).val = 0 := by rw [hx0]; rfl
    rw [hval0, Nat.mod_eq_of_lt (by omega : L - 1 + 0 < L)]
    omega
  · rw [if_neg hx0]
    have hx_val_pos : 0 < (x 0).val := by
      rcases Nat.eq_zero_or_pos (x 0).val with h | h
      · exact absurd (Fin.ext h : x 0 = 0) hx0
      · exact h
    have hcompute : (L - 1 + (L - (x 0).val)) % L = L - 1 - (x 0).val := by
      have hrw : L - 1 + (L - (x 0).val) = L + (L - 1 - (x 0).val) := by omega
      rw [hrw, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hcompute]
    omega

/-! ## §2 — Time of `timeReflectionSite` reflects on non-boundary values. -/

/-- **For `(x 0).val ∉ {0, L/2}`: the time of `timeReflectionSite x`
reflects the plus/minus sector strictly.**

Base-time transformation: `t ↦ (L - t) mod L`. For `t ∉ {0, L/2}`
and Even L, this maps `(0, L/2)` bijectively to `(L/2, L)` and vice
versa. -/
lemma timeReflectionSite_sector_nonboundary (hL : Even L) (x : LatticeSite L)
    (h : (x 0).val ≠ 0 ∧ (x 0).val ≠ L / 2) :
    ((timeReflectionSite x) 0).val < L / 2 ↔ L / 2 ≤ (x 0).val := by
  obtain ⟨k, hk⟩ := hL
  have hhalf : L / 2 = k := by omega
  have hL_pos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hx_lt : (x 0).val < L := (x 0).isLt
  obtain ⟨hne_zero, hne_half⟩ := h
  unfold timeReflectionSite
  simp only [Function.update_self]
  rw [Fin.val_neg]
  rw [if_neg (fun hx => hne_zero (by rw [hx]; rfl))]
  omega

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.shiftTimeNeg_timeReflectionSite_sector
#print axioms PF.YangMills.timeReflectionSite_sector_nonboundary
