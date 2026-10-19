/-
# Yang-Mills — Lattice sector decomposition under site reflection

**Rio's YM step 4 (sector-split route A for Wilson RP), 2026-10-19.** Legion's
scoping `codex/YM_OS_SCOPE_SITE_REFLECTION_2026-10-17.md §4` identified that
site reflection admits a straddle-free three-way split

  Λ(L) = Λ₊ ⊔ Λ₀ ⊔ Λ₋   (requires `Even L`)

* `Λ₊` — temporal links with base `t ∈ [0, L/2 − 1]`,
         spatial links at `t ∈ [1, L/2 − 1]`
* `Λ₀` — spatial links at `t ∈ {0, L/2}` (both boundary slices)
* `Λ₋` — temporal links with base `t ∈ [L/2, L − 1]`,
         spatial links at `t ∈ [L/2 + 1, L − 1]`

The link-involution `linkTheta` (base-site reflection + the ê₀-shift on
temporal links) swaps `Λ₊` and `Λ₋` and fixes `Λ₀`.

**This file is Phase A — sector classification + swap property.** The
no-straddling plaquette theorem (Legion's step 4, HIGH difficulty) and
the sector-wise action decomposition follow in subsequent files.

### Three-axiom bar

Every declaration kernel-clean `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-19.
-/
import PF.YangMills.WilsonActionReflectionInvariance_2026_10_18

set_option autoImplicit false

namespace PF.YangMills

open Finset

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Sector labels. -/

/-- A link-sector label for the three-way split under site reflection. -/
inductive LinkSector | plus | zero | minus
deriving DecidableEq, Repr

namespace LinkSector

/-- Reflection action on sector labels: swaps `plus ↔ minus`, fixes `zero`. -/
def reflect : LinkSector → LinkSector
  | plus => minus
  | zero => zero
  | minus => plus

@[simp] lemma reflect_plus : reflect plus = minus := rfl
@[simp] lemma reflect_zero : reflect zero = zero := rfl
@[simp] lemma reflect_minus : reflect minus = plus := rfl

/-- `reflect` is an involution. -/
lemma reflect_involutive : Function.Involutive reflect := by
  intro s
  cases s <;> rfl

end LinkSector

/-! ## §2 — The link involution `linkTheta` (set-level, forgets the inverse).

The gauge-field reflection `timeReflectionGaugeField` on a temporal link
*composes* a base-site shift with an SU(2) inverse. For the purposes of
counting / sector classification, we only need the base-site shift. This
`linkTheta` captures that structure as an involution on `LatticeLink L`. -/

/-- Site-level reflection on links: reflect the base site, and for temporal
links additionally subtract `ê₀` to track the actual link endpoints. -/
def linkTheta (ℓ : LatticeLink L) : LatticeLink L :=
  if ℓ.2 = 0 then
    (shiftTimeNeg (timeReflectionSite ℓ.1), 0)
  else
    (timeReflectionSite ℓ.1, ℓ.2)

/-- `linkTheta` is an involution on `LatticeLink L`. -/
lemma linkTheta_involutive : Function.Involutive (linkTheta (L := L)) := by
  intro ℓ
  rcases ℓ with ⟨x, d⟩
  unfold linkTheta
  simp only
  by_cases hd : d = 0
  · subst hd
    simp only [if_true]
    exact Prod.mk.injEq .. |>.mpr
      ⟨shiftTimeNeg_timeReflectionSite_involutive x, rfl⟩
  · simp only [if_neg hd]
    exact Prod.mk.injEq .. |>.mpr
      ⟨timeReflectionSite_involutive x, rfl⟩

/-- `linkTheta` is a bijection. -/
lemma linkTheta_bijective : Function.Bijective (linkTheta (L := L)) :=
  linkTheta_involutive.bijective

/-! ## §3 — The sector classification (requires `Even L`). -/

/-- Classify a lattice link into `plus | zero | minus` under site reflection.
The classification uses `L/2` as the exact midpoint; it is only
semantically meaningful when `L` is even, but the function itself is
defined on all `L ≥ 1`. (The `Even L` hypothesis is attached to the
downstream theorems that use the classification, not to the definition.) -/
def linkSector (ℓ : LatticeLink L) : LinkSector :=
  let t := (ℓ.1 0).val
  let M := L / 2
  if ℓ.2 = 0 then
    -- temporal link: based at t; spans [t, t+1 mod L]
    if t < M then LinkSector.plus else LinkSector.minus
  else
    -- spatial link at time t
    if t = 0 ∨ t = M then LinkSector.zero
    else if t < M then LinkSector.plus
    else LinkSector.minus

/-! ## §4 — Time-value computations under `shiftTimeNeg ∘ timeReflectionSite`
and `timeReflectionSite`. The classification only needs case-based values. -/

/-- The time value of `θx`: `(θx 0).val = (L - (x 0).val) % L`. -/
lemma timeReflectionSite_time_val (x : LatticeSite L) :
    ((timeReflectionSite x) 0).val = (L - (x 0).val) % L := by
  unfold timeReflectionSite
  rw [Function.update_self, Fin.neg_def]

/-- The time value of `shiftTimeNeg(θx)` for `L ≥ 2`: an explicit case
split on whether `(x 0).val = 0`. -/
lemma shiftTimeNeg_timeReflectionSite_time_val (hL2 : 2 ≤ L) (x : LatticeSite L) :
    ((shiftTimeNeg (timeReflectionSite x)) 0).val
      = if (x 0).val = 0 then L - 1 else L - (x 0).val - 1 := by
  unfold shiftTimeNeg
  rw [Function.update_self]
  rw [Fin.sub_def]
  rw [timeReflectionSite_time_val]
  have h1val : ((1 : Fin L) : ℕ) = 1 := by
    simp [Fin.val_one', Nat.mod_eq_of_lt (show 1 < L by omega)]
  rw [h1val]
  set t := (x 0).val with ht_def
  have ht_lt : t < L := (x 0).isLt
  by_cases ht0 : t = 0
  · simp only [ht0, if_pos rfl]
    have h_mod1 : (L - 0) % L = 0 := by
      rw [Nat.sub_zero, Nat.mod_self]
    -- goal: (L - 1 + (L - 0) % L) % L = L - 1   (order: L-1 first per Fin.sub_def)
    rw [h_mod1, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)
  · have ht_pos : 0 < t := Nat.pos_of_ne_zero ht0
    simp only [if_neg ht0]
    have h_mod1 : (L - t) % L = L - t := Nat.mod_eq_of_lt (by omega)
    rw [h_mod1]
    -- goal: (L - 1 + (L - t)) % L = L - t - 1
    have h_eq : (L - 1) + (L - t) = L + (L - t - 1) := by omega
    rw [h_eq, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)

/-! ## §5 — `linkTheta` reflects sector labels, under `Even L`. -/

/-- **Key:** for `Even L`, the sector classification intertwines with the
link involution: `linkSector (linkTheta ℓ) = (linkSector ℓ).reflect`. -/
theorem linkSector_linkTheta (hL : Even L) (ℓ : LatticeLink L) :
    linkSector (linkTheta ℓ) = (linkSector ℓ).reflect := by
  obtain ⟨M, hM⟩ := hL
  have hL_eq : L = 2 * M := by omega
  have hM_pos : 0 < M := by have := Nat.pos_of_ne_zero (NeZero.ne L); omega
  have hM_eq : L / 2 = M := by omega
  have hL2 : 2 ≤ L := by omega
  rcases ℓ with ⟨x, d⟩
  set t := (x 0).val with ht_def
  have ht_lt : t < L := (x 0).isLt
  -- Dispatch on direction + relation of t to M (and to 0).
  unfold linkTheta linkSector
  simp only
  by_cases hd : d = 0
  · -- Temporal link
    subst hd
    simp only [if_true]
    rw [shiftTimeNeg_timeReflectionSite_time_val hL2]
    rw [hM_eq]
    rw [← ht_def]
    -- Image: if t = 0 then L - 1 else L - t - 1.
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · -- t = 0: image = L - 1 = 2M - 1 ≥ M. Original: plus. Image: minus.
      rw [ht0]
      simp only [if_pos rfl]
      have h_img_ge : ¬ (L - 1 < M) := by omega
      simp [h_img_ge, hM_pos, LinkSector.reflect]
    · -- t > 0: image = L - t - 1.
      have h_t_ne : t ≠ 0 := Nat.pos_iff_ne_zero.mp ht0
      simp only [if_neg h_t_ne]
      by_cases ht_lt_M : t < M
      · have h_img_ge : ¬ (L - t - 1 < M) := by omega
        simp [h_img_ge, ht_lt_M, LinkSector.reflect]
      · have h_img_lt : L - t - 1 < M := by omega
        simp [h_img_lt, ht_lt_M, LinkSector.reflect]
  · -- Spatial link
    simp only [if_neg hd]
    rw [timeReflectionSite_time_val]
    rw [hM_eq]
    rw [← ht_def]
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · rw [ht0]
      have h_mod : (L - 0) % L = 0 := by rw [Nat.sub_zero, Nat.mod_self]
      rw [h_mod]
      simp [LinkSector.reflect, hM_pos.ne']
    · have h_mod : (L - t) % L = L - t := Nat.mod_eq_of_lt (by omega)
      rw [h_mod]
      by_cases ht_eq_M : t = M
      · rw [ht_eq_M]
        have h1 : L - M = M := by omega
        rw [h1]
        simp [LinkSector.reflect]
      · by_cases ht_lt_M : t < M
        · have h_orig_ne_zero : t ≠ 0 := Nat.pos_iff_ne_zero.mp ht0
          have h_img_ne_zero : L - t ≠ 0 := by omega
          have h_img_ne_M : L - t ≠ M := by omega
          have h_img_not_lt : ¬ (L - t < M) := by omega
          simp [h_orig_ne_zero, ht_eq_M, ht_lt_M, h_img_ne_zero, h_img_ne_M,
                h_img_not_lt, LinkSector.reflect]
        · have ht_gt_M : M < t := lt_of_le_of_ne (not_lt.mp ht_lt_M) (Ne.symm ht_eq_M)
          have h_orig_ne_zero : t ≠ 0 := Nat.pos_iff_ne_zero.mp ht0
          have h_img_ne_zero : L - t ≠ 0 := by omega
          have h_img_ne_M : L - t ≠ M := by omega
          have h_img_lt : L - t < M := by omega
          simp [h_orig_ne_zero, ht_eq_M, ht_lt_M, h_img_ne_zero, h_img_ne_M,
                h_img_lt, LinkSector.reflect]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.LinkSector.reflect
#print axioms PF.YangMills.LinkSector.reflect_involutive
#print axioms PF.YangMills.linkTheta
#print axioms PF.YangMills.linkTheta_involutive
#print axioms PF.YangMills.linkTheta_bijective
#print axioms PF.YangMills.linkSector
#print axioms PF.YangMills.timeReflectionSite_time_val
#print axioms PF.YangMills.shiftTimeNeg_timeReflectionSite_time_val
#print axioms PF.YangMills.linkSector_linkTheta
