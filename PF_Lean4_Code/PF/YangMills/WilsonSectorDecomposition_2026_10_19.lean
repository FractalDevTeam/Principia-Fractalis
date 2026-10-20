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

/-! ## §6 — Phase B: no-straddling plaquette theorem.

**Claim:** For `Even L` and a non-diagonal plaquette `p = (x, μ, ν)` with
`μ ≠ ν`, every one of `p`'s four links has sector `plaquetteSector p` or
`zero`. In particular, no plaquette has both a `Λ₊` link and a `Λ₋` link.

The diagonal case `μ = ν = 0` is excluded (plaquette holonomy = 1, density
= 0, so these contribute nothing to the Wilson action). Legion measured
0 straddling for all non-diagonal plaquettes at L = 4, 6, 8.
-/

/-- The sector assigned to a plaquette based on its base time. Diagonal
plaquettes get `plus` by default (density 0, so assignment is arbitrary). -/
def plaquetteSector (p : Plaquette L) : LinkSector :=
  if (p.1 0).val < L / 2 then LinkSector.plus else LinkSector.minus

/-- Time coordinate of `shiftSite x μ` for a spatial direction `μ ≠ 0` is
unchanged (modification is in coord `μ`, not coord 0). -/
lemma shiftSite_spatial_time_val {μ : LatticeDir} (hμ : μ ≠ 0)
    (x : LatticeSite L) :
    ((shiftSite x μ) 0).val = (x 0).val := by
  unfold shiftSite
  rw [Function.update_of_ne (Ne.symm hμ)]

/-- Time coordinate of `shiftSite x 0`: `((x + ê₀) 0).val = ((x 0).val + 1) % L`. -/
lemma shiftSite_temporal_time_val (x : LatticeSite L) :
    ((shiftSite x 0) 0).val = ((x 0).val + 1) % L := by
  unfold shiftSite
  rw [Function.update_self]
  rw [Fin.add_def]
  have h1val : ((1 : Fin L) : ℕ) = 1 % L := Fin.val_one' L
  rw [h1val]
  rcases eq_or_ne L 1 with hL1 | hL1
  · subst hL1
    simp [Nat.mod_one]
  · have hL_ge : 2 ≤ L := by
      have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
      omega
    rw [Nat.mod_eq_of_lt (by omega : 1 < L)]

/-! ## §7 — Sector characterization by direction and base time. -/

/-- A temporal link at base time `t < M` is in `plus`. -/
lemma linkSector_temporal_t_lt_half (ℓ : LatticeLink L) (hd : ℓ.2 = 0)
    (ht : (ℓ.1 0).val < L / 2) : linkSector ℓ = LinkSector.plus := by
  unfold linkSector
  simp [hd, ht]

/-- A temporal link at base time `t ≥ M` is in `minus`. -/
lemma linkSector_temporal_t_ge_half (ℓ : LatticeLink L) (hd : ℓ.2 = 0)
    (ht : L / 2 ≤ (ℓ.1 0).val) : linkSector ℓ = LinkSector.minus := by
  unfold linkSector
  simp [hd, Nat.not_lt.mpr ht]

/-- A spatial link at time `t` with `t ≤ M` is `plus` or `zero`. -/
lemma linkSector_spatial_t_le_half (ℓ : LatticeLink L) (hd : ℓ.2 ≠ 0)
    (ht : (ℓ.1 0).val ≤ L / 2) :
    linkSector ℓ = LinkSector.plus ∨ linkSector ℓ = LinkSector.zero := by
  unfold linkSector
  simp only [hd, if_false]
  by_cases h0 : (ℓ.1 0).val = 0
  · right
    simp [h0]
  by_cases hM : (ℓ.1 0).val = L / 2
  · right
    simp [hM]
  · left
    have ht_lt : (ℓ.1 0).val < L / 2 := lt_of_le_of_ne ht hM
    simp [ht_lt, h0, hM]

/-- A spatial link at time `t` with `t = 0 ∨ t ≥ M` is `minus` or `zero`. -/
lemma linkSector_spatial_t_ge_half_or_zero (ℓ : LatticeLink L) (hd : ℓ.2 ≠ 0)
    (ht : (ℓ.1 0).val = 0 ∨ L / 2 ≤ (ℓ.1 0).val) :
    linkSector ℓ = LinkSector.minus ∨ linkSector ℓ = LinkSector.zero := by
  unfold linkSector
  simp only [hd, if_false]
  rcases ht with h0 | hM_le
  · right
    simp [h0]
  by_cases hM : (ℓ.1 0).val = L / 2
  · right
    simp [hM]
  · have hM_lt : L / 2 < (ℓ.1 0).val :=
      lt_of_le_of_ne hM_le (Ne.symm hM)
    have h0 : (ℓ.1 0).val ≠ 0 := by
      intro h0_eq
      rw [h0_eq] at hM_lt
      exact Nat.not_lt_zero _ hM_lt
    left
    simp [h0, hM, Nat.not_lt.mpr (le_of_lt hM_lt)]

/-! ## §8 — Plaquette-link lemmas: each link is `plaquetteSector p` or `zero`
for `Even L`, non-diagonal plaquette (`μ ≠ ν`). -/

variable {μ ν : LatticeDir}

/-- Case: `t < M`. Every link of a non-diagonal plaquette is `plus` or `zero`. -/
lemma plaquette_links_plusOrZero (hL : Even L) (p : Plaquette L)
    (hμν : p.2.1 ≠ p.2.2)
    (ht : (p.1 0).val < L / 2) (ℓ : LatticeLink L)
    (hℓ : ℓ = (p.1, p.2.1) ∨ ℓ = (shiftSite p.1 p.2.1, p.2.2)
             ∨ ℓ = (shiftSite p.1 p.2.2, p.2.1) ∨ ℓ = (p.1, p.2.2)) :
    linkSector ℓ = LinkSector.plus ∨ linkSector ℓ = LinkSector.zero := by
  obtain ⟨M, hM⟩ := hL
  have hL_eq : L = 2 * M := by omega
  have hM_pos : 0 < M := by have := Nat.pos_of_ne_zero (NeZero.ne L); omega
  have hM_eq : L / 2 = M := by omega
  rw [hM_eq] at ht
  -- Links 1, 4: base time t; links 2, 3: base time depends on direction.
  -- For each case, prove the sector lemma.
  rcases hℓ with h1 | h2 | h3 | h4
  · -- Link 1: (p.1, p.2.1), base time t
    subst h1
    by_cases hd : p.2.1 = 0
    · left
      apply linkSector_temporal_t_lt_half _ hd
      rw [hM_eq]; exact ht
    · apply linkSector_spatial_t_le_half _ hd
      rw [hM_eq]; exact le_of_lt ht
  · -- Link 2: (shiftSite p.1 p.2.1, p.2.2)
    subst h2
    by_cases hd1 : p.2.1 = 0
    · -- μ = 0, so ν ≠ 0 (by hμν). Base time of (shiftSite x 0, ν) is (t+1) % L.
      have hd2 : p.2.2 ≠ 0 := by rw [hd1] at hμν; exact fun h => hμν h.symm
      apply linkSector_spatial_t_le_half _ hd2
      show ((shiftSite p.1 p.2.1) 0).val ≤ L / 2
      rw [hd1, shiftSite_temporal_time_val, hM_eq]
      have ht_le : (p.1 0).val ≤ M - 1 := by omega
      have h_mod : ((p.1 0).val + 1) % L = (p.1 0).val + 1 := by
        apply Nat.mod_eq_of_lt
        have : (p.1 0).val + 1 ≤ M := by omega
        omega
      rw [h_mod]; omega
    · -- μ ≠ 0: base time of (shiftSite x μ, ν) is t
      by_cases hd2 : p.2.2 = 0
      · left
        apply linkSector_temporal_t_lt_half _ hd2
        rw [shiftSite_spatial_time_val hd1, hM_eq]; exact ht
      · apply linkSector_spatial_t_le_half _ hd2
        rw [shiftSite_spatial_time_val hd1, hM_eq]; exact le_of_lt ht
  · -- Link 3: (shiftSite p.1 p.2.2, p.2.1)
    subst h3
    by_cases hd2 : p.2.2 = 0
    · have hd1 : p.2.1 ≠ 0 := by rw [hd2] at hμν; exact hμν
      apply linkSector_spatial_t_le_half _ hd1
      show ((shiftSite p.1 p.2.2) 0).val ≤ L / 2
      rw [hd2, shiftSite_temporal_time_val, hM_eq]
      have ht_le : (p.1 0).val ≤ M - 1 := by omega
      have h_mod : ((p.1 0).val + 1) % L = (p.1 0).val + 1 := by
        apply Nat.mod_eq_of_lt
        have : (p.1 0).val + 1 ≤ M := by omega
        omega
      rw [h_mod]; omega
    · by_cases hd1 : p.2.1 = 0
      · left
        apply linkSector_temporal_t_lt_half _ hd1
        rw [shiftSite_spatial_time_val hd2, hM_eq]; exact ht
      · apply linkSector_spatial_t_le_half _ hd1
        rw [shiftSite_spatial_time_val hd2, hM_eq]; exact le_of_lt ht
  · -- Link 4: (p.1, p.2.2)
    subst h4
    by_cases hd : p.2.2 = 0
    · left
      apply linkSector_temporal_t_lt_half _ hd
      rw [hM_eq]; exact ht
    · apply linkSector_spatial_t_le_half _ hd
      rw [hM_eq]; exact le_of_lt ht

/-- Case: `t ≥ M`. Every link of a non-diagonal plaquette is `minus` or `zero`. -/
lemma plaquette_links_minusOrZero (hL : Even L) (p : Plaquette L)
    (hμν : p.2.1 ≠ p.2.2)
    (ht : L / 2 ≤ (p.1 0).val) (ℓ : LatticeLink L)
    (hℓ : ℓ = (p.1, p.2.1) ∨ ℓ = (shiftSite p.1 p.2.1, p.2.2)
             ∨ ℓ = (shiftSite p.1 p.2.2, p.2.1) ∨ ℓ = (p.1, p.2.2)) :
    linkSector ℓ = LinkSector.minus ∨ linkSector ℓ = LinkSector.zero := by
  obtain ⟨M, hM⟩ := hL
  have hL_eq : L = 2 * M := by omega
  have hM_pos : 0 < M := by have := Nat.pos_of_ne_zero (NeZero.ne L); omega
  have hM_eq : L / 2 = M := by omega
  rw [hM_eq] at ht
  have h_t_lt : (p.1 0).val < L := (p.1 0).isLt
  rcases hℓ with h1 | h2 | h3 | h4
  · subst h1
    by_cases hd : p.2.1 = 0
    · left
      apply linkSector_temporal_t_ge_half _ hd
      rw [hM_eq]; exact ht
    · apply linkSector_spatial_t_ge_half_or_zero _ hd
      right; rw [hM_eq]; exact ht
  · subst h2
    by_cases hd1 : p.2.1 = 0
    · have hd2 : p.2.2 ≠ 0 := by rw [hd1] at hμν; exact fun h => hμν h.symm
      apply linkSector_spatial_t_ge_half_or_zero _ hd2
      show ((shiftSite p.1 p.2.1) 0).val = 0 ∨ L / 2 ≤ ((shiftSite p.1 p.2.1) 0).val
      rw [hd1, shiftSite_temporal_time_val, hM_eq]
      -- (t+1) % L: either = 0 (when t = L-1) or ≥ M+1 ≥ M.
      by_cases h_t_last : (p.1 0).val = L - 1
      · left
        rw [h_t_last]
        have : L - 1 + 1 = L := by omega
        rw [this, Nat.mod_self]
      · right
        have h_t_lt_last : (p.1 0).val + 1 < L := by omega
        have h_mod : ((p.1 0).val + 1) % L = (p.1 0).val + 1 :=
          Nat.mod_eq_of_lt h_t_lt_last
        rw [h_mod]; omega
    · by_cases hd2 : p.2.2 = 0
      · left
        apply linkSector_temporal_t_ge_half _ hd2
        rw [shiftSite_spatial_time_val hd1, hM_eq]; exact ht
      · apply linkSector_spatial_t_ge_half_or_zero _ hd2
        right; rw [shiftSite_spatial_time_val hd1, hM_eq]; exact ht
  · subst h3
    by_cases hd2 : p.2.2 = 0
    · have hd1 : p.2.1 ≠ 0 := by rw [hd2] at hμν; exact hμν
      apply linkSector_spatial_t_ge_half_or_zero _ hd1
      show ((shiftSite p.1 p.2.2) 0).val = 0 ∨ L / 2 ≤ ((shiftSite p.1 p.2.2) 0).val
      rw [hd2, shiftSite_temporal_time_val, hM_eq]
      by_cases h_t_last : (p.1 0).val = L - 1
      · left
        rw [h_t_last]
        have : L - 1 + 1 = L := by omega
        rw [this, Nat.mod_self]
      · right
        have h_t_lt_last : (p.1 0).val + 1 < L := by omega
        have h_mod : ((p.1 0).val + 1) % L = (p.1 0).val + 1 :=
          Nat.mod_eq_of_lt h_t_lt_last
        rw [h_mod]; omega
    · by_cases hd1 : p.2.1 = 0
      · left
        apply linkSector_temporal_t_ge_half _ hd1
        rw [shiftSite_spatial_time_val hd2, hM_eq]; exact ht
      · apply linkSector_spatial_t_ge_half_or_zero _ hd1
        right; rw [shiftSite_spatial_time_val hd2, hM_eq]; exact ht
  · subst h4
    by_cases hd : p.2.2 = 0
    · left
      apply linkSector_temporal_t_ge_half _ hd
      rw [hM_eq]; exact ht
    · apply linkSector_spatial_t_ge_half_or_zero _ hd
      right; rw [hM_eq]; exact ht

/-! ## §9 — The no-straddling theorem. -/

/-- **★ NO-STRADDLING ★** For `Even L` and non-diagonal plaquette
`p = (x, μ, ν)` with `μ ≠ ν`, every link of `p` has sector
`plaquetteSector p` or `zero`.

Equivalently: no plaquette has both a `Λ₊` link and a `Λ₋` link.
This is Legion's §4 measured property, now a theorem. -/
theorem no_straddling (hL : Even L) (p : Plaquette L)
    (hμν : p.2.1 ≠ p.2.2) (ℓ : LatticeLink L)
    (hℓ : ℓ = (p.1, p.2.1) ∨ ℓ = (shiftSite p.1 p.2.1, p.2.2)
             ∨ ℓ = (shiftSite p.1 p.2.2, p.2.1) ∨ ℓ = (p.1, p.2.2)) :
    linkSector ℓ = plaquetteSector p ∨ linkSector ℓ = LinkSector.zero := by
  unfold plaquetteSector
  by_cases ht : (p.1 0).val < L / 2
  · simp only [if_pos ht]
    exact plaquette_links_plusOrZero hL p hμν ht ℓ hℓ
  · simp only [if_neg ht]
    exact plaquette_links_minusOrZero hL p hμν (Nat.not_lt.mp ht) ℓ hℓ

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
#print axioms PF.YangMills.plaquetteSector
#print axioms PF.YangMills.shiftSite_spatial_time_val
#print axioms PF.YangMills.shiftSite_temporal_time_val
#print axioms PF.YangMills.linkSector_temporal_t_lt_half
#print axioms PF.YangMills.linkSector_temporal_t_ge_half
#print axioms PF.YangMills.linkSector_spatial_t_le_half
#print axioms PF.YangMills.linkSector_spatial_t_ge_half_or_zero
#print axioms PF.YangMills.plaquette_links_plusOrZero
#print axioms PF.YangMills.plaquette_links_minusOrZero
#print axioms PF.YangMills.no_straddling
