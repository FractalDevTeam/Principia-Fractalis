/-
# Slit Disc Preconnectedness — Discharge of `SlitDiscPreconnectedReachability`

This file discharges the named topological precondition
`SlitDiscPreconnectedReachability` from
`PF/Analytic/JonquieresIdentityDischarge.lean`:

    IsPreconnected (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain)

The slit disc `ball 0 1 ∩ JonquieresAnalyticDomain` equals the open
unit disc minus the radial segment `(-1, 0]`, because
`JonquieresAnalyticDomain = SlitPlane ∩ Complex.slitPlane =
ℂ \ ((-∞, 0] ∪ [1, ∞))` and `[1, ∞) ∩ ball 0 1 = ∅` (since `|z| < 1`
forces `z.re < 1`).

## Strategy

We decompose the slit disc as the union of three CONVEX (hence
path-connected) pieces inside `ball 0 1`:

* `D_upper := ball 0 1 ∩ H_upper` (upper open half disc)
* `D_lower := ball 0 1 ∩ H_lower` (lower open half disc)
* `D_right := ball 0 1 ∩ H_right` (right open half disc)

where `H_right := {z : ℂ | 0 < z.re}`. Each is convex as an
intersection of two convex sets (`ball 0 1` is convex via
`convex_ball`; `H_upper`, `H_lower`, `H_right` are open
half-spaces). The pairwise overlaps
`D_upper ∩ D_right` and `D_lower ∩ D_right` are nonempty (witnessed
by `(1+i)/2` and `(1-i)/2` respectively, both of modulus `√2/2 < 1`).

Each piece is contained in `JonquieresAnalyticDomain`:
* `D_upper`, `D_lower`: their points have `z.im ≠ 0`, so they avoid
  both `(-∞, 0] ⊆ {z.im = 0}` and `[1, ∞) ⊆ {z.im = 0}`.
* `D_right`: `0 < z.re` excludes `(-∞, 0]`; `|z| < 1` excludes
  `[1, ∞)` (would need `z.re ≥ 1`).

Coverage: any `z ∈ ball 0 1 ∩ JonquieresAnalyticDomain` is in at
least one piece — case split on `z.im`. If `z.im > 0`: `D_upper`.
If `z.im < 0`: `D_lower`. If `z.im = 0`: then `z ∉ (-∞, 0]` forces
`z.re > 0`, so `z ∈ D_right`.

Path-connectedness propagates via two applications of
`IsPathConnected.union` (gluing `D_upper ∪ D_right`, then
`(D_upper ∪ D_right) ∪ D_lower`, with each glue point witnessed
by the explicit overlap point).

Stage L15 — Slit disc preconnectedness discharge (2026-05-21).
-/

import PF.Analytic.JonquieresIdentityDischarge

set_option linter.unusedSimpArgs false

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set

/-! ## The three convex half-discs -/

/-- Upper open half-plane. -/
private def H_upper_J : Set ℂ := {z : ℂ | 0 < z.im}

/-- Lower open half-plane. -/
private def H_lower_J : Set ℂ := {z : ℂ | z.im < 0}

/-- Right open half-plane. -/
private def H_right_J : Set ℂ := {z : ℂ | 0 < z.re}

/-- Upper open half-plane is convex. -/
private theorem H_upper_J_convex : Convex ℝ H_upper_J := by
  unfold H_upper_J
  exact convex_halfSpace_gt
    { map_add := fun x y => by simp [Complex.add_im]
      map_smul := fun c x => by simp [Complex.smul_im] } 0

/-- Lower open half-plane is convex. -/
private theorem H_lower_J_convex : Convex ℝ H_lower_J := by
  unfold H_lower_J
  exact convex_halfSpace_lt
    { map_add := fun x y => by simp [Complex.add_im]
      map_smul := fun c x => by simp [Complex.smul_im] } 0

/-- Right open half-plane is convex. -/
private theorem H_right_J_convex : Convex ℝ H_right_J := by
  unfold H_right_J
  exact convex_halfSpace_gt
    { map_add := fun x y => by simp [Complex.add_re]
      map_smul := fun c x => by simp [Complex.smul_re] } 0

/-- Upper half-disc: open unit disc intersected with the upper half-plane. -/
private def D_upper : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ H_upper_J

/-- Lower half-disc: open unit disc intersected with the lower half-plane. -/
private def D_lower : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ H_lower_J

/-- Right half-disc: open unit disc intersected with the right half-plane. -/
private def D_right : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ H_right_J

/-- The upper half-disc is convex. -/
private theorem D_upper_convex : Convex ℝ D_upper :=
  (convex_ball (0 : ℂ) 1).inter H_upper_J_convex

/-- The lower half-disc is convex. -/
private theorem D_lower_convex : Convex ℝ D_lower :=
  (convex_ball (0 : ℂ) 1).inter H_lower_J_convex

/-- The right half-disc is convex. -/
private theorem D_right_convex : Convex ℝ D_right :=
  (convex_ball (0 : ℂ) 1).inter H_right_J_convex

/-! ## Non-emptiness witnesses -/

/-- `(i/2) ∈ D_upper`: imaginary part `1/2 > 0`, modulus `1/2 < 1`. -/
private theorem half_I_mem_D_upper : (Complex.I / 2) ∈ D_upper := by
  refine ⟨?_, ?_⟩
  · -- modulus
    rw [Metric.mem_ball, dist_zero_right]
    have : ‖Complex.I / 2‖ = 1 / 2 := by
      rw [norm_div, Complex.norm_I, Complex.norm_ofNat]
    rw [this]; norm_num
  · -- 0 < im
    show (0 : ℝ) < (Complex.I / 2).im
    simp [Complex.div_im, Complex.I_im, Complex.I_re]

/-- `(-i/2) ∈ D_lower`. -/
private theorem neg_half_I_mem_D_lower : (-(Complex.I / 2)) ∈ D_lower := by
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    have : ‖-(Complex.I / 2)‖ = 1 / 2 := by
      rw [norm_neg, norm_div, Complex.norm_I, Complex.norm_ofNat]
    rw [this]; norm_num
  · show (-(Complex.I / 2)).im < (0 : ℝ)
    simp [Complex.neg_im, Complex.div_im, Complex.I_im, Complex.I_re]

/-- `(1/2) ∈ D_right`: real part `1/2 > 0`, modulus `1/2 < 1`. -/
private theorem half_mem_D_right : ((1 : ℂ) / 2) ∈ D_right := by
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    have : ‖(1 : ℂ) / 2‖ = 1 / 2 := by
      rw [norm_div, norm_one, Complex.norm_ofNat]
    rw [this]; norm_num
  · show (0 : ℝ) < ((1 : ℂ) / 2).re
    simp [Complex.div_re]

/-! ## Path-connectedness of each piece -/

private theorem D_upper_nonempty : D_upper.Nonempty :=
  ⟨Complex.I / 2, half_I_mem_D_upper⟩

private theorem D_lower_nonempty : D_lower.Nonempty :=
  ⟨-(Complex.I / 2), neg_half_I_mem_D_lower⟩

private theorem D_right_nonempty : D_right.Nonempty :=
  ⟨(1 : ℂ) / 2, half_mem_D_right⟩

private theorem D_upper_isPathConnected : IsPathConnected D_upper :=
  D_upper_convex.isPathConnected D_upper_nonempty

private theorem D_lower_isPathConnected : IsPathConnected D_lower :=
  D_lower_convex.isPathConnected D_lower_nonempty

private theorem D_right_isPathConnected : IsPathConnected D_right :=
  D_right_convex.isPathConnected D_right_nonempty

/-! ## Overlap witnesses -/

/-- `(1+i)/4` lies in both `D_upper` and `D_right`. -/
private theorem one_plus_I_div_four_mem_upper_right :
    ((1 + Complex.I) / 4) ∈ D_upper ∩ D_right := by
  -- modulus² = 2/16 = 1/8 < 1, so modulus < 1.
  have h_norm : ‖(1 + Complex.I) / 4‖ < 1 := by
    have h_sq : ‖(1 + Complex.I) / 4‖ ^ 2 < 1 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      have : Complex.normSq ((1 + Complex.I) / 4) = 1 / 8 := by
        rw [show ((1 + Complex.I) / 4 : ℂ) = (1/4 : ℂ) + (Complex.I / 4) by ring,
            Complex.normSq_add]
        simp [Complex.normSq_apply, Complex.div_re, Complex.div_im,
              Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
              Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
              Complex.conj_re, Complex.conj_im]
        ring
      rw [this]; norm_num
    have h_nonneg : (0 : ℝ) ≤ ‖(1 + Complex.I) / 4‖ := norm_nonneg _
    nlinarith [h_sq, h_nonneg]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- ball
    rw [Metric.mem_ball, dist_zero_right]; exact h_norm
  · -- upper: im > 0
    show (0 : ℝ) < ((1 + Complex.I) / 4).im
    simp [Complex.div_im, Complex.add_im, Complex.one_im, Complex.I_im,
          Complex.add_re, Complex.one_re, Complex.I_re]
  · rw [Metric.mem_ball, dist_zero_right]; exact h_norm
  · -- right: re > 0
    show (0 : ℝ) < ((1 + Complex.I) / 4).re
    simp [Complex.div_re, Complex.add_im, Complex.one_im, Complex.I_im,
          Complex.add_re, Complex.one_re, Complex.I_re]

/-- `(1-i)/4` lies in both `D_lower` and `D_right`. -/
private theorem one_minus_I_div_four_mem_lower_right :
    ((1 - Complex.I) / 4) ∈ D_lower ∩ D_right := by
  have h_norm : ‖(1 - Complex.I) / 4‖ < 1 := by
    have h_sq : ‖(1 - Complex.I) / 4‖ ^ 2 < 1 ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      have : Complex.normSq ((1 - Complex.I) / 4) = 1 / 8 := by
        rw [show ((1 - Complex.I) / 4 : ℂ) = (1/4 : ℂ) + (-(Complex.I / 4)) by ring,
            Complex.normSq_add]
        simp [Complex.normSq_apply, Complex.div_re, Complex.div_im,
              Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
              Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
              Complex.neg_re, Complex.neg_im,
              Complex.conj_re, Complex.conj_im]
        ring
      rw [this]; norm_num
    have h_nonneg : (0 : ℝ) ≤ ‖(1 - Complex.I) / 4‖ := norm_nonneg _
    nlinarith [h_sq, h_nonneg]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Metric.mem_ball, dist_zero_right]; exact h_norm
  · -- lower: im < 0
    show ((1 - Complex.I) / 4).im < (0 : ℝ)
    simp only [Complex.div_im, Complex.sub_im, Complex.one_im, Complex.I_im,
          Complex.sub_re, Complex.one_re, Complex.I_re, Complex.normSq_ofNat]
    norm_num
  · rw [Metric.mem_ball, dist_zero_right]; exact h_norm
  · -- right: re > 0
    show (0 : ℝ) < ((1 - Complex.I) / 4).re
    simp only [Complex.div_re, Complex.sub_im, Complex.one_im, Complex.I_im,
          Complex.sub_re, Complex.one_re, Complex.I_re, Complex.normSq_ofNat]
    norm_num

/-! ## Containment in the slit disc -/

/-- Slit disc shorthand. -/
private def SlitDisc : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain

/-- `D_upper ⊆ SlitDisc`: points with `z.im > 0` are in
    `Complex.slitPlane` (because `z.im ≠ 0`) and in `SlitPlane`
    (because the branch cut requires `z.im = 0`). -/
private theorem D_upper_subset_SlitDisc : D_upper ⊆ SlitDisc := by
  intro z ⟨hz_ball, hz_im⟩
  refine ⟨hz_ball, ?_, ?_⟩
  · -- SlitPlane: z ∉ BranchCut := {w | w.im = 0 ∧ 1 ≤ w.re}
    -- z.im > 0, so z.im ≠ 0.
    intro h_cut
    have h_im_zero : z.im = 0 := h_cut.1
    have : (0 : ℝ) < z.im := hz_im
    linarith
  · -- Complex.slitPlane: 0 < z.re ∨ z.im ≠ 0; right disjunct
    rw [Complex.mem_slitPlane_iff]
    right
    have : (0 : ℝ) < z.im := hz_im
    linarith

/-- `D_lower ⊆ SlitDisc`. -/
private theorem D_lower_subset_SlitDisc : D_lower ⊆ SlitDisc := by
  intro z ⟨hz_ball, hz_im⟩
  refine ⟨hz_ball, ?_, ?_⟩
  · intro h_cut
    have h_im_zero : z.im = 0 := h_cut.1
    have : z.im < (0 : ℝ) := hz_im
    linarith
  · rw [Complex.mem_slitPlane_iff]
    right
    have : z.im < (0 : ℝ) := hz_im
    linarith

/-- `D_right ⊆ SlitDisc`: `0 < z.re` excludes `(-∞, 0]` (and
    excludes the branch cut `[1, ∞)` together with `|z| < 1`). -/
private theorem D_right_subset_SlitDisc : D_right ⊆ SlitDisc := by
  intro z ⟨hz_ball, hz_re⟩
  refine ⟨hz_ball, ?_, ?_⟩
  · -- z ∉ BranchCut: need ¬(z.im = 0 ∧ 1 ≤ z.re).
    intro h_cut
    obtain ⟨_, h_re_ge⟩ := h_cut
    -- 1 ≤ z.re, but |z| < 1 gives z.re ≤ |z| < 1.
    have h_ball : ‖z‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hz_ball; exact hz_ball
    have h_re_le : z.re ≤ ‖z‖ := Complex.re_le_norm z
    linarith
  · rw [Complex.mem_slitPlane_iff]
    left
    exact hz_re

/-! ## Coverage of the slit disc -/

/-- `SlitDisc ⊆ D_upper ∪ D_lower ∪ D_right`: case split on `z.im`. -/
private theorem SlitDisc_subset_union :
    SlitDisc ⊆ D_upper ∪ D_lower ∪ D_right := by
  intro z hz
  obtain ⟨hz_ball, hz_dom⟩ := hz
  -- hz_dom : z ∈ JonquieresAnalyticDomain = SlitPlane ∩ Complex.slitPlane
  rcases lt_trichotomy z.im 0 with h_neg | h_zero | h_pos
  · -- z.im < 0 → D_lower
    left; right
    exact ⟨hz_ball, h_neg⟩
  · -- z.im = 0 → z ∈ Complex.slitPlane forces 0 < z.re
    right
    refine ⟨hz_ball, ?_⟩
    have h_slit : z ∈ Complex.slitPlane := hz_dom.2
    rw [Complex.mem_slitPlane_iff] at h_slit
    rcases h_slit with h_re | h_im_ne
    · exact h_re
    · exact absurd h_zero h_im_ne
  · -- z.im > 0 → D_upper
    left; left
    exact ⟨hz_ball, h_pos⟩

/-- The reverse inclusion: each piece is inside `SlitDisc`. -/
private theorem union_subset_SlitDisc :
    D_upper ∪ D_lower ∪ D_right ⊆ SlitDisc := by
  intro z hz
  rcases hz with (hu | hl) | hr
  · exact D_upper_subset_SlitDisc hu
  · exact D_lower_subset_SlitDisc hl
  · exact D_right_subset_SlitDisc hr

/-- Set equality: the slit disc is the three-piece union. -/
private theorem SlitDisc_eq_union :
    SlitDisc = D_upper ∪ D_lower ∪ D_right := by
  apply Set.Subset.antisymm
  · exact SlitDisc_subset_union
  · exact union_subset_SlitDisc

/-! ## Path-connectedness via gluing -/

/-- The slit disc is path-connected via two-step gluing through the
    right half-disc. -/
private theorem SlitDisc_isPathConnected : IsPathConnected SlitDisc := by
  rw [SlitDisc_eq_union]
  -- Glue D_upper with D_right first: overlap (1+i)/4
  have h_overlap_ur : (D_upper ∩ D_right).Nonempty :=
    ⟨(1 + Complex.I) / 4, one_plus_I_div_four_mem_upper_right⟩
  have h_step1 : IsPathConnected (D_upper ∪ D_right) :=
    D_upper_isPathConnected.union D_right_isPathConnected h_overlap_ur
  -- Now glue D_lower in via overlap (1-i)/4 ∈ D_lower ∩ D_right
  -- (which is automatically inside (D_upper ∪ D_right) via the right-disc).
  have h_overlap_lr : (D_lower ∩ D_right).Nonempty :=
    ⟨(1 - Complex.I) / 4, one_minus_I_div_four_mem_lower_right⟩
  -- Need: (D_upper ∪ D_right) ∩ D_lower nonempty.
  -- (1-i)/4 ∈ D_right ⊆ D_upper ∪ D_right, and (1-i)/4 ∈ D_lower.
  have h_overlap_glue : ((D_upper ∪ D_right) ∩ D_lower).Nonempty := by
    obtain ⟨w, hw_lower, hw_right⟩ := h_overlap_lr
    refine ⟨w, ?_, hw_lower⟩
    right; exact hw_right
  have h_step2 : IsPathConnected ((D_upper ∪ D_right) ∪ D_lower) :=
    h_step1.union D_lower_isPathConnected h_overlap_glue
  -- Reassociate: (D_upper ∪ D_right) ∪ D_lower = D_upper ∪ D_lower ∪ D_right
  have h_assoc :
      (D_upper ∪ D_right) ∪ D_lower = D_upper ∪ D_lower ∪ D_right := by
    ext x
    simp only [Set.mem_union]
    tauto
  rw [← h_assoc]
  exact h_step2

/-! ## Final discharge -/

/-- **The slit disc is preconnected** — the discharge of
    `SlitDiscPreconnectedReachability`. -/
theorem SlitDisc_isPreconnected :
    IsPreconnected (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain) :=
  SlitDisc_isPathConnected.isConnected.isPreconnected

/-- **DISCHARGE**: the named topological precondition
    `SlitDiscPreconnectedReachability` holds. Combined with
    `discAgreementReduced_of_sharper_and_reachability`, this retires
    one of the three named gaps in the disc-agreement reduction. -/
theorem slitDiscPreconnectedReachability_proved :
    SlitDiscPreconnectedReachability :=
  SlitDisc_isPreconnected

end PrincipiaTractalis.Analytic.Sheaf
