/-
# PF.NaiveHeightQ_r130

★★★ 2026-07-27 — B1 OF THE NON-TORSION ARC ★★★

The naive (multiplicative) height on ℚ, built from scratch: mathlib v4.24 has
no height machinery (`Mathlib/NumberTheory/Height/` is master-2026 only).

This is stone B1 of the arc mapped in
`codex/BSD_NONTORSION_ARC_PLAN_2026-07-27.md`: the height API needed to run
the single-curve duplication argument on 37a1 and discharge
`NonTorsionCertificate` (r129). The two load-bearing exports:

* `naiveHeight q = max |num q| (den q)` with `1 ≤ naiveHeight q`;
* `infinite_of_unbounded_naiveHeight`: a family of rationals of unbounded
  height has infinite range — the lemma that will convert strict height
  growth along `2^n • Q` into `¬IsOfFinAddOrder Q`.

HONEST SCOPE. Height API only. No elliptic curves appear; nothing here
certifies any point as non-torsion.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`, no
project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-27.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith

namespace PrincipiaTractalis.NaiveHeightQ

/-! ## §1 — the height -/

/-- The naive multiplicative height of a rational in lowest terms:
`H(a/b) = max |a| b`. `Rat` is always reduced, so no normalization is needed. -/
def naiveHeight (q : ℚ) : ℕ :=
  max q.num.natAbs q.den

theorem one_le_naiveHeight (q : ℚ) : 1 ≤ naiveHeight q :=
  le_trans q.pos (le_max_right _ _)

theorem naiveHeight_pos (q : ℚ) : 0 < naiveHeight q :=
  one_le_naiveHeight q

@[simp]
theorem naiveHeight_zero : naiveHeight 0 = 1 := rfl

@[simp]
theorem naiveHeight_one : naiveHeight 1 = 1 := rfl

theorem naiveHeight_intCast (n : ℤ) : naiveHeight (n : ℚ) = max n.natAbs 1 := by
  unfold naiveHeight
  rw [Rat.num_intCast, Rat.den_intCast]

theorem num_natAbs_le_naiveHeight (q : ℚ) : q.num.natAbs ≤ naiveHeight q :=
  le_max_left _ _

theorem den_le_naiveHeight (q : ℚ) : q.den ≤ naiveHeight q :=
  le_max_right _ _

/-- Two rationals with the same height data are still distinct rationals only
via `num`/`den`; conversely equal rationals share their height. -/
theorem naiveHeight_congr {p q : ℚ} (h : p = q) : naiveHeight p = naiveHeight q := by
  rw [h]

/-! ## §2 — finiteness: bounded height ⟺ finitely many rationals -/

/-- **Northcott for ℚ, the trivial direction we need:** any finite set of
rationals has bounded naive height. -/
theorem exists_bound_of_finite {s : Set ℚ} (hs : s.Finite) :
    ∃ B : ℕ, ∀ q ∈ s, naiveHeight q ≤ B := by
  classical
  refine ⟨(hs.toFinset.image naiveHeight).sup id, fun q hq => ?_⟩
  exact Finset.le_sup (f := id)
    (Finset.mem_image_of_mem naiveHeight (hs.mem_toFinset.mpr hq))

/-- **The conversion lemma for B5.** If a family of rationals has unbounded
naive height, its range is infinite. Applied to `n ↦ x(2^n • Q)`, strict
height growth will contradict the finiteness of a torsion orbit. -/
theorem infinite_of_unbounded_naiveHeight {ι : Type*} (f : ι → ℚ)
    (hf : ∀ B : ℕ, ∃ i, B < naiveHeight (f i)) : (Set.range f).Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := exists_bound_of_finite hfin
  obtain ⟨i, hi⟩ := hf B
  exact absurd (hB (f i) (Set.mem_range_self i)) (not_le.mpr hi)

/-- Strictly increasing height along a sequence forces unbounded height:
`naiveHeight (f (n+1)) > naiveHeight (f n)` for all `n` gives
`naiveHeight (f n) ≥ naiveHeight (f 0) + n`. -/
theorem le_naiveHeight_of_strict_growth (f : ℕ → ℚ)
    (hgrow : ∀ n, naiveHeight (f n) < naiveHeight (f (n + 1))) (n : ℕ) :
    naiveHeight (f 0) + n ≤ naiveHeight (f n) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h := hgrow k
      omega

/-- A sequence of rationals with strictly increasing naive height has
infinite range. -/
theorem infinite_of_strict_height_growth (f : ℕ → ℚ)
    (hgrow : ∀ n, naiveHeight (f n) < naiveHeight (f (n + 1))) :
    (Set.range f).Infinite := by
  refine infinite_of_unbounded_naiveHeight f fun B => ⟨B + 1, ?_⟩
  have h := le_naiveHeight_of_strict_growth f hgrow (B + 1)
  have h0 := one_le_naiveHeight (f 0)
  omega

/-! ## §3 — the growth engine, abstractly

The duplication inequality (B4) will give: `h(next) * κ ≥ h^4` for the
explicit curve constant `κ`. This section proves once and for all that such a
step function, started above the threshold `κ`, grows strictly — so B5 only
needs to check ONE concrete height against `κ` by `norm_num`. -/

/-- **The threshold lemma.** From the quartic step `a ^ 4 ≤ κ * b`, strict
growth `a < b` follows as soon as `a` clears the threshold `κ`:
`b ≥ a⁴/κ > a³ ≥ a`. Stated multiplication-only to stay in ℕ. -/
theorem next_gt_of_pow_four_le {κ a b : ℕ} (hκ : 0 < κ)
    (hthresh : κ < a) (hstep : a ^ 4 ≤ κ * b) : a < b := by
  by_contra hle
  push_neg at hle
  have ha0 : 0 < a := lt_trans hκ hthresh
  have h1 : κ * b ≤ κ * a := mul_le_mul_left' hle κ
  have h2 : κ * a < a * a := mul_lt_mul_of_pos_right hthresh ha0
  have h3 : a * a ≤ a ^ 4 := by
    calc a * a = a ^ 2 := (pow_two a).symm
    _ ≤ a ^ 4 := Nat.pow_le_pow_right ha0 (by norm_num)
  linarith

/-- Iterating the step keeps the iterate above the threshold, so strict
growth persists forever. -/
theorem forever_above_threshold {κ : ℕ} (h : ℕ → ℕ) (hκ : 0 < κ)
    (hstep : ∀ n, h n ^ 4 ≤ κ * h (n + 1)) (h0 : κ < h 0) :
    ∀ n, κ < h n ∧ h n < h (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨h0, next_gt_of_pow_four_le hκ h0 (hstep 0)⟩
  | succ k ih =>
      have hk1 : κ < h (k + 1) := lt_trans ih.1 ih.2
      exact ⟨hk1, next_gt_of_pow_four_le hκ hk1 (hstep (k + 1))⟩

/-- **The B5 driver.** A sequence of rationals whose heights satisfy the
quartic duplication step `h(n)⁴ ≤ κ·h(n+1)`, with one concrete height above
the constant `κ`, has infinite range. This is the exact interface the
duplication inequality (B4) plus one `norm_num` computation (B5) will feed. -/
theorem infinite_of_duplication_step {κ : ℕ} (f : ℕ → ℚ) (hκ : 0 < κ)
    (hstep : ∀ n, naiveHeight (f n) ^ 4 ≤ κ * naiveHeight (f (n + 1)))
    (h0 : κ < naiveHeight (f 0)) : (Set.range f).Infinite :=
  infinite_of_strict_height_growth f fun n =>
    (forever_above_threshold (fun n => naiveHeight (f n)) hκ hstep h0 n).2

end PrincipiaTractalis.NaiveHeightQ

#print axioms PrincipiaTractalis.NaiveHeightQ.infinite_of_unbounded_naiveHeight
#print axioms PrincipiaTractalis.NaiveHeightQ.infinite_of_duplication_step
