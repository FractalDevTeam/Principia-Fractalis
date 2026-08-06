/-
# PF.CantorFunction_r207 — the Cantor staircase, and the exact Hausdorff
# dimension of the ternary Cantor set

Companion to `PF.CantorDimension_r206`, which supplies the covering (UPPER)
bound `dimH cantorSet ≤ logb 3 2` and the abstract Hölder transfer lemma
`le_dimH_of_holder_surj`.  This file constructs the missing ingredient — the
Cantor function — and closes the LOWER bound, hence the exact value.

## What this file proves

* `cantorFunction : ℝ → ℝ` — the Cantor staircase (devil's staircase).  It is
  **not** in mathlib.  Constructed as the pointwise/uniform limit of the
  explicit approximants `capprox n` (a telescoping series, summed with
  `tsum`), NOT via an abstract Banach fixed point in `C([0,1], ℝ)`.

* `continuous_cantorFunction`, `cantorFunction_mono`,
  `cantorFunction_zero : cantorFunction 0 = 0`,
  `cantorFunction_one : cantorFunction 1 = 1`,
  `cantorFunction_nonneg`, `cantorFunction_le_one`.

* The two defining functional equations, for `x ∈ [0,1]`:
  `cantorFunction (x / 3) = cantorFunction x / 2` and
  `cantorFunction ((2 + x) / 3) = (1 + cantorFunction x) / 2`.

* `cantorFunction_middle` — `cantorFunction ≡ 1/2` on `[1/3, 2/3]`.

* `cantorFunction_holder : HolderWith 2 (Real.logb 3 2).toNNReal cantorFunction`
  — the Cantor staircase is globally Hölder on `ℝ` with the sharp exponent
  `logb 3 2` and constant `2`.

* `unitInterval_subset_image : Set.Icc (0:ℝ) 1 ⊆ cantorFunction '' cantorSet`
  — the staircase already maps the Cantor set ONTO the unit interval (proved
  by generating all dyadic rationals inside the image and closing up; the
  image is compact hence closed).

* `le_dimH_cantorSet : ENNReal.ofReal (Real.logb 3 2) ≤ dimH cantorSet` — the
  LOWER bound, via r206's `le_dimH_of_holder_surj`.

* `dimH_cantorSet : dimH cantorSet = ENNReal.ofReal (Real.logb 3 2)`.

## HONESTY STATEMENT

1. **The equality IS established here.**  `dimH_cantorSet` states the exact
   Hausdorff dimension of mathlib's ternary `cantorSet`.  The `≤` half is
   NOT proved in this file: it is imported from `PF.CantorDimension_r206`
   (`dimH_cantorSet_le`).  This file proves the `≥` half and takes the
   `le_antisymm`.

2. The lower bound is obtained by a **measure-free** route: no Cantor–Lebesgue
   measure, no Frostman estimate.  Only the Hölder regularity of the staircase
   and `dimH (Icc 0 1) = 1`.

3. The route through countability of `Icc 0 1 \ cantorFunction '' cantorSet`
   was NOT needed: exact surjectivity of the staircase from `cantorSet` onto
   `Icc 0 1` is proved directly.

4. No `sorry`, no `native_decide`, no project axioms.  All results reduce to
   `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic
import PF.CantorDimension_r206

open scoped NNReal ENNReal Topology
open Set

namespace PrincipiaTractalis.CantorFunction

/-! ## §1 — the approximants

`capprox 0` is the clamp `x ↦ max 0 (min x 1)`; each step applies the
"middle-third averaging" operator

  `(Φ g) x = (g (min (3x) 1) + g (max (3x - 2) 0)) / 2`.

The clamping inside the arguments makes `Φ g` continuous for *any* continuous
`g` — no gluing conditions are needed — while on functions with `g 0 = 0`,
`g 1 = 1` the operator is a `(1/2)`-contraction in the sup norm.  That is the
whole trick. -/

/-- The `n`-th Cantor-staircase approximant. -/
noncomputable def capprox : ℕ → ℝ → ℝ
  | 0, x => max 0 (min x 1)
  | n + 1, x => (capprox n (min (3 * x) 1) + capprox n (max (3 * x - 2) 0)) / 2

theorem capprox_zero_apply (x : ℝ) : capprox 0 x = max 0 (min x 1) := rfl

theorem capprox_succ_apply (n : ℕ) (x : ℝ) :
    capprox (n + 1) x = (capprox n (min (3 * x) 1) + capprox n (max (3 * x - 2) 0)) / 2 := rfl

theorem capprox_nonneg (n : ℕ) (x : ℝ) : 0 ≤ capprox n x := by
  induction n generalizing x with
  | zero => rw [capprox_zero_apply]; exact le_max_left _ _
  | succ n ih =>
      rw [capprox_succ_apply]
      have h1 := ih (min (3 * x) 1)
      have h2 := ih (max (3 * x - 2) 0)
      linarith

theorem capprox_le_one (n : ℕ) (x : ℝ) : capprox n x ≤ 1 := by
  induction n generalizing x with
  | zero => rw [capprox_zero_apply]; exact max_le zero_le_one (min_le_right _ _)
  | succ n ih =>
      rw [capprox_succ_apply]
      have h1 := ih (min (3 * x) 1)
      have h2 := ih (max (3 * x - 2) 0)
      linarith

theorem capprox_at_zero (n : ℕ) : capprox n 0 = 0 := by
  induction n with
  | zero => rw [capprox_zero_apply]; norm_num
  | succ n ih =>
      rw [capprox_succ_apply, show (3 : ℝ) * 0 - 2 = -2 by ring,
        show max (-2 : ℝ) 0 = 0 by norm_num, show (3 : ℝ) * 0 = 0 by ring,
        show min (0 : ℝ) 1 = 0 by norm_num, ih]
      norm_num

theorem capprox_at_one (n : ℕ) : capprox n 1 = 1 := by
  induction n with
  | zero => rw [capprox_zero_apply]; norm_num
  | succ n ih =>
      rw [capprox_succ_apply, show (3 : ℝ) * 1 - 2 = 1 by ring,
        show max (1 : ℝ) 0 = 1 by norm_num, show (3 : ℝ) * 1 = 3 by ring,
        show min (3 : ℝ) 1 = 1 by norm_num, ih]
      norm_num

theorem capprox_mono (n : ℕ) : Monotone (capprox n) := by
  induction n with
  | zero =>
      intro a b hab
      rw [capprox_zero_apply, capprox_zero_apply]
      exact max_le_max le_rfl (min_le_min hab le_rfl)
  | succ n ih =>
      intro a b hab
      rw [capprox_succ_apply, capprox_succ_apply]
      have h1 : capprox n (min (3 * a) 1) ≤ capprox n (min (3 * b) 1) :=
        ih (min_le_min (by linarith) le_rfl)
      have h2 : capprox n (max (3 * a - 2) 0) ≤ capprox n (max (3 * b - 2) 0) :=
        ih (max_le_max (by linarith) le_rfl)
      linarith

theorem capprox_continuous (n : ℕ) : Continuous (capprox n) := by
  induction n with
  | zero =>
      have h : capprox 0 = fun x : ℝ => max 0 (min x 1) := rfl
      rw [h]
      exact continuous_const.max (continuous_id.min continuous_const)
  | succ n ih =>
      have h1 : Continuous fun x : ℝ => min (3 * x) 1 :=
        (continuous_const.mul continuous_id).min continuous_const
      have h2 : Continuous fun x : ℝ => max (3 * x - 2) 0 :=
        ((continuous_const.mul continuous_id).sub continuous_const).max continuous_const
      have h : capprox (n + 1)
          = fun x : ℝ => (capprox n (min (3 * x) 1) + capprox n (max (3 * x - 2) 0)) / 2 := rfl
      rw [h]
      exact (((ih.comp h1).add (ih.comp h2)).div_const 2)

/-- Vanishing to the left of `0`. -/
theorem capprox_of_nonpos (n : ℕ) : ∀ x : ℝ, x ≤ 0 → capprox n x = 0 := by
  induction n with
  | zero =>
      intro x hx
      rw [capprox_zero_apply]
      exact max_eq_left ((min_le_left x 1).trans hx)
  | succ n ih =>
      intro x hx
      rw [capprox_succ_apply, min_eq_left (by linarith : 3 * x ≤ 1),
        max_eq_right (by linarith : 3 * x - 2 ≤ 0), ih (3 * x) (by linarith), ih 0 le_rfl]
      norm_num

/-- Constant `1` to the right of `1`. -/
theorem capprox_of_one_le (n : ℕ) : ∀ x : ℝ, 1 ≤ x → capprox n x = 1 := by
  induction n with
  | zero =>
      intro x hx
      rw [capprox_zero_apply, min_eq_right hx, max_eq_right zero_le_one]
  | succ n ih =>
      intro x hx
      rw [capprox_succ_apply, min_eq_right (by linarith : (1 : ℝ) ≤ 3 * x),
        max_eq_left (by linarith : (0 : ℝ) ≤ 3 * x - 2), ih 1 le_rfl,
        ih (3 * x - 2) (by linarith)]
      norm_num

/-- **The contraction estimate.**  Successive approximants differ by at most
`2^(-n)`, uniformly on all of `ℝ`.  This is where the two boundary values
`capprox n 0 = 0`, `capprox n 1 = 1` do their work: on each of the two halves
of the case split, one of the two averaged terms cancels exactly. -/
theorem capprox_diff (n : ℕ) (x : ℝ) : |capprox (n + 1) x - capprox n x| ≤ (1 / 2 : ℝ) ^ n := by
  induction n generalizing x with
  | zero =>
      have h1 := capprox_nonneg 1 x
      have h2 := capprox_le_one 1 x
      have h3 := capprox_nonneg 0 x
      have h4 := capprox_le_one 0 x
      rw [pow_zero, abs_sub_le_iff]
      constructor <;> linarith
  | succ n ih =>
      rw [capprox_succ_apply (n + 1) x, capprox_succ_apply n x]
      rcases le_total x (1 / 3 : ℝ) with hx | hx
      · have hb : max (3 * x - 2) 0 = (0 : ℝ) := max_eq_right (by linarith)
        rw [hb, capprox_at_zero, capprox_at_zero]
        have h := ih (min (3 * x) 1)
        have key : |(capprox (n + 1) (min (3 * x) 1) + 0) / 2
              - (capprox n (min (3 * x) 1) + 0) / 2|
            = |capprox (n + 1) (min (3 * x) 1) - capprox n (min (3 * x) 1)| / 2 := by
          rw [show (capprox (n + 1) (min (3 * x) 1) + 0) / 2
                - (capprox n (min (3 * x) 1) + 0) / 2
              = (capprox (n + 1) (min (3 * x) 1) - capprox n (min (3 * x) 1)) / 2 from by ring,
            abs_div]
          norm_num
        rw [key, pow_succ]
        linarith
      · have ha : min (3 * x) 1 = (1 : ℝ) := min_eq_right (by linarith)
        rw [ha, capprox_at_one, capprox_at_one]
        have h := ih (max (3 * x - 2) 0)
        have key : |(1 + capprox (n + 1) (max (3 * x - 2) 0)) / 2
              - (1 + capprox n (max (3 * x - 2) 0)) / 2|
            = |capprox (n + 1) (max (3 * x - 2) 0) - capprox n (max (3 * x - 2) 0)| / 2 := by
          rw [show (1 + capprox (n + 1) (max (3 * x - 2) 0)) / 2
                - (1 + capprox n (max (3 * x - 2) 0)) / 2
              = (capprox (n + 1) (max (3 * x - 2) 0) - capprox n (max (3 * x - 2) 0)) / 2 from by
                ring,
            abs_div]
          norm_num
        rw [key, pow_succ]
        linarith

theorem capprox_summable (x : ℝ) : Summable fun n : ℕ => capprox (n + 1) x - capprox n x := by
  refine Summable.of_norm_bounded
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)) ?_
  intro n
  rw [Real.norm_eq_abs]
  exact capprox_diff n x

/-! ## §2 — the Cantor staircase -/

/-- **The Cantor function (devil's staircase)**, defined as the sum of the
telescoping series of approximants. -/
noncomputable def cantorFunction (x : ℝ) : ℝ :=
  capprox 0 x + ∑' n : ℕ, (capprox (n + 1) x - capprox n x)

theorem tendsto_capprox (x : ℝ) :
    Filter.Tendsto (fun n => capprox n x) Filter.atTop (𝓝 (cantorFunction x)) := by
  have hs := (capprox_summable x).hasSum.tendsto_sum_nat
  have hrw : ∀ n : ℕ, ∑ i ∈ Finset.range n, (capprox (i + 1) x - capprox i x)
      = capprox n x - capprox 0 x := fun n => Finset.sum_range_sub (fun i => capprox i x) n
  simp only [hrw] at hs
  have h2 := hs.add_const (capprox 0 x)
  have h3 : (fun n : ℕ => capprox n x - capprox 0 x + capprox 0 x) = fun n => capprox n x := by
    funext n; ring
  rw [h3] at h2
  have h4 : (∑' n : ℕ, (capprox (n + 1) x - capprox n x)) + capprox 0 x = cantorFunction x := by
    rw [cantorFunction]; ring
  rwa [h4] at h2

theorem cantorFunction_of_tendsto {x L : ℝ}
    (h : Filter.Tendsto (fun n => capprox n x) Filter.atTop (𝓝 L)) : cantorFunction x = L :=
  tendsto_nhds_unique (tendsto_capprox x) h

@[simp] theorem cantorFunction_zero : cantorFunction 0 = 0 := by
  refine cantorFunction_of_tendsto ?_
  rw [show (fun n : ℕ => capprox n 0) = fun _ => (0 : ℝ) from funext capprox_at_zero]
  exact tendsto_const_nhds

@[simp] theorem cantorFunction_one : cantorFunction 1 = 1 := by
  refine cantorFunction_of_tendsto ?_
  rw [show (fun n : ℕ => capprox n 1) = fun _ => (1 : ℝ) from funext capprox_at_one]
  exact tendsto_const_nhds

theorem cantorFunction_nonneg (x : ℝ) : 0 ≤ cantorFunction x :=
  ge_of_tendsto' (tendsto_capprox x) fun n => capprox_nonneg n x

theorem cantorFunction_le_one (x : ℝ) : cantorFunction x ≤ 1 :=
  le_of_tendsto' (tendsto_capprox x) fun n => capprox_le_one n x

theorem cantorFunction_mono : Monotone cantorFunction := fun a b hab =>
  le_of_tendsto_of_tendsto' (tendsto_capprox a) (tendsto_capprox b) fun n => capprox_mono n hab

theorem continuous_cantorFunction : Continuous cantorFunction := by
  have h1 : Continuous fun x : ℝ => capprox 0 x := capprox_continuous 0
  have h2 : Continuous fun x : ℝ => ∑' n : ℕ, (capprox (n + 1) x - capprox n x) := by
    refine continuous_tsum (u := fun n : ℕ => (1 / 2 : ℝ) ^ n)
      (fun n => (capprox_continuous (n + 1)).sub (capprox_continuous n))
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
    intro n x
    rw [Real.norm_eq_abs]
    exact capprox_diff n x
  exact h1.add h2

/-! ### The functional equations -/

theorem capprox_succ_div_three {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    capprox (n + 1) (x / 3) = capprox n x / 2 := by
  rw [capprox_succ_apply, show (3 : ℝ) * (x / 3) = x by ring, min_eq_left hx1,
    max_eq_right (by linarith : x - 2 ≤ 0), capprox_at_zero]
  ring

theorem capprox_succ_two_add_div_three {x : ℝ} (hx0 : 0 ≤ x) (_hx1 : x ≤ 1) (n : ℕ) :
    capprox (n + 1) ((2 + x) / 3) = (1 + capprox n x) / 2 := by
  rw [capprox_succ_apply, show (3 : ℝ) * ((2 + x) / 3) = 2 + x by ring,
    min_eq_right (by linarith : (1 : ℝ) ≤ 2 + x), show (2 : ℝ) + x - 2 = x by ring,
    max_eq_left hx0, capprox_at_one]

/-- **First functional equation.** -/
theorem cantorFunction_div_three {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    cantorFunction (x / 3) = cantorFunction x / 2 := by
  refine cantorFunction_of_tendsto ?_
  rw [← Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => capprox n (x / 3)) 1]
  rw [show (fun n : ℕ => capprox (n + 1) (x / 3)) = fun n : ℕ => capprox n x / 2 from
    funext fun n => capprox_succ_div_three hx0 hx1 n]
  exact (tendsto_capprox x).div_const 2

/-- **Second functional equation.** -/
theorem cantorFunction_two_add_div_three {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    cantorFunction ((2 + x) / 3) = (1 + cantorFunction x) / 2 := by
  refine cantorFunction_of_tendsto ?_
  rw [← Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => capprox n ((2 + x) / 3)) 1]
  rw [show (fun n : ℕ => capprox (n + 1) ((2 + x) / 3)) = fun n : ℕ => (1 + capprox n x) / 2 from
    funext fun n => capprox_succ_two_add_div_three hx0 hx1 n]
  exact ((tendsto_capprox x).const_add 1).div_const 2

theorem cantorFunction_of_nonpos {x : ℝ} (hx : x ≤ 0) : cantorFunction x = 0 := by
  refine cantorFunction_of_tendsto ?_
  rw [show (fun n : ℕ => capprox n x) = fun _ => (0 : ℝ) from
    funext fun n => capprox_of_nonpos n x hx]
  exact tendsto_const_nhds

theorem cantorFunction_of_one_le {x : ℝ} (hx : 1 ≤ x) : cantorFunction x = 1 := by
  refine cantorFunction_of_tendsto ?_
  rw [show (fun n : ℕ => capprox n x) = fun _ => (1 : ℝ) from
    funext fun n => capprox_of_one_le n x hx]
  exact tendsto_const_nhds

/-- Global form of the left functional equation (valid for all `x ≤ 1/3`). -/
theorem cantorFunction_left {x : ℝ} (hx : x ≤ 1 / 3) :
    cantorFunction x = cantorFunction (3 * x) / 2 := by
  rcases le_or_gt x 0 with h | h
  · rw [cantorFunction_of_nonpos h, cantorFunction_of_nonpos (by linarith : 3 * x ≤ 0)]
    norm_num
  · have h1 : (0 : ℝ) ≤ 3 * x := by linarith
    have h2 : 3 * x ≤ 1 := by linarith
    have h3 := cantorFunction_div_three h1 h2
    rwa [show 3 * x / 3 = x from by ring] at h3

/-- Global form of the right functional equation (valid for all `2/3 ≤ x`). -/
theorem cantorFunction_right {x : ℝ} (hx : 2 / 3 ≤ x) :
    cantorFunction x = (1 + cantorFunction (3 * x - 2)) / 2 := by
  rcases le_or_gt 1 x with h | h
  · rw [cantorFunction_of_one_le h, cantorFunction_of_one_le (by linarith : (1 : ℝ) ≤ 3 * x - 2)]
    norm_num
  · have h1 : (0 : ℝ) ≤ 3 * x - 2 := by linarith
    have h2 : 3 * x - 2 ≤ 1 := by linarith
    have h3 := cantorFunction_two_add_div_three h1 h2
    rwa [show (2 + (3 * x - 2)) / 3 = x from by ring] at h3

theorem cantorFunction_one_third : cantorFunction (1 / 3) = 1 / 2 := by
  have h := cantorFunction_left (le_refl (1 / 3 : ℝ))
  rw [show (3 : ℝ) * (1 / 3) = 1 from by ring, cantorFunction_one] at h
  linarith

theorem cantorFunction_two_thirds : cantorFunction (2 / 3) = 1 / 2 := by
  have h := cantorFunction_right (le_refl (2 / 3 : ℝ))
  rw [show (3 : ℝ) * (2 / 3) - 2 = 0 from by ring, cantorFunction_zero] at h
  linarith

/-- The staircase is flat on the first removed middle third. -/
theorem cantorFunction_middle {x : ℝ} (h1 : 1 / 3 ≤ x) (h2 : x ≤ 2 / 3) :
    cantorFunction x = 1 / 2 := by
  have a := cantorFunction_mono h1
  have b := cantorFunction_mono h2
  rw [cantorFunction_one_third] at a
  rw [cantorFunction_two_thirds] at b
  linarith

/-! ## §3 — the Hölder estimate with exponent `logb 3 2` -/

theorem logb_three_two_pos : 0 < Real.logb 3 2 :=
  Real.logb_pos (by norm_num) (by norm_num)

theorem rpow_three_logb : (3 : ℝ) ^ (Real.logb 3 2) = 2 :=
  Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

/-- **The dyadic modulus of continuity** (ordered form).  `|x - y| ≤ 3^(-n)`
forces `|f x - f y| ≤ 2^(-n)`. -/
theorem cantorFunction_modulus_aux (n : ℕ) : ∀ x y : ℝ, x ≤ y → y - x ≤ (1 / 3 : ℝ) ^ n →
    |cantorFunction x - cantorFunction y| ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
      intro x y _ _
      have h1 := cantorFunction_nonneg x
      have h2 := cantorFunction_le_one x
      have h3 := cantorFunction_nonneg y
      have h4 := cantorFunction_le_one y
      rw [pow_zero, abs_sub_le_iff]
      constructor <;> linarith
  | succ n ih =>
      have hpow3 : (1 / 3 : ℝ) ^ (n + 1) ≤ 1 / 3 := by
        have h : (1 / 3 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have hp : (0 : ℝ) < (1 / 3 : ℝ) ^ n := by positivity
        rw [pow_succ]
        nlinarith
      have h3pow : (3 : ℝ) * ((1 / 3 : ℝ) ^ (n + 1)) = (1 / 3 : ℝ) ^ n := by
        rw [pow_succ]; ring
      -- both points in the left third
      have hA : ∀ a b : ℝ, a ≤ b → b ≤ 1 / 3 → b - a ≤ (1 / 3 : ℝ) ^ (n + 1) →
          |cantorFunction a - cantorFunction b| ≤ (1 / 2 : ℝ) ^ (n + 1) := by
        intro a b hab hb hd
        rw [cantorFunction_left (hab.trans hb), cantorFunction_left hb]
        have h := ih (3 * a) (3 * b) (by linarith) (by linarith)
        rw [show cantorFunction (3 * a) / 2 - cantorFunction (3 * b) / 2
            = (cantorFunction (3 * a) - cantorFunction (3 * b)) / 2 from by ring, abs_div]
        rw [show |(2 : ℝ)| = 2 from by norm_num, pow_succ]
        linarith
      -- both points in the right third
      have hB : ∀ a b : ℝ, a ≤ b → 2 / 3 ≤ a → b - a ≤ (1 / 3 : ℝ) ^ (n + 1) →
          |cantorFunction a - cantorFunction b| ≤ (1 / 2 : ℝ) ^ (n + 1) := by
        intro a b hab ha hd
        rw [cantorFunction_right ha, cantorFunction_right (ha.trans hab)]
        have h := ih (3 * a - 2) (3 * b - 2) (by linarith) (by linarith)
        rw [show (1 + cantorFunction (3 * a - 2)) / 2 - (1 + cantorFunction (3 * b - 2)) / 2
            = (cantorFunction (3 * a - 2) - cantorFunction (3 * b - 2)) / 2 from by ring, abs_div]
        rw [show |(2 : ℝ)| = 2 from by norm_num, pow_succ]
        linarith
      intro x y hxy hd
      by_cases hy : y ≤ 1 / 3
      · exact hA x y hxy hy hd
      push_neg at hy
      by_cases hx : 2 / 3 ≤ x
      · exact hB x y hxy hx hd
      push_neg at hx
      by_cases hx1 : 1 / 3 ≤ x
      · have hfx : cantorFunction x = 1 / 2 := cantorFunction_middle hx1 hx.le
        by_cases hy2 : y ≤ 2 / 3
        · have hfy : cantorFunction y = 1 / 2 := cantorFunction_middle (by linarith) hy2
          have hz : |cantorFunction x - cantorFunction y| = 0 := by rw [hfx, hfy]; simp
          rw [hz]
          positivity
        · push_neg at hy2
          have h2 := hB (2 / 3) y (by linarith) le_rfl (by linarith)
          rw [cantorFunction_two_thirds] at h2
          rw [hfx]
          exact h2
      · push_neg at hx1
        have hfy : cantorFunction y = 1 / 2 :=
          cantorFunction_middle (by linarith) (by linarith)
        have h2 := hA x (1 / 3) (by linarith) le_rfl (by linarith)
        rw [cantorFunction_one_third] at h2
        rw [hfy]
        exact h2

theorem cantorFunction_modulus (n : ℕ) {x y : ℝ} (h : |x - y| ≤ (1 / 3 : ℝ) ^ n) :
    |cantorFunction x - cantorFunction y| ≤ (1 / 2 : ℝ) ^ n := by
  rcases le_total x y with hxy | hxy
  · refine cantorFunction_modulus_aux n x y hxy ?_
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)] at h
    exact h
  · rw [abs_sub_comm]
    refine cantorFunction_modulus_aux n y x hxy ?_
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)] at h
    exact h

/-- Sandwich a number in `(0,1]` between consecutive powers of `1/3`. -/
theorem exists_pow_sandwich {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ n : ℕ, (1 / 3 : ℝ) ^ (n + 1) < t ∧ t ≤ (1 / 3 : ℝ) ^ n := by
  classical
  have hex : ∃ n : ℕ, (1 / 3 : ℝ) ^ (n + 1) < t := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (1 / 3 : ℝ) < 1)
    refine ⟨k, lt_of_le_of_lt ?_ hk⟩
    have hp : (0 : ℝ) < (1 / 3 : ℝ) ^ k := by positivity
    rw [pow_succ]
    nlinarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h, pow_zero]; exact ht1
  · have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    have hmin := Nat.find_min hex hlt
    push_neg at hmin
    have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rwa [heq] at hmin

/-- **The sharp Hölder estimate**, in `dist` form:
`|f x - f y| ≤ 2 · |x - y|^(logb 3 2)` for all reals. -/
theorem cantorFunction_dist_le (x y : ℝ) :
    |cantorFunction x - cantorFunction y| ≤ 2 * |x - y| ^ (Real.logb 3 2) := by
  have hd0 : 0 < Real.logb 3 2 := logb_three_two_pos
  rcases eq_or_lt_of_le (abs_nonneg (x - y)) with h0 | h0
  · have hxy : x = y := sub_eq_zero.1 (abs_eq_zero.1 h0.symm)
    subst hxy
    simp [Real.zero_rpow hd0.ne']
  rcases le_or_gt |x - y| 1 with ht1 | ht1
  · obtain ⟨n, hn1, hn2⟩ := exists_pow_sandwich h0 ht1
    have h13 : ((1 : ℝ) / 3) ^ (Real.logb 3 2) = 1 / 2 :=
      PrincipiaTractalis.CantorDimension.rpow_one_third_logb
    have hkey : ((1 / 3 : ℝ) ^ n) ^ (Real.logb 3 2) = (1 / 2 : ℝ) ^ n := by
      rw [← Real.rpow_natCast (1 / 3 : ℝ) n,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 3),
        mul_comm (n : ℝ) (Real.logb 3 2),
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 3), h13, Real.rpow_natCast]
    have hstep : (1 / 3 : ℝ) ^ n ≤ 3 * |x - y| := by
      have h : (1 / 3 : ℝ) ^ (n + 1) = (1 / 3 : ℝ) ^ n / 3 := by rw [pow_succ]; ring
      rw [h] at hn1
      linarith
    calc |cantorFunction x - cantorFunction y| ≤ (1 / 2 : ℝ) ^ n := cantorFunction_modulus n hn2
      _ = ((1 / 3 : ℝ) ^ n) ^ (Real.logb 3 2) := hkey.symm
      _ ≤ (3 * |x - y|) ^ (Real.logb 3 2) := by
          exact Real.rpow_le_rpow (by positivity) hstep hd0.le
      _ = (3 : ℝ) ^ (Real.logb 3 2) * |x - y| ^ (Real.logb 3 2) :=
          Real.mul_rpow (by norm_num) (abs_nonneg _)
      _ = 2 * |x - y| ^ (Real.logb 3 2) := by rw [rpow_three_logb]
  · have h1 : |cantorFunction x - cantorFunction y| ≤ 1 := by
      have a1 := cantorFunction_nonneg x
      have a2 := cantorFunction_le_one x
      have a3 := cantorFunction_nonneg y
      have a4 := cantorFunction_le_one y
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have h2 : (1 : ℝ) ≤ |x - y| ^ (Real.logb 3 2) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) ht1.le hd0.le
      rwa [Real.one_rpow] at h
    linarith

/-- **The Cantor staircase is Hölder with the sharp exponent `logb 3 2`.**

This statement does not exist in mathlib. -/
theorem cantorFunction_holder :
    HolderWith 2 (Real.logb 3 2).toNNReal cantorFunction := by
  intro x y
  have hd0 : (0 : ℝ) ≤ Real.logb 3 2 := logb_three_two_pos.le
  have hcoe : (((Real.logb 3 2).toNNReal : ℝ≥0) : ℝ) = Real.logb 3 2 :=
    Real.coe_toNNReal _ hd0
  have h2 : ((2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_coe_nnreal]
    norm_num
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, hcoe,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hd0, h2,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact ENNReal.ofReal_le_ofReal (cantorFunction_dist_le x y)

theorem cantorFunction_holderOn_cantorSet :
    HolderOnWith 2 (Real.logb 3 2).toNNReal cantorFunction cantorSet :=
  cantorFunction_holder.holderOnWith cantorSet

/-! ## §4 — the staircase maps the Cantor set ONTO `[0,1]` -/

theorem one_mem_cantorSet : (1 : ℝ) ∈ cantorSet := by
  simp only [cantorSet, Set.mem_iInter]
  intro n
  induction n with
  | zero => exact Set.mem_Icc.2 ⟨by norm_num, le_refl 1⟩
  | succ n ih => exact Or.inr ⟨1, ih, by norm_num⟩

theorem cantorSet_div_three {x : ℝ} (hx : x ∈ cantorSet) : x / 3 ∈ cantorSet := by
  rw [cantorSet_eq_union_halves]
  exact Or.inl ⟨x, hx, rfl⟩

theorem cantorSet_two_add_div_three {x : ℝ} (hx : x ∈ cantorSet) : (2 + x) / 3 ∈ cantorSet := by
  rw [cantorSet_eq_union_halves]
  exact Or.inr ⟨x, hx, rfl⟩

theorem isClosed_image_cantorSet : IsClosed (cantorFunction '' cantorSet) :=
  (isCompact_cantorSet.image continuous_cantorFunction).isClosed

theorem half_mem_image {s : ℝ} (hs : s ∈ cantorFunction '' cantorSet) :
    s / 2 ∈ cantorFunction '' cantorSet := by
  obtain ⟨x, hx, rfl⟩ := hs
  refine ⟨x / 3, cantorSet_div_three hx, ?_⟩
  have hx01 := cantorSet_subset_unitInterval hx
  exact cantorFunction_div_three hx01.1 hx01.2

theorem one_add_half_mem_image {s : ℝ} (hs : s ∈ cantorFunction '' cantorSet) :
    (1 + s) / 2 ∈ cantorFunction '' cantorSet := by
  obtain ⟨x, hx, rfl⟩ := hs
  refine ⟨(2 + x) / 3, cantorSet_two_add_div_three hx, ?_⟩
  have hx01 := cantorSet_subset_unitInterval hx
  exact cantorFunction_two_add_div_three hx01.1 hx01.2

/-- Every dyadic rational of `[0,1]` is in the image of the Cantor set. -/
theorem dyadic_mem_image : ∀ (n k : ℕ), k ≤ 2 ^ n →
    ((k : ℝ) / 2 ^ n) ∈ cantorFunction '' cantorSet := by
  intro n
  induction n with
  | zero =>
      intro k hk
      simp only [pow_zero] at hk
      interval_cases k
      · rw [show ((0 : ℕ) : ℝ) / 2 ^ 0 = (0 : ℝ) from by norm_num]
        exact ⟨0, zero_mem_cantorSet, cantorFunction_zero⟩
      · rw [show ((1 : ℕ) : ℝ) / 2 ^ 0 = (1 : ℝ) from by norm_num]
        exact ⟨1, one_mem_cantorSet, cantorFunction_one⟩
  | succ n ih =>
      intro k hk
      rcases le_total k (2 ^ n) with h | h
      · have hmem := half_mem_image (ih k h)
        rwa [show ((k : ℝ) / 2 ^ n) / 2 = (k : ℝ) / 2 ^ (n + 1) from by rw [pow_succ]; ring]
          at hmem
      · have hj : k - 2 ^ n ≤ 2 ^ n := by omega
        have hmem := one_add_half_mem_image (ih (k - 2 ^ n) hj)
        have hcast : ((k - 2 ^ n : ℕ) : ℝ) = (k : ℝ) - 2 ^ n := by
          rw [Nat.cast_sub h]; push_cast; ring
        rw [hcast] at hmem
        have hpow : ((2 : ℝ) ^ n) ≠ 0 := by positivity
        rwa [show (1 + ((k : ℝ) - 2 ^ n) / 2 ^ n) / 2 = (k : ℝ) / 2 ^ (n + 1) from by
          rw [pow_succ]; field_simp; ring] at hmem

/-- **Surjectivity onto the unit interval.** -/
theorem unitInterval_subset_image :
    Set.Icc (0 : ℝ) 1 ⊆ cantorFunction '' cantorSet := by
  intro y hy
  obtain ⟨hy0, hy1⟩ := hy
  have hmem : y ∈ closure (cantorFunction '' cantorSet) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    have hpow : (0 : ℝ) < 2 ^ n := by positivity
    set k := ⌊y * 2 ^ n⌋₊ with hk
    have hkle : (k : ℝ) ≤ y * 2 ^ n := Nat.floor_le (by positivity)
    have hklt : y * 2 ^ n < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hk2 : k ≤ 2 ^ n := by
      have hle : y * 2 ^ n ≤ (2 : ℝ) ^ n := by nlinarith
      have hcast : ((2 : ℝ) ^ n) = ((2 ^ n : ℕ) : ℝ) := by push_cast; ring
      have h' : k ≤ ⌊((2 ^ n : ℕ) : ℝ)⌋₊ := by
        rw [← hcast]
        exact Nat.floor_mono hle
      rwa [Nat.floor_natCast] at h'
    refine ⟨(k : ℝ) / 2 ^ n, dyadic_mem_image n k hk2, ?_⟩
    have hA : (k : ℝ) / 2 ^ n ≤ y := by rw [div_le_iff₀ hpow]; exact hkle
    have hB : y - (k : ℝ) / 2 ^ n < (1 / 2 : ℝ) ^ n := by
      have h1 : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by rw [div_pow, one_pow]
      rw [h1, sub_lt_iff_lt_add, div_add_div_same, lt_div_iff₀ hpow]
      linarith
    rw [Real.dist_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - (k : ℝ) / 2 ^ n)]
    linarith
  rwa [isClosed_image_cantorSet.closure_eq] at hmem

/-! ## §5 — the exact Hausdorff dimension -/

theorem dimH_unitInterval : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
  have h : (interior (Set.Icc (0 : ℝ) 1)).Nonempty := by
    rw [interior_Icc]
    exact ⟨1 / 2, by norm_num, by norm_num⟩
  rw [Real.dimH_of_nonempty_interior h]
  simp

/-- **Lower bound for the Hausdorff dimension of the ternary Cantor set.** -/
theorem le_dimH_cantorSet : ENNReal.ofReal (Real.logb 3 2) ≤ dimH cantorSet := by
  have hr : 0 < (Real.logb 3 2).toNNReal := Real.toNNReal_pos.2 logb_three_two_pos
  have h := PrincipiaTractalis.CantorDimension.le_dimH_of_holder_surj hr
    cantorFunction_holderOn_cantorSet unitInterval_subset_image
  rwa [dimH_unitInterval, mul_one] at h

/-- **THE HAUSDORFF DIMENSION OF THE TERNARY CANTOR SET.**

`dimH cantorSet = logb 3 2 = log 2 / log 3 ≈ 0.6309`.

The `≤` half is `PF.CantorDimension_r206.dimH_cantorSet_le` (a covering
argument through the Moran/Falconer engine of r205); the `≥` half is
`le_dimH_cantorSet` above (the Cantor staircase, Hölder transfer, no measure
theory). -/
theorem dimH_cantorSet : dimH cantorSet = ENNReal.ofReal (Real.logb 3 2) :=
  le_antisymm PrincipiaTractalis.CantorDimension.dimH_cantorSet_le le_dimH_cantorSet

/-! ## Axiom audit -/

#print axioms capprox_diff
#print axioms continuous_cantorFunction
#print axioms cantorFunction_zero
#print axioms cantorFunction_one
#print axioms cantorFunction_mono
#print axioms cantorFunction_div_three
#print axioms cantorFunction_two_add_div_three
#print axioms cantorFunction_middle
#print axioms cantorFunction_modulus
#print axioms cantorFunction_dist_le
#print axioms cantorFunction_holder
#print axioms one_mem_cantorSet
#print axioms dyadic_mem_image
#print axioms unitInterval_subset_image
#print axioms dimH_unitInterval
#print axioms le_dimH_cantorSet
#print axioms dimH_cantorSet

end PrincipiaTractalis.CantorFunction
