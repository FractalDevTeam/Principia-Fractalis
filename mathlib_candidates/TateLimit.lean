/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Tate's telescoping limit

Let `T : α → α` be a self-map, `f : α → ℝ` a function, `d > 1` a real number, and
suppose `f` is *almost homogeneous of weight `d` along `T`*, meaning

`|f (T x) - d * f x| ≤ C`  for all `x`.

Then the rescaled iterates `f (T^[n] x) / d ^ n` converge, and the limit is the
unique function that is *exactly* homogeneous (`g (T x) = d * g x`) and stays a
bounded distance from `f`. This is the argument Tate used to construct the
canonical (Néron–Tate) height on an abelian variety, where `T` is multiplication
by `2`, `f` is the logarithmic naive height, and `d = 4`; but as the statements
below show, it uses nothing about `α` beyond the self-map.

## Main definitions

* `Function.tateLimit f T d` : the function `x ↦ lim_{n} f (T^[n] x) / d ^ n`.

## Main results

* `Function.tendsto_tateLimit` : the defining limit exists.
* `Function.tateLimit_comp_self` : the limit is exactly homogeneous.
* `Function.abs_tateLimit_sub_le` : `|tateLimit f T d x - f x| ≤ C / (d - 1)`.
* `Function.abs_tateLimit_sub_iterate_le` : the same bound at depth `n`, scaled by
  `d ^ n`. This is the effective form: it lets a finite computation of
  `f (T^[n] x)` bound the limit to any desired accuracy.
* `Function.eq_of_comp_self_of_abs_sub_le` : uniqueness — two exactly homogeneous
  functions at bounded distance from one another are equal.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Theorem
  VIII.9.3 and the telescoping lemma preceding it.
-/

open Filter Topology

namespace Function

variable {α : Type*} (f : α → ℝ) (T : α → α) (d : ℝ)

/-- The rescaled iterates whose limit defines `Function.tateLimit`. -/
noncomputable def tateSeq (x : α) (n : ℕ) : ℝ := f (T^[n] x) / d ^ n

/-- **Tate's limit**: `x ↦ lim_{n → ∞} f (T^[n] x) / d ^ n`.

Junk value (via `limUnder`) unless the sequence converges; `Function.tendsto_tateLimit`
gives the hypotheses under which it does. -/
noncomputable def tateLimit (x : α) : ℝ := limUnder atTop (tateSeq f T d x)

variable {f T d} {C : ℝ}

@[simp] theorem tateSeq_zero (x : α) : tateSeq f T d x 0 = f x := by simp [tateSeq]

theorem tateSeq_comp_self (hd : d ≠ 0) (x : α) (n : ℕ) :
    tateSeq f T d (T x) n = d * tateSeq f T d x (n + 1) := by
  simp only [tateSeq, ← iterate_succ_apply, pow_succ]
  field_simp

/-- The telescoping estimate: consecutive terms differ by at most `C / d ^ (n + 1)`. -/
theorem abs_tateSeq_succ_sub_le (hd : 0 < d) (h : ∀ x, |f (T x) - d * f x| ≤ C)
    (x : α) (n : ℕ) :
    |tateSeq f T d x (n + 1) - tateSeq f T d x n| ≤ C / d ^ (n + 1) := by
  have hpos : (0 : ℝ) < d ^ (n + 1) := by positivity
  have hne : (d : ℝ) ^ n ≠ 0 := by positivity
  have key := h (T^[n] x)
  have hrw : tateSeq f T d x (n + 1) - tateSeq f T d x n
      = (f (T (T^[n] x)) - d * f (T^[n] x)) / d ^ (n + 1) := by
    simp only [tateSeq, iterate_succ_apply', pow_succ]
    field_simp
  rw [hrw, abs_div, abs_of_pos hpos]
  gcongr

theorem dist_tateSeq_succ_le (hd : 0 < d) (h : ∀ x, |f (T x) - d * f x| ≤ C)
    (x : α) (n : ℕ) :
    dist (tateSeq f T d x n) (tateSeq f T d x (n + 1)) ≤ C / d * (1 / d) ^ n := by
  rw [Real.dist_eq, abs_sub_comm]
  refine (abs_tateSeq_succ_sub_le hd h x n).trans_eq ?_
  rw [div_pow, one_pow, div_mul_div_comm, mul_one, ← pow_succ']

theorem cauchySeq_tateSeq (hd : 1 < d) (h : ∀ x, |f (T x) - d * f x| ≤ C) (x : α) :
    CauchySeq (tateSeq f T d x) :=
  cauchySeq_of_le_geometric (1 / d) (C / d)
    ((div_lt_one (by linarith)).2 (by linarith))
    (dist_tateSeq_succ_le (by linarith) h x)

/-- The limit defining `Function.tateLimit` exists. -/
theorem tendsto_tateLimit (hd : 1 < d) (h : ∀ x, |f (T x) - d * f x| ≤ C) (x : α) :
    Tendsto (tateSeq f T d x) atTop (𝓝 (tateLimit f T d x)) :=
  (cauchySeq_tateSeq hd h x).tendsto_limUnder

/-- **The limit is exactly homogeneous**, where `f` was only almost so. -/
theorem tateLimit_comp_self (hd : 1 < d) (h : ∀ x, |f (T x) - d * f x| ≤ C) (x : α) :
    tateLimit f T d (T x) = d * tateLimit f T d x := by
  have hd0 : d ≠ 0 := by positivity
  have h1 : Tendsto (fun n => tateSeq f T d x (n + 1)) atTop
      (𝓝 (tateLimit f T d x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_tateLimit hd h x)
  refine tendsto_nhds_unique (tendsto_tateLimit hd h (T x)) ?_
  simpa only [← tateSeq_comp_self hd0] using h1.const_mul d

/-- Iterated form of `Function.tateLimit_comp_self`. -/
theorem tateLimit_iterate (hd : 1 < d) (h : ∀ x, |f (T x) - d * f x| ≤ C) (x : α)
    (n : ℕ) : tateLimit f T d (T^[n] x) = d ^ n * tateLimit f T d x := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [iterate_succ_apply', tateLimit_comp_self hd h, ih, pow_succ]; ring

/-- **The window**: the limit never moves `f` by more than `C / (d - 1)`. -/
theorem abs_tateLimit_sub_le (hd : 1 < d) (h : ∀ x, |f (T x) - d * f x| ≤ C) (x : α) :
    |tateLimit f T d x - f x| ≤ C / (d - 1) := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hr : (1 : ℝ) / d < 1 := (div_lt_one hd0).2 (by linarith)
  have key := dist_le_of_le_geometric_of_tendsto₀ (1 / d) (C / d) hr
    (dist_tateSeq_succ_le hd0 h x) (tendsto_tateLimit hd h x)
  rw [Real.dist_eq, tateSeq_zero] at key
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
  have e1 : (1 : ℝ) - 1 / d = (d - 1) / d := by field_simp
  have hconst : C / d / (1 - 1 / d) = C / (d - 1) := by
    rw [e1, div_div_eq_mul_div, div_mul_cancel₀ C hdne]
  rw [hconst] at key
  rwa [abs_sub_comm]

/-- **The effective window**: knowing `f (T^[n] x)` pins the limit to within
`C / ((d - 1) * d ^ n)`. Doubling the depth squares the accuracy, which is what
makes finite computations certify statements about the limit. -/
theorem abs_tateLimit_sub_iterate_le (hd : 1 < d) (h : ∀ x, |f (T x) - d * f x| ≤ C)
    (x : α) (n : ℕ) :
    |tateLimit f T d x - tateSeq f T d x n| ≤ C / (d - 1) / d ^ n := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hpow : (0 : ℝ) < d ^ n := by positivity
  have hwin := abs_tateLimit_sub_le hd h (T^[n] x)
  rw [tateLimit_iterate hd h x n] at hwin
  rw [le_div_iff₀ hpow]
  have e : d ^ n * (tateLimit f T d x - tateSeq f T d x n)
      = d ^ n * tateLimit f T d x - f (T^[n] x) := by
    simp only [tateSeq]; field_simp
  calc |tateLimit f T d x - tateSeq f T d x n| * d ^ n
      = |d ^ n * (tateLimit f T d x - tateSeq f T d x n)| := by
        rw [abs_mul, abs_of_pos hpow]; ring
    _ = |d ^ n * tateLimit f T d x - f (T^[n] x)| := by rw [e]
    _ ≤ C / (d - 1) := hwin

/-- **Uniqueness**: an exactly homogeneous function is determined by its bounded
distance from another one. Combined with `Function.abs_tateLimit_sub_le`, this says
`tateLimit f T d` is *the* homogeneous function near `f`. -/
theorem eq_of_comp_self_of_abs_sub_le {g₁ g₂ : α → ℝ} {B : ℝ} (hd : 1 < d)
    (h₁ : ∀ x, g₁ (T x) = d * g₁ x) (h₂ : ∀ x, g₂ (T x) = d * g₂ x)
    (hb : ∀ x, |g₁ x - g₂ x| ≤ B) : g₁ = g₂ := by
  have hiter : ∀ (g : α → ℝ), (∀ x, g (T x) = d * g x) →
      ∀ (x : α) (n : ℕ), g (T^[n] x) = d ^ n * g x := by
    intro g hg x n
    induction n with
    | zero => simp
    | succ k ih => rw [iterate_succ_apply', hg, ih, pow_succ]; ring
  funext x
  have hpow : ∀ n : ℕ, (0 : ℝ) < d ^ n := fun n => by positivity
  -- `|g₁ x - g₂ x| ≤ B / d ^ n` for every `n`, and `B / d ^ n → 0`.
  have hle : ∀ n : ℕ, |g₁ x - g₂ x| ≤ B / d ^ n := by
    intro n
    have hbn := hb (T^[n] x)
    rw [hiter g₁ h₁ x n, hiter g₂ h₂ x n, ← mul_sub, abs_mul,
      abs_of_pos (hpow n)] at hbn
    rwa [le_div_iff₀ (hpow n), mul_comm]
  have htend : Tendsto (fun n : ℕ => B / d ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hd)
  have : |g₁ x - g₂ x| ≤ 0 := ge_of_tendsto' htend hle
  have := le_antisymm this (abs_nonneg _)
  rwa [abs_eq_zero, sub_eq_zero] at this

end Function
