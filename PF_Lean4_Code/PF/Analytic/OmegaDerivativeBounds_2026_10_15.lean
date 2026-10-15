/-
# PF.Analytic.OmegaDerivativeBounds_2026_10_15

**L2/L3 steps of the IBP decay chain** for `‖Λ₀(1+it)‖ ≤ C/|t|`.

Pablo's directive 2026-10-14 authorized the full `L2 → L3 → L4 → L5` IBP
decay chain. This file lands two intermediate steps:

* `omega_prime_cross_term_nonpos`: `(1/2)·ω(x) + x·ω'(x) ≤ 0` for `x ≥ 1`.
  This is the sign fact that forces `F_plus_antitone` on `Ici 0`
  (`F_plus(u) = exp(u/2) · ω(exp u)`).

* `F_plus_antitone_on_Ici_zero`: `F_plus` is antitone on `Ici 0`.

The cross-term sign fact comes from writing both sides as the single
series `∑' m, [(1/2) − π·m²·x] · exp(−π·m²·x)`. For `x ≥ 1` and every
`m ≥ 1` the coefficient is bounded above by `(1/2) − π·x ≤ (1/2) − π < 0`
(since `π > 1/2`), so every term is non-positive and the sum is.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/

import PF.Analytic.OmegaDerivative_2026_10_14
import PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace OmegaDerivativeBounds20261015

open Real MeasureTheory Set Topology Filter
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.Lambda0TightestBoundsMellin20261014

noncomputable section

/-! ## §1 — The combined series expression

The series `(1/2) · ω(x) + x · ω'(x) = ∑' m, [(1/2) − π·m²·x] · exp(−π·m²·x)`.
-/

/-- Each term of `(1/2)·ω(x) + x·ω'(x)` as a single series term. -/
def crossTerm (x : ℝ) (n : ℕ) : ℝ :=
  ((1 / 2) - π * ((n : ℝ) + 1) ^ 2 * x) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)

/-- Each term is non-positive for `x ≥ 1`. -/
lemma crossTerm_nonpos (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    crossTerm x n ≤ 0 := by
  unfold crossTerm
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ_gt_half : (1 / 2 : ℝ) < π := by linarith [Real.pi_gt_three]
  have hn : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    nlinarith [h1]
  have h_coef : (1 / 2 : ℝ) - π * ((n : ℝ) + 1) ^ 2 * x ≤ 0 := by
    have h1 : π * ((n : ℝ) + 1) ^ 2 * x ≥ π := by
      have hp_pos : 0 < π := hπ
      have h2 : π * 1 * 1 ≤ π * ((n : ℝ) + 1) ^ 2 * x := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hn hp_pos.le
        · exact hx
        · linarith
        · positivity
      linarith
    linarith [hπ_gt_half]
  have h_exp_pos : (0 : ℝ) < Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) :=
    Real.exp_pos _
  exact mul_nonpos_of_nonpos_of_nonneg h_coef h_exp_pos.le

/-- Summability of the combined series. -/
lemma summable_crossTerm {x : ℝ} (hx : 0 < x) :
    Summable (crossTerm x) := by
  unfold crossTerm
  -- Split: ∑ ((1/2) - π·m²·x)·exp(-πm²x)
  --     = (1/2)·∑ exp(-πm²x) - π·x·∑ m²·exp(-πm²x)
  -- Both are summable (first = ω, second = -ω'/π scaled).
  have h_omega : Summable fun n : ℕ =>
      Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := summable_omega hx
  have h_omega_mul : Summable fun n : ℕ =>
      π * ((n : ℝ) + 1) ^ 2 * x * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := by
    -- Bound by n² · exp(-r·n²·x) shift, then multiply by constants.
    -- Alternative: use the omega_term_deriv summability × x.
    have h_bound := summable_omega_term_deriv_bound hx
    -- summable_omega_term_deriv_bound : Summable (π · (n+1)² · exp(-π · (n+1)² · x))
    -- We need: Summable (π · (n+1)² · x · exp(...)) = x · (above)
    have h_mul_x := h_bound.mul_left x
    refine h_mul_x.congr fun n => ?_
    ring
  have h_sum : Summable fun n : ℕ =>
      (1 / 2 : ℝ) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
      - π * ((n : ℝ) + 1) ^ 2 * x * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) :=
    (h_omega.mul_left (1/2)).sub h_omega_mul
  refine h_sum.congr fun n => ?_
  ring

/-- **The series identity**: `(1/2)·ω(x) + x·ω'(x) = ∑' n, crossTerm x n`. -/
lemma omega_plus_cross_eq_tsum {x : ℝ} (hx : 0 < x) :
    (1 / 2) * omega x + x * omega' x = ∑' n : ℕ, crossTerm x n := by
  have h1 : Summable fun n : ℕ =>
      (1 / 2 : ℝ) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) :=
    (summable_omega hx).mul_left _
  have h2 : Summable fun n : ℕ =>
      x * (-(π * ((n : ℝ) + 1) ^ 2)
            * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)) := by
    have h_bound := summable_omega_term_deriv_bound hx
    have h_neg := h_bound.neg
    have h_mul := h_neg.mul_left x
    refine h_mul.congr fun n => ?_
    ring
  calc (1 / 2) * omega x + x * omega' x
      = (1 / 2) * (∑' n : ℕ, Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x))
          + x * (∑' n : ℕ, -(π * ((n : ℝ) + 1) ^ 2)
                              * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)) := rfl
    _ = (∑' n : ℕ, (1 / 2 : ℝ) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x))
          + (∑' n : ℕ, x * (-(π * ((n : ℝ) + 1) ^ 2)
                              * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x))) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ = ∑' n : ℕ, ((1 / 2 : ℝ) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
                   + x * (-(π * ((n : ℝ) + 1) ^ 2)
                              * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x))) :=
        (tsum_add h1 h2).symm
    _ = ∑' n : ℕ, crossTerm x n := by
        congr 1; funext n
        unfold crossTerm; ring

/-! ## §2 — The cross-term sign fact -/

/-- **`(1/2)·ω(x) + x·ω'(x) ≤ 0` for `x ≥ 1`.**
Each term of the combined series is non-positive. -/
theorem omega_prime_cross_term_nonpos {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2) * omega x + x * omega' x ≤ 0 := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [omega_plus_cross_eq_tsum hx_pos]
  exact tsum_nonpos (fun n => crossTerm_nonpos n hx)

end

/-! ## §3 — L3a: `F_plus` antitone on `Ici 0`

Combines `omega_prime_cross_term_nonpos` with `F_plus_hasDerivAt` to show
the derivative of `F_plus` is non-positive on `Ioi 0`, then uses
`antitoneOn_of_deriv_nonpos`.
-/

/-- The derivative of `F_plus` is non-positive on `Ioi 0`. -/
lemma deriv_F_plus_nonpos_on_Ioi {u : ℝ} (hu : 0 < u) :
    deriv F_plus u ≤ 0 := by
  have h_hasDeriv := F_plus_hasDerivAt u
  rw [h_hasDeriv.deriv]
  -- Deriv = (1/2) * exp(u/2) * omega(exp u) + exp(u/2) * (omega'(exp u) * exp u)
  --       = exp(u/2) * [(1/2) * omega(exp u) + exp u * omega'(exp u)]
  have h_exp_u_pos : 0 < Real.exp u := Real.exp_pos _
  have h_exp_u_ge_one : (1 : ℝ) ≤ Real.exp u := by
    have := Real.exp_pos u
    have h := Real.add_one_le_exp u
    linarith
  have h_cross := omega_prime_cross_term_nonpos h_exp_u_ge_one
  -- h_cross : (1/2) * omega (exp u) + exp u * omega' (exp u) ≤ 0
  have h_exp_half_pos : 0 < Real.exp (u / 2) := Real.exp_pos _
  have h_rewrite :
      (1 / 2) * Real.exp (u / 2) * omega (Real.exp u)
      + Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u)
      = Real.exp (u / 2) *
          ((1 / 2) * omega (Real.exp u) + Real.exp u * omega' (Real.exp u)) := by ring
  rw [h_rewrite]
  exact mul_nonpos_of_nonneg_of_nonpos h_exp_half_pos.le h_cross

/-- `F_plus` is continuous on all of ℝ (hence on `Ici 0`). -/
lemma F_plus_continuous : Continuous F_plus := by
  unfold F_plus
  have h_exp_half : Continuous fun u : ℝ => Real.exp (u / 2) :=
    Real.continuous_exp.comp (continuous_id.div_const 2)
  have h_omega_exp : Continuous fun u : ℝ => omega (Real.exp u) := by
    -- omega is continuous on Ioi 0, and exp u ∈ Ioi 0 for all u ∈ ℝ.
    have h_omega_cont : ContinuousOn omega (Ioi 0) := continuousOn_omega
    exact h_omega_cont.comp_continuous Real.continuous_exp
      (fun u => Real.exp_pos u)
  exact h_exp_half.mul h_omega_exp

/-- `F_plus` is differentiable on all of ℝ (hence on interior (Ici 0) = Ioi 0). -/
lemma F_plus_differentiable : Differentiable ℝ F_plus :=
  fun u => (F_plus_hasDerivAt u).differentiableAt

/-- **`F_plus` is antitone on `Ici 0`.** -/
theorem F_plus_antitone_on_Ici_zero : AntitoneOn F_plus (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact F_plus_continuous.continuousOn
  · rw [interior_Ici]
    exact F_plus_differentiable.differentiableOn
  · intro u hu
    rw [interior_Ici, mem_Ioi] at hu
    exact deriv_F_plus_nonpos_on_Ioi hu

/-! ## §4 — L3b/c: F± tendsto 0 at atTop

Both `F_minus(u) = ω(e^u)` and `F_plus(u) = e^(u/2)·ω(e^u)` tend to 0 as
`u → ∞`, by combining `ω(x) → 0` at `atTop` (from the geometric bound)
with substitution via `tendsto_comp_exp_atTop`.
-/

/-- `exp(-π·x) → 0` as `x → ∞`. Direct composition. -/
lemma tendsto_exp_neg_pi_mul_atTop_zero :
    Tendsto (fun x : ℝ => Real.exp (-π * x)) atTop (nhds 0) := by
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_pi_x : Tendsto (fun x : ℝ => π * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop hπ_pos
  have h_neg_pi_x : Tendsto (fun x : ℝ => -π * x) atTop atBot := by
    have h_neg := Filter.tendsto_neg_atTop_atBot.comp h_pi_x
    refine h_neg.congr fun x => ?_
    simp [Function.comp]
  exact Real.tendsto_exp_atBot.comp h_neg_pi_x

/-- `omega(x) → 0` as `x → ∞`. Via squeeze with the geometric upper bound. -/
theorem omega_tendsto_atTop_zero : Tendsto omega atTop (nhds 0) := by
  -- Upper bound: for x ≥ 1, omega(x) ≤ (23/22) · exp(-πx), using
  -- 1 - exp(-πx) ≥ 22/23 (since exp(-πx) ≤ exp(-π) ≤ 1/23 for x ≥ 1).
  have h_bound : ∀ᶠ x : ℝ in atTop,
      omega x ≤ (23 / 22) * Real.exp (-π * x) := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun x hx => ?_⟩
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have h_geom := omega_le_geometric hx_pos
    -- h_geom : omega x ≤ exp(-π·x) / (1 - exp(-π·x))
    have h_exp_x_le : Real.exp (-π * x) ≤ Real.exp (-π) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, hx]
    have h_exp_pi_le : Real.exp (-π) ≤ 1 / 23 := by
      have h := exp_pi_gt_twentythree
      rw [Real.exp_neg]
      rw [show (1 / 23 : ℝ) = (23 : ℝ)⁻¹ from by norm_num]
      exact inv_anti₀ (by norm_num : (0 : ℝ) < 23) h.le
    have h_exp_x_le_23 : Real.exp (-π * x) ≤ 1 / 23 :=
      le_trans h_exp_x_le h_exp_pi_le
    have h_one_sub_pos : 0 < 1 - Real.exp (-π * x) := by
      have h_exp_pos : 0 < Real.exp (-π * x) := Real.exp_pos _
      have h_exp_lt_one : Real.exp (-π * x) < 1 := by linarith
      linarith
    have h_one_sub_ge : 22 / 23 ≤ 1 - Real.exp (-π * x) := by linarith
    have h_inv_le : 1 / (1 - Real.exp (-π * x)) ≤ 23 / 22 := by
      rw [div_le_div_iff₀ h_one_sub_pos (by norm_num : (0 : ℝ) < 22)]
      linarith
    calc omega x ≤ Real.exp (-π * x) / (1 - Real.exp (-π * x)) := h_geom
      _ = Real.exp (-π * x) * (1 / (1 - Real.exp (-π * x))) := by ring
      _ ≤ Real.exp (-π * x) * (23 / 22) :=
          mul_le_mul_of_nonneg_left h_inv_le (Real.exp_pos _).le
      _ = (23 / 22) * Real.exp (-π * x) := by ring
  have h_nn : ∀ᶠ x : ℝ in atTop, 0 ≤ omega x :=
    Filter.Eventually.of_forall omega_nonneg
  have h_tendsto_rhs : Tendsto (fun x : ℝ => (23 / 22) * Real.exp (-π * x)) atTop (nhds 0) := by
    have := tendsto_exp_neg_pi_mul_atTop_zero.const_mul (23 / 22 : ℝ)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tendsto_rhs h_nn h_bound

/-- `F_minus(u) = ω(exp u) → 0` as `u → ∞`. -/
theorem F_minus_tendsto_atTop_zero : Tendsto F_minus atTop (nhds 0) := by
  unfold F_minus
  rw [show (fun u : ℝ => omega (Real.exp u)) = omega ∘ Real.exp from rfl]
  exact omega_tendsto_atTop_zero.comp Real.tendsto_exp_atTop

/-- `F_plus(u) = exp(u/2) · ω(exp u) → 0` as `u → ∞`.
Uses the stronger bound `F_plus(u) ≤ exp(u/2 − π·exp u)/(1−exp(−π))` and
`u/2 − π·exp(u) → −∞`. -/
theorem F_plus_tendsto_atTop_zero : Tendsto F_plus atTop (nhds 0) := by
  -- Bound: for u ≥ 0, F_plus(u) = exp(u/2)·ω(exp u) ≤ exp(u/2)·(23/22)·exp(-π·exp u)
  --                              = (23/22) · exp(u/2 - π·exp u)
  -- As u → ∞: u/2 - π·exp(u) → -∞ (super-exp dominates linear).
  have h_bound : ∀ᶠ u : ℝ in atTop,
      F_plus u ≤ (23 / 22) * Real.exp (u / 2 - π * Real.exp u) := by
    rw [Filter.eventually_atTop]
    refine ⟨0, fun u hu => ?_⟩
    unfold F_plus
    have h_exp_u_ge_one : (1 : ℝ) ≤ Real.exp u := by
      have h := Real.add_one_le_exp u
      linarith
    have h_exp_u_pos : (0 : ℝ) < Real.exp u := Real.exp_pos u
    have h_geom := omega_le_geometric h_exp_u_pos
    have h_exp_eu_le : Real.exp (-π * Real.exp u) ≤ Real.exp (-π) := by
      apply Real.exp_le_exp.mpr
      have h_pi_pos : 0 < π := Real.pi_pos
      nlinarith
    have h_exp_pi_le : Real.exp (-π) ≤ 1 / 23 := by
      have h := exp_pi_gt_twentythree
      rw [Real.exp_neg]
      rw [show (1 / 23 : ℝ) = (23 : ℝ)⁻¹ from by norm_num]
      exact inv_anti₀ (by norm_num : (0 : ℝ) < 23) h.le
    have h_exp_eu_le_23 : Real.exp (-π * Real.exp u) ≤ 1 / 23 :=
      le_trans h_exp_eu_le h_exp_pi_le
    have h_one_sub_pos : 0 < 1 - Real.exp (-π * Real.exp u) := by
      have h_exp_pos : 0 < Real.exp (-π * Real.exp u) := Real.exp_pos _
      have h_exp_lt_one : Real.exp (-π * Real.exp u) < 1 := by linarith
      linarith
    have h_one_sub_ge : 22 / 23 ≤ 1 - Real.exp (-π * Real.exp u) := by linarith
    have h_inv_le : 1 / (1 - Real.exp (-π * Real.exp u)) ≤ 23 / 22 := by
      rw [div_le_div_iff₀ h_one_sub_pos (by norm_num : (0 : ℝ) < 22)]
      linarith
    have h_half_pos : 0 < Real.exp (u / 2) := Real.exp_pos _
    calc Real.exp (u / 2) * omega (Real.exp u)
        ≤ Real.exp (u / 2) * (Real.exp (-π * Real.exp u)
                              / (1 - Real.exp (-π * Real.exp u))) :=
          mul_le_mul_of_nonneg_left h_geom h_half_pos.le
      _ = Real.exp (u / 2) * Real.exp (-π * Real.exp u)
          * (1 / (1 - Real.exp (-π * Real.exp u))) := by ring
      _ ≤ Real.exp (u / 2) * Real.exp (-π * Real.exp u) * (23 / 22) :=
          mul_le_mul_of_nonneg_left h_inv_le
            (mul_nonneg h_half_pos.le (Real.exp_pos _).le)
      _ = (23 / 22) * (Real.exp (u / 2) * Real.exp (-π * Real.exp u)) := by ring
      _ = (23 / 22) * Real.exp (u / 2 + (-π * Real.exp u)) := by
          rw [← Real.exp_add]
      _ = (23 / 22) * Real.exp (u / 2 - π * Real.exp u) := by ring_nf
  have h_nn : ∀ᶠ u : ℝ in atTop, 0 ≤ F_plus u :=
    Filter.Eventually.of_forall F_plus_nonneg
  -- Now show RHS → 0.
  have h_exponent_atBot : Tendsto (fun u : ℝ => u / 2 - π * Real.exp u) atTop atBot := by
    -- u/2 - π·exp(u). As u → ∞: exp(u) → ∞ (atTop), so π·exp(u) → atTop,
    -- so -π·exp(u) → atBot. The "u/2" term is dominated.
    have h_exp : Tendsto Real.exp atTop atTop := Real.tendsto_exp_atTop
    have h_pi_exp : Tendsto (fun u : ℝ => π * Real.exp u) atTop atTop :=
      h_exp.const_mul_atTop Real.pi_pos
    have h_neg_pi_exp : Tendsto (fun u : ℝ => -(π * Real.exp u)) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp h_pi_exp
    -- u/2 is bounded above by u, so u/2 + (-π·exp u) → atBot via "atBot + id ... "
    -- Easier: for u ≥ 1, u/2 - π·exp(u) ≤ u - π·exp(u). And u - π·exp(u) → atBot
    -- since exp(u) grows faster than linear.
    -- Actually, u/2 - π·exp(u) ≤ -π·exp(u)/2 for u large enough (since exp(u)/2 ≥ u
    -- for u ≥ some threshold). Use isLittleO: u = o(exp(u)).
    -- Simpler: just use tendsto_atBot_add_const using (tendsto_atBot.add_le).
    -- Or: use Filter.tendsto_atBot_mono: if f ≤ g eventually and g → atBot, then f → atBot.
    have h_bound_exponent : ∀ᶠ u : ℝ in atTop,
        u / 2 - π * Real.exp u ≤ -(π / 2) * Real.exp u := by
      rw [Filter.eventually_atTop]
      refine ⟨1, fun u hu => ?_⟩
      -- Need u/2 - π·exp(u) ≤ -(π/2)·exp(u)
      -- Equivalent to u/2 ≤ π·exp(u) - (π/2)·exp(u) = (π/2)·exp(u)
      -- i.e., u ≤ π·exp(u)
      -- For u ≥ 1: exp(u) ≥ e > u (true for u ≤ e; need stronger for u > e).
      -- Use: exp(u) ≥ u + 1 ≥ u (true all u ≥ 0). And π ≥ 3 ≥ 1. So π·exp(u) ≥ exp(u) ≥ u.
      have h_exp_ge_u : u ≤ Real.exp u := by
        have := Real.add_one_le_exp u; linarith
      have h_pi_ge_one : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
      have h_pi_exp_ge_u : u ≤ π * Real.exp u := by
        calc u ≤ Real.exp u := h_exp_ge_u
          _ = 1 * Real.exp u := (one_mul _).symm
          _ ≤ π * Real.exp u :=
              mul_le_mul_of_nonneg_right h_pi_ge_one (Real.exp_pos u).le
      linarith
    have h_neg_half_pi_exp : Tendsto (fun u : ℝ => -(π / 2) * Real.exp u) atTop atBot := by
      have h_half_pi_exp : Tendsto (fun u : ℝ => (π / 2) * Real.exp u) atTop atTop :=
        h_exp.const_mul_atTop (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)
      have := Filter.tendsto_neg_atTop_atBot.comp h_half_pi_exp
      refine this.congr (fun u => ?_)
      simp [Function.comp]
    exact Filter.tendsto_atBot_mono' atTop h_bound_exponent h_neg_half_pi_exp
  have h_exp_exp_zero : Tendsto (fun u : ℝ => Real.exp (u / 2 - π * Real.exp u)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_exponent_atBot
  have h_rhs : Tendsto (fun u : ℝ => (23 / 22) * Real.exp (u / 2 - π * Real.exp u)) atTop (nhds 0) := by
    have := h_exp_exp_zero.const_mul (23 / 22 : ℝ)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_rhs h_nn h_bound

/-! ## §5 — Variation integrals: `∫_0^∞ (−F'_±(u)) du = ω(1)`

These are the IBP-ready bounds: for a monotone-decreasing F with F(∞) = 0,
`∫_0^∞ (−F'(u)) du = F(0) − 0 = F(0)` by FTC-on-`Ioi 0`
(`integral_Ioi_of_hasDerivAt_of_nonpos`).
-/

/-- `deriv F_minus u = omega' (exp u) · exp u ≤ 0` for all `u`. -/
lemma deriv_F_minus_nonpos (u : ℝ) : deriv F_minus u ≤ 0 := by
  have h := F_minus_hasDerivAt u
  rw [h.deriv]
  have h_omega' := omega'_nonpos (Real.exp_pos u)
  have h_exp_pos : 0 < Real.exp u := Real.exp_pos u
  exact mul_nonpos_of_nonpos_of_nonneg h_omega' h_exp_pos.le

/-- `F_minus` continuity (follows from omega_continuous + exp continuous). -/
lemma F_minus_continuous : Continuous F_minus := by
  unfold F_minus
  have h_omega_cont : ContinuousOn omega (Ioi 0) := continuousOn_omega
  exact h_omega_cont.comp_continuous Real.continuous_exp (fun u => Real.exp_pos u)

/-- **`∫_0^∞ deriv F_minus = -F_minus(0) = -omega(1)`.** -/
theorem integral_deriv_F_minus_Ioi_eq :
    ∫ u in Ioi (0 : ℝ), deriv F_minus u = -omega 1 := by
  have h_cont : ContinuousWithinAt F_minus (Ici 0) 0 :=
    F_minus_continuous.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)
  have h_deriv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F_minus (deriv F_minus x) x :=
    fun x _ => (F_minus_hasDerivAt x).congr_deriv ((F_minus_hasDerivAt x).deriv).symm
  have h_nonpos : ∀ x ∈ Ioi (0 : ℝ), deriv F_minus x ≤ 0 :=
    fun x _ => deriv_F_minus_nonpos x
  have h_tendsto := F_minus_tendsto_atTop_zero
  have h := integral_Ioi_of_hasDerivAt_of_nonpos h_cont h_deriv h_nonpos h_tendsto
  simp [F_minus, Real.exp_zero] at h
  linarith

/-- **`∫_0^∞ (−deriv F_minus u) du = omega(1)`.** The variation. -/
theorem integral_neg_deriv_F_minus_Ioi_eq :
    ∫ u in Ioi (0 : ℝ), -(deriv F_minus u) = omega 1 := by
  rw [MeasureTheory.integral_neg]
  rw [integral_deriv_F_minus_Ioi_eq]
  ring

/-- **`∫_0^∞ deriv F_plus = -F_plus(0) = -omega(1)`.**
Via `integral_Ioi_of_hasDerivAt_of_nonpos` applied to `F_plus`. -/
theorem integral_deriv_F_plus_Ioi_eq :
    ∫ u in Ioi (0 : ℝ), deriv F_plus u = -omega 1 := by
  have h_cont : ContinuousWithinAt F_plus (Ici 0) 0 :=
    F_plus_continuous.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)
  have h_deriv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F_plus (deriv F_plus x) x :=
    fun x _ => (F_plus_hasDerivAt x).congr_deriv ((F_plus_hasDerivAt x).deriv).symm
  have h_nonpos : ∀ x ∈ Ioi (0 : ℝ), deriv F_plus x ≤ 0 :=
    fun x hx => deriv_F_plus_nonpos_on_Ioi (mem_Ioi.mp hx)
  have h_tendsto := F_plus_tendsto_atTop_zero
  have h := integral_Ioi_of_hasDerivAt_of_nonpos h_cont h_deriv h_nonpos h_tendsto
  simp [F_plus, Real.exp_zero] at h
  linarith

/-- **`∫_0^∞ (−deriv F_plus u) du = omega(1)`.** -/
theorem integral_neg_deriv_F_plus_Ioi_eq :
    ∫ u in Ioi (0 : ℝ), -(deriv F_plus u) = omega 1 := by
  rw [MeasureTheory.integral_neg]
  rw [integral_deriv_F_plus_Ioi_eq]
  ring

/-! ## §Axiom check -/

#print axioms crossTerm_nonpos
#print axioms summable_crossTerm
#print axioms omega_plus_cross_eq_tsum
#print axioms omega_prime_cross_term_nonpos
#print axioms deriv_F_plus_nonpos_on_Ioi
#print axioms F_plus_continuous
#print axioms F_plus_differentiable
#print axioms F_plus_antitone_on_Ici_zero
#print axioms tendsto_exp_neg_pi_mul_atTop_zero
#print axioms omega_tendsto_atTop_zero
#print axioms F_minus_tendsto_atTop_zero
#print axioms F_plus_tendsto_atTop_zero
#print axioms deriv_F_minus_nonpos
#print axioms F_minus_continuous
#print axioms integral_deriv_F_minus_Ioi_eq
#print axioms integral_neg_deriv_F_minus_Ioi_eq
#print axioms integral_deriv_F_plus_Ioi_eq
#print axioms integral_neg_deriv_F_plus_Ioi_eq

end OmegaDerivativeBounds20261015
end PrincipiaTractalis
