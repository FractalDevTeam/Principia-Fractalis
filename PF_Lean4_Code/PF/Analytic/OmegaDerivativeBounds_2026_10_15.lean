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

set_option autoImplicit false

namespace PrincipiaTractalis
namespace OmegaDerivativeBounds20261015

open Real MeasureTheory Set Topology
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014

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

end

/-! ## §Axiom check -/

#print axioms crossTerm_nonpos
#print axioms summable_crossTerm
#print axioms omega_plus_cross_eq_tsum
#print axioms omega_prime_cross_term_nonpos
#print axioms deriv_F_plus_nonpos_on_Ioi
#print axioms F_plus_continuous
#print axioms F_plus_differentiable
#print axioms F_plus_antitone_on_Ici_zero

end OmegaDerivativeBounds20261015
end PrincipiaTractalis
