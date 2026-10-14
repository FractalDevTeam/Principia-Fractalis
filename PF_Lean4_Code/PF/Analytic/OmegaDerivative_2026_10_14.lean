/-
# PF.Analytic.OmegaDerivative_2026_10_14

**Pointwise derivative of the Jacobi theta tail `ω`.**

Proves `HasDerivAt omega (omega' x) x` for `x > 0`, where

  `omega' x := ∑' n : ℕ, -π · ((n : ℝ) + 1)^2 · exp(-π · ((n : ℝ) + 1)^2 · x)`

is the term-by-term derivative of the series `omega x = ∑' n, exp(…)`.

Interchange of `d/dx` and `∑'` is justified by uniform summable bound on
the strip `Ioi δ` for any `δ > 0`, using mathlib's
`hasDerivAt_tsum_of_isPreconnected`. The summable bound uses mathlib's
`Real.summable_pow_mul_exp_neg_nat_mul`.

This is the first ingredient of the IBP decay chain
(`codex/LAMBDA0_IBP_DECAY_STRATEGY_2026-10-14.md`).

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.XiThetaIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

namespace PrincipiaTractalis
namespace OmegaDerivative20261014

open Real MeasureTheory Set Topology
open PrincipiaTractalis.XiThetaIntegral

noncomputable section

/-- Term-by-term derivative of `omega x = ∑' n, exp(-π · (n+1)² · x)`. -/
def omega' (x : ℝ) : ℝ :=
  ∑' n : ℕ, (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x))

/-- Each term's pointwise derivative. -/
lemma hasDerivAt_omega_term (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)) x := by
  have h : HasDerivAt (fun y : ℝ => (-π * ((n : ℝ) + 1) ^ 2) * y)
      ((-π * ((n : ℝ) + 1) ^ 2) * 1) x :=
    (hasDerivAt_id x).const_mul _
  have h2 := h.exp
  convert h2 using 1
  ring

/-- For any `δ > 0`, on `Ioi δ` the term derivatives have the uniform summable bound
    `|g'_n(x)| ≤ π · (n+1)² · exp(-π · (n+1)² · δ)`. -/
lemma omega_term_deriv_abs_le_on_Ioi {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) {x : ℝ} (hx : δ < x) :
    ‖-(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)‖
      ≤ π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ) := by
  rw [Real.norm_eq_abs, abs_mul, abs_neg]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
  have h1 : |π * ((n : ℝ) + 1) ^ 2| = π * ((n : ℝ) + 1) ^ 2 := by
    rw [abs_of_nonneg]; positivity
  have h2 : |Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)|
             = Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) :=
    abs_of_pos (Real.exp_pos _)
  rw [h1, h2]
  have h_mono : Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
              ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ) := by
    apply Real.exp_le_exp.mpr
    have hterm_nn : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
    nlinarith [hterm_nn, hx]
  have h_lhs_nn : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left h_mono h_lhs_nn

/-- The dominating series `n ↦ π · (n+1)² · exp(-π · (n+1)² · δ)` is summable for `δ > 0`. -/
lemma summable_omega_term_deriv_bound {δ : ℝ} (hδ : 0 < δ) :
    Summable fun n : ℕ =>
      π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ) := by
  -- Compare to Σ π · (n+1)² · exp(-π·δ·(n+1)), using (n+1)² ≥ (n+1) ≥ 0.
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπδ : (0 : ℝ) < π * δ := mul_pos hπ hδ
  -- `Real.summable_pow_mul_exp_neg_nat_mul k hr` gives Summable (fun n : ℕ => n^k * exp(-r·n))
  have h_mathlib : Summable fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-(π * δ) * (n : ℝ)) :=
    Real.summable_pow_mul_exp_neg_nat_mul 2 hπδ
  -- Shift n → n+1 (summability is preserved under cofinite shift).
  have h_shift : Summable fun n : ℕ =>
      ((n : ℝ) + 1) ^ 2 * Real.exp (-(π * δ) * ((n : ℝ) + 1)) := by
    have h_succ : (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * Real.exp (-(π * δ) * ((n : ℝ) + 1)))
                = (fun n : ℕ => ((Nat.succ n : ℕ) : ℝ) ^ 2
                              * Real.exp (-(π * δ) * ((Nat.succ n : ℕ) : ℝ))) := by
      ext n
      push_cast
      ring_nf
    rw [h_succ]
    exact h_mathlib.comp_injective Nat.succ_injective
  -- Multiply by π.
  have h_pi : Summable fun n : ℕ =>
      π * (((n : ℝ) + 1) ^ 2 * Real.exp (-(π * δ) * ((n : ℝ) + 1))) :=
    h_shift.mul_left π
  -- Dominate: π·(n+1)²·exp(-πδ·(n+1)²) ≤ π·(n+1)²·exp(-πδ·(n+1)).
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h_pi
  rw [show π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ)
      = π * (((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ)) from by ring,
      show π * (((n : ℝ) + 1) ^ 2 * Real.exp (-(π * δ) * ((n : ℝ) + 1)))
      = π * (((n : ℝ) + 1) ^ 2 * Real.exp (-(π * δ) * ((n : ℝ) + 1))) from rfl]
  apply mul_le_mul_of_nonneg_left _ hπ.le
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2)
  apply Real.exp_le_exp.mpr
  have h_sq_ge : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    nlinarith [h1, sq_nonneg ((n : ℝ) + 1 - 1)]
  nlinarith [h_sq_ge, hπ.le, hδ.le]

/-- **Term-wise derivative of `omega` on `Ioi 0`.** -/
theorem omega_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt omega (omega' x) x := by
  -- Choose δ = x/2 > 0 and use hasDerivAt_tsum_of_isPreconnected on Ioi δ.
  set δ := x / 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hx_mem : δ < x := by rw [hδ_def]; linarith
  -- The uniform summable bound.
  have h_u_summable := summable_omega_term_deriv_bound hδ_pos
  -- Summability of omega at a reference point x > 0.
  have hx_summ := summable_omega hx
  -- Apply hasDerivAt_tsum_of_isPreconnected on Ioi δ (open & preconnected = convex interval).
  unfold omega omega'
  have h_apply :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ => π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ))
      (g := fun (n : ℕ) (y : ℝ) => Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      (g' := fun (n : ℕ) (y : ℝ) =>
        -(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      (t := Ioi δ) (y₀ := x) (y := x)
      h_u_summable
      isOpen_Ioi
      (convex_Ioi δ).isPreconnected
      (fun n y _ => hasDerivAt_omega_term n y)
      (fun n y hy => omega_term_deriv_abs_le_on_Ioi hδ_pos n (mem_Ioi.mp hy))
      hx_mem hx_summ hx_mem
  exact h_apply

/-! ## §Sign of `omega'` -/

/-- Each term of `omega' x` is non-positive at `x > 0`. -/
lemma omega'_term_nonpos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    -(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) ≤ 0 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
  have h_coef_nonneg : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 :=
    mul_nonneg hπ.le hn
  have h_exp_pos : (0 : ℝ) < Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := Real.exp_pos _
  have : 0 ≤ π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) :=
    mul_nonneg h_coef_nonneg h_exp_pos.le
  linarith

/-- **`omega'(x) ≤ 0` on `Ioi 0`.** Immediate from term-wise non-positivity + summability. -/
theorem omega'_nonpos {x : ℝ} (hx : 0 < x) : omega' x ≤ 0 := by
  unfold omega'
  -- The series' terms are all ≤ 0 and the series is summable (shown by the
  -- same bound as the derivative-bound summability).
  have h_summ : Summable fun n : ℕ =>
      -(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := by
    have h_abs_summ : Summable fun n : ℕ =>
        π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := by
      -- Same proof as summable_omega_term_deriv_bound but at x instead of δ.
      have hπ : (0 : ℝ) < π := Real.pi_pos
      have hπx : (0 : ℝ) < π * x := mul_pos hπ hx
      have h_mathlib : Summable fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-(π * x) * (n : ℝ)) :=
        Real.summable_pow_mul_exp_neg_nat_mul 2 hπx
      have h_shift : Summable fun n : ℕ =>
          ((n : ℝ) + 1) ^ 2 * Real.exp (-(π * x) * ((n : ℝ) + 1)) := by
        have h_succ : (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * Real.exp (-(π * x) * ((n : ℝ) + 1)))
                    = (fun n : ℕ => ((Nat.succ n : ℕ) : ℝ) ^ 2
                                  * Real.exp (-(π * x) * ((Nat.succ n : ℕ) : ℝ))) := by
          ext n; push_cast; ring_nf
        rw [h_succ]
        exact h_mathlib.comp_injective Nat.succ_injective
      have h_pi : Summable fun n : ℕ =>
          π * (((n : ℝ) + 1) ^ 2 * Real.exp (-(π * x) * ((n : ℝ) + 1))) :=
        h_shift.mul_left π
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h_pi
      have h_rewrite : π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
          = π * (((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)) := by ring
      rw [h_rewrite]
      apply mul_le_mul_of_nonneg_left _ hπ.le
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2)
      apply Real.exp_le_exp.mpr
      have h_sq_ge : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
          have := Nat.cast_nonneg (α := ℝ) n
          linarith
        nlinarith [h1, sq_nonneg ((n : ℝ) + 1 - 1)]
      nlinarith [h_sq_ge, hπ.le, hx.le]
    have h_neg := h_abs_summ.neg
    convert h_neg using 1
    ext n; ring
  exact tsum_nonpos (fun n => omega'_term_nonpos n hx)

/-! ## §Omega differentiability on `Ioi 0` -/

/-- **`omega` is differentiable on `Ioi 0`.** Immediate from `omega_hasDerivAt`. -/
theorem differentiableOn_omega : DifferentiableOn ℝ omega (Ioi 0) := by
  intro x hx
  exact (omega_hasDerivAt (mem_Ioi.mp hx)).differentiableAt.differentiableWithinAt

/-- **`deriv omega x = omega' x` on `Ioi 0`.** -/
theorem deriv_omega_eq {x : ℝ} (hx : 0 < x) : deriv omega x = omega' x :=
  (omega_hasDerivAt hx).deriv

end

/-! ## §Axiom check -/

#print axioms hasDerivAt_omega_term
#print axioms omega_term_deriv_abs_le_on_Ioi
#print axioms summable_omega_term_deriv_bound
#print axioms omega_hasDerivAt
#print axioms omega'_term_nonpos
#print axioms omega'_nonpos
#print axioms differentiableOn_omega
#print axioms deriv_omega_eq

end OmegaDerivative20261014
end PrincipiaTractalis
