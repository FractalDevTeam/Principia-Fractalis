/-
# PF.Analytic.OmegaSecondDerivative_2026_10_18

**The second derivative of `ω`** — the first new derivative order in the tree.
Stage 1 of the Tier-3 first brick (`codex/TIER3_PREFLIGHT_2026-10-18.md`).

The pre-flight found that the tree has **only** first-derivative content
(`omega'`, `omega_hasDerivAt`, `F_plus_hasDerivAt`, …) and no second or third
derivative anywhere. This file supplies the second order for `ω`, as a direct
mirror of `OmegaDerivative_2026_10_14`'s first-order construction:

| first order (existing) | second order (here) |
|---|---|
| `omega'` | `omega''` |
| `hasDerivAt_omega_term` | `hasDerivAt_omega'_term` |
| `omega_term_deriv_abs_le_on_Ioi` | `omega'_term_deriv_abs_le_on_Ioi` |
| `summable_omega_term_deriv_bound` | `summable_omega'_term_deriv_bound` |
| `omega_hasDerivAt` | `omega'_hasDerivAt` |
| `omega'_nonpos` | `omega''_nonneg` |
| `deriv_omega_eq` | `deriv_omega'_eq` |

The only substantive changes are an extra factor `−π(n+1)²` in each term (so the
dominating series needs `(n+1)⁴` rather than `(n+1)²`, i.e.
`Real.summable_pow_mul_exp_neg_nat_mul 4` in place of `… 2`) and the sign:
`ω′ ≤ 0` becomes `ω″ ≥ 0`, each term being a square times a positive
exponential.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-18.
-/
import PF.Analytic.OmegaDerivative_2026_10_14
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

namespace PrincipiaTractalis
namespace OmegaSecondDerivative20261018

open Real MeasureTheory Set Topology
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014

noncomputable section

/-! ## §1 — The termwise second derivative series. -/

/-- Term-by-term second derivative of `omega`:
`ω″(x) = ∑' n, (π(n+1)²)² · exp(−π(n+1)²x)`.

Every term is non-negative, which is the sign flip from `omega'`. -/
def omega'' (x : ℝ) : ℝ :=
  ∑' n : ℕ, ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x))

/-- Each `omega'`-term's pointwise derivative, from `hasDerivAt_omega_term`
scaled by the constant `−π(n+1)²`. -/
lemma hasDerivAt_omega'_term (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => -(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)) x := by
  have h := (hasDerivAt_omega_term n x).const_mul (-(π * ((n : ℝ) + 1) ^ 2))
  convert h using 1
  ring

/-- For any `δ > 0`, on `Ioi δ` the second-derivative terms have the uniform
summable bound `(π(n+1)²)² · exp(−π(n+1)²δ)`. -/
lemma omega'_term_deriv_abs_le_on_Ioi {δ : ℝ} (_hδ : 0 < δ)
    (n : ℕ) {x : ℝ} (hx : δ < x) :
    ‖(π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)‖
      ≤ (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ) := by
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |(π * ((n : ℝ) + 1) ^ 2) ^ 2| = (π * ((n : ℝ) + 1) ^ 2) ^ 2 :=
    abs_of_nonneg (by positivity)
  have h2 : |Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)|
      = Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := abs_of_pos (Real.exp_pos _)
  rw [h1, h2]
  have h_mono : Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
      ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ) := by
    apply Real.exp_le_exp.mpr
    have hterm_nn : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
    nlinarith [hterm_nn, hx]
  exact mul_le_mul_of_nonneg_left h_mono (by positivity)

/-- The dominating series for the second derivative is summable for `δ > 0`.

Mirror of `summable_omega_term_deriv_bound`, with `(n+1)⁴` in place of `(n+1)²`
(hence `Real.summable_pow_mul_exp_neg_nat_mul 4`) and `π²` in place of `π`. -/
lemma summable_omega'_term_deriv_bound {δ : ℝ} (hδ : 0 < δ) :
    Summable fun n : ℕ =>
      (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπδ : (0 : ℝ) < π * δ := mul_pos hπ hδ
  have h_mathlib : Summable fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-(π * δ) * (n : ℝ)) :=
    Real.summable_pow_mul_exp_neg_nat_mul 4 hπδ
  have h_shift : Summable fun n : ℕ =>
      ((n : ℝ) + 1) ^ 4 * Real.exp (-(π * δ) * ((n : ℝ) + 1)) := by
    have h_succ : (fun n : ℕ => ((n : ℝ) + 1) ^ 4 * Real.exp (-(π * δ) * ((n : ℝ) + 1)))
                = (fun n : ℕ => ((Nat.succ n : ℕ) : ℝ) ^ 4
                              * Real.exp (-(π * δ) * ((Nat.succ n : ℕ) : ℝ))) := by
      ext n
      push_cast
      ring_nf
    rw [h_succ]
    exact h_mathlib.comp_injective Nat.succ_injective
  have h_pi : Summable fun n : ℕ =>
      π ^ 2 * (((n : ℝ) + 1) ^ 4 * Real.exp (-(π * δ) * ((n : ℝ) + 1))) :=
    h_shift.mul_left (π ^ 2)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h_pi
  rw [show (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ)
      = π ^ 2 * (((n : ℝ) + 1) ^ 4 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ)) from by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ π ^ 2)
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 4)
  apply Real.exp_le_exp.mpr
  have h_sq_ge : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    nlinarith [h1]
  nlinarith [h_sq_ge, hπ.le, hδ.le]

/-- Summability of the `omega'` terms themselves at any `x > 0`, which
`hasDerivAt_tsum_of_isPreconnected` needs at the reference point. -/
lemma summable_omega'_term {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      -(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := by
  have hδ : (0 : ℝ) < x / 2 := by positivity
  have hlt : x / 2 < x := by linarith
  exact Summable.of_norm_bounded (summable_omega_term_deriv_bound hδ)
    (fun n => omega_term_deriv_abs_le_on_Ioi hδ n hlt)

/-! ## §2 — `omega'` is differentiable on `Ioi 0`, with derivative `omega''`. -/

/-- **★ Term-wise second derivative of `omega` on `Ioi 0` ★**
`HasDerivAt omega' (omega'' x) x` for `x > 0`.

Same proof shape as `omega_hasDerivAt`: choose `δ = x/2 > 0` and apply
`hasDerivAt_tsum_of_isPreconnected` on the open convex set `Ioi δ`. -/
theorem omega'_hasDerivAt {x : ℝ} (hx : 0 < x) : HasDerivAt omega' (omega'' x) x := by
  set δ := x / 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have hx_mem : δ < x := by rw [hδ_def]; linarith
  have h_u_summable := summable_omega'_term_deriv_bound hδ_pos
  have hx_summ := summable_omega'_term hx
  unfold omega' omega''
  exact hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ =>
        (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * δ))
      (g := fun (n : ℕ) (y : ℝ) =>
        -(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      (g' := fun (n : ℕ) (y : ℝ) =>
        (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      (t := Ioi δ) (y₀ := x) (y := x)
      h_u_summable
      isOpen_Ioi
      (convex_Ioi δ).isPreconnected
      (fun n y _ => hasDerivAt_omega'_term n y)
      (fun n y hy => omega'_term_deriv_abs_le_on_Ioi hδ_pos n (mem_Ioi.mp hy))
      hx_mem hx_summ hx_mem

/-- `deriv omega' x = omega'' x` for `x > 0`. -/
theorem deriv_omega'_eq {x : ℝ} (hx : 0 < x) : deriv omega' x = omega'' x :=
  (omega'_hasDerivAt hx).deriv

/-- **`omega'` is differentiable on `Ioi 0`.** -/
theorem differentiableOn_omega' : DifferentiableOn ℝ omega' (Ioi 0) := fun _x hx =>
  ((omega'_hasDerivAt (mem_Ioi.mp hx)).differentiableAt).differentiableWithinAt

/-! ## §3 — Sign: `omega'' ≥ 0`, the flip from `omega' ≤ 0`. -/

/-- Each term of `omega'' x` is non-negative — a square times a positive
exponential. -/
lemma omega''_term_nonneg (n : ℕ) (_x : ℝ) :
    0 ≤ (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * _x) := by
  positivity

/-- **`omega'' ≥ 0` everywhere the series converges.**

Note this is unconditional: for `x ≤ 0` the series diverges and `tsum` returns
its junk value `0`, which also satisfies the bound. -/
theorem omega''_nonneg (x : ℝ) : 0 ≤ omega'' x := by
  unfold omega''
  exact tsum_nonneg fun n => omega''_term_nonneg n x

/-- `|omega'' x| = omega'' x`. -/
theorem abs_omega''_eq (x : ℝ) : |omega'' x| = omega'' x :=
  abs_of_nonneg (omega''_nonneg x)

end

end OmegaSecondDerivative20261018
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.omega''
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.hasDerivAt_omega'_term
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.omega'_term_deriv_abs_le_on_Ioi
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.summable_omega'_term_deriv_bound
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.summable_omega'_term
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.omega'_hasDerivAt
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.deriv_omega'_eq
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.differentiableOn_omega'
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.omega''_nonneg
#print axioms PrincipiaTractalis.OmegaSecondDerivative20261018.abs_omega''_eq
