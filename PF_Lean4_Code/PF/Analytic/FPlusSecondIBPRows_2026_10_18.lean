/-
# PF.Analytic.FPlusSecondIBPRows_2026_10_18

**The three remaining hypotheses for a second integration by parts.**
Completes the Tier-3 first brick (`codex/TIER3_PREFLIGHT_2026-10-18.md`), whose
gap list named exactly these three as "mirrors of existing patterns with `F₊″`
in hand":

| row | content |
|---|---|
| 1 | `Tendsto (deriv F_plus) atTop (𝓝 0)` — mirror of `F_plus_tendsto_atTop_zero` |
| 2 | `ContinuousWithinAt (deriv F_plus) (Ici 0) 0` |
| 3 | `deriv F_plus 0 = ω(1)/2 + ω′(1)` and `deriv F_minus 0 = ω′(1)` |

With these, `ibp_phase` (`Lambda0IBPIdentity_2026_10_15:306`) can be instantiated
a **second** time at `F := deriv F_plus`, `F′ := deriv (deriv F_plus)`: its six
hypotheses are `hc`/`hcre` (free, the phase is purely imaginary), `hFderiv`
(= `F_plus'_hasDerivAt`), `hFcont0` (row 2), `hFtop` (row 1), `hFint`
(= `integrableOn_deriv_F_plus`, existing) and `hF'int`
(= `integrableOn_deriv_deriv_F_plus`, stage 3). Row 3 supplies the new boundary
constant the identity produces.

### Row 1's majorant

Same shape as stage 3, one term shorter. For `u ≥ 0`, with
`E = exp(−π·eᵘ) ≤ exp(−π)exp(−πu)`:

  `|F₊′(u)| ≤ ½e^{u/2}·(23/22)E + e^{3u/2}·2πE ≤ (23/44 + 2π)·E·e^{3u/2}`
          `≤ 9·exp(−π)·exp(u(3/2 − π))`

and `3/2 − π < 0`, so `squeeze_zero_norm'` closes the limit. As in stage 3 the
constant is deliberately loose: `23/44 + 2π = 6.81`, but `9` is provable from
`Real.pi_le_four` alone and the constant is irrelevant to a limit.

### Row 2 needs no new analysis

`ω′` is *differentiable* on `Ioi 0` (stage 1), hence continuous there, and
`eᵘ > 0` always — so `ContinuousAt (ω′ ∘ exp)` is free from
`HasDerivAt.continuousAt`. No uniform-convergence argument for `ω′`'s
continuity is needed, which is the one thing that could have made this row
expensive.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-18.
-/
import PF.Analytic.FPlusSecondDerivative_2026_10_18
import PF.Analytic.OmegaDerivativeBounds_2026_10_15

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FPlusSecondIBPRows20261018

open Real MeasureTheory Set Topology Filter
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.OmegaDerivGeometricBounds20261018
open PrincipiaTractalis.FPlusSecondDerivative20261018
open PrincipiaTractalis.OmegaDerivativeBounds20261015
open PrincipiaTractalis.Lambda0TightestBoundsMellin20261014

noncomputable section

/-! ## §1 — Row 1: `deriv F_plus → 0` at `+∞`. -/

/-- The majorant for `F₊′`, one term shorter than stage 3's for `F₊″`. -/
theorem abs_F_plus'_le {u : ℝ} (hu : 0 ≤ u) :
    |F_plus' u| ≤ 9 * Real.exp (-π) * Real.exp (u * (3 / 2 - π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have he1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  set E := Real.exp (-π * Real.exp u) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hw : omega (Real.exp u) ≤ (23 / 22) * E := omega_le_of_one_le he1
  have hw' : |omega' (Real.exp u)| ≤ 2 * π * E := abs_omega'_le he1
  have hh : (0 : ℝ) < Real.exp (u / 2) := Real.exp_pos _
  have heu : (0 : ℝ) < Real.exp u := Real.exp_pos _
  have h32 : Real.exp (u / 2) ≤ Real.exp (u * (3 / 2)) := by
    apply Real.exp_le_exp.mpr; linarith
  have h12 : Real.exp (u / 2) * Real.exp u = Real.exp (u * (3 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  -- termwise
  have hA : |(1 / 2 : ℝ) * (Real.exp (u / 2) * omega (Real.exp u))|
      ≤ (23 / 44) * (E * Real.exp (u * (3 / 2))) := by
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) * (Real.exp (u / 2) * omega (Real.exp u)) :=
      mul_nonneg (by norm_num) (mul_nonneg hh.le (omega_nonneg _))
    rw [abs_of_nonneg hnn]
    have h1 : (1 / 2 : ℝ) * (Real.exp (u / 2) * omega (Real.exp u))
        ≤ (1 / 2) * (Real.exp (u / 2) * ((23 / 22) * E)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
      exact mul_le_mul_of_nonneg_left hw hh.le
    nlinarith [h1, h32, hEpos, hh]
  have hB : |Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u)|
      ≤ (2 * π) * (E * Real.exp (u * (3 / 2))) := by
    have hfac : |Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u)|
        = (Real.exp (u / 2) * Real.exp u) * |omega' (Real.exp u)| := by
      rw [abs_mul, abs_mul, abs_of_pos hh, abs_of_pos heu]
      ring
    rw [hfac, h12]
    have h1 : Real.exp (u * (3 / 2)) * |omega' (Real.exp u)|
        ≤ Real.exp (u * (3 / 2)) * (2 * π * E) :=
      mul_le_mul_of_nonneg_left hw' (Real.exp_pos _).le
    nlinarith [h1]
  -- assemble
  have hsum : |F_plus' u| ≤ ((23 / 44 : ℝ) + 2 * π) * (E * Real.exp (u * (3 / 2))) := by
    unfold F_plus'
    calc |(1 / 2 : ℝ) * (Real.exp (u / 2) * omega (Real.exp u))
            + Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u)|
        ≤ |(1 / 2 : ℝ) * (Real.exp (u / 2) * omega (Real.exp u))|
          + |Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u)| := abs_add _ _
      _ ≤ ((23 / 44 : ℝ) + 2 * π) * (E * Real.exp (u * (3 / 2))) := by
          linarith [hA, hB]
  have hCle : (23 / 44 : ℝ) + 2 * π ≤ 9 := by
    nlinarith [Real.pi_le_four, Real.pi_pos]
  have hEle : E ≤ Real.exp (-π) * Real.exp (-π * u) := exp_neg_pi_exp_le hu
  have hprod : E * Real.exp (u * (3 / 2))
      ≤ Real.exp (-π) * Real.exp (u * (3 / 2 - π)) := by
    have hL : Real.exp (-π) * Real.exp (-π * u) * Real.exp (u * (3 / 2))
        = Real.exp (-π + -π * u + u * (3 / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    have hR : Real.exp (-π) * Real.exp (u * (3 / 2 - π))
        = Real.exp (-π + u * (3 / 2 - π)) := by
      rw [← Real.exp_add]
    have hfac : Real.exp (-π) * Real.exp (-π * u) * Real.exp (u * (3 / 2))
        = Real.exp (-π) * Real.exp (u * (3 / 2 - π)) := by
      rw [hL, hR]; congr 1; ring
    calc E * Real.exp (u * (3 / 2))
        ≤ (Real.exp (-π) * Real.exp (-π * u)) * Real.exp (u * (3 / 2)) :=
          mul_le_mul_of_nonneg_right hEle (Real.exp_pos _).le
      _ = Real.exp (-π) * Real.exp (u * (3 / 2 - π)) := hfac
  have hPnn : (0 : ℝ) ≤ E * Real.exp (u * (3 / 2)) := by positivity
  calc |F_plus' u|
      ≤ ((23 / 44 : ℝ) + 2 * π) * (E * Real.exp (u * (3 / 2))) := hsum
    _ ≤ 9 * (E * Real.exp (u * (3 / 2))) := mul_le_mul_of_nonneg_right hCle hPnn
    _ ≤ 9 * (Real.exp (-π) * Real.exp (u * (3 / 2 - π))) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = 9 * Real.exp (-π) * Real.exp (u * (3 / 2 - π)) := by ring

/-- `exp(u·c) → 0` as `u → ∞` for `c < 0`. -/
theorem tendsto_exp_mul_const_atTop_zero {c : ℝ} (hc : c < 0) :
    Tendsto (fun u : ℝ => Real.exp (u * c)) atTop (nhds 0) :=
  Real.tendsto_exp_atBot.comp (Filter.tendsto_id.atTop_mul_const_of_neg hc)

/-- **★ Row 1: `Tendsto (deriv F_plus) atTop (𝓝 0)` ★** -/
theorem tendsto_deriv_F_plus_atTop_zero :
    Tendsto (deriv F_plus) atTop (nhds 0) := by
  rw [deriv_F_plus_eq_F_plus']
  have hc : (3 / 2 - π : ℝ) < 0 := by linarith [Real.pi_gt_three]
  have hmaj : Tendsto (fun u : ℝ => 9 * Real.exp (-π) * Real.exp (u * (3 / 2 - π)))
      atTop (nhds 0) := by
    have h := tendsto_exp_mul_const_atTop_zero hc
    have := h.const_mul (9 * Real.exp (-π))
    simpa using this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [Real.norm_eq_abs]
  exact abs_F_plus'_le hu

/-! ## §2 — Row 2: continuity of `deriv F_plus` at the left boundary. -/

/-- `u ↦ ω(eᵘ)` is continuous — this is `F_minus_continuous`. -/
theorem continuous_omega_comp_exp : Continuous (fun u : ℝ => omega (Real.exp u)) :=
  F_minus_continuous

/-- `u ↦ ω′(eᵘ)` is continuous.

No new analysis: `ω′` is differentiable on `Ioi 0` by `omega'_hasDerivAt`
(stage 1), hence continuous there, and `eᵘ > 0` always. -/
theorem continuous_omega'_comp_exp : Continuous (fun u : ℝ => omega' (Real.exp u)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have h1 : ContinuousAt omega' (Real.exp u) :=
    (omega'_hasDerivAt (Real.exp_pos u)).continuousAt
  have h2 : ContinuousAt Real.exp u := Real.continuous_exp.continuousAt
  exact h1.comp h2

theorem continuous_exp_half : Continuous (fun u : ℝ => Real.exp (u / 2)) :=
  Real.continuous_exp.comp (continuous_id.div_const 2)

/-- `F₊′` is continuous on all of `ℝ`. -/
theorem continuous_F_plus' : Continuous F_plus' := by
  unfold F_plus'
  exact (continuous_const.mul (continuous_exp_half.mul continuous_omega_comp_exp)).add
    (continuous_exp_half.mul (continuous_omega'_comp_exp.mul Real.continuous_exp))

/-- **★ Row 2: `ContinuousWithinAt (deriv F_plus) (Ici 0) 0` ★** -/
theorem continuousWithinAt_deriv_F_plus_zero :
    ContinuousWithinAt (deriv F_plus) (Ici 0) 0 := by
  rw [deriv_F_plus_eq_F_plus']
  exact continuous_F_plus'.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)

/-! ## §3 — Row 3: the new boundary constants. -/

/-- **★ Row 3a: `deriv F_plus 0 = ω(1)/2 + ω′(1)` ★**

Numerically `−0.1141956486`; the identity is what the IBP consumes. -/
theorem deriv_F_plus_zero : deriv F_plus 0 = omega 1 / 2 + omega' 1 := by
  rw [deriv_F_plus_eq_F_plus']
  unfold F_plus'
  norm_num
  ring

/-- **★ Row 3b: `deriv F_minus 0 = ω′(1)` ★**

Numerically `−0.1358043514`. -/
theorem deriv_F_minus_zero : deriv F_minus 0 = omega' 1 := by
  simpa using (F_minus_hasDerivAt (0 : ℝ)).deriv

/-! ## §4 — The six `ibp_phase` hypotheses, collected.

Every hypothesis a second integration by parts needs at
`F := deriv F_plus`, `F′ := deriv (deriv F_plus)`, in one place. -/

/-- `hFderiv` for the second IBP: `deriv F_plus` has `deriv (deriv F_plus)` as
its derivative at every point of `Ioi 0`. -/
theorem hasDerivAt_deriv_F_plus (x : ℝ) (_hx : x ∈ Ioi (0 : ℝ)) :
    HasDerivAt (deriv F_plus) (deriv (deriv F_plus) x) x := by
  rw [deriv_F_plus_eq_F_plus', deriv_F_plus'_eq_F_plus'']
  exact F_plus'_hasDerivAt x

end

end FPlusSecondIBPRows20261018
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.abs_F_plus'_le
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.tendsto_exp_mul_const_atTop_zero
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.tendsto_deriv_F_plus_atTop_zero
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.continuous_omega_comp_exp
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.continuous_omega'_comp_exp
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.continuous_F_plus'
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.continuousWithinAt_deriv_F_plus_zero
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.deriv_F_plus_zero
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.deriv_F_minus_zero
#print axioms PrincipiaTractalis.FPlusSecondIBPRows20261018.hasDerivAt_deriv_F_plus
