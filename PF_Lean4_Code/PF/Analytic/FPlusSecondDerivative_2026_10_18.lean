/-
# PF.Analytic.FPlusSecondDerivative_2026_10_18

**`F₊″`, its exponential majorant, and `IntegrableOn F₊″ (Ioi 0)`** — stage 3
of the Tier-3 first brick (`codex/TIER3_PREFLIGHT_2026-10-18.md`), completing
Route 2.

With `F₊(u) = exp(u/2)·ω(exp u)`:

  `F₊′(u)  = ½exp(u/2)·ω(eᵘ) + exp(u/2)·(ω′(eᵘ)·eᵘ)`         (existing)
  `F₊″(u)  = ¼exp(u/2)·ω(eᵘ) + 2exp(u/2)·(ω′(eᵘ)·eᵘ)
               + exp(u/2)·(ω″(eᵘ)·eᵘ·eᵘ)`                      (here)

i.e. `¼e^{u/2}ω + 2e^{3u/2}ω′ + e^{5u/2}ω″` — verified numerically to 26
digits before building.

### The majorant, and why Route 1 is not needed

For `u ≥ 0` we have `eᵘ ≥ 1`, so stage 2's bounds apply at `x = eᵘ`:

  `ω(eᵘ) ≤ (23/22)·E`,  `|ω′(eᵘ)| ≤ 2π·E`,  `ω″(eᵘ) ≤ 4π²·E`,
  where `E = exp(−π·eᵘ) ≤ exp(−π)·exp(−πu)`  (from `eᵘ ≥ 1 + u`).

Hence, bounding `e^{u/2}` and `e^{3u/2}` by `e^{5u/2}`,

  `|F₊″(u)| ≤ (23/88 + 4π + 4π²)·exp(−π)·exp(u(5/2 − π)) ≤ 81·exp(−π)·exp(u(5/2 − π))`

and `5/2 − π < 0`, so the majorant is integrable on `(0,∞)`. **No convexity
sign lemma, no `crossTerm` apparatus** — the pre-flight's Route 1, priced at
200–400 L of risk, is bypassed entirely.

Measurability comes free: every `HasDerivAt` here holds for **all** `u` (the
only side condition is `eᵘ > 0`), so `deriv F₊′ = F₊″` as functions and
`aestronglyMeasurable_deriv` applies.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-18.
-/
import PF.Analytic.OmegaDerivGeometricBounds_2026_10_18
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FPlusSecondDerivative20261018

open Real MeasureTheory Set Topology
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.OmegaDerivGeometricBounds20261018
open PrincipiaTractalis.Lambda0TightestBoundsMellin20261014

noncomputable section

/-! ## §1 — The explicit first and second derivatives of `F_plus`. -/

/-- Explicit first derivative of `F_plus`, exactly as `F_plus_hasDerivAt` states it. -/
def F_plus' (u : ℝ) : ℝ :=
  (1 / 2) * (Real.exp (u / 2) * omega (Real.exp u))
    + Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u)

/-- `deriv F_plus = F_plus'` as functions — `F_plus_hasDerivAt` is unconditional. -/
theorem deriv_F_plus_eq_F_plus' : deriv F_plus = F_plus' := by
  funext u
  rw [(F_plus_hasDerivAt u).deriv]
  unfold F_plus'
  ring

/-- Explicit second derivative:
`¼e^{u/2}ω(eᵘ) + 2e^{u/2}(ω′(eᵘ)eᵘ) + e^{u/2}(ω″(eᵘ)eᵘeᵘ)`. -/
def F_plus'' (u : ℝ) : ℝ :=
  (1 / 4) * Real.exp (u / 2) * omega (Real.exp u)
    + 2 * (Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u))
    + Real.exp (u / 2) * (omega'' (Real.exp u) * Real.exp u * Real.exp u)

/-- **★ `HasDerivAt F_plus' (F_plus'' u) u`, for every `u` ★**

Product and chain rules on `exp(·/2)`, `ω ∘ exp` and `ω′ ∘ exp`; the only side
condition anywhere is `exp u > 0`, which is free, so this is unconditional. -/
theorem F_plus'_hasDerivAt (u : ℝ) : HasDerivAt F_plus' (F_plus'' u) u := by
  have hexp : HasDerivAt Real.exp (Real.exp u) u := Real.hasDerivAt_exp u
  have hhalf : HasDerivAt (fun y : ℝ => y / 2) ((1 : ℝ) / 2) u := by
    have := (hasDerivAt_id u).div_const 2
    convert this using 1
  have hexp_half : HasDerivAt (fun y : ℝ => Real.exp (y / 2))
      ((1 / 2) * Real.exp (u / 2)) u := by
    have h := hhalf.exp
    convert h using 1
    ring
  have homega_exp : HasDerivAt (fun y : ℝ => omega (Real.exp y))
      (omega' (Real.exp u) * Real.exp u) u :=
    (omega_hasDerivAt (Real.exp_pos u)).comp u hexp
  have homega'_exp : HasDerivAt (fun y : ℝ => omega' (Real.exp y))
      (omega'' (Real.exp u) * Real.exp u) u :=
    (omega'_hasDerivAt (Real.exp_pos u)).comp u hexp
  have hT1 : HasDerivAt (fun y : ℝ => (1 / 2) * (Real.exp (y / 2) * omega (Real.exp y)))
      ((1 / 2) * ((1 / 2) * Real.exp (u / 2) * omega (Real.exp u)
        + Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u))) u :=
    (hexp_half.mul homega_exp).const_mul (1 / 2)
  have hT2 : HasDerivAt
      (fun y : ℝ => Real.exp (y / 2) * (omega' (Real.exp y) * Real.exp y))
      ((1 / 2) * Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u)
        + Real.exp (u / 2) * (omega'' (Real.exp u) * Real.exp u * Real.exp u
            + omega' (Real.exp u) * Real.exp u)) u :=
    hexp_half.mul (homega'_exp.mul hexp)
  have hsum := hT1.add hT2
  show HasDerivAt (fun y : ℝ => (1 / 2) * (Real.exp (y / 2) * omega (Real.exp y))
      + Real.exp (y / 2) * (omega' (Real.exp y) * Real.exp y)) (F_plus'' u) u
  convert hsum using 1
  unfold F_plus''
  ring

/-- `deriv F_plus' = F_plus''`, hence `deriv (deriv F_plus) = F_plus''`. -/
theorem deriv_F_plus'_eq_F_plus'' : deriv F_plus' = F_plus'' := by
  funext u
  exact (F_plus'_hasDerivAt u).deriv

/-- **`deriv (deriv F_plus) = F_plus''`** — the form the second IBP consumes. -/
theorem deriv_deriv_F_plus_eq : deriv (deriv F_plus) = F_plus'' := by
  rw [deriv_F_plus_eq_F_plus', deriv_F_plus'_eq_F_plus'']

/-! ## §2 — The exponential majorant. -/

/-- `ω(x) ≤ (23/22)·exp(−πx)` for `x ≥ 1`. -/
lemma omega_le_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    omega x ≤ (23 / 22) * Real.exp (-π * x) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hgeom := omega_le_geometric hx0
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h_le_pi : Real.exp (-π * x) ≤ Real.exp (-π) := by
    apply Real.exp_le_exp.mpr; nlinarith [hπ, hx]
  have h23 : Real.exp (-π) ≤ 1 / 23 := exp_neg_pi_le_one_twentythird
  have hlt : Real.exp (-π * x) ≤ 1 / 23 := le_trans h_le_pi h23
  have hpos : (0 : ℝ) < Real.exp (-π * x) := Real.exp_pos _
  have hden : (0 : ℝ) < 1 - Real.exp (-π * x) := by linarith
  have hinv : 1 / (1 - Real.exp (-π * x)) ≤ 23 / 22 := by
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 22)]
    linarith
  calc omega x ≤ Real.exp (-π * x) / (1 - Real.exp (-π * x)) := hgeom
    _ = Real.exp (-π * x) * (1 / (1 - Real.exp (-π * x))) := by ring
    _ ≤ Real.exp (-π * x) * (23 / 22) := mul_le_mul_of_nonneg_left hinv hpos.le
    _ = (23 / 22) * Real.exp (-π * x) := by ring

/-- `exp(−π·eᵘ) ≤ exp(−π)·exp(−πu)` for `u ≥ 0`, from `eᵘ ≥ 1 + u`. -/
lemma exp_neg_pi_exp_le {u : ℝ} (_hu : 0 ≤ u) :
    Real.exp (-π * Real.exp u) ≤ Real.exp (-π) * Real.exp (-π * u) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := Real.add_one_le_exp u
  have hπ : (0 : ℝ) < π := Real.pi_pos
  nlinarith [h, hπ]

/-- **★ The majorant: `|F₊″(u)| ≤ 81·exp(−π)·exp(u(5/2 − π))` for `u ≥ 0` ★** -/
theorem abs_F_plus''_le {u : ℝ} (hu : 0 ≤ u) :
    |F_plus'' u| ≤ 81 * Real.exp (-π) * Real.exp (u * (5 / 2 - π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have he1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  set E := Real.exp (-π * Real.exp u) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  -- the three ingredient bounds, at x = exp u ≥ 1
  have hw : omega (Real.exp u) ≤ (23 / 22) * E := omega_le_of_one_le he1
  have hw' : |omega' (Real.exp u)| ≤ 2 * π * E := abs_omega'_le he1
  have hw'' : omega'' (Real.exp u) ≤ 4 * π ^ 2 * E := omega''_le he1
  have hw_nn : 0 ≤ omega (Real.exp u) := omega_nonneg (Real.exp u)
  have hw''_nn : 0 ≤ omega'' (Real.exp u) := omega''_nonneg _
  -- exp growth comparisons, all ≤ exp(5u/2)
  have hh : (0 : ℝ) < Real.exp (u / 2) := Real.exp_pos _
  have heu : (0 : ℝ) < Real.exp u := Real.exp_pos _
  have h52 : Real.exp (u / 2) ≤ Real.exp (u * (5 / 2)) := by
    apply Real.exp_le_exp.mpr; linarith
  have h32 : Real.exp (u / 2) * Real.exp u ≤ Real.exp (u * (5 / 2)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
  have h12 : Real.exp (u / 2) * Real.exp u * Real.exp u = Real.exp (u * (5 / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  -- termwise absolute bounds
  have hA : |(1 / 4 : ℝ) * Real.exp (u / 2) * omega (Real.exp u)|
      ≤ (23 / 88) * (E * Real.exp (u * (5 / 2))) := by
    rw [abs_of_nonneg (by positivity)]
    have : (1 / 4 : ℝ) * Real.exp (u / 2) * omega (Real.exp u)
        ≤ (1 / 4) * Real.exp (u / 2) * ((23 / 22) * E) := by
      apply mul_le_mul_of_nonneg_left hw (by positivity)
    nlinarith [this, h52, hEpos, hh]
  have hB : |2 * (Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u))|
      ≤ (4 * π) * (E * Real.exp (u * (5 / 2))) := by
    have hfac : |2 * (Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u))|
        = 2 * (Real.exp (u / 2) * Real.exp u) * |omega' (Real.exp u)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        abs_of_pos hh, abs_of_pos heu]
      ring
    rw [hfac]
    have h1 : 2 * (Real.exp (u / 2) * Real.exp u) * |omega' (Real.exp u)|
        ≤ 2 * (Real.exp (u / 2) * Real.exp u) * (2 * π * E) :=
      mul_le_mul_of_nonneg_left hw' (by positivity)
    nlinarith [h1, h32, hEpos, hπ]
  have hC : |Real.exp (u / 2) * (omega'' (Real.exp u) * Real.exp u * Real.exp u)|
      ≤ (4 * π ^ 2) * (E * Real.exp (u * (5 / 2))) := by
    rw [abs_of_nonneg (by positivity)]
    have hrw : Real.exp (u / 2) * (omega'' (Real.exp u) * Real.exp u * Real.exp u)
        = (Real.exp (u / 2) * Real.exp u * Real.exp u) * omega'' (Real.exp u) := by ring
    rw [hrw, h12]
    have := mul_le_mul_of_nonneg_left hw'' (le_of_lt (Real.exp_pos (u * (5 / 2))))
    nlinarith [this]
  -- assemble
  have hsum : |F_plus'' u| ≤ ((23 / 88) + 4 * π + 4 * π ^ 2) * (E * Real.exp (u * (5 / 2))) := by
    unfold F_plus''
    calc |(1 / 4 : ℝ) * Real.exp (u / 2) * omega (Real.exp u)
            + 2 * (Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u))
            + Real.exp (u / 2) * (omega'' (Real.exp u) * Real.exp u * Real.exp u)|
        ≤ |(1 / 4 : ℝ) * Real.exp (u / 2) * omega (Real.exp u)
            + 2 * (Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u))|
          + |Real.exp (u / 2) * (omega'' (Real.exp u) * Real.exp u * Real.exp u)| :=
          abs_add _ _
      _ ≤ (|(1 / 4 : ℝ) * Real.exp (u / 2) * omega (Real.exp u)|
            + |2 * (Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u))|)
          + |Real.exp (u / 2) * (omega'' (Real.exp u) * Real.exp u * Real.exp u)| := by
          have := abs_add ((1 / 4 : ℝ) * Real.exp (u / 2) * omega (Real.exp u))
            (2 * (Real.exp (u / 2) * (omega' (Real.exp u) * Real.exp u)))
          linarith
      _ ≤ ((23 / 88) + 4 * π + 4 * π ^ 2) * (E * Real.exp (u * (5 / 2))) := by
          linarith [hA, hB, hC]
  -- numeric: 23/88 + 4π + 4π² ≤ 53, and E ≤ exp(−π)exp(−πu)
  have hCle : (23 / 88 : ℝ) + 4 * π + 4 * π ^ 2 ≤ 81 := by
    nlinarith [Real.pi_le_four, Real.pi_pos]
  have hEle : E ≤ Real.exp (-π) * Real.exp (-π * u) := exp_neg_pi_exp_le hu
  have hprod : E * Real.exp (u * (5 / 2))
      ≤ Real.exp (-π) * Real.exp (u * (5 / 2 - π)) := by
    have hfac : Real.exp (-π) * Real.exp (-π * u) * Real.exp (u * (5 / 2))
        = Real.exp (-π) * Real.exp (u * (5 / 2 - π)) := by
      have hL : Real.exp (-π) * Real.exp (-π * u) * Real.exp (u * (5 / 2))
          = Real.exp (-π + -π * u + u * (5 / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      have hR : Real.exp (-π) * Real.exp (u * (5 / 2 - π))
          = Real.exp (-π + u * (5 / 2 - π)) := by
        rw [← Real.exp_add]
      rw [hL, hR]
      congr 1
      ring
    calc E * Real.exp (u * (5 / 2))
        ≤ (Real.exp (-π) * Real.exp (-π * u)) * Real.exp (u * (5 / 2)) :=
          mul_le_mul_of_nonneg_right hEle (Real.exp_pos _).le
      _ = Real.exp (-π) * Real.exp (u * (5 / 2 - π)) := hfac
  have hPnn : (0 : ℝ) ≤ E * Real.exp (u * (5 / 2)) := by positivity
  have step1 : ((23 / 88 : ℝ) + 4 * π + 4 * π ^ 2) * (E * Real.exp (u * (5 / 2)))
      ≤ 81 * (E * Real.exp (u * (5 / 2))) := mul_le_mul_of_nonneg_right hCle hPnn
  have step2 : (81 : ℝ) * (E * Real.exp (u * (5 / 2)))
      ≤ 81 * (Real.exp (-π) * Real.exp (u * (5 / 2 - π))) :=
    mul_le_mul_of_nonneg_left hprod (by norm_num)
  calc |F_plus'' u|
      ≤ ((23 / 88 : ℝ) + 4 * π + 4 * π ^ 2) * (E * Real.exp (u * (5 / 2))) := hsum
    _ ≤ 81 * (E * Real.exp (u * (5 / 2))) := step1
    _ ≤ 81 * (Real.exp (-π) * Real.exp (u * (5 / 2 - π))) := step2
    _ = 81 * Real.exp (-π) * Real.exp (u * (5 / 2 - π)) := by ring

/-! ## §3 — Integrability on `Ioi 0`. -/

/-- **★ `IntegrableOn F₊″ (Ioi 0)` — Route 2 complete ★**

Dominated by `81·exp(−π)·exp(u(5/2 − π))` with `5/2 − π < 0`. Measurability is
free from `aestronglyMeasurable_deriv`, since `F₊″ = deriv F₊′` as functions. -/
theorem F_plus''_integrable_Ioi : IntegrableOn F_plus'' (Ioi (0 : ℝ)) := by
  have hcoeff : (5 / 2 - π : ℝ) < 0 := by linarith [Real.pi_gt_three]
  have hexp := integrableOn_exp_mul_Ioi (a := 5 / 2 - π) hcoeff 0
  have hbound : IntegrableOn
      (fun u : ℝ => 81 * Real.exp (-π) * Real.exp ((5 / 2 - π) * u)) (Ioi (0 : ℝ)) :=
    hexp.const_mul _
  have hmeas : AEStronglyMeasurable F_plus''
      (Measure.restrict volume (Ioi (0 : ℝ))) := by
    rw [← deriv_F_plus'_eq_F_plus'']
    exact (aestronglyMeasurable_deriv F_plus' _)
  refine hbound.mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with u hu
  have h := abs_F_plus''_le (le_of_lt (mem_Ioi.mp hu))
  rw [Real.norm_eq_abs]
  have hcomm : Real.exp (u * (5 / 2 - π)) = Real.exp ((5 / 2 - π) * u) := by
    rw [mul_comm]
  rw [hcomm] at h
  exact h

/-- **`IntegrableOn (deriv (deriv F_plus)) (Ioi 0)`** — the hypothesis the
second integration by parts needs, with no sign lemma anywhere. -/
theorem integrableOn_deriv_deriv_F_plus :
    IntegrableOn (deriv (deriv F_plus)) (Ioi (0 : ℝ)) := by
  rw [deriv_deriv_F_plus_eq]
  exact F_plus''_integrable_Ioi

end

end FPlusSecondDerivative20261018
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.FPlusSecondDerivative20261018.deriv_F_plus_eq_F_plus'
#print axioms PrincipiaTractalis.FPlusSecondDerivative20261018.F_plus'_hasDerivAt
#print axioms PrincipiaTractalis.FPlusSecondDerivative20261018.deriv_F_plus'_eq_F_plus''
#print axioms PrincipiaTractalis.FPlusSecondDerivative20261018.deriv_deriv_F_plus_eq
#print axioms PrincipiaTractalis.FPlusSecondDerivative20261018.omega_le_of_one_le
#print axioms PrincipiaTractalis.FPlusSecondDerivative20261018.exp_neg_pi_exp_le
#print axioms PrincipiaTractalis.FPlusSecondDerivative20261018.abs_F_plus''_le
#print axioms PrincipiaTractalis.FPlusSecondDerivative20261018.F_plus''_integrable_Ioi
#print axioms PrincipiaTractalis.FPlusSecondDerivative20261018.integrableOn_deriv_deriv_F_plus
