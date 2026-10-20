/-
# PF.Analytic.Lambda0PrimeThetaLogBound_2026_10_19

**A 6.28x tighter uniform bound on `Λ₀'` on the right edge, from the
log-weighted theta integral.**

  **‖(deriv completedRiemannZeta₀) (1 + it)‖ ≤ e^{-π} / (π²(1 - e^{-π}))**
                                             ≈ 0.0045763   (≤ 3/650)

uniformly in `t : ℝ`, replacing the Cauchy-at-radius-1 bound `50/1727 ≈
0.0289519` of `Lambda0UltraTightBoundsMellin_2026_10_14`.

## Why this is the Gate-2 unblock

Gate-2 is `(1 + 2|t|)·‖Λ₀‖ + (t² + |t|)·‖Λ₀'‖ ≤ 2`. The **second** term is
the binding one: at the `c = 55/8` box edge `t = 111/16` it contributes
`1.594` of the failing total `2.025`, against `0.431` from the first. So the
Gate-2 wall is a `Λ₀'` wall, and no improvement to the `Λ₀` bound can move it
far — including the Tier-3 sharp identity `Λ₀ = 1/t² − (4/t²)(I₊+I₋)`, whose
bound `(1 + 4K)/t²` with the **exact** `K = ∫|F₊″| + ∫|F₋″| = 1/4` equals
`0.0416` at that `t` and so is *1.44x worse* than `50/1727` there; it only
overtakes the uniform constant for `t ≥ 8.31`.

## Where the 6.28x comes from

The existing bound reaches `Λ₀'` by Cauchy's estimate `‖Λ₀'‖ ≤ M/R` on a disc
of radius `R = 1`. The radius cannot grow: the strip bound's proof needs both
theta exponents `σ/2−1` and `(1−σ)/2−1` to be `≤ 0`, which pins `σ ∈ [0,2]`,
i.e. `R ≤ 1`. And at `R = 1` the sup `M` cannot fall below `≈ 0.0236`. So
Cauchy is capped around `0.024`, a mere `1.2x`.

Differentiating the theta integral instead produces a `log x` factor:

  `Λ₀'(s) = ∫_1^∞ ½ log x · (x^{s/2−1} − x^{(1−s)/2−1}) · ω(x) dx`

whose modulus on the strip is bounded by `∫_1^∞ log x · ω(x) dx`. With
`ω(x) ≤ e^{-πx}/(1−e^{-π})` (the same majorant the `Λ₀` bound uses) and
`log x ≤ x − 1`, the weight turns `∫_1^∞ e^{-πx} dx = e^{-π}/π` into
`∫_1^∞ (x−1)e^{-πx} dx = e^{-π}/π²`. The whole gain is that one factor of
`1/π`, together with the `½` cancelling the `2` from the two terms:
`2/π → 1/π²`, i.e. exactly `1/(2π) = 6.28x`.

## Effect on the march

With `‖Λ₀'‖ ≤ 3/650` and `‖Λ₀‖ ≤ 50/1727` unchanged, Gate-2 holds for
`|t| ≤ 14.974` (was `6.886`):

| `t` | load | budget |
|---|---|---|
| `111/16 = 6.9375` (the c=55/8 edge) | `0.6847` | 2 |
| `13` (the R1 march target) | `1.6217` | 2 |
| `14.5` (the R2 upper end) | `1.9059` | 2 |

So the `c = 55/8` box passes with **2.9x headroom**, and Gate-2 never binds
again up to `t ≈ 14.974`. (`t = 15`, R3's top, lands at `2.0052` — just over;
see the note for the `Λ₀`-side follow-on that covers it.)

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-19.
-/

import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14
import PF.Analytic.R1Neighborhood_2026_10_09
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0PrimeThetaLogBound20261019

open Complex Real MeasureTheory Set Filter
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.Lambda0UniformBound20261014
open PrincipiaTractalis.Lambda0PrimeUniformBound20261014
open PrincipiaTractalis.Lambda0TightestBoundsMellin20261014
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.EdgeReDerivBound20261014
open PrincipiaTractalis.R1Neighborhood20261009

noncomputable section

/-! ## §1 — The elementary integral `∫_1^∞ (x−1) e^{-πx} dx = e^{-π}/π²` -/

/-- Antiderivative of `(x−1)e^{-πx}`. -/
private def G (x : ℝ) : ℝ := ((1 - x) / π - 1 / π ^ 2) * Real.exp (-π * x)

private lemma hasDerivAt_G (x : ℝ) :
    HasDerivAt G ((x - 1) * Real.exp (-π * x)) x := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h1 : HasDerivAt (fun y : ℝ => (1 - y) / π - 1 / π ^ 2) (-(1 / π)) x := by
    have hb : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have ha : HasDerivAt (fun y : ℝ => (1 - y) / π) (-(1 / π)) x := by
      have := hb.div_const π
      simpa [neg_div] using this
    simpa using ha.sub_const (1 / π ^ 2)
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-π * y)) (-π * Real.exp (-π * x)) x := by
    have hl : HasDerivAt (fun y : ℝ => -π * y) (-π) x := by
      simpa using (hasDerivAt_id x).const_mul (-π)
    simpa [mul_comm] using hl.exp
  have hG : G = fun y : ℝ => ((1 - y) / π - 1 / π ^ 2) * Real.exp (-π * y) := rfl
  rw [hG]
  convert h1.mul h2 using 1
  have hne : π ≠ 0 := ne_of_gt hpi
  field_simp
  ring

private lemma tendsto_G_atTop : Tendsto G atTop (nhds 0) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hne : π ≠ 0 := ne_of_gt hpi
  have h1 : Tendsto (fun u : ℝ => (1 / π - 1 / π ^ 2) * Real.exp (-u)) atTop (nhds 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (1 / π - 1 / π ^ 2)
    rwa [mul_zero] at h
  have h2 : Tendsto (fun u : ℝ => (1 / π ^ 2) * (u * Real.exp (-u))) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (1 / π ^ 2)
    rw [mul_zero] at h
    simp only [pow_one] at h
    exact h
  have hgt : Tendsto
      (fun u : ℝ => (1 / π - 1 / π ^ 2) * Real.exp (-u) - (1 / π ^ 2) * (u * Real.exp (-u)))
      atTop (nhds 0) := by
    have h := h1.sub h2
    rwa [sub_zero] at h
  have hcomp : Tendsto (fun x : ℝ => π * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hpi tendsto_id
  have hres := hgt.comp hcomp
  refine hres.congr (fun x => ?_)
  simp only [Function.comp_apply, G]
  field_simp
  ring

/-- `(x−1)e^{-πx}` is integrable on `(1, ∞)`: dominate by `e^{-1}e^{-(π-1)x}`. -/
private lemma integrableOn_sub_one_mul_exp :
    IntegrableOn (fun x : ℝ => (x - 1) * Real.exp (-π * x)) (Ioi 1) volume := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hpi1 : (0 : ℝ) < π - 1 := by nlinarith [Real.pi_gt_three]
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-1 : ℝ) * Real.exp (-(π - 1) * x))
      (Ioi 1) volume := (exp_neg_integrableOn_Ioi 1 hpi1).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (((continuous_id.sub continuous_const).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx1 : (1 : ℝ) ≤ x := le_of_lt (mem_Ioi.mp hx)
    have hnn : (0 : ℝ) ≤ (x - 1) * Real.exp (-π * x) :=
      mul_nonneg (by linarith) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hxle : x - 1 ≤ Real.exp (x - 1) := by
      have := Real.add_one_le_exp (x - 1)
      linarith
    have hsplit : Real.exp (x - 1) = Real.exp (-1 : ℝ) * Real.exp x := by
      rw [← Real.exp_add]; ring_nf
    have hepos : (0 : ℝ) < Real.exp (-π * x) := Real.exp_pos _
    calc (x - 1) * Real.exp (-π * x)
        ≤ Real.exp (x - 1) * Real.exp (-π * x) :=
          mul_le_mul_of_nonneg_right hxle hepos.le
      _ = Real.exp (-1 : ℝ) * (Real.exp x * Real.exp (-π * x)) := by rw [hsplit]; ring
      _ = Real.exp (-1 : ℝ) * Real.exp (-(π - 1) * x) := by
          rw [← Real.exp_add]; ring_nf

/-- **`∫_1^∞ (x−1) e^{-πx} dx = e^{-π}/π²`.** -/
private lemma integral_sub_one_mul_exp_Ioi :
    ∫ x in Ioi (1 : ℝ), (x - 1) * Real.exp (-π * x) = Real.exp (-π) / π ^ 2 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hne : π ≠ 0 := ne_of_gt hpi
  have hcont : ContinuousWithinAt G (Ici 1) 1 := by
    have hc : Continuous G := by
      have hG : G = fun y : ℝ => ((1 - y) / π - 1 / π ^ 2) * Real.exp (-π * y) := rfl
      rw [hG]
      exact (((continuous_const.sub continuous_id).div_const π).sub continuous_const).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    exact hc.continuousWithinAt
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun x _ => hasDerivAt_G x) integrableOn_sub_one_mul_exp tendsto_G_atTop
  rw [hmain]
  have hG1 : G 1 = -(Real.exp (-π) / π ^ 2) := by
    simp only [G]
    rw [show (1 : ℝ) - 1 = 0 from by ring, show -π * (1 : ℝ) = -π from by ring]
    field_simp
    ring
  rw [hG1]
  ring

/-! ## §2 — The log-weighted dominating function -/

/-- `logDom x = log x · e^{-πx} / (1 − e^{-π})`: the majorant for the
`s`-derivative of the theta integrand on the strip `σ ∈ [0,2]`. -/
def logDom (x : ℝ) : ℝ := Real.log x * Real.exp (-π * x) / (1 - Real.exp (-π))

private lemma integrableOn_log_mul_exp :
    IntegrableOn (fun x : ℝ => Real.log x * Real.exp (-π * x)) (Ioi 1) volume := by
  refine Integrable.mono' integrableOn_sub_one_mul_exp ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    refine Real.continuousOn_log.mono ?_
    intro x hx
    exact ne_of_gt (lt_trans zero_lt_one (mem_Ioi.mp hx))
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx1 : (1 : ℝ) ≤ x := le_of_lt (mem_Ioi.mp hx)
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hepos : (0 : ℝ) < Real.exp (-π * x) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlog hepos.le)]
    exact mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hx0) hepos.le

private lemma logDom_integrableOn : IntegrableOn logDom (Ioi 1) volume := by
  have hrw : logDom
      = fun x : ℝ => (1 - Real.exp (-π))⁻¹ * (Real.log x * Real.exp (-π * x)) := by
    funext x
    simp only [logDom]
    rw [div_eq_mul_inv]
    ring
  rw [hrw]
  exact integrableOn_log_mul_exp.const_mul _

/-- **`∫_1^∞ logDom ≤ e^{-π}/(π²(1 − e^{-π}))`.** -/
private lemma integral_logDom_le :
    ∫ x in Ioi (1 : ℝ), logDom x ≤ Real.exp (-π) / (π ^ 2 * (1 - Real.exp (-π))) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hden := one_sub_exp_neg_pi_pos
  have hrw : logDom
      = fun x : ℝ => (1 - Real.exp (-π))⁻¹ * (Real.log x * Real.exp (-π * x)) := by
    funext x
    simp only [logDom]
    rw [div_eq_mul_inv]
    ring
  rw [hrw, integral_const_mul]
  have hmono : ∫ x in Ioi (1 : ℝ), Real.log x * Real.exp (-π * x)
      ≤ ∫ x in Ioi (1 : ℝ), (x - 1) * Real.exp (-π * x) := by
    refine setIntegral_mono_on integrableOn_log_mul_exp integrableOn_sub_one_mul_exp
      measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one (mem_Ioi.mp hx)
    exact mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos hx0) (Real.exp_pos _).le
  rw [integral_sub_one_mul_exp_Ioi] at hmono
  have hinv_pos : (0 : ℝ) < (1 - Real.exp (-π))⁻¹ := by positivity
  calc (1 - Real.exp (-π))⁻¹ * ∫ x in Ioi (1 : ℝ), Real.log x * Real.exp (-π * x)
      ≤ (1 - Real.exp (-π))⁻¹ * (Real.exp (-π) / π ^ 2) :=
        mul_le_mul_of_nonneg_left hmono hinv_pos.le
    _ = Real.exp (-π) / (π ^ 2 * (1 - Real.exp (-π))) := by field_simp

/-! ## §3 — The theta integrand and its `s`-derivative -/

/-- The theta integrand of `completedRiemannZeta₀`. -/
def Fth (s : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ ((1 - s) / 2 - 1)) * ((omega x : ℝ) : ℂ)

/-- Its derivative in `s`, written so that measurability is immediate. -/
def Fth' (s : ℂ) (x : ℝ) : ℂ :=
  (((x : ℂ) ^ (s / 2 - 1) * ((omega x : ℝ) : ℂ)
      - (x : ℂ) ^ ((1 - s) / 2 - 1) * ((omega x : ℝ) : ℂ))
    * ((Real.log x : ℝ) : ℂ)) * (1 / 2)

/-- `x^w · ω(x)` is integrable on `(1,∞)` for **every** complex exponent `w`,
from `integrableOn_cpow_smul_evenKernel_sub_one`. -/
private lemma integrableOn_cpow_mul_omega (w : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ w * ((omega x : ℝ) : ℂ)) (Ioi 1) volume := by
  have h := (integrableOn_cpow_smul_evenKernel_sub_one w).div_const 2
  refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one (mem_Ioi.mp hx)
  rw [evenKernel_zero_eq hx0]
  simp only [smul_eq_mul]
  push_cast
  ring

private lemma aesm_Fth (s : ℂ) :
    AEStronglyMeasurable (Fth s) (volume.restrict (Ioi 1)) := by
  have hA := (integrableOn_cpow_mul_omega (s / 2 - 1)).aestronglyMeasurable
  have hB := (integrableOn_cpow_mul_omega ((1 - s) / 2 - 1)).aestronglyMeasurable
  have hrw : Fth s = fun x : ℝ => (x : ℂ) ^ (s / 2 - 1) * ((omega x : ℝ) : ℂ)
      + (x : ℂ) ^ ((1 - s) / 2 - 1) * ((omega x : ℝ) : ℂ) := by
    funext x
    simp only [Fth]
    ring
  rw [hrw]
  exact hA.add hB

private lemma aesm_Fth' (s : ℂ) :
    AEStronglyMeasurable (Fth' s) (volume.restrict (Ioi 1)) := by
  have hA := (integrableOn_cpow_mul_omega (s / 2 - 1)).aestronglyMeasurable
  have hB := (integrableOn_cpow_mul_omega ((1 - s) / 2 - 1)).aestronglyMeasurable
  have hlog : AEStronglyMeasurable (fun x : ℝ => ((Real.log x : ℝ) : ℂ))
      (volume.restrict (Ioi 1)) :=
    (Complex.continuous_ofReal.measurable.comp Real.measurable_log).aestronglyMeasurable
  exact ((hA.sub hB).mul hlog).mul_const _

private lemma integrableOn_Fth (s : ℂ) : IntegrableOn (Fth s) (Ioi 1) volume := by
  have hA := integrableOn_cpow_mul_omega (s / 2 - 1)
  have hB := integrableOn_cpow_mul_omega ((1 - s) / 2 - 1)
  have hrw : Fth s = fun x : ℝ => (x : ℂ) ^ (s / 2 - 1) * ((omega x : ℝ) : ℂ)
      + (x : ℂ) ^ ((1 - s) / 2 - 1) * ((omega x : ℝ) : ℂ) := by
    funext x
    simp only [Fth]
    ring
  rw [hrw]
  exact hA.add hB

/-- **`Fth'` really is the `s`-derivative of `Fth`**, for every `x > 0`. -/
private lemma hasDerivAt_Fth {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun r : ℂ => Fth r x) (Fth' s x) s := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hlog : ((Real.log x : ℝ) : ℂ) = Complex.log (x : ℂ) := Complex.ofReal_log hx.le
  have e1 : HasDerivAt (fun r : ℂ => r / 2 - 1) (1 / 2 : ℂ) s := by
    simpa using ((hasDerivAt_id s).div_const 2).sub_const 1
  have d1 : HasDerivAt (fun r : ℂ => (x : ℂ) ^ (r / 2 - 1))
      ((x : ℂ) ^ (s / 2 - 1) * Complex.log (x : ℂ) * (1 / 2)) s :=
    e1.const_cpow (Or.inl hxc)
  have e2 : HasDerivAt (fun r : ℂ => (1 - r) / 2 - 1) (-(1 / 2) : ℂ) s := by
    have hb : HasDerivAt (fun r : ℂ => 1 - r) (-1 : ℂ) s := by
      simpa using (hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)
    have h := (hb.div_const 2).sub_const 1
    simpa [neg_div] using h
  have d2 : HasDerivAt (fun r : ℂ => (x : ℂ) ^ ((1 - r) / 2 - 1))
      ((x : ℂ) ^ ((1 - s) / 2 - 1) * Complex.log (x : ℂ) * (-(1 / 2))) s :=
    e2.const_cpow (Or.inl hxc)
  have dsum := (d1.add d2).mul_const ((omega x : ℝ) : ℂ)
  have hFth : (fun r : ℂ => Fth r x)
      = fun r : ℂ => ((x : ℂ) ^ (r / 2 - 1) + (x : ℂ) ^ ((1 - r) / 2 - 1))
          * ((omega x : ℝ) : ℂ) := rfl
  rw [hFth]
  convert dsum using 1
  simp only [Fth', hlog]
  ring

/-- **Strip bound on the derivative integrand.** For `σ = s.re ∈ [0,2]` and
`x ≥ 1`, `‖Fth' s x‖ ≤ logDom x`. -/
private lemma norm_Fth'_le {s : ℂ} (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2)
    {x : ℝ} (hx : 1 ≤ x) : ‖Fth' s x‖ ≤ logDom x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hden := one_sub_exp_neg_pi_pos
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have homega : 0 ≤ omega x := omega_nonneg _
  have ha : ‖(x : ℂ) ^ (s / 2 - 1)‖ = x ^ (s.re / 2 - 1 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    congr 1
    simp [Complex.sub_re]
  have hb : ‖(x : ℂ) ^ ((1 - s) / 2 - 1)‖ = x ^ ((1 - s.re) / 2 - 1 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    congr 1
    simp [Complex.sub_re, Complex.one_re]
  have h1 : x ^ (s.re / 2 - 1 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have h2 : x ^ ((1 - s.re) / 2 - 1 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have homega_norm : ‖((omega x : ℝ) : ℂ)‖ = omega x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg homega]
  have hdiff : ‖(x : ℂ) ^ (s / 2 - 1) * ((omega x : ℝ) : ℂ)
      - (x : ℂ) ^ ((1 - s) / 2 - 1) * ((omega x : ℝ) : ℂ)‖ ≤ 2 * omega x := by
    calc ‖(x : ℂ) ^ (s / 2 - 1) * ((omega x : ℝ) : ℂ)
            - (x : ℂ) ^ ((1 - s) / 2 - 1) * ((omega x : ℝ) : ℂ)‖
        ≤ ‖(x : ℂ) ^ (s / 2 - 1) * ((omega x : ℝ) : ℂ)‖
            + ‖(x : ℂ) ^ ((1 - s) / 2 - 1) * ((omega x : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = (x ^ (s.re / 2 - 1 : ℝ) + x ^ ((1 - s.re) / 2 - 1 : ℝ)) * omega x := by
          rw [norm_mul, norm_mul, ha, hb, homega_norm]; ring
      _ ≤ 2 * omega x := by nlinarith [homega]
  have hlog_norm : ‖((Real.log x : ℝ) : ℂ)‖ = Real.log x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_ofNat]
  have homega_bd : omega x ≤ Real.exp (-π * x) / (1 - Real.exp (-π)) := by
    have hw := omega_le_geometric hx0
    have h_exp_mono : Real.exp (-π * x) ≤ Real.exp (-π) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hpi]
    have h_den_x_pos : (0 : ℝ) < 1 - Real.exp (-π * x) := by
      linarith [exp_neg_pi_le_eighth, h_exp_mono]
    have h_inv : (1 - Real.exp (-π * x))⁻¹ ≤ (1 - Real.exp (-π))⁻¹ :=
      inv_anti₀ hden (by linarith)
    calc omega x ≤ Real.exp (-π * x) / (1 - Real.exp (-π * x)) := hw
      _ = Real.exp (-π * x) * (1 - Real.exp (-π * x))⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp (-π * x) * (1 - Real.exp (-π))⁻¹ :=
          mul_le_mul_of_nonneg_left h_inv (Real.exp_pos _).le
      _ = Real.exp (-π * x) / (1 - Real.exp (-π)) := (div_eq_mul_inv _ _).symm
  simp only [Fth', norm_mul, hlog_norm, hhalf]
  have hstep : ‖(x : ℂ) ^ (s / 2 - 1) * ((omega x : ℝ) : ℂ)
      - (x : ℂ) ^ ((1 - s) / 2 - 1) * ((omega x : ℝ) : ℂ)‖ * Real.log x * (1 / 2)
      ≤ Real.log x * omega x := by
    have h := mul_le_mul_of_nonneg_right hdiff hlog
    nlinarith [h]
  refine hstep.trans ?_
  simp only [logDom]
  calc Real.log x * omega x
      ≤ Real.log x * (Real.exp (-π * x) * (1 - Real.exp (-π))⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hlog
        rw [← div_eq_mul_inv]
        exact homega_bd
    _ = Real.log x * Real.exp (-π * x) * (1 - Real.exp (-π))⁻¹ := by ring

/-! ## §4 — Differentiation under the integral sign -/

/-- Points of the ball of radius `1/2` about `1 + it` lie in the strip
`σ ∈ [0,2]`. -/
private lemma re_mem_strip {t : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (⟨1, t⟩ : ℂ) (1 / 2)) : 0 ≤ s.re ∧ s.re ≤ 2 := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have h := abs_re_le_norm (s - (⟨1, t⟩ : ℂ))
  have h1 : (s - (⟨1, t⟩ : ℂ)).re = s.re - 1 := by simp [Complex.sub_re]
  rw [h1] at h
  have h2 : |s.re - 1| ≤ 1 / 2 := le_trans h hs.le
  have h3 := abs_le.mp h2
  exact ⟨by linarith [h3.1], by linarith [h3.2]⟩

/-- **`Λ₀` is differentiable at `1 + it` with the log-weighted integral as
its derivative.** -/
theorem hasDerivAt_lambda0_edge (t : ℝ) :
    HasDerivAt completedRiemannZeta₀
      (∫ x in Ioi (1 : ℝ), Fth' (⟨1, t⟩ : ℂ) x) (⟨1, t⟩ : ℂ) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hF_meas : ∀ᶠ s : ℂ in nhds (⟨1, t⟩ : ℂ),
      AEStronglyMeasurable (Fth s) (volume.restrict (Ioi 1)) :=
    Filter.Eventually.of_forall (fun s => aesm_Fth s)
  have h_bound : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      ∀ s ∈ Metric.ball (⟨1, t⟩ : ℂ) (1 / 2), ‖Fth' s x‖ ≤ logDom x := by
    rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    intro s hs
    obtain ⟨h0, h2⟩ := re_mem_strip hs
    exact norm_Fth'_le h0 h2 (le_of_lt (mem_Ioi.mp hx))
  have h_diff : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      ∀ s ∈ Metric.ball (⟨1, t⟩ : ℂ) (1 / 2),
        HasDerivAt (fun r : ℂ => Fth r x) (Fth' s x) s := by
    rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    intro s _
    exact hasDerivAt_Fth (lt_trans zero_lt_one (mem_Ioi.mp hx)) s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hhalf hF_meas (integrableOn_Fth (⟨1, t⟩ : ℂ)) (aesm_Fth' (⟨1, t⟩ : ℂ))
    h_bound logDom_integrableOn h_diff
  have hcongr : (fun s : ℂ => ∫ x in Ioi (1 : ℝ), Fth s x) = completedRiemannZeta₀ := by
    funext s
    exact (completedRiemannZeta₀_eq_theta_integral s).symm
  rw [← hcongr]
  exact key.2

/-! ## §5 — THE BOUND -/

/-- **`‖Λ₀'(1+it)‖ ≤ e^{-π}/(π²(1 − e^{-π}))`**, uniformly in `t`.

This is `1/(2π) ≈ 0.159` times the existing Cauchy-at-radius-1 constant
`2e^{-π}/(π(1 − e^{-π}))`, i.e. **6.28x tighter**. -/
theorem lambda0_prime_abs_le_theta_log (t : ℝ) :
    ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
      ≤ Real.exp (-π) / (π ^ 2 * (1 - Real.exp (-π))) := by
  rw [(hasDerivAt_lambda0_edge t).deriv]
  have h_ae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖Fth' (⟨1, t⟩ : ℂ) x‖ ≤ logDom x := by
    rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    refine norm_Fth'_le ?_ ?_ (le_of_lt (mem_Ioi.mp hx))
    · simp
    · simp
  exact le_trans (norm_integral_le_of_norm_le logDom_integrableOn h_ae) integral_logDom_le

/-- **Rational form: `‖Λ₀'(1+it)‖ ≤ 3/650`.**

From `e^{-π} ≤ 1/23`, `1 − e^{-π} ≥ 22/23` and `π > 157/50`:
`e^{-π}/(π²(1−e^{-π})) ≤ (1/23)/((157/50)²·(22/23)) = 2500/542278 ≈ 0.0046111
 ≤ 3/650 = 0.0046154`. -/
theorem lambda0_prime_abs_le_three_over_650 (t : ℝ) :
    ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 3 / 650 := by
  refine (lambda0_prime_abs_le_theta_log t).trans ?_
  have hpi : (157 : ℝ) / 50 < π := by
    have h := Real.pi_gt_d2
    linarith [show (3.14 : ℝ) = 157 / 50 by norm_num]
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have h_exp := exp_neg_pi_le_one_twentythird
  have h_exp_pos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
  have h_1_sub : (22 : ℝ) / 23 ≤ 1 - Real.exp (-π) :=
    one_sub_exp_neg_pi_ge_twentytwo_twentythirds
  have h_1_sub_pos : (0 : ℝ) < 1 - Real.exp (-π) := by linarith
  have h_prod_pos : (0 : ℝ) < π ^ 2 * (1 - Real.exp (-π)) := by positivity
  rw [div_le_iff₀ h_prod_pos]
  nlinarith [h_exp, h_exp_pos, hpi, hpi_pos, h_1_sub, sq_nonneg (π - 157 / 50)]

/-! ## §6 — Gate-2 with the new constant -/

/-- **Gate-2 numerator inequality out to `|t| ≤ 14`.**

`(1 + 2|t|)·(50/1727) + (t² + |t|)·(3/650) ≤ 2`.

At `|t| = 14` the left side is `0.8396 + 0.9692 = 1.8088`. The old pair
`(50/1727, 50/1727)` failed already at `|t| = 6.94`. -/
theorem gate2_num_bound_le_fourteen {t : ℝ} (ht : |t| ≤ 14) :
    (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (3 / 650) ≤ 2 := by
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  rw [h_t_sq]
  nlinarith [h_abs_nn, ht]

/-- **‖d/ds ξ(1+it)‖ ≤ 1 for `|t| ≤ 14`** — Gate-2, unconditionally, with no
box-local hypothesis and no `K_sum` side condition. -/
theorem norm_deriv_riemannXiEntire_le_one_le_fourteen {t : ℝ} (ht : |t| ≤ 14) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  rw [deriv_riemannXiEntire_at t, norm_div]
  have h2_norm : ‖(2 : ℂ)‖ = 2 := by
    show ‖((2 : ℕ) : ℂ)‖ = 2
    rw [Complex.norm_natCast]
    norm_num
  rw [h2_norm]
  have h_L := lambda0_abs_le_fifty_over_1727 t
  have h_Lp := lambda0_prime_abs_le_three_over_650 t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_num : ‖(2 * (⟨1, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
      + (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
          * deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hm1 : ‖2 * (⟨1, t⟩ : ℂ) - 1‖ * ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
        ≤ (1 + 2 * |t|) * (50 / 1727) :=
      mul_le_mul h_2s h_L (norm_nonneg _) (by linarith)
    have hm2 : ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖
        * ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
        ≤ (t ^ 2 + |t|) * (3 / 650) := by
      refine mul_le_mul h_ss h_Lp (norm_nonneg _) ?_
      nlinarith [sq_nonneg t, h_abs_nn]
    linarith [gate2_num_bound_le_fourteen ht]
  linarith

/-! ## §7 — The c = 55/8 pilot hbound, unconditionally

`Gate2BoxLocalC55_8_2026_10_19.lean` (`b9d6d27e`) proves this box's hbound
**conditional on `K_sum ≤ 1/16`**, where
`K_sum = ∫|F₊″| + ∫|F₋″|`. That hypothesis is **false**: by
`boundary_const_eq_neg_quarter` (`223354b9`) together with `F₊″, F₋″ ≥ 0`,

  `K_sum = −(F₊'(0) + F₋'(0)) = −(ω(1)/2 + 2ω'(1)) = 1/4`

exactly — four times the hypothesis. Worse, the conclusion there needs
`K_sum ≤ 0.0782`, so no sharper estimate of `K_sum` can rescue it: at
`t = 111/16` the sharp bound `(1 + 4·(1/4))/t² = 2/t² = 0.0416` is *larger*
than the uniform `50/1727 = 0.0290` it was meant to replace.

The theorems below carry **no hypothesis**. -/

/-- **|d/dt (Re ξ)| ≤ 1 for `|t| ≤ 14`.** Chain-rule descent. -/
theorem abs_deriv_edgeRe_le_one_le_fourteen {t : ℝ} (ht : |t| ≤ 14) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le :
      |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
        ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ := abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  linarith [norm_deriv_riemannXiEntire_le_one_le_fourteen ht]

/-- **THE c = 55/8 PILOT HBOUND, UNCONDITIONAL** — the Gate-2 side of
`R1_box_centered_of_lb (L := 1)` at centre `55/8`, radius `1/16`.

This is the drop-in replacement for
`Gate2BoxLocalC55_8_20261019.pilot_r1_hbound_c55_8_r1_16`, which cannot be
discharged. -/
theorem pilot_r1_hbound_c55_8_r1_16 :
    ∀ x ∈ Set.Icc ((109 : ℝ) / 16) (111 / 16), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| = x := abs_of_pos (by linarith [hx.1])
  refine abs_deriv_edgeRe_le_one_le_fourteen ?_
  rw [hx_abs]
  linarith [hx.2]

/-- **Every box centre from `55/8` up to `13` passes Gate-2**, at radius
`1/16`: for `c ∈ [55/8, 13]` the edge `|t| ≤ c + 1/16 ≤ 13.0625 ≤ 14`. -/
theorem pilot_r1_hbound_box {c : ℝ} (hc_lo : (55 : ℝ) / 8 ≤ c) (hc_hi : c ≤ 13) :
    ∀ x ∈ Set.Icc (c - 1 / 16) (c + 1 / 16), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_pos : (0 : ℝ) < x := by linarith [hx.1]
  have hx_abs : |x| = x := abs_of_pos hx_pos
  refine abs_deriv_edgeRe_le_one_le_fourteen ?_
  rw [hx_abs]
  linarith [hx.2]

end

end Lambda0PrimeThetaLogBound20261019
end PrincipiaTractalis

/-! ## Axiom check -/

#print axioms PrincipiaTractalis.Lambda0PrimeThetaLogBound20261019.hasDerivAt_lambda0_edge
#print axioms PrincipiaTractalis.Lambda0PrimeThetaLogBound20261019.lambda0_prime_abs_le_theta_log
#print axioms PrincipiaTractalis.Lambda0PrimeThetaLogBound20261019.lambda0_prime_abs_le_three_over_650
#print axioms PrincipiaTractalis.Lambda0PrimeThetaLogBound20261019.gate2_num_bound_le_fourteen
#print axioms PrincipiaTractalis.Lambda0PrimeThetaLogBound20261019.norm_deriv_riemannXiEntire_le_one_le_fourteen
#print axioms PrincipiaTractalis.Lambda0PrimeThetaLogBound20261019.abs_deriv_edgeRe_le_one_le_fourteen
#print axioms PrincipiaTractalis.Lambda0PrimeThetaLogBound20261019.pilot_r1_hbound_c55_8_r1_16
#print axioms PrincipiaTractalis.Lambda0PrimeThetaLogBound20261019.pilot_r1_hbound_box
