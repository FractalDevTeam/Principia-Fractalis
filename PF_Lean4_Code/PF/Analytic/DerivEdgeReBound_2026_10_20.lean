/-
# PF.Analytic.DerivEdgeReBound_2026_10_20

**The two exact `F″` integral constants, and the second-derivative
nonnegativity they rest on.**

  `F₊″ ≥ 0` and `F₋″ ≥ 0` on `u ≥ 0`
  `∫₀^∞ (F₊″ + F₋″) = 1/4`            (the `K_sum` constant)
  `∫₀^∞ u·F₊″ = ∫₀^∞ u·F₋″ = ω(1)`

## Why these are the constants that matter

Differentiating the Tier-3 sharp identity
`Λ₀(1+it) = 1/t² − (4/t²)(I₊+I₋)` gives, with `S(t) = I₊ + I₋`,

  `Re ξ(1+it) = 2·Re S + (2/t)·Im S`
  `d/dt Re ξ(1+it) = 2·Re S' + (2/t)·Im S' − (2/t²)·Im S`

and `|S| ≤ ∫(F₊″+F₋″)`, `|S'| ≤ ½∫u(F₊″+F₋″)`, so

  `|deriv edgeRe t| ≤ 2ω(1)·(1 + 1/t) + 1/(2t²)`.

Measured, that is `0.096–0.110` — against the **best possible** triangle bound
on `ξ' = ((2s−1)Λ₀ + s(s−1)Λ₀')/2`, which is flat at `0.157–0.173` because
those two terms cancel (2.5× at `t = 6.75` rising to 36× at `t = 13`). The
Tier-3 form cancels the `O(1)` parts *analytically* instead: measured
cancellation `1.0×` up to `t = 11` and `1.2×` at `t = 13`, versus `397×` for
the naive `(1 − t²R − tI)/2` form. That 124× conditioning difference is why
this representation is the one to enclose.

Consequence for the march, measured: `L = 1` (what Gate-2 proves today) needs
**193** boxes to cover `[6.75, 13]` and caps `r = 1/16` at `c = 9.046`;
`L₀ = 2ω(1)(1+1/c) + 1/(2c²)` needs **19** and carries `r = 1/16` to
`c = 12.30`.

## The two integrals

Both are exact, not estimates. With `F₊″, F₋″ ≥ 0`:

* `∫₀^∞ F″ = −F′(0)` by FTC, and `F₊′(0) + F₋′(0) = ω(1)/2 + 2ω'(1) = −1/4`
  (`boundary_const_eq_neg_quarter`, `223354b9`). So the sum is `1/4` — which
  also **closes the standing `K_sum` OPEN**: `Gate2BoxLocalC55_8_2026_10_19`
  assumes `K_sum ≤ 1/16`, and `K_sum` is exactly `1/4`.
* `∫₀^∞ u·F″ = F(0)` by FTC on `u·F′ − F`, and `F₊(0) = F₋(0) = ω(1)`.

## Nonnegativity, termwise

`F₋″ = x(x·ω″ + ω′)` and `F₊″ = e^{u/2}[¼ω + x(x·ω″ + 2ω′)]` with `x = exp u`,
so both reduce to `x·ω″(x) + k·ω′(x) ≥ 0` for `k ∈ {1, 2}`. Termwise that is
`π n²(π n² x − k)·exp(−π n² x) ≥ 0`, which needs only `π n² x ≥ k`; at the
worst point `n = 1`, `x = 1` it is `π ≥ k`, and `π > 2`. One lemma covers both.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-20.
-/

import PF.Analytic.ThetaBoundaryConstant_2026_10_19
import PF.Analytic.OmegaDerivGeometricBounds_2026_10_18
import PF.Analytic.FMinusSecondIBP_2026_10_18

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace PrincipiaTractalis
namespace DerivEdgeReBound20261020

open Real MeasureTheory Set Filter Topology
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.OmegaDerivGeometricBounds20261018
open PrincipiaTractalis.FPlusSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondIBPRows20261018
open PrincipiaTractalis.FMinusSecondIBP20261018
open PrincipiaTractalis.OmegaDerivativeBounds20261015
open PrincipiaTractalis.Lambda0IBPIdentity20261015
open PrincipiaTractalis.ThetaBoundaryConstant20261019
open scoped Real

noncomputable section

/-! ## §1 — Summability of the `ω″` family on `x ≥ 1` -/

/-- The `ω″` terms are summable for `x > 0`. Same comparison
`omega''_le` uses internally. -/
lemma summable_omega''_term {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := by
  have hδ : (0 : ℝ) < x / 2 := by positivity
  have hlt : x / 2 < x := by linarith
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_omega'_term_deriv_bound hδ)
  have h_mono : Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)
      ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * (x / 2)) := by
    apply Real.exp_le_exp.mpr
    have hterm_nn : (0 : ℝ) ≤ π * ((n : ℝ) + 1) ^ 2 := by positivity
    nlinarith [hterm_nn, hlt]
  exact mul_le_mul_of_nonneg_left h_mono (by positivity)

/-! ## §2 — The combined nonnegativity `x·ω″ + k·ω′ ≥ 0` -/

/-- **`x·ω″(x) + k·ω′(x) ≥ 0` for `x ≥ 1` and `0 ≤ k ≤ 2`.**

Termwise the summand is `π n²(π n² x − k)·exp(−π n² x)`, nonnegative as soon as
`π n² x ≥ k`; the worst case `n = 1`, `x = 1` gives `π ≥ k`, and `π > 2 ≥ k`.
`k = 1` yields `F₋″ ≥ 0` and `k = 2` yields `F₊″ ≥ 0`. -/
theorem omega_combo_nonneg {x k : ℝ} (hx : 1 ≤ x) (_hk0 : 0 ≤ k) (hk2 : k ≤ 2) :
    0 ≤ x * omega'' x + k * omega' x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ2 : (2 : ℝ) < π := by
    have := Real.pi_gt_three; linarith
  -- the two summable families
  have hs2 := summable_omega''_term hx0
  have hs1 := summable_omega'_term hx0
  have hs2x : Summable fun n : ℕ =>
      x * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)) :=
    hs2.mul_left x
  have hs1k : Summable fun n : ℕ =>
      k * (-(π * ((n : ℝ) + 1) ^ 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)) :=
    hs1.mul_left k
  -- pull the scalars inside and merge
  have hx_eq : x * omega'' x
      = ∑' n : ℕ, x * ((π * ((n : ℝ) + 1) ^ 2) ^ 2
          * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)) := by
    rw [omega'']
    exact (tsum_mul_left).symm
  have hk_eq : k * omega' x
      = ∑' n : ℕ, k * (-(π * ((n : ℝ) + 1) ^ 2)
          * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x)) := by
    rw [omega']
    exact (tsum_mul_left).symm
  rw [hx_eq, hk_eq, ← hs2x.tsum_add hs1k]
  refine tsum_nonneg (fun n => ?_)
  -- termwise: π(n+1)²(π(n+1)²x − k)·exp(−π(n+1)²x) ≥ 0
  set A : ℝ := π * ((n : ℝ) + 1) ^ 2 with hA
  have hA_ge : π ≤ A := by
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    calc π = π * 1 := by ring
      _ ≤ π * ((n : ℝ) + 1) ^ 2 := by exact mul_le_mul_of_nonneg_left h1 hπ.le
  have hA_pos : (0 : ℝ) < A := lt_of_lt_of_le hπ hA_ge
  have hAx_ge : k ≤ A * x := by
    calc k ≤ 2 := hk2
      _ ≤ π := hπ2.le
      _ ≤ A := hA_ge
      _ = A * 1 := by ring
      _ ≤ A * x := mul_le_mul_of_nonneg_left hx hA_pos.le
  have hexp : (0 : ℝ) < Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := Real.exp_pos _
  have hkey : x * (A ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x))
      + k * (-A * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x))
      = A * (A * x - k) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) := by ring
  rw [hkey]
  have : (0 : ℝ) ≤ A * (A * x - k) := by
    apply mul_nonneg hA_pos.le
    linarith
  exact mul_nonneg this hexp.le

/-! ## §3 — `F₊″ ≥ 0` and `F₋″ ≥ 0` -/

/-- **`F₋″ ≥ 0` on `u ≥ 0`.** `F₋″ = x·(x·ω″ + ω′)` with `x = exp u`. -/
theorem F_minus''_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ F_minus'' u := by
  have hx1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  have hxpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hcombo := omega_combo_nonneg (x := Real.exp u) (k := 1) hx1 (by norm_num) (by norm_num)
  have heq : F_minus'' u
      = Real.exp u * (Real.exp u * omega'' (Real.exp u) + 1 * omega' (Real.exp u)) := by
    rw [F_minus'']; ring
  rw [heq]
  exact mul_nonneg hxpos.le hcombo

/-- **`F₊″ ≥ 0` on `u ≥ 0`.**
`F₊″ = exp(u/2)·[¼·ω + x·(x·ω″ + 2·ω′)]`; the first summand is nonnegative and
the second is `omega_combo_nonneg` at `k = 2`. -/
theorem F_plus''_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ F_plus'' u := by
  have hx1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  have hxpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hhalf : (0 : ℝ) < Real.exp (u / 2) := Real.exp_pos _
  have hcombo := omega_combo_nonneg (x := Real.exp u) (k := 2) hx1 (by norm_num) (by norm_num)
  have homega : (0 : ℝ) ≤ omega (Real.exp u) := omega_nonneg _
  have heq : F_plus'' u
      = Real.exp (u / 2)
          * (1 / 4 * omega (Real.exp u)
              + Real.exp u * (Real.exp u * omega'' (Real.exp u)
                  + 2 * omega' (Real.exp u))) := by
    rw [F_plus'']; ring
  rw [heq]
  refine mul_nonneg hhalf.le ?_
  have h1 : (0 : ℝ) ≤ 1 / 4 * omega (Real.exp u) := by positivity
  have h2 : (0 : ℝ) ≤ Real.exp u * (Real.exp u * omega'' (Real.exp u)
      + 2 * omega' (Real.exp u)) := mul_nonneg hxpos.le hcombo
  linarith

/-- `|F₊″| = F₊″` on `u ≥ 0`. -/
theorem abs_F_plus''_eq {u : ℝ} (hu : 0 ≤ u) : |F_plus'' u| = F_plus'' u :=
  abs_of_nonneg (F_plus''_nonneg hu)

/-- `|F₋″| = F₋″` on `u ≥ 0`. -/
theorem abs_F_minus''_eq {u : ℝ} (hu : 0 ≤ u) : |F_minus'' u| = F_minus'' u :=
  abs_of_nonneg (F_minus''_nonneg hu)

/-! ## §4 — `∫₀^∞ F″` by FTC, and `K_sum = 1/4` -/

/-- `∫₀^∞ F₊″ = −(ω(1)/2 + ω'(1))`, by FTC on `deriv F_plus`. -/
theorem integral_F_plus''_eq :
    ∫ u in Ioi (0 : ℝ), F_plus'' u = -(omega 1 / 2 + omega' 1) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    continuousWithinAt_deriv_F_plus_zero
    (fun x hx => hasDerivAt_deriv_F_plus x hx)
    integrableOn_deriv_deriv_F_plus
    tendsto_deriv_F_plus_atTop_zero
  rw [deriv_F_plus_zero] at h
  have hfun : (fun u => deriv (deriv F_plus) u) = F_plus'' := by
    funext u
    rw [deriv_F_plus_eq_F_plus', deriv_F_plus'_eq_F_plus'']
  rw [hfun] at h
  rw [h]
  ring

/-- `∫₀^∞ F₋″ = −ω'(1)`, by FTC on `deriv F_minus`. -/
theorem integral_F_minus''_eq :
    ∫ u in Ioi (0 : ℝ), F_minus'' u = -(omega' 1) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    continuousWithinAt_deriv_F_minus_zero
    (fun x hx => hasDerivAt_deriv_F_minus x hx)
    integrableOn_deriv_deriv_F_minus
    tendsto_deriv_F_minus_atTop_zero
  rw [deriv_F_minus_zero] at h
  have hfun : (fun u => deriv (deriv F_minus) u) = F_minus'' := by
    funext u
    rw [deriv_F_minus_eq_F_minus', deriv_F_minus'_eq_F_minus'']
  rw [hfun] at h
  rw [h]
  ring

/-- **★ `K_sum = 1/4` ★** — `∫₀^∞ |F₊″| + ∫₀^∞ |F₋″| = 1/4`.

This closes the hypothesis `Gate2BoxLocalC55_8_2026_10_19` assumes
(`K_sum ≤ 1/16`): the true value is `1/4`, four times that bound. -/
theorem K_sum_eq_quarter :
    (∫ u in Ioi (0 : ℝ), |F_plus'' u|) + (∫ u in Ioi (0 : ℝ), |F_minus'' u|)
      = 1 / 4 := by
  have hp : (∫ u in Ioi (0 : ℝ), |F_plus'' u|) = ∫ u in Ioi (0 : ℝ), F_plus'' u := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    exact abs_F_plus''_eq (le_of_lt (mem_Ioi.mp hu))
  have hm : (∫ u in Ioi (0 : ℝ), |F_minus'' u|) = ∫ u in Ioi (0 : ℝ), F_minus'' u := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    exact abs_F_minus''_eq (le_of_lt (mem_Ioi.mp hu))
  rw [hp, hm, integral_F_plus''_eq, integral_F_minus''_eq]
  have hb := boundary_const_eq_neg_quarter
  linarith

/-! ## §5 — The weighted integrals `∫₀^∞ u·F″ = ω(1)`

The only wrinkle is keeping every majorant a bare exponential. `u ≤ 5·exp(u/5)`
(from `t ≤ exp t`) converts `u·exp(u·c)` into `5·exp(u·(c + 1/5))`, and for
both `c = 5/2 − π` and `c = 2 − π` the shifted exponent is still negative
(`27/10 − π < 0`, `11/5 − π < 0`). So no polynomial-times-exponential
integrability or limit lemma is needed anywhere below. -/

/-- `u ≤ 5·exp(u/5)` for `0 ≤ u`. -/
private lemma le_five_mul_exp_fifth {u : ℝ} (hu : 0 ≤ u) : u ≤ 5 * Real.exp (u / 5) := by
  have h : u / 5 ≤ Real.exp (u / 5) := by
    have := Real.add_one_le_exp (u / 5)
    linarith
  linarith

/-- `u·exp(u·c) → 0` as `u → ∞` whenever `c + 1/5 < 0`. -/
private lemma tendsto_mul_exp_atTop_zero {c : ℝ} (hc : c + 1 / 5 < 0) :
    Tendsto (fun u : ℝ => u * Real.exp (u * c)) atTop (nhds 0) := by
  have hmaj : Tendsto (fun u : ℝ => 5 * Real.exp (u * (c + 1 / 5))) atTop (nhds 0) := by
    have h := tendsto_exp_mul_const_atTop_zero hc
    have h5 := h.const_mul (5 : ℝ)
    simpa using h5
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ u * Real.exp (u * c))]
  have h1 := le_five_mul_exp_fifth hu
  have hpos : (0 : ℝ) < Real.exp (u * c) := Real.exp_pos _
  calc u * Real.exp (u * c) ≤ 5 * Real.exp (u / 5) * Real.exp (u * c) :=
        mul_le_mul_of_nonneg_right h1 hpos.le
    _ = 5 * Real.exp (u * (c + 1 / 5)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- `u·exp(u·c)` is integrable on `Ioi 0` whenever `c + 1/5 < 0`. -/
private lemma integrableOn_mul_exp {c : ℝ} (hc : c + 1 / 5 < 0) :
    IntegrableOn (fun u : ℝ => u * Real.exp (u * c)) (Ioi 0) volume := by
  have hb : (0 : ℝ) < -(c + 1 / 5) := by linarith
  have hg : IntegrableOn (fun u : ℝ => 5 * Real.exp (-(-(c + 1 / 5)) * u))
      (Ioi 0) volume := (exp_neg_integrableOn_Ioi 0 hb).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact ((continuous_id.mul (Real.continuous_exp.comp
      (continuous_id.mul continuous_const))).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (mem_Ioi.mp hu)
    have hpos : (0 : ℝ) < Real.exp (u * c) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ u * Real.exp (u * c))]
    have h1 := le_five_mul_exp_fifth hu0
    calc u * Real.exp (u * c) ≤ 5 * Real.exp (u / 5) * Real.exp (u * c) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = 5 * Real.exp (-(-(c + 1 / 5)) * u) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- `u·F₊″` is integrable on `Ioi 0`. -/
lemma integrableOn_mul_F_plus'' :
    IntegrableOn (fun u : ℝ => u * F_plus'' u) (Ioi 0) volume := by
  have hc : (5 / 2 - π : ℝ) + 1 / 5 < 0 := by linarith [Real.pi_gt_three]
  have hg : IntegrableOn (fun u : ℝ => (81 * Real.exp (-π))
      * (u * Real.exp (u * (5 / 2 - π)))) (Ioi 0) volume :=
    (integrableOn_mul_exp hc).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (continuous_id.aestronglyMeasurable.mul
      (integrableOn_deriv_deriv_F_plus.congr_fun
        (fun u _ => by rw [deriv_F_plus_eq_F_plus', deriv_F_plus'_eq_F_plus''])
        measurableSet_Ioi).aestronglyMeasurable)
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (mem_Ioi.mp hu)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0]
    have hb := abs_F_plus''_le hu0
    have := mul_le_mul_of_nonneg_left hb hu0
    calc u * |F_plus'' u| ≤ u * (81 * Real.exp (-π) * Real.exp (u * (5 / 2 - π))) := this
      _ = 81 * Real.exp (-π) * (u * Real.exp (u * (5 / 2 - π))) := by ring

/-- `u·F₋″` is integrable on `Ioi 0`. -/
lemma integrableOn_mul_F_minus'' :
    IntegrableOn (fun u : ℝ => u * F_minus'' u) (Ioi 0) volume := by
  have hc : (2 - π : ℝ) + 1 / 5 < 0 := by linarith [Real.pi_gt_three]
  have hg : IntegrableOn (fun u : ℝ => (72 * Real.exp (-π))
      * (u * Real.exp (u * (2 - π)))) (Ioi 0) volume :=
    (integrableOn_mul_exp hc).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (continuous_id.aestronglyMeasurable.mul
      (integrableOn_deriv_deriv_F_minus.congr_fun
        (fun u _ => by rw [deriv_F_minus_eq_F_minus', deriv_F_minus'_eq_F_minus''])
        measurableSet_Ioi).aestronglyMeasurable)
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (mem_Ioi.mp hu)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0]
    have hb := abs_F_minus''_le hu0
    have := mul_le_mul_of_nonneg_left hb hu0
    calc u * |F_minus'' u| ≤ u * (72 * Real.exp (-π) * Real.exp (u * (2 - π))) := this
      _ = 72 * Real.exp (-π) * (u * Real.exp (u * (2 - π))) := by ring

/-! ## §6 — `∫₀^∞ u·F″ = F(0) = ω(1)`

FTC with antiderivative `G(u) = u·F′(u) − F(u)`, whose derivative is
`F′ + u·F″ − F′ = u·F″`. At `0` it is `−F(0)`; at `∞` it vanishes because
`u·F′(u) → 0` (the `u ≤ 5exp(u/5)` trick again) and `F(u) → 0`. -/

private def G_plus (u : ℝ) : ℝ := u * F_plus' u - F_plus u
private def G_minus (u : ℝ) : ℝ := u * F_minus' u - F_minus u

private lemma hasDerivAt_F_plus'_at {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) :
    HasDerivAt F_plus' (F_plus'' u) u := by
  have h := hasDerivAt_deriv_F_plus u hu
  rw [deriv_F_plus_eq_F_plus'] at h
  have he : deriv F_plus' u = F_plus'' u := by rw [deriv_F_plus'_eq_F_plus'']
  rw [he] at h
  exact h

private lemma hasDerivAt_F_minus'_at {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) :
    HasDerivAt F_minus' (F_minus'' u) u := by
  have h := hasDerivAt_deriv_F_minus u hu
  rw [deriv_F_minus_eq_F_minus'] at h
  have he : deriv F_minus' u = F_minus'' u := by rw [deriv_F_minus'_eq_F_minus'']
  rw [he] at h
  exact h

private lemma hasDerivAt_G_plus {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) :
    HasDerivAt G_plus (u * F_plus'' u) u := by
  have h2 : HasDerivAt F_plus (F_plus' u) u := by
    have hd := F_plus_hasDerivAt u
    rw [F_plus']
    convert hd using 1
    ring
  have h := ((hasDerivAt_id u).mul (hasDerivAt_F_plus'_at hu)).sub h2
  simp only [id_eq] at h
  have hval : 1 * F_plus' u + u * F_plus'' u - F_plus' u = u * F_plus'' u := by ring
  rw [hval] at h
  exact h

private lemma hasDerivAt_G_minus {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) :
    HasDerivAt G_minus (u * F_minus'' u) u := by
  have h2 : HasDerivAt F_minus (F_minus' u) u := by
    have hd := F_minus_hasDerivAt u
    rw [F_minus']
    convert hd using 1
  have h := ((hasDerivAt_id u).mul (hasDerivAt_F_minus'_at hu)).sub h2
  simp only [id_eq] at h
  have hval : 1 * F_minus' u + u * F_minus'' u - F_minus' u = u * F_minus'' u := by ring
  rw [hval] at h
  exact h

private lemma tendsto_G_plus_atTop : Tendsto G_plus atTop (nhds 0) := by
  have hc : (3 / 2 - π : ℝ) + 1 / 5 < 0 := by linarith [Real.pi_gt_three]
  have hd : (1 / 2 - π : ℝ) < 0 := by linarith [Real.pi_gt_three]
  have h1 : Tendsto (fun u : ℝ => u * F_plus' u) atTop (nhds 0) := by
    have hmaj : Tendsto (fun u : ℝ => (9 * Real.exp (-π))
        * (u * Real.exp (u * (3 / 2 - π)))) atTop (nhds 0) := by
      have h := (tendsto_mul_exp_atTop_zero hc).const_mul (9 * Real.exp (-π))
      simpa using h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu]
    have hstep := mul_le_mul_of_nonneg_left (abs_F_plus'_le hu) hu
    calc u * |F_plus' u| ≤ u * (9 * Real.exp (-π) * Real.exp (u * (3 / 2 - π))) := hstep
      _ = 9 * Real.exp (-π) * (u * Real.exp (u * (3 / 2 - π))) := by ring
  have h2 : Tendsto F_plus atTop (nhds 0) := by
    have hmaj : Tendsto (fun u : ℝ => (23 / 22 * Real.exp (-π))
        * Real.exp (u * (1 / 2 - π))) atTop (nhds 0) := by
      have h := (tendsto_exp_mul_const_atTop_zero hd).const_mul (23 / 22 * Real.exp (-π))
      simpa using h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (F_plus_nonneg u)]
    have hb := F_plus_le_exp_bound hu
    linarith [hb]
  have hsub := h1.sub h2
  rw [sub_zero] at hsub
  exact hsub

private lemma tendsto_G_minus_atTop : Tendsto G_minus atTop (nhds 0) := by
  have hc : (1 - π : ℝ) + 1 / 5 < 0 := by linarith [Real.pi_gt_three]
  have hd : (-π : ℝ) < 0 := by linarith [Real.pi_gt_three]
  have h1 : Tendsto (fun u : ℝ => u * F_minus' u) atTop (nhds 0) := by
    have hmaj : Tendsto (fun u : ℝ => (8 * Real.exp (-π))
        * (u * Real.exp (u * (1 - π)))) atTop (nhds 0) := by
      have h := (tendsto_mul_exp_atTop_zero hc).const_mul (8 * Real.exp (-π))
      simpa using h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu]
    have hstep := mul_le_mul_of_nonneg_left (abs_F_minus'_le hu) hu
    calc u * |F_minus' u|
        ≤ u * (8 * Real.exp (-π) * Real.exp (u * (1 - π))) := hstep
      _ = 8 * Real.exp (-π) * (u * Real.exp (u * (1 - π))) := by ring
  have h2 : Tendsto F_minus atTop (nhds 0) := by
    have hmaj : Tendsto (fun u : ℝ => (23 / 22 : ℝ) * Real.exp (u * (-π)))
        atTop (nhds 0) := by
      have h := (tendsto_exp_mul_const_atTop_zero hd).const_mul (23 / 22 : ℝ)
      simpa using h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (F_minus_nonneg u)]
    have hb := F_minus_le_exp_neg_pi_mul hu
    have hcomm : Real.exp (-π * u) = Real.exp (u * (-π)) := by rw [mul_comm]
    calc F_minus u ≤ 23 / 22 * Real.exp (-π * u) := hb
      _ = 23 / 22 * Real.exp (u * (-π)) := by rw [hcomm]
  have hsub := h1.sub h2
  rw [sub_zero] at hsub
  exact hsub

private lemma continuousWithinAt_G_plus_zero : ContinuousWithinAt G_plus (Ici 0) 0 := by
  have hF' : ContinuousWithinAt F_plus' (Ici 0) 0 := by
    have h := continuousWithinAt_deriv_F_plus_zero
    rwa [deriv_F_plus_eq_F_plus'] at h
  have hF : ContinuousWithinAt F_plus (Ici 0) 0 :=
    ((F_plus_hasDerivAt 0).continuousAt).continuousWithinAt
  exact (continuousWithinAt_id.mul hF').sub hF

private lemma continuousWithinAt_G_minus_zero : ContinuousWithinAt G_minus (Ici 0) 0 := by
  have hF' : ContinuousWithinAt F_minus' (Ici 0) 0 := by
    have h := continuousWithinAt_deriv_F_minus_zero
    rwa [deriv_F_minus_eq_F_minus'] at h
  have hF : ContinuousWithinAt F_minus (Ici 0) 0 :=
    ((F_minus_hasDerivAt 0).continuousAt).continuousWithinAt
  exact (continuousWithinAt_id.mul hF').sub hF

/-- **★ `∫₀^∞ u·F₊″ = ω(1)` ★** -/
theorem integral_mul_F_plus''_eq :
    ∫ u in Ioi (0 : ℝ), u * F_plus'' u = omega 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    continuousWithinAt_G_plus_zero
    (fun x hx => hasDerivAt_G_plus hx)
    integrableOn_mul_F_plus''
    tendsto_G_plus_atTop
  rw [h]
  have hG0 : G_plus 0 = -(omega 1) := by
    rw [G_plus, F_plus_zero]
    ring
  rw [hG0]
  ring

/-- **★ `∫₀^∞ u·F₋″ = ω(1)` ★** -/
theorem integral_mul_F_minus''_eq :
    ∫ u in Ioi (0 : ℝ), u * F_minus'' u = omega 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    continuousWithinAt_G_minus_zero
    (fun x hx => hasDerivAt_G_minus hx)
    integrableOn_mul_F_minus''
    tendsto_G_minus_atTop
  rw [h]
  have hG0 : G_minus 0 = -(omega 1) := by
    rw [G_minus, F_minus_zero]
    ring
  rw [hG0]
  ring

/-- **★ The weighted constant: `∫₀^∞ u·(|F₊″| + |F₋″|) = 2·ω(1)` ★**

This is the constant that controls `|S′|` in
`d/dt Re ξ(1+it) = 2·Re S′ + (2/t)·Im S′ − (2/t²)·Im S`. -/
theorem weighted_K_sum_eq :
    (∫ u in Ioi (0 : ℝ), u * |F_plus'' u|)
      + (∫ u in Ioi (0 : ℝ), u * |F_minus'' u|) = 2 * omega 1 := by
  have hp : (∫ u in Ioi (0 : ℝ), u * |F_plus'' u|)
      = ∫ u in Ioi (0 : ℝ), u * F_plus'' u := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    rw [abs_F_plus''_eq (le_of_lt (mem_Ioi.mp hu))]
  have hm : (∫ u in Ioi (0 : ℝ), u * |F_minus'' u|)
      = ∫ u in Ioi (0 : ℝ), u * F_minus'' u := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    rw [abs_F_minus''_eq (le_of_lt (mem_Ioi.mp hu))]
  rw [hp, hm, integral_mul_F_plus''_eq, integral_mul_F_minus''_eq]
  ring

end

end DerivEdgeReBound20261020
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.summable_omega''_term
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.omega_combo_nonneg
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.F_minus''_nonneg
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.F_plus''_nonneg
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.integral_F_plus''_eq
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.integral_F_minus''_eq
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.K_sum_eq_quarter
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.integrableOn_mul_F_plus''
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.integrableOn_mul_F_minus''
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.integral_mul_F_plus''_eq
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.integral_mul_F_minus''_eq
#print axioms PrincipiaTractalis.DerivEdgeReBound20261020.weighted_K_sum_eq
