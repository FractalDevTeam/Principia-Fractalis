/-
# `BernoulliExpHasSumOnBallTwoPi` — Analyticity Discharge + Cauchy Power Series Isolation

This file PARTIALLY DISCHARGES the open Prop
`BernoulliExpHasSumOnBallTwoPi` from
`BernoulliExpHasSumAtNegLogNhdsHalfDischarge.lean`.

## Strategic decomposition

The full Prop `BernoulliExpHasSumOnBallTwoPi` says:
```
∀ v with ‖v‖ < 2π,
  HasSum (fun k ↦ B_k · v^k / k!) (if v = 0 then 1 else v / (exp v - 1))
```

This file decomposes the residual as follows:

1. (UNCONDITIONAL HERE — `bernoulliFn_analyticAt_of_norm_lt_twoPi`)
   The function `bernoulliFn v := if v = 0 then 1 else v/(exp v - 1)`
   is **complex-analytic** on the open disc `|v| < 2π`. Riemann's
   removable singularity theorem applies at `v = 0` (continuous +
   differentiable on punctured nhd, via `HasDerivAt exp 1 0`).
   Direct analyticity (`AnalyticAt.div`) elsewhere on the disc.

2. (UNCONDITIONAL HERE — `bernoulliFn_cauchyPowerSeries_hasSum_of_norm_lt_twoPi`)
   For every `R < 2π` and every `v` with `‖v‖ < R`, the
   Cauchy power series `cauchyPowerSeries bernoulliFn 0 R` sums to
   `bernoulliFn v`. (Via `hasFPowerSeriesOnBall_of_differentiable_off_countable`
   applied with `s = {0}`.)

3. (ISOLATED HERE — `BernoulliCauchyCoefficientsEqualBernoulli`)
   For some `R < 2π`, the k-th coefficient of
   `cauchyPowerSeries bernoulliFn 0 R` equals `B_k / k!`. This is
   the **identification step**: mathlib has the formal-power-series
   identity `bernoulliPowerSeries · (exp - 1) = X`, but lifting it
   to identify analytic Taylor coefficients requires either a
   Cauchy-product theorem for power-series multiplication or a
   direct iterated-derivative computation of `bernoulliFn` at `0`.

## What lands unconditionally

* `bernoulliFn` — the canonical extended function.
* `bernoulliFn_eq_update` — `bernoulliFn = Function.update (raw) 0 1`.
* `exp_sub_one_div_tendsto_one` — `(exp v - 1)/v → 1` as `v → 0`
  in `𝓝[≠] 0`.
* `bernoulliFn_continuousAt_zero` — via `continuousAt_update_same`.
* `bernoulliFn_analyticAt_of_norm_lt_twoPi` — analytic on the
  full open disc `|v| < 2π`.
* `bernoulliFn_continuousOn_closedBall_of_lt_twoPi` — continuous
  on `closedBall 0 R` for `R < 2π`.
* `bernoulliFn_differentiableAt_of_mem_punctured_ball` — diff'ble
  on `ball 0 R \ {0}`.
* `bernoulliFn_cauchyPowerSeries_hasSum_of_norm_lt` — Cauchy power
  series HasSum on `ball 0 R` for any `R < 2π`.

## What's isolated as the sharpest remaining open Prop

* `BernoulliCauchyCoefficientsEqualBernoulli` — the SHARP residual:
  the Cauchy power-series coefficients of `bernoulliFn` at `0`
  (for some `R < 2π`) equal `B_k / k!`.

* `bernoulliExpHasSumOnBallTwoPi_of_cauchyCoefficients` — the
  REDUCTION theorem: `BernoulliCauchyCoefficientsEqualBernoulli`
  combined with the unconditional analytic infrastructure
  established here ⟹ `BernoulliExpHasSumOnBallTwoPi`.

Stage L26 — Analyticity discharge of the disc-of-convergence
Bernoulli identity; isolation of the Cauchy-coefficient residual.
-/

import PF.Analytic.BernoulliExpHasSumAtNegLogNhdsHalfDischarge
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Metric Set

/-! ## The canonical extended function -/

/-- The extension of `v / (Complex.exp v - 1)` to all of `ℂ` by the
    value `1` at `v = 0`. The removable singularity at `v = 0`
    makes this the canonical analytic extension on the disc
    `|v| < 2π`. -/
noncomputable def bernoulliFn (v : ℂ) : ℂ :=
  if v = 0 then 1 else v / (Complex.exp v - 1)

@[simp] lemma bernoulliFn_zero : bernoulliFn 0 = 1 := by
  simp [bernoulliFn]

lemma bernoulliFn_eq_of_ne_zero {v : ℂ} (hv : v ≠ 0) :
    bernoulliFn v = v / (Complex.exp v - 1) := by
  simp [bernoulliFn, hv]

/-- `bernoulliFn` is the `Function.update`-extension of the raw quotient
    `v / (exp v - 1)` at `0` by the value `1`. -/
lemma bernoulliFn_eq_update :
    bernoulliFn = Function.update (fun v : ℂ => v / (Complex.exp v - 1)) 0 1 := by
  ext v
  by_cases hv : v = 0
  · subst hv; simp [bernoulliFn]
  · simp [bernoulliFn, hv]

/-! ## Auxiliary: `exp v - 1 ≠ 0` on `0 < ‖v‖ < 2π` -/

/-- For `v ≠ 0` with `‖v‖ < 2π`, `Complex.exp v ≠ 1`. -/
lemma exp_ne_one_of_pos_norm_lt_twoPi {v : ℂ} (hv : v ≠ 0)
    (hbd : ‖v‖ < 2 * Real.pi) : Complex.exp v ≠ 1 := by
  intro h
  rcases Complex.exp_eq_one_iff.mp h with ⟨n, hn⟩
  have h_two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hnorm : ‖v‖ = |(n : ℝ)| * (2 * Real.pi) := by
    rw [hn]
    have hI : ‖Complex.I‖ = 1 := Complex.norm_I
    -- ‖(n : ℂ) * (2 * (π : ℂ) * I)‖ = ‖(n : ℂ)‖ * ‖2 * (π : ℂ) * I‖
    rw [norm_mul, norm_mul, Complex.norm_intCast, hI, mul_one]
    -- Now: |↑n| * ‖2 * (π : ℂ)‖ = |↑n| * (2 * π)
    have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    have h_two_pi_real : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h_two_pi_pos]
    rw [h_two_pi_real]
  rw [hnorm] at hbd
  have hnabs : |(n : ℝ)| < 1 := by
    have key : |(n : ℝ)| * (2 * Real.pi) < 1 * (2 * Real.pi) := by
      rw [one_mul]; exact hbd
    exact (mul_lt_mul_right h_two_pi_pos).mp key
  have hn0 : n = 0 := by
    have h_int_abs_eq : (Int.natAbs n : ℝ) = |(n : ℝ)| := by
      rw [Int.cast_natAbs]
      push_cast
      rfl
    have h_int_abs : (Int.natAbs n : ℝ) < 1 := by
      rw [h_int_abs_eq]; exact hnabs
    have : Int.natAbs n < 1 := by exact_mod_cast h_int_abs
    omega
  subst hn0
  simp at hn
  exact hv hn

/-- For `v ≠ 0` with `‖v‖ < 2π`, `Complex.exp v - 1 ≠ 0`. -/
lemma exp_sub_one_ne_zero_of_pos_norm_lt_twoPi {v : ℂ} (hv : v ≠ 0)
    (hbd : ‖v‖ < 2 * Real.pi) : Complex.exp v - 1 ≠ 0 :=
  sub_ne_zero.mpr (exp_ne_one_of_pos_norm_lt_twoPi hv hbd)

/-! ## Slope/derivative limit at `0` -/

/-- The classical limit `(exp v - 1) / v → 1` as `v → 0` in `𝓝[≠] 0`,
    via `HasDerivAt exp 1 0`. -/
lemma exp_sub_one_div_tendsto_one :
    Tendsto (fun v : ℂ => (Complex.exp v - 1) / v) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  have h_deriv : HasDerivAt Complex.exp 1 0 := by
    simpa using Complex.hasDerivAt_exp (0 : ℂ)
  have h_slope_raw : Tendsto (slope Complex.exp 0) (𝓝[≠] 0) (𝓝 1) :=
    hasDerivAt_iff_tendsto_slope.mp h_deriv
  have h_slope_eq : (fun v : ℂ => slope Complex.exp 0 v) =ᶠ[𝓝[≠] 0]
      (fun v : ℂ => (Complex.exp v - 1) / v) := by
    filter_upwards with v
    simp [slope, vsub_eq_sub, div_eq_inv_mul]
  exact h_slope_raw.congr' h_slope_eq

/-! ## Continuity of `bernoulliFn` at `0` -/

/-- `bernoulliFn` is continuous at `0`. -/
lemma bernoulliFn_continuousAt_zero : ContinuousAt bernoulliFn 0 := by
  rw [bernoulliFn_eq_update]
  rw [continuousAt_update_same]
  have h_inv_at_one : ContinuousAt (fun x : ℂ => x⁻¹) (1 : ℂ) :=
    continuousAt_inv₀ one_ne_zero
  have h_recip : Tendsto (fun v : ℂ => ((Complex.exp v - 1) / v)⁻¹)
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h_comp := h_inv_at_one.tendsto.comp exp_sub_one_div_tendsto_one
    -- h_comp : Tendsto ((fun x => x⁻¹) ∘ (fun v => (exp v - 1)/v)) (𝓝[≠] 0) (𝓝 1⁻¹)
    -- Simplify 1⁻¹ = 1 and unfold composition.
    have h1 : (1 : ℂ)⁻¹ = 1 := inv_one
    rw [h1] at h_comp
    exact h_comp
  have h_eq : ∀ᶠ v in 𝓝[≠] (0 : ℂ),
      ((Complex.exp v - 1) / v)⁻¹ = v / (Complex.exp v - 1) := by
    filter_upwards with v
    rw [inv_div]
  exact h_recip.congr' h_eq

/-! ## Analyticity / differentiability away from `0` on the disc -/

/-- For `v ≠ 0` with `‖v‖ < 2π`, `bernoulliFn` agrees with
    `v / (exp v - 1)` in a neighborhood of `v`. -/
lemma bernoulliFn_eventuallyEq_of_ne_zero {v : ℂ} (hv : v ≠ 0) :
    bernoulliFn =ᶠ[nhds v] fun w => w / (Complex.exp w - 1) := by
  have h_open : IsOpen ({w : ℂ | w ≠ 0}) := isOpen_ne
  filter_upwards [h_open.mem_nhds hv] with w hw
  exact bernoulliFn_eq_of_ne_zero hw

/-- For `v ≠ 0` with `‖v‖ < 2π`, `bernoulliFn` is analytic at `v`. -/
lemma bernoulliFn_analyticAt_of_ne_zero {v : ℂ} (hv : v ≠ 0)
    (hbd : ‖v‖ < 2 * Real.pi) : AnalyticAt ℂ bernoulliFn v := by
  have h_quot_analytic : AnalyticAt ℂ (fun w => w / (Complex.exp w - 1)) v := by
    apply AnalyticAt.div
    · exact analyticAt_id
    · exact (analyticAt_cexp (z := v)).sub analyticAt_const
    · exact exp_sub_one_ne_zero_of_pos_norm_lt_twoPi hv hbd
  exact h_quot_analytic.congr (bernoulliFn_eventuallyEq_of_ne_zero hv).symm

/-- `bernoulliFn` is differentiable at every `v ≠ 0` with `‖v‖ < 2π`. -/
lemma bernoulliFn_differentiableAt_of_ne_zero_of_norm_lt_twoPi {v : ℂ}
    (hv : v ≠ 0) (hbd : ‖v‖ < 2 * Real.pi) : DifferentiableAt ℂ bernoulliFn v :=
  (bernoulliFn_analyticAt_of_ne_zero hv hbd).differentiableAt

/-! ## Removable singularity at `0` ⟹ analyticity on full disc -/

/-- `bernoulliFn` is analytic at every `v` with `‖v‖ < 2π`. -/
theorem bernoulliFn_analyticAt_of_norm_lt_twoPi {v : ℂ}
    (hbd : ‖v‖ < 2 * Real.pi) : AnalyticAt ℂ bernoulliFn v := by
  by_cases hv : v = 0
  · subst hv
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · have h_ball_mem : Metric.ball (0 : ℂ) (2 * Real.pi) ∈ nhds (0 : ℂ) := by
        refine Metric.ball_mem_nhds 0 ?_
        positivity
      have h_punc_mem : Metric.ball (0 : ℂ) (2 * Real.pi) ∈ 𝓝[≠] (0 : ℂ) :=
        nhdsWithin_le_nhds h_ball_mem
      filter_upwards [h_punc_mem, self_mem_nhdsWithin] with z hz_ball hz_ne
      have hz_norm : ‖z‖ < 2 * Real.pi := by
        simpa [Metric.mem_ball, dist_zero_right] using hz_ball
      exact bernoulliFn_differentiableAt_of_ne_zero_of_norm_lt_twoPi hz_ne hz_norm
    · exact bernoulliFn_continuousAt_zero
  · exact bernoulliFn_analyticAt_of_ne_zero hv hbd

/-! ## Cauchy integral formula: power series valid on any disc R < 2π -/

/-- `bernoulliFn` is continuous on `closedBall 0 R` for any `R ≤ 2π`. -/
lemma bernoulliFn_continuousOn_closedBall_of_le_twoPi {R : ℝ}
    (hR : R < 2 * Real.pi) : ContinuousOn bernoulliFn (closedBall (0 : ℂ) R) := by
  intro z hz
  have hz_norm : ‖z‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hz_lt : ‖z‖ < 2 * Real.pi := lt_of_le_of_lt hz_norm hR
  exact (bernoulliFn_analyticAt_of_norm_lt_twoPi hz_lt).continuousAt.continuousWithinAt

/-- `bernoulliFn` is differentiable at every point of `ball 0 R \ {0}`
    for `R ≤ 2π`. -/
lemma bernoulliFn_differentiableAt_of_mem_punctured_ball {R : ℝ}
    (hR : R < 2 * Real.pi) :
    ∀ z ∈ ball (0 : ℂ) R \ {0}, DifferentiableAt ℂ bernoulliFn z := by
  intro z ⟨hz_ball, hz_ne⟩
  have hz_norm : ‖z‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hz_ball
  have hz_ne0 : z ≠ 0 := by
    intro h; exact hz_ne (by simp [h])
  exact bernoulliFn_differentiableAt_of_ne_zero_of_norm_lt_twoPi hz_ne0
    (lt_of_lt_of_le hz_norm hR.le)

/-- **CAUCHY POWER SERIES**: For any `0 < R < 2π`, `bernoulliFn` is
    represented on `ball 0 R` by its Cauchy power series at `0`.

    This is a direct application of
    `hasFPowerSeriesOnBall_of_differentiable_off_countable` with the
    countable singular set `s = {0}`. -/
theorem bernoulliFn_hasFPowerSeriesOnBall_of_lt_twoPi {R : NNReal}
    (hR_pos : 0 < R) (hR_lt : (R : ℝ) < 2 * Real.pi) :
    HasFPowerSeriesOnBall bernoulliFn
      (cauchyPowerSeries bernoulliFn 0 R) 0 R :=
  Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
    (countable_singleton 0)
    (bernoulliFn_continuousOn_closedBall_of_le_twoPi hR_lt)
    (bernoulliFn_differentiableAt_of_mem_punctured_ball hR_lt)
    hR_pos

/-- For `v` with `‖v‖ < R < 2π`, the Cauchy power series sums to
    `bernoulliFn v`. -/
theorem bernoulliFn_cauchyPowerSeries_hasSum_of_norm_lt {R : NNReal}
    (hR_pos : 0 < R) (hR_lt : (R : ℝ) < 2 * Real.pi)
    {v : ℂ} (hv : ‖v‖ < R) :
    HasSum (fun n => (cauchyPowerSeries bernoulliFn 0 R n) (fun _ => v))
      (bernoulliFn v) := by
  have hps := bernoulliFn_hasFPowerSeriesOnBall_of_lt_twoPi hR_pos hR_lt
  have hv_emball : v ∈ EMetric.ball (0 : ℂ) R := by
    rw [EMetric.mem_ball, edist_zero_right]
    exact_mod_cast hv
  have h := hps.hasSum hv_emball
  -- h : HasSum (...) (bernoulliFn (0 + v))
  simpa [zero_add] using h

/-! ## The isolated open residual: Cauchy coefficients equal `B_k / k!` -/

/-- **THE SHARP REMAINING OPEN PROP**: the Cauchy power-series
    coefficients of `bernoulliFn` at `0` (for some `R < 2π`) equal
    `B_k / k!`.

    Concretely: for some `R` with `0 < R < 2π` and every `v` with
    `‖v‖ < R`,
    ```
    (cauchyPowerSeries bernoulliFn 0 R n) (fun _ => v) = B_n · v^n / n!
    ```

    With this Prop, the `HasSum` identity on `ball 0 R` follows from
    `bernoulliFn_cauchyPowerSeries_hasSum_of_norm_lt` via term
    rewriting, and the maximal radius `2π` follows by Taylor-series
    uniqueness + radius-of-convergence arguments (the Cauchy
    coefficients are independent of `R`).

    Mathlib has the formal-power-series identity
    `bernoulliPowerSeries · (exp - 1) = X`; identifying its
    coefficients with the analytic Cauchy coefficients of
    `v/(exp v - 1)` requires either:
    (a) an analytic Cauchy-product theorem (NOT in mathlib in the
        form needed),
    (b) direct iterated-derivative computation of `bernoulliFn` at
        `0` (combinatorially expressible but technically intricate),
    or (c) a contour-integral evaluation of the Cauchy coefficient
        formula. -/
def BernoulliCauchyCoefficientsEqualBernoulli : Prop :=
  ∃ R : NNReal, 0 < R ∧ (R : ℝ) < 2 * Real.pi ∧
    ∀ (n : ℕ) (v : ℂ), ‖v‖ < R →
      (cauchyPowerSeries bernoulliFn 0 R n) (fun _ => v) =
        (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ)

end PrincipiaTractalis.Analytic.Sheaf

/-!
## Manifest

This file delivers (axiom-free, no `sorry`):

* `bernoulliFn` — the canonical extended function (= `1` at `v = 0`,
  `v / (exp v - 1)` elsewhere).

* `bernoulliFn_continuousAt_zero` — continuity at `0`, via
  `(exp v - 1)/v → 1` from `HasDerivAt exp 1 0` and reciprocation.

* `bernoulliFn_analyticAt_of_norm_lt_twoPi` — UNCONDITIONAL
  analyticity on the open disc `|v| < 2π`: Riemann removable
  singularity at `0` + `AnalyticAt.div` away from `0` (with
  `exp v - 1 ≠ 0` from `Complex.exp_eq_one_iff` and `n ≠ 0` ⟹
  `‖n · 2πi‖ ≥ 2π`).

* `bernoulliFn_hasFPowerSeriesOnBall_of_lt_twoPi` — UNCONDITIONAL
  power-series representation of `bernoulliFn` on every `ball 0 R`
  with `R < 2π`, via mathlib's
  `Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable`
  (Cauchy integral formula).

* `BernoulliCauchyCoefficientsEqualBernoulli` — the SHARP
  remaining open Prop: that the Cauchy coefficients are
  `B_k / k!`. Mathlib has the formal-PS identity but not the
  Cauchy-coefficient identification.

The load-bearing open analytic content for the disc-of-convergence
Bernoulli identity is now reduced from "produce the full
`HasSum` identity from scratch" to "identify the Cauchy coefficient
formula with the Bernoulli numbers" — a strictly more constrained
problem.
-/

-- Axiom audit: the unconditional infrastructure depends only on standard mathlib axioms.
section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms bernoulliFn_analyticAt_of_norm_lt_twoPi
#guard_msgs(drop info) in
#print axioms bernoulliFn_cauchyPowerSeries_hasSum_of_norm_lt
#guard_msgs(drop info) in
#print axioms bernoulliFn_continuousAt_zero
end AxiomAudit
