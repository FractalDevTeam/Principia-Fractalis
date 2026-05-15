/-
# Hankel Lower-Edge DCT Invocation

The final DCT-invocation step for the lower-edge integral. Mirrors
`HankelUpperEdgeDCTProof.lean`, adapted to the wrapped-branch
integrand `e^(2πi(s-1)) · (t - iε)^(s-1) · e^(-(t-iε))`.

**Target theorem** (for `0 < Re s ≤ 1`):

```
Tendsto (fun ε : ℝ => ∫ t in Ioi 0, hankelLowerEdgeIntegrand s ε t)
        (𝓝[>] 0)
        (𝓝 (e^(2πi(s-1)) · Γ(s)))
```

Stage L4 — Lower-edge DCT closure.
-/

import PF.Analytic.HankelUpperEdgeDCTProof

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory Set

/-! ## ε-uniform integrand bound for the regime `0 < Re s ≤ 1` -/

/-- **ε-uniform bound** on the lower-edge integrand for `0 < Re s ≤ 1`:

      `‖F ε t‖ ≤ exp(-2π·Im s) · exp(|Im s|·π/2) · t^(Re s - 1) · exp(-t)`. -/
theorem hankelLowerEdgeIntegrand_norm_le_of_re_le_one
    {s : ℂ} (hs : s.re ≤ 1) (t ε : ℝ) (ht : 0 < t) :
    ‖hankelLowerEdgeIntegrand s ε t‖ ≤
    Real.exp (-(2 * Real.pi * s.im)) *
    Real.exp (|s.im| * Real.pi / 2) *
    t ^ (s.re - 1) * Real.exp (-t) := by
  have h_main := norm_hankelLowerEdgeIntegrand_le t ε ht s
  -- h_main: ‖F‖ ≤ exp(-2π·Im s) · (‖t - iε‖^(Re s - 1) · exp(|Im s|·π/2)) · exp(-t)
  rw [norm_lower_eq_upper] at h_main
  -- h_main: ‖F‖ ≤ exp(-2π·Im s) · (‖t + iε‖^(Re s - 1) · exp(|Im s|·π/2)) · exp(-t)
  have h_rpow := norm_rpow_upper_edge_le_of_re_le_one t ε ht s hs
  -- h_rpow: ‖t + iε‖^(Re s - 1) ≤ t^(Re s - 1)
  have h_branch_nn : 0 ≤ Real.exp (-(2 * Real.pi * s.im)) := Real.exp_nonneg _
  have h_const_nn : 0 ≤ Real.exp (|s.im| * Real.pi / 2) := Real.exp_nonneg _
  have h_exp_nn : 0 ≤ Real.exp (-t) := Real.exp_nonneg _
  calc ‖hankelLowerEdgeIntegrand s ε t‖
      ≤ Real.exp (-(2 * Real.pi * s.im)) *
          (‖(t : ℂ) + (ε : ℂ) * I‖ ^ (s.re - 1) *
           Real.exp (|s.im| * Real.pi / 2)) *
          Real.exp (-t) := h_main
    _ ≤ Real.exp (-(2 * Real.pi * s.im)) *
          (t ^ (s.re - 1) * Real.exp (|s.im| * Real.pi / 2)) *
          Real.exp (-t) := by
        apply mul_le_mul_of_nonneg_right _ h_exp_nn
        apply mul_le_mul_of_nonneg_left _ h_branch_nn
        exact mul_le_mul_of_nonneg_right h_rpow h_const_nn
    _ = Real.exp (-(2 * Real.pi * s.im)) *
          Real.exp (|s.im| * Real.pi / 2) *
          t ^ (s.re - 1) * Real.exp (-t) := by ring

/-! ## AE strong measurability of the lower-edge integrand -/

/-- **Continuity of the lower-edge integrand** on `Ioi 0`.

    Composition of continuous functions: `e^(2πi(s-1))` is constant,
    `z(t) := t - iε` is continuous, `z(t) ∈ slitPlane` for `t > 0`,
    so `cpow` is continuous there; `exp(-z)` is continuous everywhere. -/
theorem hankelLowerEdgeIntegrand_continuousOn (s : ℂ) (ε : ℝ) :
    ContinuousOn (fun t : ℝ => hankelLowerEdgeIntegrand s ε t) (Ioi 0) := by
  unfold hankelLowerEdgeIntegrand
  have h_z_cont : Continuous (fun t : ℝ => (t : ℂ) - (ε : ℂ) * I) :=
    Complex.continuous_ofReal.sub continuous_const
  -- Factor: e^(2πi(s-1)) (constant) · (cpow · exp)
  apply ContinuousOn.mul
  · -- Constant factor
    exact continuousOn_const
  apply ContinuousOn.mul
  · -- (· ^ (s - 1)) ∘ z continuous on Ioi 0
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have h_z_slit : (t : ℂ) - (ε : ℂ) * I ∈ Complex.slitPlane := by
      show 0 < ((t : ℂ) - (ε : ℂ) * I).re ∨ ((t : ℂ) - (ε : ℂ) * I).im ≠ 0
      left
      simp
      exact Set.mem_Ioi.mp ht
    have h_z_tendsto : Tendsto (fun u : ℝ => (u : ℂ) - (ε : ℂ) * I) (𝓝 t)
                                (𝓝 ((t : ℂ) - (ε : ℂ) * I)) :=
      h_z_cont.continuousAt
    exact h_z_tendsto.cpow tendsto_const_nhds h_z_slit
  · -- exp(-z) continuous everywhere
    intro t _
    apply ContinuousAt.continuousWithinAt
    have h_neg_tendsto : Tendsto (fun u : ℝ => -((u : ℂ) - (ε : ℂ) * I)) (𝓝 t)
                                  (𝓝 (-((t : ℂ) - (ε : ℂ) * I))) :=
      h_z_cont.neg.continuousAt
    exact (Complex.continuous_exp.tendsto _).comp h_neg_tendsto

/-- **AE strong measurability** of the lower-edge integrand on
    `volume.restrict (Ioi 0)`. -/
theorem hankelLowerEdgeIntegrand_aestronglyMeasurable (s : ℂ) (ε : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => hankelLowerEdgeIntegrand s ε t)
                          (volume.restrict (Ioi 0)) :=
  (hankelLowerEdgeIntegrand_continuousOn s ε).aestronglyMeasurable measurableSet_Ioi

/-! ## Limit-integral identification -/

/-- **Integral of `gammaLowerLimitIntegrand` equals `e^(2πi(s-1)) · Γ(s)`**
    for `0 < Re s`. Pulls the constant branch factor out of the integral
    and applies `integral_gammaPrincipalIntegrand_eq_Gamma`. -/
theorem integral_gammaLowerLimitIntegrand_eq
    {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Ioi (0 : ℝ), gammaLowerLimitIntegrand s t =
    Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) * Complex.Gamma s := by
  have : (fun t : ℝ => gammaLowerLimitIntegrand s t) =
         fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) *
                      gammaPrincipalIntegrand s t := by
    ext t
    exact gammaLowerLimitIntegrand_eq_factor s t
  rw [this]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_gammaPrincipalIntegrand_eq_Gamma hs]

/-! ## The DCT-application theorem (`0 < Re s ≤ 1` case) -/

/-- **Lower-edge integral converges to `e^(2πi(s-1)) · Γ(s)`** for
    `0 < Re s ≤ 1`. Same DCT pattern as the upper edge. -/
theorem hankelLowerEdge_integral_tends_to_branch_Gamma_of_re_le_one
    {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), hankelLowerEdgeIntegrand s ε t)
            (𝓝[>] 0)
            (𝓝 (Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) *
                 Complex.Gamma s)) := by
  rw [← integral_gammaLowerLimitIntegrand_eq hs]
  set bound : ℝ → ℝ := fun t =>
    Real.exp (-(2 * Real.pi * s.im)) *
    Real.exp (|s.im| * Real.pi / 2) *
    t ^ (s.re - 1) * Real.exp (-t)
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall (fun _ =>
      hankelLowerEdgeIntegrand_aestronglyMeasurable s _))
    ?_ ?_ ?_
  · -- ε-uniform bound
    refine Filter.Eventually.of_forall (fun ε => ?_)
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact hankelLowerEdgeIntegrand_norm_le_of_re_le_one hs1 t ε
      (Set.mem_Ioi.mp ht)
  · -- Integrability of bound
    have h := lower_edge_dominating_integrable hs
    -- h : IntegrableOn (fun t => exp(-2π·Im s) * exp(|Im s|·π/2) * (t^(Re s - 1) · exp(-t))) (Ioi 0)
    refine h.congr ?_
    filter_upwards with t
    show Real.exp (-(2 * Real.pi * s.im)) *
         Real.exp (|s.im| * Real.pi / 2) *
         (t ^ (s.re - 1) * Real.exp (-t)) = bound t
    show Real.exp (-(2 * Real.pi * s.im)) *
         Real.exp (|s.im| * Real.pi / 2) *
         (t ^ (s.re - 1) * Real.exp (-t)) =
         Real.exp (-(2 * Real.pi * s.im)) *
         Real.exp (|s.im| * Real.pi / 2) *
         t ^ (s.re - 1) * Real.exp (-t)
    ring
  · -- Pointwise convergence
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact hankelLowerEdgeIntegrand_tendsto_pointwise_pos (Set.mem_Ioi.mp ht)

end PrincipiaTractalis.Analytic
