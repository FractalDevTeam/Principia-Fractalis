/-
# Hankel Upper-Edge Integral: DCT Application

The convergence of the upper-edge integral to `Γ(s)` as `ε → 0⁺`,
combining the pointwise convergence (`HankelUpperEdgeDCT`), the
modulus bound (`HankelUpperEdgeBound`), and the integrability
(`HankelIntegrability`) into the full DCT-application form.

**Target theorem** (for `0 < Re s ≤ 1`, the harder critical-strip case):

```
Tendsto (fun ε : ℝ => ∫ t in Set.Ioi 0, hankelUpperEdgeIntegrand s ε t)
        (𝓝[>] 0)
        (𝓝 (Complex.Gamma s))
```

This file:
* Proves the **limit-integral identification**:
  `∫ t in Ioi 0, gammaPrincipalIntegrand s t = Complex.Gamma s`
  for `0 < Re s`, via `Complex.Gamma_eq_integral`.

* States the full DCT-application theorem as the open conclusion,
  with all ingredients (pointwise convergence, ε-uniform bound,
  integrability of bound) traceable to previously-proven lemmas.

Stage L4 — DCT-application bridge to Γ(s).
-/

import PF.Analytic.HankelIntegrability

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory Set

/-! ## Limit-integral identification with `Γ(s)` -/

/-- **Principal integrand matches mathlib's `GammaIntegral` integrand**.

    `gammaPrincipalIntegrand s t = (t : ℂ)^(s-1) · Complex.exp(-(t : ℂ))
                                  = ↑(Real.exp(-t)) · (t : ℂ)^(s-1)`,

    matching `Complex.GammaIntegral s = ∫ x in Ioi 0, ↑(-x).exp · x^(s-1)`. -/
theorem gammaPrincipalIntegrand_eq_GammaIntegral_integrand (s : ℂ) (t : ℝ) :
    gammaPrincipalIntegrand s t =
    ↑((-t).exp : ℝ) * (t : ℂ) ^ (s - 1) := by
  unfold gammaPrincipalIntegrand
  rw [show Complex.exp (-(t : ℂ)) = ↑((-t).exp : ℝ) by
        rw [show -(t : ℂ) = (((-t) : ℝ) : ℂ) from by push_cast; ring,
            Complex.ofReal_exp]]
  ring

/-- **The integral of the principal integrand on `(0, ∞)` equals `Γ(s)`**
    for `0 < Re s`. Direct from `Complex.Gamma_eq_integral` after
    matching the integrand form. -/
theorem integral_gammaPrincipalIntegrand_eq_Gamma {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Ioi (0 : ℝ), gammaPrincipalIntegrand s t = Complex.Gamma s := by
  rw [Complex.Gamma_eq_integral hs]
  -- Complex.GammaIntegral s := ∫ x in Ioi 0, ↑(-x).exp * x^(s - 1)
  unfold Complex.GammaIntegral
  congr 1
  ext t
  exact gammaPrincipalIntegrand_eq_GammaIntegral_integrand s t

/-! ## DCT setup: ε-uniform bound for the regime `0 < Re s ≤ 1` -/

/-- **ε-uniform integrand bound for `0 < Re s ≤ 1`**: combining
    `norm_hankelUpperEdgeIntegrand_le` (cpow & exp modulus) with
    `norm_rpow_upper_edge_le_of_re_le_one` (rpow antitone in base
    for nonpositive exponent), we get the ε-independent dominating
    function

      `‖F ε t‖ ≤ exp(|Im s|·π/2) · t^(Re s - 1) · exp(-t)`. -/
theorem hankelUpperEdgeIntegrand_norm_le_of_re_le_one
    {s : ℂ} (hs : s.re ≤ 1) (t ε : ℝ) (ht : 0 < t) :
    ‖hankelUpperEdgeIntegrand s ε t‖ ≤
    Real.exp (|s.im| * Real.pi / 2) * t ^ (s.re - 1) * Real.exp (-t) := by
  have h_main := norm_hankelUpperEdgeIntegrand_le t ε ht s
  -- h_main: ‖integrand‖ ≤ ‖t + iε‖^(Re s - 1) · exp(|Im s|·π/2) · exp(-t)
  have h_rpow := norm_rpow_upper_edge_le_of_re_le_one t ε ht s hs
  -- h_rpow: ‖t + iε‖^(Re s - 1) ≤ t^(Re s - 1)
  have h_const_nn : 0 ≤ Real.exp (|s.im| * Real.pi / 2) := Real.exp_nonneg _
  have h_exp_nn : 0 ≤ Real.exp (-t) := Real.exp_nonneg _
  calc ‖hankelUpperEdgeIntegrand s ε t‖
      ≤ ‖(t : ℂ) + (ε : ℂ) * I‖ ^ (s.re - 1) *
          Real.exp (|s.im| * Real.pi / 2) * Real.exp (-t) := h_main
    _ ≤ t ^ (s.re - 1) * Real.exp (|s.im| * Real.pi / 2) * Real.exp (-t) := by
        apply mul_le_mul_of_nonneg_right _ h_exp_nn
        exact mul_le_mul_of_nonneg_right h_rpow h_const_nn
    _ = Real.exp (|s.im| * Real.pi / 2) * t ^ (s.re - 1) * Real.exp (-t) := by ring

/-! ## Open: the DCT application proper

The full DCT-application theorem:

```
theorem hankelUpperEdge_integral_tends_to_Gamma_of_re_le_one
    {s : ℂ} (hs : 0 < s.re) (hs1 : s.re ≤ 1) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), hankelUpperEdgeIntegrand s ε t)
            (𝓝[>] 0)
            (𝓝 (Complex.Gamma s))
```

Proof structure:
1. **AE measurability**: each `F ε := fun t => hankelUpperEdgeIntegrand s ε t`
   is continuous on `Ioi 0` (composition of continuous functions), hence
   strongly measurable on the measurable set `Ioi 0`.

2. **ε-uniform bound**: `hankelUpperEdgeIntegrand_norm_le_of_re_le_one`
   (proven above) gives `‖F ε t‖ ≤ M · t^(Re s - 1) · exp(-t)` with
   `M := exp(|Im s|·π/2)`, for all `ε > 0` and `t > 0`.

3. **Integrability of the bound**: `upper_edge_dominating_integrable`
   from `HankelIntegrability.lean` gives integrability of the bound on
   `Ioi 0` for `Re s > 0`.

4. **Pointwise convergence**: `hankelUpperEdgeIntegrand_tendsto_pointwise_pos`
   from `HankelUpperEdgeDCT.lean` gives the pointwise limit
   `F ε t → gammaPrincipalIntegrand s t` as `ε → 0⁺` for each `t > 0`.

5. **DCT invocation**: apply
   `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
   with the above ingredients (`𝓝[>] 0` is countably generated since
   it is the neighborhood-within filter of a metric space).

6. **Limit identification**: combine the DCT conclusion (giving
   `∫ F ε → ∫ gammaPrincipalIntegrand`) with
   `integral_gammaPrincipalIntegrand_eq_Gamma` (proven above) to
   conclude `∫ F ε → Complex.Gamma s`.

The case `Re s ≥ 1` requires a different bound `(t² + 1)^((Re s - 1)/2)`
(from `norm_rpow_upper_edge_le_of_re_ge_one` in `HankelUpperEdgeBound`)
and a separate integrability argument (the bound grows polynomially
in t, dominated by `exp(-t)`).

With the limit identification in step 6 proven above (axiom-clean),
the remaining work is mechanical: the DCT invocation. The reduction
of the polylog-route axiom retirement to "apply
tendsto_integral_filter_of_dominated_convergence" is now complete.
-/

end PrincipiaTractalis.Analytic
