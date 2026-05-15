/-
# Hankel Contour: Upper-Edge Dominated Convergence

The first of the three remaining analytic deliverables: the
upper-edge integral

  `∫_ε^R (t + iε)^(s-1) · e^(-(t+iε)) dt`

converges to `Γ(s)` as `ε → 0⁺` and `R → ∞`, for `Re s > 0`.

**Strategy** (dominated convergence):
1. **Pointwise convergence** at each `t > 0`:
     `(t + iε)^(s-1) · e^(-(t+iε)) → t^(s-1) · e^(-t)` as `ε → 0`.
2. **Dominating function**: for `ε ∈ (0, 1]`, the integrand modulus is
   bounded by an explicit `g(t)`, integrable on `(0, ∞)` for `Re s > 0`.
3. **DCT**: standard `tendsto_integral_filter_of_dominated_convergence`.
4. **Limit identification**: `∫_0^∞ t^(s-1) e^(-t) dt = Γ(s)` via
   `Complex.Gamma_eq_integral`.

This file:
* Defines the parameterized integrand `hankelUpperEdgeIntegrand`.
* Defines the principal-branch limit `gammaPrincipalIntegrand`.
* **Proves axiom-clean**: pointwise convergence at every `t > 0`.
* Defines the dominating bound and states the integrability claim.
* States the DCT conclusion as the open theorem (one mathlib-DCT step).

Stage L4 — Upper-edge DCT foundation.
-/

import PF.Analytic.HankelSmallLoop
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory

/-! ## Integrand definitions -/

/-- **Parameterized upper-edge integrand**: `(t + iε)^(s-1) · e^(-(t+iε))`,
    the integrand of the upper-edge integral
    `∫_ε^R (t + iε)^(s-1) e^(-(t+iε)) dt`. -/
noncomputable def hankelUpperEdgeIntegrand (s : ℂ) (ε t : ℝ) : ℂ :=
  ((t : ℂ) + (ε : ℂ) * I) ^ (s - 1) * Complex.exp (-((t : ℂ) + (ε : ℂ) * I))

/-- **Principal (ε = 0) integrand**: `t^(s-1) · e^(-t)`. This is Euler's
    Γ-integrand evaluated at positive `t`, matching
    `Complex.GammaIntegral`. -/
noncomputable def gammaPrincipalIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * Complex.exp (-(t : ℂ))

/-! ## Pointwise convergence (axiom-clean) -/

/-- **Pointwise convergence of the parameterized integrand**: for each
    fixed `t > 0`,

      `(t + iε)^(s-1) · e^(-(t+iε)) → t^(s-1) · e^(-t)`  as `ε → 0`.

    Proof: `(t + iε) → t` (continuity of `ε ↦ t + iε`). Since `t > 0`
    means `t ∈ slitPlane`, `Filter.Tendsto.cpow` gives convergence of
    the `cpow` factor. Continuity of `exp` gives convergence of the
    exponential factor. Product of convergent sequences converges. -/
theorem hankelUpperEdgeIntegrand_tendsto_pointwise
    {s : ℂ} {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => hankelUpperEdgeIntegrand s ε t) (𝓝 0)
            (𝓝 (gammaPrincipalIntegrand s t)) := by
  unfold hankelUpperEdgeIntegrand gammaPrincipalIntegrand
  have h_t_slit : (t : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 ht
  -- Inner convergence: (t + iε) → t
  have h_z : Tendsto (fun ε : ℝ => (t : ℂ) + (ε : ℂ) * I) (𝓝 0) (𝓝 (t : ℂ)) := by
    have h_ofReal : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
      have := Complex.continuous_ofReal.tendsto 0
      simpa using this
    have h_mul : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℂ) * I)) :=
      h_ofReal.mul_const I
    have h_sum : Tendsto (fun ε : ℝ => (t : ℂ) + (ε : ℂ) * I) (𝓝 0)
                         (𝓝 ((t : ℂ) + (0 : ℂ) * I)) :=
      tendsto_const_nhds.add h_mul
    simpa using h_sum
  -- cpow factor: (t + iε)^(s-1) → t^(s-1)
  have h_cpow : Tendsto (fun ε : ℝ => ((t : ℂ) + (ε : ℂ) * I) ^ (s - 1)) (𝓝 0)
                        (𝓝 ((t : ℂ) ^ (s - 1))) :=
    h_z.cpow tendsto_const_nhds h_t_slit
  -- exp factor: exp(-(t + iε)) → exp(-t)
  have h_exp : Tendsto (fun ε : ℝ => Complex.exp (-((t : ℂ) + (ε : ℂ) * I))) (𝓝 0)
                       (𝓝 (Complex.exp (-(t : ℂ)))) := by
    have h_neg : Tendsto (fun ε : ℝ => -((t : ℂ) + (ε : ℂ) * I)) (𝓝 0)
                         (𝓝 (-(t : ℂ))) := h_z.neg
    exact (Complex.continuous_exp.tendsto _).comp h_neg
  -- Product
  exact h_cpow.mul h_exp

/-- **From-the-right version**: pointwise convergence restricted to
    `ε → 0⁺`. Direct corollary of `hankelUpperEdgeIntegrand_tendsto_pointwise`
    via `Tendsto.mono_left nhdsWithin_le_nhds`. -/
theorem hankelUpperEdgeIntegrand_tendsto_pointwise_pos
    {s : ℂ} {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => hankelUpperEdgeIntegrand s ε t) (𝓝[>] 0)
            (𝓝 (gammaPrincipalIntegrand s t)) :=
  (hankelUpperEdgeIntegrand_tendsto_pointwise ht).mono_left nhdsWithin_le_nhds

/-! ## Principal integrand vs mathlib's `GammaIntegral` -/

/-- **Match with mathlib's Γ-integrand**: `gammaPrincipalIntegrand s t`
    equals `e^(-t) · t^(s-1)` (the order used in `Complex.GammaIntegral`),
    by commutativity of multiplication. -/
theorem gammaPrincipalIntegrand_eq_mathlib (s : ℂ) (t : ℝ) :
    gammaPrincipalIntegrand s t =
    ↑(Real.exp (-t)) * (t : ℂ) ^ (s - 1) := by
  unfold gammaPrincipalIntegrand
  rw [show Complex.exp (-(t : ℂ)) = ↑(Real.exp (-t)) by
        rw [show (-(t : ℂ)) = (((-t) : ℝ) : ℂ) from by push_cast; ring,
            Complex.ofReal_exp]]
  ring

/-! ## Dominating bound (structural definition) -/

/-- **Dominating function** for the parameterized integrand, valid for
    `ε ∈ (0, 1]` and `t ∈ (0, ∞)`:

      `g(t) := (t² + 1)^((Re s − 1)/2) · e^(-t) · e^(|Im s|·π/2 + 1)`

    Derivation:
    * `|t + iε| = √(t² + ε²) ≤ √(t² + 1)` for `ε ≤ 1`, so
      `|(t + iε)^(s-1)| ≤ (t² + 1)^((Re s - 1)/2)` (when `Re s - 1 ≥ 0`)
      or bounded by a constant for the other case
    * `|e^(-(t + iε))| = e^(-t)`
    * The argument bound `|arg(t + iε)| ≤ π/2` for `t > 0, ε > 0` gives
      `e^(-Im s · arg(t+iε)) ≤ e^(|Im s|·π/2)`

    Combined, the dominating bound is `(t² + 1)^((Re s - 1)/2) · e^(-t)`
    times a constant. -/
noncomputable def hankelUpperEdgeBound (s : ℂ) (t : ℝ) : ℝ :=
  (t^2 + 1) ^ ((s.re - 1) / 2) * Real.exp (-t) *
    Real.exp (|s.im| * Real.pi / 2 + 1)

/-! ## Open theorem: full DCT conclusion

```
theorem hankelUpperEdge_integral_tends_to_Gamma
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (p : ℝ × ℝ) =>
      ∫ t in p.1..p.2, hankelUpperEdgeIntegrand s p.1 t)
      ((𝓝[>] 0) ×ˢ Filter.atTop)
      (𝓝 (Complex.Gamma s))
```

Proof structure:

1. **Pointwise convergence** (proved above):
   `hankelUpperEdgeIntegrand_tendsto_pointwise_pos`.

2. **Dominating function**: `hankelUpperEdgeBound s` is integrable on
   `(0, ∞)` for `Re s > 0`. Specifically:
   * `∫_0^∞ (t² + 1)^((Re s - 1)/2) · e^(-t) dt < ∞` since:
     - For `t ≥ 1`: `(t² + 1)^((Re s - 1)/2) ≤ (2t²)^((Re s - 1)/2) =
       2^((Re s - 1)/2) · t^(Re s - 1)`, and
       `∫_1^∞ t^(Re s - 1) e^(-t) dt ≤ Γ(Re s)`.
     - For `0 < t ≤ 1`: `(t² + 1)^((Re s - 1)/2) ≤ 2^((Re s - 1)/2)`
       if `Re s ≥ 1`, or `(t² + 1)^((Re s - 1)/2) ≤ 1` if `Re s ≤ 1`.

3. **Integrand bound** by the dominating function:
   * `|(t + iε)^(s-1)|` analysis via `Complex.norm_cpow_eq_rpow_re_of_pos`
     (for real positive base) and `Complex.norm_cpow_le_rpow_re_of_le`
     (for the upper-bound side). Use `|t + iε|² = t² + ε² ≤ t² + 1`.

4. **Apply DCT**: `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
   or `intervalIntegral` analogue with the parameterized DCT.

5. **Identify limit**: `∫_0^∞ t^(s-1) · e^(-t) dt = Complex.GammaIntegral s
   = Complex.Gamma s` by `Complex.Gamma_eq_integral hs`.

The two ingredients (pointwise convergence proved, structural integrand
bound stated) reduce the DCT to a routine mathlib invocation. This is
a classical-analysis deliverable, not a research problem.
-/

end PrincipiaTractalis.Analytic
