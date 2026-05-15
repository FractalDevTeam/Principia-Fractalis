/-
# Hankel Contour: Lower-Edge Dominated Convergence

The second of the three remaining analytic deliverables: the
lower-edge integral

  `∫_ε^R (wrapped branch of (t - iε)^(s-1)) · e^(-(t-iε)) dt`

converges to `e^(2πi(s-1)) · Γ(s)` as `ε → 0⁺` and `R → ∞`, for `Re s > 0`.

**Branch convention**: the lower edge of the Hankel contour is the
analytic continuation around 0 of the upper edge's branch. With the
principal branch on the upper edge taking `arg = 0⁺` for `t + iε → t`,
the lower edge's branch takes `arg = 2π⁻` for `t - iε → t`. The
relationship to mathlib's principal `Complex.cpow`:

  `(wrapped) (t - iε)^(s-1) = e^(2πi(s-1)) · (principal)(t - iε)^(s-1)`

so the wrapped lower-edge integrand is

  `e^(2πi(s-1)) · (t - iε)^(s-1) · e^(-(t-iε))`

where the cpow is the *principal* `Complex.cpow`. As `ε → 0⁺`, the
principal `(t - iε)^(s-1) → t^(s-1)` (since arg → 0⁻ from below), so
the wrapped integrand → `e^(2πi(s-1)) · t^(s-1) · e^(-t)`.

This file:
* Defines the parameterized lower-edge integrand `hankelLowerEdgeIntegrand`
  with the explicit branch factor.
* Defines the wrapped-branch limit `gammaLowerLimitIntegrand`.
* **Proves axiom-clean**: pointwise convergence at every `t > 0`.
* States the DCT conclusion as the open theorem.

Stage L4 — Lower-edge DCT foundation.
-/

import PF.Analytic.HankelUpperEdgeDCT

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory

/-! ## Lower-edge integrand definitions -/

/-- **Parameterized lower-edge integrand** (wrapped branch):
    `e^(2πi(s-1)) · (t - iε)^(s-1) · e^(-(t-iε))`,

    where `(·)^(s-1)` is the *principal* `Complex.cpow` and the
    constant prefactor `e^(2πi(s-1))` accounts for the branch wrap
    around 0 (arg jumping from 0 to 2π). -/
noncomputable def hankelLowerEdgeIntegrand (s : ℂ) (ε t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) *
  (((t : ℂ) - (ε : ℂ) * I) ^ (s - 1) *
   Complex.exp (-((t : ℂ) - (ε : ℂ) * I)))

/-- **Wrapped-branch limit integrand**: `e^(2πi(s-1)) · t^(s-1) · e^(-t)`.

    Limit of `hankelLowerEdgeIntegrand s ε t` as `ε → 0`. Differs from
    `gammaPrincipalIntegrand` by the constant branch factor. -/
noncomputable def gammaLowerLimitIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) * gammaPrincipalIntegrand s t

/-! ## Pointwise convergence (axiom-clean) -/

/-- **Pointwise convergence** at each `t > 0`:

      `hankelLowerEdgeIntegrand s ε t → gammaLowerLimitIntegrand s t`
      as `ε → 0`.

    Proof structure mirrors the upper-edge case. The only differences
    are the sign on `iε` (handled via `Tendsto.sub`) and the constant
    branch prefactor (carries through the limit unchanged). -/
theorem hankelLowerEdgeIntegrand_tendsto_pointwise
    {s : ℂ} {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => hankelLowerEdgeIntegrand s ε t) (𝓝 0)
            (𝓝 (gammaLowerLimitIntegrand s t)) := by
  unfold hankelLowerEdgeIntegrand gammaLowerLimitIntegrand gammaPrincipalIntegrand
  have h_t_slit : (t : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 ht
  -- Inner convergence: (t - iε) → t
  have h_z : Tendsto (fun ε : ℝ => (t : ℂ) - (ε : ℂ) * I) (𝓝 0) (𝓝 (t : ℂ)) := by
    have h_ofReal : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
      have := Complex.continuous_ofReal.tendsto 0
      simpa using this
    have h_mul : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℂ) * I)) :=
      h_ofReal.mul_const I
    have h_diff : Tendsto (fun ε : ℝ => (t : ℂ) - (ε : ℂ) * I) (𝓝 0)
                          (𝓝 ((t : ℂ) - (0 : ℂ) * I)) :=
      tendsto_const_nhds.sub h_mul
    simpa using h_diff
  -- cpow factor (principal branch): (t - iε)^(s-1) → t^(s-1)
  have h_cpow : Tendsto (fun ε : ℝ => ((t : ℂ) - (ε : ℂ) * I) ^ (s - 1)) (𝓝 0)
                        (𝓝 ((t : ℂ) ^ (s - 1))) :=
    h_z.cpow tendsto_const_nhds h_t_slit
  -- exp factor: exp(-(t - iε)) → exp(-t)
  have h_exp : Tendsto (fun ε : ℝ => Complex.exp (-((t : ℂ) - (ε : ℂ) * I))) (𝓝 0)
                       (𝓝 (Complex.exp (-(t : ℂ)))) := by
    have h_neg : Tendsto (fun ε : ℝ => -((t : ℂ) - (ε : ℂ) * I)) (𝓝 0)
                         (𝓝 (-(t : ℂ))) := h_z.neg
    exact (Complex.continuous_exp.tendsto _).comp h_neg
  -- Inner product (cpow × exp factor)
  have h_inner : Tendsto (fun ε : ℝ =>
      ((t : ℂ) - (ε : ℂ) * I) ^ (s - 1) *
      Complex.exp (-((t : ℂ) - (ε : ℂ) * I))) (𝓝 0)
      (𝓝 ((t : ℂ) ^ (s - 1) * Complex.exp (-(t : ℂ)))) :=
    h_cpow.mul h_exp
  -- Multiply by constant branch factor e^(2πi(s-1))
  exact tendsto_const_nhds.mul h_inner

/-- **From-the-right version**: pointwise convergence restricted to
    `ε → 0⁺`. -/
theorem hankelLowerEdgeIntegrand_tendsto_pointwise_pos
    {s : ℂ} {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => hankelLowerEdgeIntegrand s ε t) (𝓝[>] 0)
            (𝓝 (gammaLowerLimitIntegrand s t)) :=
  (hankelLowerEdgeIntegrand_tendsto_pointwise ht).mono_left nhdsWithin_le_nhds

/-! ## Algebraic relationship to the upper-edge integrand -/

/-- **Limit-form relationship**: `gammaLowerLimitIntegrand` differs from
    `gammaPrincipalIntegrand` by the constant factor `e^(2πi(s-1))`. -/
theorem gammaLowerLimitIntegrand_eq_factor (s : ℂ) (t : ℝ) :
    gammaLowerLimitIntegrand s t =
    Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) *
    gammaPrincipalIntegrand s t := by
  rfl

/-! ## Open theorem: full DCT conclusion for the lower edge

```
theorem hankelLowerEdge_integral_tends_to_branch_factor_times_Gamma
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (p : ℝ × ℝ) =>
      ∫ t in p.1..p.2, hankelLowerEdgeIntegrand s p.1 t)
      ((𝓝[>] 0) ×ˢ Filter.atTop)
      (𝓝 (Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) * Complex.Gamma s))
```

Proof structure (mirrors the upper-edge case):

1. **Pointwise convergence** (proved above):
   `hankelLowerEdgeIntegrand_tendsto_pointwise_pos`.

2. **Dominating function**: same `hankelUpperEdgeBound s` works (since
   `|t - iε| = |t + iε|`); the constant branch factor's modulus is
   `e^(-2π·Im s)`, absorbed into the dominating bound's constant.

3. **Integrand bound** by the dominating function: identical analysis
   to the upper edge, plus a factor `|e^(2πi(s-1))| = e^(-2π·Im(s-1))
   = e^(2π·(1 - Re s)... wait that's not right.

   |e^(2πi(s-1))| = e^(Re(2πi(s-1))) = e^(2π · Im(-(s-1)))
                  = e^(-2π · Im(s-1)) = e^(-2π · Im s).
   This is a constant (in t and ε), bounded for fixed s.

4. **Apply DCT**: standard mathlib invocation.

5. **Identify limit**: the integral
   `∫_0^∞ gammaLowerLimitIntegrand s t dt`
   `= e^(2πi(s-1)) · ∫_0^∞ gammaPrincipalIntegrand s t dt`
   `= e^(2πi(s-1)) · Γ(s)`  (factor out the constant, apply
   `Complex.Gamma_eq_integral hs`).

The constant prefactor pulls through linearly, so the lower-edge DCT
reduces to the upper-edge DCT plus a multiplicative constant. With
the algebraic chain in `HankelEdgeIntegrals.lean`, combining this
limit with the upper-edge limit gives the edge-difference value
`(1 - e^(2πi(s-1))) · Γ(s) = 2i · e^(iπ(s-1)) · sin(πs) · Γ(s)`.

Combined with `HankelSmallLoop.hankelSmallLoopBound_tendsto_zero`,
this closes the Hankel-integral identity:

  `∮_H t^(s-1) e^(-t) dt = 2πi / Γ(1-s)`

modulo the three explicit DCT/bound mathlib applications.
-/

end PrincipiaTractalis.Analytic
