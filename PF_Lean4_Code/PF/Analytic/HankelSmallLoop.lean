/-
# Hankel Contour: Small-Loop Estimate

The third (and final) analytic piece of the Hankel-contour deformation:
the integral around the small circle of radius `ε` near `0` vanishes as
`ε → 0⁺`, provided `Re s > 0`.

**Setup**: parameterize the small loop as `t(θ) = ε · e^(iθ)` for
`θ ∈ [−π+δ, π−δ]` (the full arc as `δ → 0`). The integrand is
`t^(s-1) · e^(-t)`, with the standard branch of `t^(s-1)`.

**Pointwise bound** on the loop: for `t = ε·e^(iθ)`,

  `|t^(s-1)| = |ε|^(Re s - 1) · e^(-Im s · θ) ≤ ε^(Re s - 1) · e^(|Im s|·π)`

(the second inequality uses `|θ| ≤ π`). Combined with `|e^(-t)| = e^(-Re t)
≤ e^|t| = e^ε`, the integrand modulus is bounded by

  `ε^(Re s - 1) · e^(|Im s|·π + ε)`.

**Arc-length bound**: the loop is a circular arc of length at most `2πε`,
so the integral magnitude is at most

  `2π · ε · ε^(Re s - 1) · e^(|Im s|·π + ε) = 2π · ε^(Re s) · e^(|Im s|·π + ε)`.

**Conclusion**: for `Re s > 0`, `ε^(Re s) → 0` as `ε → 0⁺` (the exp
factor stays bounded), so the bound tends to 0 and the small-loop
integral vanishes.

This file:
* Defines `hankelSmallLoopBound s ε := 2π · ε^(Re s) · e^(|Im s|·π + ε)`.
* **Proves axiom-clean**: `hankelSmallLoopBound s ε → 0` as `ε → 0⁺`
  for `Re s > 0`.

The integral itself, and the bound-by-integration step, is documented as
the open dominated-convergence application.

Stage L4 — Hankel small-loop estimate (analytic content).
-/

import PF.Analytic.HankelEdgeIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology Real

/-! ## The small-loop bound function -/

/-- **Small-loop bound**: `2π · ε^(Re s) · e^(|Im s|·π + ε)`.

    This is an upper bound on the magnitude of the small-circle integral
    `∮_{|t|=ε} t^(s-1) · e^(-t) dt` (with the standard branch of `t^(s-1)`).

    Derivation: arc-length `≤ 2πε`, integrand magnitude
    `≤ ε^(Re s - 1) · e^(|Im s|·π + ε)`, product gives this bound. -/
noncomputable def hankelSmallLoopBound (s : ℂ) (ε : ℝ) : ℝ :=
  2 * Real.pi * ε ^ s.re * Real.exp (|s.im| * Real.pi + ε)

/-! ## The bound vanishes as ε → 0⁺ (for Re s > 0) -/

/-- **Pure `rpow` factor tends to 0**: for `Re s > 0`,
    `ε ^ (Re s) → 0` as `ε → 0⁺`. -/
theorem rpow_re_tendsto_zero_of_pos {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun ε : ℝ => ε ^ s.re) (𝓝[>] 0) (𝓝 0) := by
  have h_cont : ContinuousAt (fun x : ℝ => x ^ s.re) 0 :=
    Real.continuousAt_rpow_const 0 s.re (Or.inr hs.le)
  have h_tend : Tendsto (fun x : ℝ => x ^ s.re) (𝓝 0)
                        (𝓝 ((0 : ℝ) ^ s.re)) := h_cont.tendsto
  rw [Real.zero_rpow hs.ne'] at h_tend
  exact h_tend.mono_left nhdsWithin_le_nhds

/-- **Exp factor stays bounded**: `Real.exp(|Im s|·π + ε) → exp(|Im s|·π)`
    as `ε → 0`. (Plain continuity.) -/
theorem exp_factor_tendsto {s : ℂ} :
    Tendsto (fun ε : ℝ => Real.exp (|s.im| * Real.pi + ε))
            (𝓝 0) (𝓝 (Real.exp (|s.im| * Real.pi))) := by
  have h_in : Tendsto (fun ε : ℝ => |s.im| * Real.pi + ε)
                      (𝓝 0) (𝓝 (|s.im| * Real.pi + 0)) := by
    exact (tendsto_const_nhds.add tendsto_id)
  simp at h_in
  exact (Real.continuous_exp.tendsto _).comp h_in

/-- **Main theorem: small-loop bound vanishes as ε → 0⁺**.

    For `Re s > 0`,

      `hankelSmallLoopBound s ε → 0`  as  `ε → 0⁺`.

    With the (open) bound-by-integration step linking
    `‖∮_{|t|=ε} t^(s-1) e^(-t) dt‖ ≤ hankelSmallLoopBound s ε`, this
    establishes that the small-loop contribution to the Hankel contour
    vanishes in the limit, leaving only the edge-difference integral. -/
theorem hankelSmallLoopBound_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun ε : ℝ => hankelSmallLoopBound s ε)
            (𝓝[>] 0) (𝓝 0) := by
  unfold hankelSmallLoopBound
  -- Split as product: (2π) · (ε^(Re s)) · (exp(|Im s|·π + ε))
  -- The middle factor → 0 (key), the others stay bounded.
  have h_rpow : Tendsto (fun ε : ℝ => ε ^ s.re) (𝓝[>] 0) (𝓝 0) :=
    rpow_re_tendsto_zero_of_pos hs
  have h_exp : Tendsto (fun ε : ℝ => Real.exp (|s.im| * Real.pi + ε))
                       (𝓝[>] 0) (𝓝 (Real.exp (|s.im| * Real.pi))) :=
    exp_factor_tendsto.mono_left nhdsWithin_le_nhds
  -- Product of "tends to 0" × "tends to bounded" is "tends to 0"
  have h_mid : Tendsto (fun ε : ℝ => ε ^ s.re * Real.exp (|s.im| * Real.pi + ε))
                       (𝓝[>] 0) (𝓝 (0 * Real.exp (|s.im| * Real.pi))) :=
    h_rpow.mul h_exp
  rw [zero_mul] at h_mid
  -- Multiply by constant 2π
  have h_const : Tendsto (fun ε : ℝ =>
        2 * Real.pi * (ε ^ s.re * Real.exp (|s.im| * Real.pi + ε)))
        (𝓝[>] 0) (𝓝 (2 * Real.pi * 0)) :=
    tendsto_const_nhds.mul h_mid
  rw [mul_zero] at h_const
  -- Match the goal form: associativity
  convert h_const using 1
  funext ε
  ring

/-! ## Open theorem: actual loop-integral bound

The substantive remaining analytic content:

```
theorem hankelSmallLoop_integral_norm_le_bound
    {s : ℂ} (hs : 0 < s.re) {ε : ℝ} (hε : 0 < ε) :
    ‖∫ θ in (-Real.pi)..(Real.pi),
       (hankelLoopZero ε θ)^(s - 1) *
       Complex.exp (-(hankelLoopZero ε θ)) *
       (deriv (hankelLoopZero ε) θ)‖ ≤
    hankelSmallLoopBound s ε
```

Proof sketch:

1. **Parameterize**: `hankelLoopZero ε θ = ε · e^(iθ)`.
   `deriv hankelLoopZero ε θ = i·ε·e^(iθ)`, so `|deriv| = ε`.

2. **Integrand magnitude**: for `t = ε·e^(iθ)`,
   ```
   |t^(s-1)| = ε^(Re s - 1) · e^(-Im s · θ) ≤ ε^(Re s - 1) · e^(|Im s|·π)
   |e^(-t)| = e^(-ε·cos θ) ≤ e^ε
   ```
   Hence the integrand `|f(θ)| ≤ ε · ε^(Re s - 1) · e^(|Im s|·π) · e^ε
                                = ε^(Re s) · e^(|Im s|·π + ε)`.

3. **Arc-length factor**: integrating over `θ ∈ [-π, π]` (length 2π):
   ```
   ‖∫₋π^π f(θ) dθ‖ ≤ ∫₋π^π |f(θ)| dθ ≤ 2π · ε^(Re s) · e^(|Im s|·π + ε)
                                       = hankelSmallLoopBound s ε.
   ```

4. **Apply** `intervalIntegral.norm_integral_le_of_norm_le_const` (or
   the un-constant version with the explicit pointwise bound).

The mathlib infrastructure:
- `intervalIntegral.norm_integral_le_*` — the integral-norm bound.
- `Complex.norm_cpow_eq_rpow_re_of_pos` — the cpow magnitude on positive
  reals; needs adaptation for complex moduli.
- Norms of `e^(iθ)` and `e^(complex)`, available throughout `Complex`.

Combined with `hankelSmallLoopBound_tendsto_zero` proven above, the
loop integral itself → 0 as ε → 0⁺ for `Re s > 0`. This closes the
small-loop analytic gap in the Hankel contour-deformation chain. -/

end PrincipiaTractalis.Analytic
