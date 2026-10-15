/-
# PF.Analytic.Lambda0DecayCeiling_2026_10_15

**THE DECAY CEILING — why the modulus route to `Re ξ(1+it) > 0` is closed.**

Rio's directive 2026-10-15, following the L4 identity
(`Lambda0IBPIdentity_2026_10_15`). This file banks, as machine-checked
theorems, the reason no sharpening of a `‖Λ₀‖` bound can ever certify
`Re ξ(1 + it) > 0` at large `t`.

## The mechanism

The second-order boundary term of the L4 identity is `F₊'(0) + F₋'(0)`, and
that sum is **exactly `−1/4`** — not approximately. The reason is the Jacobi
theta functional equation evaluated at its own *self-dual point* `x = 1`:

  `θ(1/x) = √x · θ(x)`  differentiated at `x = 1`  gives  `θ'(1) = −θ(1)/4`,

i.e. in terms of `ω` (where `θ = 1 + 2ω`):

  `ω'(1) = −(1 + 2ω(1))/8`.                       (`omega_deriv_one`)

Since `F₋'(0) = ω'(1)` and `F₊'(0) = ω(1)/2 + ω'(1)`, their sum collapses:

  `F₊'(0) + F₋'(0) = ω(1)/2 + 2ω'(1) = −1/4`.      (`deriv_F_sum_zero`)

Feeding that into L4 gives the leading asymptotic `Λ₀(1 + it) = 1/t² + O(1/t³)`
with leading constant **exactly 1**.

## Why that closes the route

`Re ξ(1+it) = (1 + Re[s(s−1)·Λ₀])/2`, so every argument of the shape "bound
`‖Λ₀‖`, then apply the triangle inequality" is limited by `|s(s−1)|·‖Λ₀‖`.
That product tends to **exactly 1** — the critical threshold — so the modulus
route lands precisely *on* `Re ξ ≥ 0` and can never reach a strict positive
bound. For the R1 gate, which needs `Mc_lb = 1/4` and hence
`|s(s−1)|·‖Λ₀‖ ≤ 1/2`, the shortfall is a factor of exactly 2.

`gate1_eventually_fails_of_threshold` states this. What saves `ξ` on the edge
is the *phase* of `s(s−1)Λ₀`, which the modulus route discards.

## Scope — read this before citing

* `omega_deriv_one` and `deriv_F_sum_zero` are UNCONDITIONAL and exact.
* `gate1_eventually_fails_of_threshold` is CONDITIONAL on the hypothesis
  `hlim : |s(s−1)·Λ₀(1+it)| → 1`. That limit is verified symbolically and
  numerically (30 digits: `t²|Λ₀|` = 0.99881 at `t = 20`, 0.99999988 at
  `t = 2000`) but is **not yet machine-checked here**.
  **Removal condition:** a second application of
  `Lambda0IBPIdentity20261015.ibp_phase` to `F₊'`/`F₋'` (needing `F''`
  integrability and `F' → 0` at infinity) plus mathlib's Riemann–Lebesgue
  (`Real.zero_at_infty_fourierIntegral`) discharges `hlim`; this file should
  then be edited to drop the hypothesis. Until then the conditional form is
  scaffolding, not the finished statement.
* This file claims NOTHING about open RH, and nothing about R1/R2/R3 coverage.
  It closes one proof route and says so.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-15.
-/

import PF.Analytic.Lambda0IBPIdentity_2026_10_15
import PF.Analytic.RiemannXiThetaBoxEnclosure_r331a

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0DecayCeiling20261015

open Complex Set MeasureTheory Filter Topology HurwitzZeta
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaDerivativeBounds20261015
open PrincipiaTractalis.Lambda0IBPIdentity20261015

noncomputable section

/-! ## §1 — the theta functional equation in `ω` form -/

/-- **The Jacobi functional equation, written for `ω`.** For `x > 0`:
`√x · (1 + 2ω(x)) = 1 + 2ω(1/x)`. This is mathlib's
`evenKernel_functional_equation` at `a = 0`, with both theta kernels rewritten
through PF's `evenKernel_zero_eq` / `cosKernel_zero_sub_one` bridges. -/
theorem omega_functional_equation {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * (1 + 2 * omega x) = 1 + 2 * omega (1 / x) := by
  have hinv : (0 : ℝ) < 1 / x := by positivity
  have hcos : cosKernel 0 (1 / x) = 1 + 2 * omega (1 / x) := by
    have h := cosKernel_zero_sub_one hinv
    linarith
  have hev : evenKernel 0 x = 1 + 2 * omega x := evenKernel_zero_eq hx
  have h := evenKernel_functional_equation 0 x
  rw [hev, hcos] at h
  have hs : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have hne : x ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  rw [h, hs]
  field_simp

/-! ## §2 — ★ the self-dual derivative identity ★ -/

/-- **★★★ `ω'(1) = −(1 + 2ω(1))/8` ★★★**

The theta functional equation differentiated at its own self-dual point
`x = 1`. Both sides of `omega_functional_equation` agree on a neighbourhood of
`1`, so their derivatives at `1` agree; evaluating each gives
`(1/2)(1 + 2ω(1)) + 2ω'(1) = −2ω'(1)`, which rearranges to the claim.

This single identity is what forces the leading constant of `Λ₀(1+it)` to be
exactly `1`, and hence what closes the modulus route. -/
theorem omega_deriv_one : omega' 1 = -(1 + 2 * omega 1) / 8 := by
  have hone : (0 : ℝ) < 1 := one_pos
  -- the two sides agree near 1
  have hEq : (fun x : ℝ => Real.sqrt x * (1 + 2 * omega x))
      =ᶠ[nhds (1 : ℝ)] (fun x : ℝ => 1 + 2 * omega (1 / x)) := by
    filter_upwards [eventually_gt_nhds hone] with x hx
    exact omega_functional_equation hx
  -- derivative of `√x · (1 + 2ω x)` at 1
  have hL : HasDerivAt (fun x : ℝ => Real.sqrt x * (1 + 2 * omega x))
      (1 / 2 * (1 + 2 * omega 1) + 2 * omega' 1) 1 := by
    have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt 1)) 1 :=
      Real.hasDerivAt_sqrt (by norm_num)
    have h2 : HasDerivAt (fun x : ℝ => 1 + 2 * omega x) (2 * omega' 1) 1 :=
      ((omega_hasDerivAt hone).const_mul 2).const_add 1
    have h := h1.mul h2
    simp only [Real.sqrt_one] at h
    convert h using 1
    ring
  -- derivative of `1 + 2ω(1/x)` at 1
  have hR : HasDerivAt (fun x : ℝ => 1 + 2 * omega (1 / x)) (-(2 * omega' 1)) 1 := by
    have h11 : ((1 : ℝ) / 1) = 1 := by norm_num
    have hinv : HasDerivAt (fun x : ℝ => 1 / x) (-1) 1 := by
      simpa [one_div] using hasDerivAt_inv (by norm_num : (1 : ℝ) ≠ 0)
    have hout : HasDerivAt omega (omega' ((1 : ℝ) / 1)) ((1 : ℝ) / 1) := by
      rw [h11]; exact omega_hasDerivAt hone
    have hcomp : HasDerivAt (fun x : ℝ => omega (1 / x))
        (omega' ((1 : ℝ) / 1) * (-1)) 1 := hout.comp 1 hinv
    rw [h11] at hcomp
    have h := (hcomp.const_mul 2).const_add 1
    convert h using 1
    ring
  have hkey := (hL.congr_of_eventuallyEq hEq.symm).unique hR
  linarith

/-! ## §3 — the boundary values of `F₊'`, `F₋'` at `0`, and their exact sum -/

/-- `F₋'(0) = ω'(1)`. -/
theorem deriv_F_minus_zero : deriv F_minus 0 = omega' 1 := by
  have h := F_minus_hasDerivAt 0
  rw [h.deriv]
  norm_num

/-- `F₊'(0) = ω(1)/2 + ω'(1)`. -/
theorem deriv_F_plus_zero : deriv F_plus 0 = omega 1 / 2 + omega' 1 := by
  have h := F_plus_hasDerivAt 0
  rw [h.deriv]
  norm_num
  ring

/-- **★★★★★ THE EXACT BOUNDARY SUM: `F₊'(0) + F₋'(0) = −1/4` ★★★★★**

Not approximately `−0.25` — exactly `−1/4`, forced by `omega_deriv_one`. This
is the second-order boundary term of the L4 identity, and the reason the
leading asymptotic constant of `Λ₀(1+it)` is exactly `1`. -/
theorem deriv_F_sum_zero : deriv F_plus 0 + deriv F_minus 0 = -(1 / 4) := by
  rw [deriv_F_plus_zero, deriv_F_minus_zero, omega_deriv_one]
  ring

/-! ## §4 — the threshold, and why the modulus route is closed -/

/-- The edge value of `ξ` in terms of `Λ₀`: `Re ξ(1+it) = (1 + Re[s(s−1)Λ₀])/2`.
This is the identity every modulus-bound argument factors through. -/
theorem re_xi_edge (t : ℝ) :
    (riemannXiEntire (⟨1, t⟩ : ℂ)).re
      = (1 + ((⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
            * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)).re) / 2 := by
  rw [re_xi_at_s 1 t]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

/-- **★★★ THE CEILING ★★★** — the modulus route cannot meet the R1 gate.

Let `B` be ANY modulus bound for `Λ₀` on the edge. If the critical product
`|s(s−1)·Λ₀(1+it)|` tends to `1` (hypothesis `hlim`; see the scope note in the
file header for its removal condition), then for all large `t` the R1 gate
requirement `|s(s−1)|·B t ≤ 1/2` is violated — by a factor approaching
exactly `2`.

So no sharpening of `B` — not a deeper IBP, not a better constant, not any
structural input — can certify the R1 gate at large `t`. The obstruction is
the true asymptotic constant, not slack in an estimate. -/
theorem gate1_eventually_fails_of_threshold
    {B : ℝ → ℝ}
    (hB : ∀ t : ℝ, ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ B t)
    (hlim : Tendsto
      (fun t : ℝ => ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖
        * ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖) atTop (nhds 1)) :
    ∀ᶠ t : ℝ in atTop,
      1 / 2 < ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖ * B t := by
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  have hev := hlim.eventually (eventually_gt_nhds hhalf)
  filter_upwards [hev] with t ht
  refine lt_of_lt_of_le ht ?_
  exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)

end

/-! ## §Axiom check -/

#print axioms omega_functional_equation
#print axioms omega_deriv_one
#print axioms deriv_F_minus_zero
#print axioms deriv_F_plus_zero
#print axioms deriv_F_sum_zero
#print axioms re_xi_edge
#print axioms gate1_eventually_fails_of_threshold

end Lambda0DecayCeiling20261015
end PrincipiaTractalis
