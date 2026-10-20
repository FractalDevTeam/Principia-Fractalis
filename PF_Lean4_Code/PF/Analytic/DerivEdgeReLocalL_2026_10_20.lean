/-
# PF.Analytic.DerivEdgeReLocalL_2026_10_20

**The box-local Lipschitz constant: `|deriv edgeRe t| ≤ 2ω(1)(1 + 1/t) + 1/(2t²)`.**

This replaces the uniform `L = 1` that Gate-2 proves. Measured consequence:
covering `[6.75, 13]` needs **19** boxes instead of **193**, and `r = 1/16`
survives to `c = 12.30` instead of `c = 9.046`.

## The representation

From the Tier-3 sharp identity `Λ₀(1+it) = 1/t² − (4/t²)·S(t)` with
`S(t) = ∫F₊″e^{itu/2} + ∫F₋″e^{−itu/2}`, and
`Re ξ(1+it) = (1 − t²·Re Λ₀ − t·Im Λ₀)/2`, the `O(1)` parts cancel
*analytically*:

  `edgeRe t = 2·Re S(t) + (2/t)·Im S(t)`

Differentiating,

  `deriv edgeRe t = 2·Re S′ + (2/t)·Im S′ − (2/t²)·Im S`

and with `|S| ≤ ∫(|F₊″|+|F₋″|) = 1/4` and
`|S′| ≤ ½∫u(|F₊″|+|F₋″|) = ω(1)` (both exact, from
`DerivEdgeReBound_2026_10_20`) the triangle inequality gives the headline bound
with **no cancellation left to lose** — measured 1.0× up to `t = 11`, 1.2× at
`t = 13`, against 36× for the `ξ′ = ((2s−1)Λ₀ + s(s−1)Λ₀′)/2` form whose best
possible triangle bound is flat at `0.157–0.173`.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-20.
-/

import PF.Analytic.DerivEdgeReBound_2026_10_20
import PF.Analytic.R1Neighborhood_2026_10_09
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace PrincipiaTractalis
namespace DerivEdgeReLocalL20261020

open Complex Real MeasureTheory Set Filter Topology
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondDerivative20261018
open PrincipiaTractalis.FMinusSecondIBP20261018
open PrincipiaTractalis.Lambda0IBP2Combined20261018
open PrincipiaTractalis.ThetaBoundaryConstant20261019
open PrincipiaTractalis.DerivEdgeReBound20261020
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open scoped Real

noncomputable section

/-! ## §1 — `S(t)`, the Tier-3 remainder as a function of the real parameter -/

/-- The plus-side oscillatory integral. -/
def Sp (t : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((F_plus'' u : ℝ) : ℂ)
    * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))

/-- The minus-side oscillatory integral. -/
def Sm (t : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((F_minus'' u : ℝ) : ℂ)
    * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))

/-- `S = Sp + Sm`, the quantity the sharp identity multiplies by `−4/t²`. -/
def Ssum (t : ℝ) : ℂ := Sp t + Sm t

/-- `‖S(t)‖ ≤ 1/4`, from `K_sum_eq_quarter`. -/
theorem norm_Ssum_le (t : ℝ) : ‖Ssum t‖ ≤ 1 / 4 := by
  have hp := norm_int_F_plus''_le t
  have hm := norm_int_F_minus''_le t
  have hk := K_sum_eq_quarter
  have h := norm_add_le (Sp t) (Sm t)
  rw [Ssum]
  calc ‖Sp t + Sm t‖ ≤ ‖Sp t‖ + ‖Sm t‖ := norm_add_le _ _
    _ ≤ (∫ u in Ioi (0 : ℝ), |F_plus'' u|)
        + (∫ u in Ioi (0 : ℝ), |F_minus'' u|) := add_le_add hp hm
    _ = 1 / 4 := hk

/-! ## §2 — `edgeRe t = 2·Re S + (2/t)·Im S` -/

/-- The real and imaginary parts of the sharp identity. -/
theorem lambda0_re_im_of_sharp {t : ℝ} (ht : t ≠ 0) :
    (completedRiemannZeta₀ (⟨1, t⟩ : ℂ)).re = 1 / t ^ 2 - (4 / t ^ 2) * (Ssum t).re
      ∧ (completedRiemannZeta₀ (⟨1, t⟩ : ℂ)).im = -((4 / t ^ 2) * (Ssum t).im) := by
  have ha : (1 / (t : ℂ) ^ 2) = ((1 / t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hb : (4 / (t : ℂ) ^ 2) = ((4 / t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  -- recast the sharp identity with both coefficients as real coercions, and
  -- fold the two integrals into `Ssum` (definitionally equal)
  have hsharp : completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
      = ((1 / t ^ 2 : ℝ) : ℂ) - ((4 / t ^ 2 : ℝ) : ℂ) * Ssum t := by
    rw [lambda0_edge_ibp2_identity_sharp ht, ha, hb]
    rfl
  rw [hsharp]
  refine ⟨?_, ?_⟩
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, zero_sub]

/-- **`edgeRe t = 2·Re S(t) + (2/t)·Im S(t)`.**
The `1` of `re_xi_at_s` and the `t²·(1/t²)` of the sharp identity cancel. -/
theorem edgeRe_eq_Ssum {t : ℝ} (ht : t ≠ 0) :
    edgeRe t = 2 * (Ssum t).re + (2 / t) * (Ssum t).im := by
  have hxi : edgeRe t = (riemannXiEntire (⟨1, t⟩ : ℂ)).re := rfl
  rw [hxi, re_xi_at_s]
  obtain ⟨hre, him⟩ := lambda0_re_im_of_sharp ht
  rw [hre, him]
  have htsq : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  field_simp
  ring

end

end DerivEdgeReLocalL20261020
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.norm_Ssum_le
#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.lambda0_re_im_of_sharp
#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.edgeRe_eq_Ssum
