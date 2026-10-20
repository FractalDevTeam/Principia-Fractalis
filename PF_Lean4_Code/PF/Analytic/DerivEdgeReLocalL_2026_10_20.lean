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

/-! ## §3 — Pointwise derivative of the two phases, and `‖phase‖ = 1` -/

/-- `s ↦ (s : ℂ)` has derivative `1`. -/
private lemma hasDerivAt_ofReal (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  simpa using Complex.ofRealCLM.hasDerivAt (x := t)

private lemma norm_phase_plus (t u : ℝ) :
    ‖Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * ((t : ℂ) / 2) * (u : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  rw [hre, Real.exp_zero]

private lemma norm_phase_minus (t u : ℝ) :
    ‖Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  rw [hre, Real.exp_zero]

private lemma hasDerivAt_phase_plus (u t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * ((s : ℂ) / 2) * (u : ℂ)))
      (Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))
        * (Complex.I * (u : ℂ) / 2)) t := by
  have hg : HasDerivAt (fun s : ℝ => Complex.I * ((s : ℂ) / 2) * (u : ℂ))
      (Complex.I * (u : ℂ) / 2) t := by
    have h3 := (((hasDerivAt_ofReal t).div_const (2 : ℂ)).const_mul
      (Complex.I)).mul_const (u : ℂ)
    convert h3 using 1
    ring
  exact hg.cexp

private lemma hasDerivAt_phase_minus (u t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(Complex.I * ((s : ℂ) / 2)) * (u : ℂ)))
      (Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))
        * (-(Complex.I * (u : ℂ)) / 2)) t := by
  have hg : HasDerivAt (fun s : ℝ => -(Complex.I * ((s : ℂ) / 2)) * (u : ℂ))
      (-(Complex.I * (u : ℂ)) / 2) t := by
    have h3 := ((((hasDerivAt_ofReal t).div_const (2 : ℂ)).const_mul
      (Complex.I)).neg).mul_const (u : ℂ)
    convert h3 using 1
    ring
  exact hg.cexp

/-! ## §4 — Measurability and integrability -/

private lemma aesm_F_plus'' :
    AEStronglyMeasurable F_plus'' (volume.restrict (Ioi (0 : ℝ))) :=
  (integrableOn_deriv_deriv_F_plus.congr_fun
    (fun u _ => by rw [deriv_F_plus_eq_F_plus', deriv_F_plus'_eq_F_plus''])
    measurableSet_Ioi).aestronglyMeasurable

private lemma aesm_F_minus'' :
    AEStronglyMeasurable F_minus'' (volume.restrict (Ioi (0 : ℝ))) :=
  (integrableOn_deriv_deriv_F_minus.congr_fun
    (fun u _ => by rw [deriv_F_minus_eq_F_minus', deriv_F_minus'_eq_F_minus''])
    measurableSet_Ioi).aestronglyMeasurable

/-! ### Explicit continuity of the phase arguments

`continuity` blows the heartbeat budget on these (observed: `isDefEq` /
`whnf` timeouts at 1.6M), so they are given by hand. -/

private lemma cont_arg_plus (t : ℝ) :
    Continuous fun u : ℝ => Complex.I * ((t : ℂ) / 2) * (u : ℂ) :=
  continuous_const.mul Complex.continuous_ofReal

private lemma cont_arg_minus (t : ℝ) :
    Continuous fun u : ℝ => -(Complex.I * ((t : ℂ) / 2)) * (u : ℂ) :=
  continuous_const.mul Complex.continuous_ofReal

private lemma cont_Iu_half : Continuous fun u : ℝ => Complex.I * (u : ℂ) / 2 :=
  (continuous_const.mul Complex.continuous_ofReal).div_const 2

private lemma cont_negIu_half : Continuous fun u : ℝ => -(Complex.I * (u : ℂ)) / 2 :=
  ((continuous_const.mul Complex.continuous_ofReal).neg).div_const 2

private lemma integrableOn_cpx_plus (t : ℝ) :
    IntegrableOn (fun u : ℝ => ((F_plus'' u : ℝ) : ℂ)
      * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))) (Ioi 0) volume := by
  have hc : (0 : ℝ) < π - 5 / 2 := by linarith [Real.pi_gt_three]
  have hg : IntegrableOn (fun u : ℝ => (81 * Real.exp (-π))
      * Real.exp (-(π - 5 / 2) * u)) (Ioi 0) volume :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable aesm_F_plus'').mul
      (Complex.continuous_exp.comp (cont_arg_plus t)).aestronglyMeasurable
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (mem_Ioi.mp hu)
    rw [norm_mul, norm_phase_plus, mul_one, Complex.norm_real, Real.norm_eq_abs]
    calc |F_plus'' u| ≤ 81 * Real.exp (-π) * Real.exp (u * (5 / 2 - π)) :=
          abs_F_plus''_le hu0
      _ = 81 * Real.exp (-π) * Real.exp (-(π - 5 / 2) * u) := by ring_nf

private lemma integrableOn_cpx_minus (t : ℝ) :
    IntegrableOn (fun u : ℝ => ((F_minus'' u : ℝ) : ℂ)
      * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))) (Ioi 0) volume := by
  have hc : (0 : ℝ) < π - 2 := by linarith [Real.pi_gt_three]
  have hg : IntegrableOn (fun u : ℝ => (72 * Real.exp (-π))
      * Real.exp (-(π - 2) * u)) (Ioi 0) volume :=
    (exp_neg_integrableOn_Ioi 0 hc).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable aesm_F_minus'').mul
      (Complex.continuous_exp.comp (cont_arg_minus t)).aestronglyMeasurable
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (mem_Ioi.mp hu)
    rw [norm_mul, norm_phase_minus, mul_one, Complex.norm_real, Real.norm_eq_abs]
    calc |F_minus'' u| ≤ 72 * Real.exp (-π) * Real.exp (u * (2 - π)) :=
          abs_F_minus''_le hu0
      _ = 72 * Real.exp (-π) * Real.exp (-(π - 2) * u) := by ring_nf

/-- Half-weighted plus bound: `(u/2)·F₊″`, with `∫ = ω(1)/2`. -/
private def bP (u : ℝ) : ℝ := u / 2 * F_plus'' u
/-- Half-weighted minus bound. -/
private def bM (u : ℝ) : ℝ := u / 2 * F_minus'' u
/-- The common dominating function for the differentiation step. -/
private def dBound (u : ℝ) : ℝ := bP u + bM u

private lemma integrableOn_bP : IntegrableOn bP (Ioi 0) volume := by
  have hI := integrableOn_mul_F_plus''
  refine IntegrableOn.congr_fun (hI.const_mul (1 / 2 : ℝ)) (fun u _ => ?_)
    measurableSet_Ioi
  simp only [bP]; ring

private lemma integrableOn_bM : IntegrableOn bM (Ioi 0) volume := by
  have hI := integrableOn_mul_F_minus''
  refine IntegrableOn.congr_fun (hI.const_mul (1 / 2 : ℝ)) (fun u _ => ?_)
    measurableSet_Ioi
  simp only [bM]; ring

private lemma integrableOn_dBound : IntegrableOn dBound (Ioi 0) volume :=
  integrableOn_bP.add integrableOn_bM

private lemma integral_bP_eq : ∫ u in Ioi (0 : ℝ), bP u = omega 1 / 2 := by
  have hE := PrincipiaTractalis.DerivEdgeReBound20261020.integral_mul_F_plus''_eq
  have h : (∫ u in Ioi (0 : ℝ), bP u)
      = (1 / 2 : ℝ) * ∫ u in Ioi (0 : ℝ), u * F_plus'' u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    simp only [bP]; ring
  rw [h, hE]; ring

private lemma integral_bM_eq : ∫ u in Ioi (0 : ℝ), bM u = omega 1 / 2 := by
  have hE := PrincipiaTractalis.DerivEdgeReBound20261020.integral_mul_F_minus''_eq
  have h : (∫ u in Ioi (0 : ℝ), bM u)
      = (1 / 2 : ℝ) * ∫ u in Ioi (0 : ℝ), u * F_minus'' u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    simp only [bM]; ring
  rw [h, hE]; ring

/-! ## §5 — Dominated differentiation of `Sp`, `Sm`, `Ssum` -/

/-- Derivative of the plus-side integral. -/
def Sp' (t : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((F_plus'' u : ℝ) : ℂ)
    * (Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)) * (Complex.I * (u : ℂ) / 2))

/-- Derivative of the minus-side integral. -/
def Sm' (t : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((F_minus'' u : ℝ) : ℂ)
    * (Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))
        * (-(Complex.I * (u : ℂ)) / 2))

/-- `S′ = Sp′ + Sm′`. -/
def Ssum' (t : ℝ) : ℂ := Sp' t + Sm' t

private lemma bound_plus {t u : ℝ} (hu0 : 0 < u) :
    ‖((F_plus'' u : ℝ) : ℂ)
      * (Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))
          * (Complex.I * (u : ℂ) / 2))‖ ≤ bP u := by
  rw [norm_mul, norm_mul, norm_phase_plus, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnI : ‖Complex.I * (u : ℂ) / 2‖ = u / 2 := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hu0]
    norm_num
  rw [hnI, abs_F_plus''_eq hu0.le]
  simp only [bP]
  exact le_of_eq (mul_comm _ _)

private lemma bound_minus {t u : ℝ} (hu0 : 0 < u) :
    ‖((F_minus'' u : ℝ) : ℂ)
      * (Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))
          * (-(Complex.I * (u : ℂ)) / 2))‖ ≤ bM u := by
  rw [norm_mul, norm_mul, norm_phase_minus, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hnI : ‖-(Complex.I * (u : ℂ)) / 2‖ = u / 2 := by
    rw [norm_div, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hu0]
    norm_num
  rw [hnI, abs_F_minus''_eq hu0.le]
  simp only [bM]
  exact le_of_eq (mul_comm _ _)

/-- Stated in exactly the tool's conclusion shape, so no unification work is
needed; `Sp` / `Sp'` are then a one-step `rfl` away. -/
private lemma dom_plus (t : ℝ) :
    IntegrableOn (fun u : ℝ => ((F_plus'' u : ℝ) : ℂ)
        * (Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))
            * (Complex.I * (u : ℂ) / 2))) (Ioi 0) volume
      ∧ HasDerivAt
          (fun s : ℝ => ∫ u in Ioi (0 : ℝ), ((F_plus'' u : ℝ) : ℂ)
            * Complex.exp (Complex.I * ((s : ℂ) / 2) * (u : ℂ)))
          (∫ u in Ioi (0 : ℝ), ((F_plus'' u : ℝ) : ℂ)
            * (Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))
                * (Complex.I * (u : ℂ) / 2))) t := by
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (s : ℝ) (u : ℝ) => ((F_plus'' u : ℝ) : ℂ)
      * Complex.exp (Complex.I * ((s : ℂ) / 2) * (u : ℂ)))
    (F' := fun (s : ℝ) (u : ℝ) => ((F_plus'' u : ℝ) : ℂ)
      * (Complex.exp (Complex.I * ((s : ℂ) / 2) * (u : ℂ))
          * (Complex.I * (u : ℂ) / 2)))
    (ε := 1) (bound := dBound) (x₀ := t) one_pos
    (Filter.Eventually.of_forall
      (fun s => (integrableOn_cpx_plus s).aestronglyMeasurable))
    (integrableOn_cpx_plus t)
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable aesm_F_plus'').mul
      ((Complex.continuous_exp.comp (cont_arg_plus t)).mul
        cont_Iu_half).aestronglyMeasurable)
    ?_ integrableOn_dBound ?_
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    intro s _
    have hu0 : (0 : ℝ) < u := mem_Ioi.mp hu
    have hb := bound_plus (t := s) hu0
    have hm : (0 : ℝ) ≤ bM u :=
      mul_nonneg (by linarith) (F_minus''_nonneg hu0.le)
    simp only [dBound]
    linarith
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    refine Filter.Eventually.of_forall (fun u _ => ?_)
    intro s _
    exact (hasDerivAt_phase_plus u s).const_mul _

private lemma dom_minus (t : ℝ) :
    IntegrableOn (fun u : ℝ => ((F_minus'' u : ℝ) : ℂ)
        * (Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))
            * (-(Complex.I * (u : ℂ)) / 2))) (Ioi 0) volume
      ∧ HasDerivAt
          (fun s : ℝ => ∫ u in Ioi (0 : ℝ), ((F_minus'' u : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * ((s : ℂ) / 2)) * (u : ℂ)))
          (∫ u in Ioi (0 : ℝ), ((F_minus'' u : ℝ) : ℂ)
            * (Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))
                * (-(Complex.I * (u : ℂ)) / 2))) t := by
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (s : ℝ) (u : ℝ) => ((F_minus'' u : ℝ) : ℂ)
      * Complex.exp (-(Complex.I * ((s : ℂ) / 2)) * (u : ℂ)))
    (F' := fun (s : ℝ) (u : ℝ) => ((F_minus'' u : ℝ) : ℂ)
      * (Complex.exp (-(Complex.I * ((s : ℂ) / 2)) * (u : ℂ))
          * (-(Complex.I * (u : ℂ)) / 2)))
    (ε := 1) (bound := dBound) (x₀ := t) one_pos
    (Filter.Eventually.of_forall
      (fun s => (integrableOn_cpx_minus s).aestronglyMeasurable))
    (integrableOn_cpx_minus t)
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable aesm_F_minus'').mul
      ((Complex.continuous_exp.comp (cont_arg_minus t)).mul
        cont_negIu_half).aestronglyMeasurable)
    ?_ integrableOn_dBound ?_
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    intro s _
    have hu0 : (0 : ℝ) < u := mem_Ioi.mp hu
    have hb := bound_minus (t := s) hu0
    have hp : (0 : ℝ) ≤ bP u :=
      mul_nonneg (by linarith) (F_plus''_nonneg hu0.le)
    simp only [dBound]
    linarith
  · rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    refine Filter.Eventually.of_forall (fun u _ => ?_)
    intro s _
    exact (hasDerivAt_phase_minus u s).const_mul _

/-- **`HasDerivAt Ssum (Ssum′ t) t`.** -/
theorem hasDerivAt_Ssum (t : ℝ) : HasDerivAt Ssum (Ssum' t) t := by
  have hp : HasDerivAt Sp (Sp' t) t := (dom_plus t).2
  have hm : HasDerivAt Sm (Sm' t) t := (dom_minus t).2
  exact hp.add hm

/-- **`‖S′(t)‖ ≤ ω(1)`**, the weighted constant from `weighted_K_sum_eq`. -/
theorem norm_Ssum_prime_le (t : ℝ) : ‖Ssum' t‖ ≤ omega 1 := by
  have hp : ‖Sp' t‖ ≤ omega 1 / 2 := by
    have hb : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
        ‖((F_plus'' u : ℝ) : ℂ)
          * (Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))
              * (Complex.I * (u : ℂ) / 2))‖ ≤ bP u := by
      rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      exact Filter.Eventually.of_forall (fun u hu => bound_plus (mem_Ioi.mp hu))
    have h := norm_integral_le_of_norm_le integrableOn_bP hb
    rwa [integral_bP_eq] at h
  have hm : ‖Sm' t‖ ≤ omega 1 / 2 := by
    have hb : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
        ‖((F_minus'' u : ℝ) : ℂ)
          * (Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))
              * (-(Complex.I * (u : ℂ)) / 2))‖ ≤ bM u := by
      rw [ae_restrict_iff' (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      exact Filter.Eventually.of_forall (fun u hu => bound_minus (mem_Ioi.mp hu))
    have h := norm_integral_le_of_norm_le integrableOn_bM hb
    rwa [integral_bM_eq] at h
  calc ‖Ssum' t‖ ≤ ‖Sp' t‖ + ‖Sm' t‖ := norm_add_le _ _
    _ ≤ omega 1 / 2 + omega 1 / 2 := add_le_add hp hm
    _ = omega 1 := by ring

/-! ## §6 — Real and imaginary parts of a real-parameter derivative -/

/-- `Re` of a `HasDerivAt` in a real parameter: `Complex.reCLM` is a continuous
ℝ-linear map, so it composes with the Fréchet derivative. -/
private lemma hasDerivAt_re_of {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s : ℝ => (f s).re) f'.re t := by
  simpa using (Complex.reCLM.hasFDerivAt.comp t h.hasFDerivAt).hasDerivAt

/-- `Im` of a `HasDerivAt` in a real parameter. -/
private lemma hasDerivAt_im_of {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s : ℝ => (f s).im) f'.im t := by
  simpa using (Complex.imCLM.hasFDerivAt.comp t h.hasFDerivAt).hasDerivAt

/-! ## §7 — ★ THE BOX-LOCAL BOUND ★ -/

/-- `edgeRe` is differentiable at every `t > 0`, with
`deriv edgeRe t = 2·Re S′ + (2/t)·Im S′ − (2/t²)·Im S`. -/
theorem hasDerivAt_edgeRe {t : ℝ} (ht : 0 < t) :
    HasDerivAt edgeRe
      (2 * (Ssum' t).re + (2 / t) * (Ssum' t).im
        - (2 / t ^ 2) * (Ssum t).im) t := by
  have htne : t ≠ 0 := ne_of_gt ht
  have hre := hasDerivAt_re_of (hasDerivAt_Ssum t)
  have him := hasDerivAt_im_of (hasDerivAt_Ssum t)
  have hinv : HasDerivAt (fun s : ℝ => 2 / s) (-(2 / t ^ 2)) t := by
    have h0 : HasDerivAt (fun s : ℝ => s⁻¹) (-1 / t ^ 2) t := (hasDerivAt_id t).inv htne
    have h1 := h0.const_mul (2 : ℝ)
    have hfun : (fun s : ℝ => 2 * s⁻¹) = fun s : ℝ => 2 / s := by
      funext s; rw [div_eq_mul_inv]
    rw [hfun] at h1
    convert h1 using 1
    field_simp
  have hsum := (hre.const_mul (2 : ℝ)).add (hinv.mul him)
  have hEq : edgeRe =ᶠ[nhds t] fun s : ℝ => 2 * (Ssum s).re + (2 / s) * (Ssum s).im := by
    filter_upwards [eventually_ne_nhds htne] with s hs
    exact edgeRe_eq_Ssum hs
  have hfinal := hsum.congr_of_eventuallyEq hEq
  convert hfinal using 1
  ring

/-- **★ `|deriv edgeRe t| ≤ 2ω(1)(1 + 1/t) + 1/(2t²)` for `t > 0` ★**

The three terms do not cancel (measured 1.0×–1.2×), so the plain triangle
inequality is already near-optimal. -/
theorem abs_deriv_edgeRe_le {t : ℝ} (ht : 0 < t) :
    |deriv edgeRe t| ≤ 2 * omega 1 * (1 + 1 / t) + 1 / (2 * t ^ 2) := by
  rw [(hasDerivAt_edgeRe ht).deriv]
  have hS' := norm_Ssum_prime_le t
  have hS := norm_Ssum_le t
  have hre' : |(Ssum' t).re| ≤ omega 1 := le_trans (Complex.abs_re_le_norm _) hS'
  have him' : |(Ssum' t).im| ≤ omega 1 := le_trans (Complex.abs_im_le_norm _) hS'
  have him : |(Ssum t).im| ≤ 1 / 4 := le_trans (Complex.abs_im_le_norm _) hS
  have hinv_nn : (0 : ℝ) ≤ 2 / t := by positivity
  have hinv2_nn : (0 : ℝ) ≤ 2 / t ^ 2 := by positivity
  set X := 2 * (Ssum' t).re with hX
  set Y := (2 / t) * (Ssum' t).im with hY
  set Z := (2 / t ^ 2) * (Ssum t).im with hZ
  have h1 : |X| ≤ 2 * omega 1 := by
    rw [hX, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have h2 : |Y| ≤ (2 / t) * omega 1 := by
    rw [hY, abs_mul, abs_of_nonneg hinv_nn]
    exact mul_le_mul_of_nonneg_left him' hinv_nn
  have h3 : |Z| ≤ (2 / t ^ 2) * (1 / 4) := by
    rw [hZ, abs_mul, abs_of_nonneg hinv2_nn]
    exact mul_le_mul_of_nonneg_left him hinv2_nn
  have htri : |X + Y - Z| ≤ |X| + |Y| + |Z| := by
    have e : X + Y - Z = X + Y + (-Z) := by ring
    rw [e]
    calc |X + Y + (-Z)| ≤ |X + Y| + |(-Z)| := abs_add _ _
      _ ≤ (|X| + |Y|) + |Z| := by
          rw [abs_neg]
          linarith [abs_add X Y]
      _ = |X| + |Y| + |Z| := by ring
  have hfin : (2 : ℝ) * omega 1 + (2 / t) * omega 1 + (2 / t ^ 2) * (1 / 4)
      = 2 * omega 1 * (1 + 1 / t) + 1 / (2 * t ^ 2) := by
    field_simp
    ring
  linarith [htri, h1, h2, h3, hfin]

/-! ## §8 — The producer-facing form -/

/-- **`L₀ c = 2·ω(1)·(1 + 1/c) + 1/(2c²)`** — the box-local Lipschitz constant
as an explicit function of the box centre. Measured `0.096–0.110` on
`c ∈ [6.75, 13]`, against the uniform `L = 1` Gate-2 proves. -/
def L0 (c : ℝ) : ℝ := 2 * omega 1 * (1 + 1 / c) + 1 / (2 * c ^ 2)

/-- **★ The hypothesis `R1_box_centered_of_lb` wants, with `L := L0 (c − r)` ★**

`L₀` is decreasing in `c`, so its value at the box's **left** edge dominates the
whole box; that is the value the producer passes. -/
theorem deriv_edgeRe_le_on_box {c r : ℝ} (_hr : 0 ≤ r) (hc : r < c) :
    ∀ x ∈ Icc (c - r) (c + r), |deriv edgeRe x| ≤ L0 (c - r) := by
  intro x hx
  rw [mem_Icc] at hx
  have hlo : (0 : ℝ) < c - r := by linarith
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hlo hx.1
  refine le_trans (abs_deriv_edgeRe_le hxpos) ?_
  have h1 : 1 / x ≤ 1 / (c - r) := one_div_le_one_div_of_le hlo hx.1
  have h2 : 1 / (2 * x ^ 2) ≤ 1 / (2 * (c - r) ^ 2) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [hlo.le, hx.1]
  have homega : (0 : ℝ) ≤ omega 1 := omega_nonneg 1
  simp only [L0]
  nlinarith [h1, h2, homega]

end

end DerivEdgeReLocalL20261020
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.norm_Ssum_le
#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.lambda0_re_im_of_sharp
#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.edgeRe_eq_Ssum
#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.hasDerivAt_Ssum
#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.norm_Ssum_prime_le
#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.hasDerivAt_edgeRe
#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.abs_deriv_edgeRe_le
#print axioms PrincipiaTractalis.DerivEdgeReLocalL20261020.deriv_edgeRe_le_on_box
