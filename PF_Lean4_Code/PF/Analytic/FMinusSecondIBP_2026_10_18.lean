/-
# PF.Analytic.FMinusSecondIBP_2026_10_18

**The minus-side Tier-3 brick, and the second IBP on the `−` branch.**
Direct mirror of the plus side (`c026332a`, `999aa8a5`, `259687e9`, `164a9843`),
instantiating the template those built.

`F₋(u) = ω(eᵘ)`, so the derivatives are one factor shorter than the plus side's
(no `exp(u/2)` prefactor to differentiate):

  `F₋′(u)  = ω′(eᵘ)·eᵘ`                              (= what `F_minus_hasDerivAt` states)
  `F₋″(u)  = ω″(eᵘ)·eᵘ·eᵘ + ω′(eᵘ)·eᵘ`

both verified numerically before building.

### Majorants (Route 2, no sign lemma)

For `u ≥ 0` we have `eᵘ ≥ 1`, so the stage-2 bounds apply at `x = eᵘ`, with
`E = exp(−π·eᵘ) ≤ exp(−π)exp(−πu)`:

  `|F₋″(u)| ≤ (4π² + 2π)·E·e^{2u} ≤ 72·exp(−π)·exp(u(2 − π))`
  `|F₋′(u)| ≤ 2π·E·eᵘ            ≤ 8·exp(−π)·exp(u(1 − π))`

and `2 − π < 0`, `1 − π < 0`. Note the minus side decays *faster* than the plus
side (`2 − π` and `1 − π` against `5/2 − π` and `3/2 − π`), because it lacks the
`e^{u/2}` growth factor. Constants are again rounded so `Real.pi_le_four`
suffices.

### What was already done

Row 3 for this branch — `deriv F_minus 0 = ω′(1)` — landed with the plus-side
rows (`259687e9`, `deriv_F_minus_zero`), so it is reused here rather than
rebuilt.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-18.
-/
import PF.Analytic.Lambda0IBP2Identity_2026_10_18

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FMinusSecondIBP20261018

open Real MeasureTheory Set Topology Filter
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.OmegaDerivGeometricBounds20261018
open PrincipiaTractalis.FPlusSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondIBPRows20261018
open PrincipiaTractalis.Lambda0IBP2Identity20261018
open PrincipiaTractalis.Lambda0IBPIdentity20261015
open PrincipiaTractalis.OmegaDerivativeBounds20261015

noncomputable section

/-! ## §1 — The explicit first and second derivatives of `F_minus`. -/

/-- `F₋′(u) = ω′(eᵘ)·eᵘ`, exactly as `F_minus_hasDerivAt` states it. -/
def F_minus' (u : ℝ) : ℝ := omega' (Real.exp u) * Real.exp u

theorem deriv_F_minus_eq_F_minus' : deriv F_minus = F_minus' := by
  funext u
  exact (F_minus_hasDerivAt u).deriv

/-- `F₋″(u) = ω″(eᵘ)·eᵘ·eᵘ + ω′(eᵘ)·eᵘ`. -/
def F_minus'' (u : ℝ) : ℝ :=
  omega'' (Real.exp u) * Real.exp u * Real.exp u + omega' (Real.exp u) * Real.exp u

/-- **★ `HasDerivAt F_minus' (F_minus'' u) u`, for every `u` ★** -/
theorem F_minus'_hasDerivAt (u : ℝ) : HasDerivAt F_minus' (F_minus'' u) u := by
  have hexp : HasDerivAt Real.exp (Real.exp u) u := Real.hasDerivAt_exp u
  have homega'_exp : HasDerivAt (fun y : ℝ => omega' (Real.exp y))
      (omega'' (Real.exp u) * Real.exp u) u :=
    (omega'_hasDerivAt (Real.exp_pos u)).comp u hexp
  exact homega'_exp.mul hexp

theorem deriv_F_minus'_eq_F_minus'' : deriv F_minus' = F_minus'' := by
  funext u
  exact (F_minus'_hasDerivAt u).deriv

/-- **`deriv (deriv F_minus) = F_minus''`**. -/
theorem deriv_deriv_F_minus_eq : deriv (deriv F_minus) = F_minus'' := by
  rw [deriv_F_minus_eq_F_minus', deriv_F_minus'_eq_F_minus'']

/-! ## §2 — The two exponential majorants. -/

/-- **★ `|F₋″(u)| ≤ 72·exp(−π)·exp(u(2 − π))` for `u ≥ 0` ★** -/
theorem abs_F_minus''_le {u : ℝ} (hu : 0 ≤ u) :
    |F_minus'' u| ≤ 72 * Real.exp (-π) * Real.exp (u * (2 - π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have he1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  set E := Real.exp (-π * Real.exp u) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have heu : (0 : ℝ) < Real.exp u := Real.exp_pos _
  have hw' : |omega' (Real.exp u)| ≤ 2 * π * E := abs_omega'_le he1
  have hw'' : omega'' (Real.exp u) ≤ 4 * π ^ 2 * E := omega''_le he1
  have hw''_nn : 0 ≤ omega'' (Real.exp u) := omega''_nonneg _
  have h2u : Real.exp u * Real.exp u = Real.exp (u * 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have heu_le : Real.exp u ≤ Real.exp (u * 2) := by
    apply Real.exp_le_exp.mpr; linarith
  -- term A : ω″(eᵘ)·e^{2u}
  have hA : |omega'' (Real.exp u) * Real.exp u * Real.exp u|
      ≤ (4 * π ^ 2) * (E * Real.exp (u * 2)) := by
    rw [abs_of_nonneg (by positivity)]
    have hrw : omega'' (Real.exp u) * Real.exp u * Real.exp u
        = Real.exp (u * 2) * omega'' (Real.exp u) := by
      rw [show omega'' (Real.exp u) * Real.exp u * Real.exp u
          = omega'' (Real.exp u) * (Real.exp u * Real.exp u) from by ring, h2u]
      ring
    rw [hrw]
    have := mul_le_mul_of_nonneg_left hw'' (Real.exp_pos (u * 2)).le
    nlinarith [this]
  -- term B : ω′(eᵘ)·eᵘ
  have hB : |omega' (Real.exp u) * Real.exp u| ≤ (2 * π) * (E * Real.exp (u * 2)) := by
    have hfac : |omega' (Real.exp u) * Real.exp u|
        = Real.exp u * |omega' (Real.exp u)| := by
      rw [abs_mul, abs_of_pos heu]; ring
    rw [hfac]
    have h1 : Real.exp u * |omega' (Real.exp u)| ≤ Real.exp u * (2 * π * E) :=
      mul_le_mul_of_nonneg_left hw' heu.le
    nlinarith [h1, heu_le, hEpos, hπ]
  have hsum : |F_minus'' u| ≤ ((4 * π ^ 2) + 2 * π) * (E * Real.exp (u * 2)) := by
    unfold F_minus''
    calc |omega'' (Real.exp u) * Real.exp u * Real.exp u
            + omega' (Real.exp u) * Real.exp u|
        ≤ |omega'' (Real.exp u) * Real.exp u * Real.exp u|
          + |omega' (Real.exp u) * Real.exp u| := abs_add _ _
      _ ≤ ((4 * π ^ 2) + 2 * π) * (E * Real.exp (u * 2)) := by linarith [hA, hB]
  have hCle : (4 * π ^ 2 : ℝ) + 2 * π ≤ 72 := by
    nlinarith [Real.pi_le_four, Real.pi_pos]
  have hEle : E ≤ Real.exp (-π) * Real.exp (-π * u) := exp_neg_pi_exp_le hu
  have hprod : E * Real.exp (u * 2) ≤ Real.exp (-π) * Real.exp (u * (2 - π)) := by
    have hL : Real.exp (-π) * Real.exp (-π * u) * Real.exp (u * 2)
        = Real.exp (-π + -π * u + u * 2) := by rw [← Real.exp_add, ← Real.exp_add]
    have hR : Real.exp (-π) * Real.exp (u * (2 - π)) = Real.exp (-π + u * (2 - π)) := by
      rw [← Real.exp_add]
    have hfac : Real.exp (-π) * Real.exp (-π * u) * Real.exp (u * 2)
        = Real.exp (-π) * Real.exp (u * (2 - π)) := by rw [hL, hR]; congr 1; ring
    calc E * Real.exp (u * 2)
        ≤ (Real.exp (-π) * Real.exp (-π * u)) * Real.exp (u * 2) :=
          mul_le_mul_of_nonneg_right hEle (Real.exp_pos _).le
      _ = Real.exp (-π) * Real.exp (u * (2 - π)) := hfac
  have hPnn : (0 : ℝ) ≤ E * Real.exp (u * 2) := by positivity
  calc |F_minus'' u|
      ≤ ((4 * π ^ 2 : ℝ) + 2 * π) * (E * Real.exp (u * 2)) := hsum
    _ ≤ 72 * (E * Real.exp (u * 2)) := mul_le_mul_of_nonneg_right hCle hPnn
    _ ≤ 72 * (Real.exp (-π) * Real.exp (u * (2 - π))) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = 72 * Real.exp (-π) * Real.exp (u * (2 - π)) := by ring

/-- **★ `|F₋′(u)| ≤ 8·exp(−π)·exp(u(1 − π))` for `u ≥ 0` ★** -/
theorem abs_F_minus'_le {u : ℝ} (hu : 0 ≤ u) :
    |F_minus' u| ≤ 8 * Real.exp (-π) * Real.exp (u * (1 - π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have he1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  set E := Real.exp (-π * Real.exp u) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have heu : (0 : ℝ) < Real.exp u := Real.exp_pos _
  have hw' : |omega' (Real.exp u)| ≤ 2 * π * E := abs_omega'_le he1
  have hfac : |F_minus' u| = Real.exp u * |omega' (Real.exp u)| := by
    unfold F_minus'
    rw [abs_mul, abs_of_pos heu]; ring
  have heq : Real.exp u = Real.exp (u * 1) := by congr 1; ring
  have hb : |F_minus' u| ≤ (2 * π) * (E * Real.exp (u * 1)) := by
    rw [hfac]
    have h1 : Real.exp u * |omega' (Real.exp u)| ≤ Real.exp u * (2 * π * E) :=
      mul_le_mul_of_nonneg_left hw' heu.le
    rw [← heq]
    nlinarith [h1]
  have hCle : (2 * π : ℝ) ≤ 8 := by nlinarith [Real.pi_le_four]
  have hEle : E ≤ Real.exp (-π) * Real.exp (-π * u) := exp_neg_pi_exp_le hu
  have hprod : E * Real.exp (u * 1) ≤ Real.exp (-π) * Real.exp (u * (1 - π)) := by
    have hL : Real.exp (-π) * Real.exp (-π * u) * Real.exp (u * 1)
        = Real.exp (-π + -π * u + u * 1) := by rw [← Real.exp_add, ← Real.exp_add]
    have hR : Real.exp (-π) * Real.exp (u * (1 - π)) = Real.exp (-π + u * (1 - π)) := by
      rw [← Real.exp_add]
    have hfac2 : Real.exp (-π) * Real.exp (-π * u) * Real.exp (u * 1)
        = Real.exp (-π) * Real.exp (u * (1 - π)) := by rw [hL, hR]; congr 1; ring
    calc E * Real.exp (u * 1)
        ≤ (Real.exp (-π) * Real.exp (-π * u)) * Real.exp (u * 1) :=
          mul_le_mul_of_nonneg_right hEle (Real.exp_pos _).le
      _ = Real.exp (-π) * Real.exp (u * (1 - π)) := hfac2
  have hPnn : (0 : ℝ) ≤ E * Real.exp (u * 1) := by positivity
  calc |F_minus' u| ≤ (2 * π : ℝ) * (E * Real.exp (u * 1)) := hb
    _ ≤ 8 * (E * Real.exp (u * 1)) := mul_le_mul_of_nonneg_right hCle hPnn
    _ ≤ 8 * (Real.exp (-π) * Real.exp (u * (1 - π))) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = 8 * Real.exp (-π) * Real.exp (u * (1 - π)) := by ring

/-! ## §3 — Integrability of `F₋″` on `Ioi 0`. -/

/-- **★ `IntegrableOn F₋″ (Ioi 0)` ★** -/
theorem F_minus''_integrable_Ioi : IntegrableOn F_minus'' (Ioi (0 : ℝ)) := by
  have hcoeff : (2 - π : ℝ) < 0 := by linarith [Real.pi_gt_three]
  have hexp := integrableOn_exp_mul_Ioi (a := 2 - π) hcoeff 0
  have hbound : IntegrableOn
      (fun u : ℝ => 72 * Real.exp (-π) * Real.exp ((2 - π) * u)) (Ioi (0 : ℝ)) :=
    hexp.const_mul _
  have hmeas : AEStronglyMeasurable F_minus''
      (Measure.restrict volume (Ioi (0 : ℝ))) := by
    rw [← deriv_F_minus'_eq_F_minus'']
    exact aestronglyMeasurable_deriv F_minus' _
  refine hbound.mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with u hu
  have h := abs_F_minus''_le (le_of_lt (mem_Ioi.mp hu))
  rw [Real.norm_eq_abs]
  have hcomm : Real.exp (u * (2 - π)) = Real.exp ((2 - π) * u) := by rw [mul_comm]
  rw [hcomm] at h
  exact h

/-- `hF'int` for the minus-branch second IBP. -/
theorem integrableOn_deriv_deriv_F_minus :
    IntegrableOn (deriv (deriv F_minus)) (Ioi (0 : ℝ)) := by
  rw [deriv_deriv_F_minus_eq]
  exact F_minus''_integrable_Ioi

/-! ## §4 — The three rows for the minus branch. -/

/-- **★ Row 1: `Tendsto (deriv F_minus) atTop (𝓝 0)` ★** -/
theorem tendsto_deriv_F_minus_atTop_zero :
    Tendsto (deriv F_minus) atTop (nhds 0) := by
  rw [deriv_F_minus_eq_F_minus']
  have hc : (1 - π : ℝ) < 0 := by linarith [Real.pi_gt_three]
  have hmaj : Tendsto (fun u : ℝ => 8 * Real.exp (-π) * Real.exp (u * (1 - π)))
      atTop (nhds 0) := by
    have h := tendsto_exp_mul_const_atTop_zero hc
    have := h.const_mul (8 * Real.exp (-π))
    simpa using this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [Real.norm_eq_abs]
  exact abs_F_minus'_le hu

/-- `F₋′` is continuous on all of `ℝ`. -/
theorem continuous_F_minus' : Continuous F_minus' := by
  unfold F_minus'
  exact continuous_omega'_comp_exp.mul Real.continuous_exp

/-- **★ Row 2: `ContinuousWithinAt (deriv F_minus) (Ici 0) 0` ★** -/
theorem continuousWithinAt_deriv_F_minus_zero :
    ContinuousWithinAt (deriv F_minus) (Ici 0) 0 := by
  rw [deriv_F_minus_eq_F_minus']
  exact continuous_F_minus'.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)

/-- `hFderiv` for the minus-branch second IBP. -/
theorem hasDerivAt_deriv_F_minus (x : ℝ) (_hx : x ∈ Ioi (0 : ℝ)) :
    HasDerivAt (deriv F_minus) (deriv (deriv F_minus) x) x := by
  rw [deriv_F_minus_eq_F_minus', deriv_F_minus'_eq_F_minus'']
  exact F_minus'_hasDerivAt x

/-! ## §5 — The second IBP on the `−` branch. -/

/-- **★ Second IBP, minus branch ★**

With `c = −i·t/2`:
`∫ (deriv F₋)·e^{cu} = −ω′(1)/c − (1/c)∫ F₋″·e^{cu}`.

Row 3 (`deriv F_minus 0 = ω′(1)`) is reused from `259687e9`. -/
theorem ibp2_F_minus_branch {t : ℝ} (ht : t ≠ 0) :
    (∫ u in Ioi (0 : ℝ),
        ((deriv F_minus u : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)))
      = -(((omega' 1 : ℝ) : ℂ) / (-(Complex.I * ((t : ℂ) / 2))))
        - (1 / (-(Complex.I * ((t : ℂ) / 2))))
            * ∫ u in Ioi (0 : ℝ),
                ((F_minus'' u : ℝ) : ℂ)
                  * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)) := by
  have h := ibp_phase (F := deriv F_minus) (F' := deriv (deriv F_minus))
    (phase_minus_ne_zero ht) (re_phase_minus t)
    (fun x hx => hasDerivAt_deriv_F_minus x hx)
    continuousWithinAt_deriv_F_minus_zero
    tendsto_deriv_F_minus_atTop_zero
    (integrableOn_phase_of_integrableOn (re_phase_minus t) integrableOn_deriv_F_minus)
    (integrableOn_phase_of_integrableOn (re_phase_minus t)
      integrableOn_deriv_deriv_F_minus)
  rw [deriv_deriv_F_minus_eq] at h
  rw [deriv_F_minus_zero] at h
  exact h

/-- **★ The minus-branch decay ★**

Bounded by `(4/t²)·∫_{Ioi 0}|F₋″|`, the integral finite (§3) and independent
of `t` — the same one-extra-power-of-`t` gain as the plus branch. -/
theorem norm_ibp2_minus_remainder_le {t : ℝ} (ht : t ≠ 0) :
    ‖(1 / (-(Complex.I * ((t : ℂ) / 2))) ^ 2)
        * ∫ u in Ioi (0 : ℝ),
            ((F_minus'' u : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))‖
      ≤ (4 / t ^ 2) * ∫ u in Ioi (0 : ℝ), |F_minus'' u| := by
  have hcre := re_phase_minus t
  have hptwise : ∀ u : ℝ,
      ‖((F_minus'' u : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))‖ = |F_minus'' u| := by
    intro u
    rw [norm_mul, norm_exp_mul_ofReal hcre, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have hle : ‖∫ u in Ioi (0 : ℝ), ((F_minus'' u : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))‖
      ≤ ∫ u in Ioi (0 : ℝ), |F_minus'' u| := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    exact le_of_eq (integral_congr_ae (Filter.Eventually.of_forall hptwise))
  have hnormsq : ‖(1 : ℂ) / (-(Complex.I * ((t : ℂ) / 2))) ^ 2‖ = 4 / t ^ 2 := by
    rw [neg_pow, show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_mul]
    exact norm_inv_phase_sq ht
  rw [norm_mul, hnormsq]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end FMinusSecondIBP20261018
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.deriv_F_minus_eq_F_minus'
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.F_minus'_hasDerivAt
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.deriv_deriv_F_minus_eq
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.abs_F_minus''_le
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.abs_F_minus'_le
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.F_minus''_integrable_Ioi
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.integrableOn_deriv_deriv_F_minus
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.tendsto_deriv_F_minus_atTop_zero
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.continuous_F_minus'
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.continuousWithinAt_deriv_F_minus_zero
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.hasDerivAt_deriv_F_minus
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.ibp2_F_minus_branch
#print axioms PrincipiaTractalis.FMinusSecondIBP20261018.norm_ibp2_minus_remainder_le
