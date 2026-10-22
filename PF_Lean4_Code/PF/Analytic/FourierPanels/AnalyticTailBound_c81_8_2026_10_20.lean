/-
# PF.Analytic.FourierPanels.AnalyticTailBound_c81_8_2026_10_20

**Analytic tail-bound companion** to the finite-segment Fourier panel pack
at `c = 81/8`.

Mirror of `AnalyticTailBound_c6_2026_10_15.lean`. The analytic argument
is c-independent since it uses `|cos|, |sin| ≤ 1` to drop the frequency
dependence.

**Truncation point.** `U = 5` (matching the c=6 case and the r120 case).

**Strategy.** For every `u ≥ 0`,

  `|nodeR_fourier_plus_at_c81_8_N3 u|  ≤ F_plus u + F_minus u`
  `|nodeR_fourier_minus_at_c81_8_N3 u| ≤ F_plus u + F_minus u`

because `omega_N3_at_exp u ≤ omega (exp u)` (the N = 3 truncation is a
partial sum of the nonneg `omega` series) and `|cos|, |sin| ≤ 1`.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

Emitted by codex/gen_box.py for c = 81/8 (2026-10-20). `c` enters the node
functions only through the phase cos((c/2)u) / sin((c/2)u), and every add-on
majorant discards it via |cos|,|sin| <= 1, so the three add-on constants are
c-independent: residue 7/10^7, analytic tail 12/10^8, omega-gap 1/10^21.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/
import PF.Analytic.FourierPanels.CoreDefs_c81_8_2026_10_16
import PF.Analytic.OmegaDerivativeBounds_2026_10_15
import PF.Analytic.FourierPanels.Seg01Range_c81_8_2026_10_16

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c81_8
namespace AnalyticTailBound

open Real MeasureTheory Set Topology Filter
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaDerivativeBounds20261015
open scoped Real

/-! ## §1 — `omega_N3_at_exp u ≤ omega (exp u)` -/

lemma omega_N3_at_exp_eq_partial_sum (u : ℝ) :
    omega_N3_at_exp u =
      ∑ n ∈ Finset.range 3, Real.exp (-π * ((n : ℝ) + 1) ^ 2 * Real.exp u) := by
  unfold omega_N3_at_exp
  simp [Finset.sum_range_succ]
  ring_nf

theorem omega_N3_at_exp_le_omega_exp (u : ℝ) :
    omega_N3_at_exp u ≤ omega (Real.exp u) := by
  have hu_pos : 0 < Real.exp u := Real.exp_pos u
  rw [omega_N3_at_exp_eq_partial_sum]
  have hterm_nn : ∀ n : ℕ, 0 ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * Real.exp u) :=
    fun _ => (Real.exp_pos _).le
  have hsum := summable_omega hu_pos
  exact hsum.sum_le_tsum (Finset.range 3) (fun n _ => hterm_nn n)

lemma omega_N3_at_exp_nonneg (u : ℝ) : 0 ≤ omega_N3_at_exp u := by
  unfold omega_N3_at_exp
  have h1 : 0 ≤ Real.exp (-(π * Real.exp u)) := (Real.exp_pos _).le
  have h2 : 0 ≤ Real.exp (-(4 * π * Real.exp u)) := (Real.exp_pos _).le
  have h3 : 0 ≤ Real.exp (-(9 * π * Real.exp u)) := (Real.exp_pos _).le
  linarith

/-! ## §2 — Pointwise bound on `nodeR_fourier_±_at_c81_8_N3` -/

theorem nodeR_fourier_plus_at_c81_8_N3_abs_le (u : ℝ) :
    |nodeR_fourier_plus_at_c81_8_N3 u| ≤ F_plus u + F_minus u := by
  unfold nodeR_fourier_plus_at_c81_8_N3 F_plus F_minus
  have h_half : u * (0.5 : ℝ) = u / 2 := by ring
  rw [h_half]
  have h_cos : |Real.cos ((5.0625 : ℝ) * u)| ≤ 1 := Real.abs_cos_le_one _
  have h_omega_N3_nn : 0 ≤ omega_N3_at_exp u := omega_N3_at_exp_nonneg u
  have h_exp_half_pos : 0 < Real.exp (u / 2) := Real.exp_pos _
  have h_factor_nn :
      0 ≤ Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by
    have := mul_nonneg h_exp_half_pos.le h_omega_N3_nn
    linarith
  rw [abs_mul]
  have h_abs_factor :
      |Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u|
      = Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u :=
    abs_of_nonneg h_factor_nn
  rw [h_abs_factor]
  have h_omega_N3_le : omega_N3_at_exp u ≤ omega (Real.exp u) :=
    omega_N3_at_exp_le_omega_exp u
  have h_plus_le :
      Real.exp (u / 2) * omega_N3_at_exp u ≤ Real.exp (u / 2) * omega (Real.exp u) :=
    mul_le_mul_of_nonneg_left h_omega_N3_le h_exp_half_pos.le
  have h_both_nn : 0 ≤ Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u :=
    h_factor_nn
  calc (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * |Real.cos ((5.0625 : ℝ) * u)|
      ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * 1 :=
        mul_le_mul_of_nonneg_left h_cos h_both_nn
    _ = Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by ring
    _ ≤ Real.exp (u / 2) * omega (Real.exp u) + omega (Real.exp u) := by
        linarith

theorem nodeR_fourier_minus_at_c81_8_N3_abs_le (u : ℝ) :
    |nodeR_fourier_minus_at_c81_8_N3 u| ≤ F_plus u + F_minus u := by
  unfold nodeR_fourier_minus_at_c81_8_N3 F_plus F_minus
  have h_half : u * (0.5 : ℝ) = u / 2 := by ring
  rw [h_half]
  have h_sin : |Real.sin ((5.0625 : ℝ) * u)| ≤ 1 := Real.abs_sin_le_one _
  have h_omega_N3_nn : 0 ≤ omega_N3_at_exp u := omega_N3_at_exp_nonneg u
  have h_exp_half_pos : 0 < Real.exp (u / 2) := Real.exp_pos _
  rw [abs_mul]
  have h_A_nn : 0 ≤ Real.exp (u / 2) * omega_N3_at_exp u :=
    mul_nonneg h_exp_half_pos.le h_omega_N3_nn
  have h_abs_sub_le :
      |Real.exp (u / 2) * omega_N3_at_exp u - omega_N3_at_exp u|
      ≤ Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by
    have := abs_sub (Real.exp (u / 2) * omega_N3_at_exp u) (omega_N3_at_exp u)
    rw [abs_of_nonneg h_A_nn, abs_of_nonneg h_omega_N3_nn] at this
    exact this
  have h_omega_N3_le : omega_N3_at_exp u ≤ omega (Real.exp u) :=
    omega_N3_at_exp_le_omega_exp u
  have h_plus_le :
      Real.exp (u / 2) * omega_N3_at_exp u ≤ Real.exp (u / 2) * omega (Real.exp u) :=
    mul_le_mul_of_nonneg_left h_omega_N3_le h_exp_half_pos.le
  calc |Real.exp (u / 2) * omega_N3_at_exp u - omega_N3_at_exp u| * |Real.sin ((5.0625 : ℝ) * u)|
      ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * |Real.sin ((5.0625 : ℝ) * u)| := by
        apply mul_le_mul_of_nonneg_right h_abs_sub_le
        exact abs_nonneg _
    _ ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * 1 := by
        apply mul_le_mul_of_nonneg_left h_sin
        linarith
    _ = Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by ring
    _ ≤ Real.exp (u / 2) * omega (Real.exp u) + omega (Real.exp u) := by
        linarith

/-! ## §3 — Integrability on `Ioi 5` -/

lemma F_plus_integrable_Ioi5 : IntegrableOn F_plus (Ioi (5 : ℝ)) :=
  F_plus_integrable_Ioi.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 5))

lemma F_minus_integrable_Ioi5 : IntegrableOn F_minus (Ioi (5 : ℝ)) :=
  F_minus_integrable_Ioi.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 5))

lemma F_plus_add_F_minus_integrable_Ioi5 :
    IntegrableOn (fun u : ℝ => F_plus u + F_minus u) (Ioi (5 : ℝ)) :=
  F_plus_integrable_Ioi5.add F_minus_integrable_Ioi5

theorem nodeR_fourier_plus_at_c81_8_N3_integrable_Ioi5 :
    IntegrableOn (fun u : ℝ => nodeR_fourier_plus_at_c81_8_N3 u) (Ioi (5 : ℝ)) := by
  have h_dom := F_plus_add_F_minus_integrable_Ioi5
  have h_meas : AEStronglyMeasurable
      (fun u : ℝ => nodeR_fourier_plus_at_c81_8_N3 u)
      (volume.restrict (Ioi (5 : ℝ))) :=
    (Seg01Range.nodeR_fourier_plus_at_c81_8_N3_continuous).aestronglyMeasurable.restrict
  refine h_dom.mono' h_meas ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (5 : ℝ)))]
    with u hu
  have hu0 : 0 ≤ u := by
    have : (5 : ℝ) < u := mem_Ioi.mp hu
    linarith
  rw [Real.norm_eq_abs]
  exact nodeR_fourier_plus_at_c81_8_N3_abs_le u

theorem nodeR_fourier_minus_at_c81_8_N3_integrable_Ioi5 :
    IntegrableOn (fun u : ℝ => nodeR_fourier_minus_at_c81_8_N3 u) (Ioi (5 : ℝ)) := by
  have h_dom := F_plus_add_F_minus_integrable_Ioi5
  have h_meas : AEStronglyMeasurable
      (fun u : ℝ => nodeR_fourier_minus_at_c81_8_N3 u)
      (volume.restrict (Ioi (5 : ℝ))) :=
    (Seg01Range.nodeR_fourier_minus_at_c81_8_N3_continuous).aestronglyMeasurable.restrict
  refine h_dom.mono' h_meas ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (5 : ℝ)))]
    with u hu
  have hu0 : 0 ≤ u := by
    have : (5 : ℝ) < u := mem_Ioi.mp hu
    linarith
  rw [Real.norm_eq_abs]
  exact nodeR_fourier_minus_at_c81_8_N3_abs_le u

/-! ## §4 — Tail integral bound: `|∫_{Ioi 5} f| ≤ 1` -/

noncomputable def tailDominator (u : ℝ) : ℝ :=
  (23 / 22 : ℝ) * Real.exp (-π) * Real.exp (u * (1 / 2 - π))
    + (23 / 22 : ℝ) * Real.exp (-π * u)

lemma tailDominator_integrable_Ioi : IntegrableOn tailDominator (Ioi (0 : ℝ)) := by
  unfold tailDominator
  have h_coeff : (1 / 2 - π : ℝ) < 0 := by linarith [Real.pi_gt_three]
  have h1 : IntegrableOn (fun u : ℝ => Real.exp ((1 / 2 - π) * u)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (a := 1 / 2 - π) (c := 0) h_coeff
  have h1' : IntegrableOn (fun u : ℝ => Real.exp (u * (1 / 2 - π))) (Ioi (0 : ℝ)) := by
    refine h1.congr_fun ?_ measurableSet_Ioi
    intro u _
    show Real.exp ((1 / 2 - π) * u) = Real.exp (u * (1 / 2 - π))
    rw [mul_comm]
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-π * u)) (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (a := -π) (c := 0) (by linarith [Real.pi_pos])
  exact (h1'.const_mul ((23 / 22 : ℝ) * Real.exp (-π))).add (h2.const_mul (23 / 22 : ℝ))

lemma tailDominator_integrable_Ioi5 : IntegrableOn tailDominator (Ioi (5 : ℝ)) :=
  tailDominator_integrable_Ioi.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 5))

lemma F_plus_add_F_minus_le_tailDominator {u : ℝ} (hu : 0 ≤ u) :
    F_plus u + F_minus u ≤ tailDominator u := by
  unfold tailDominator
  have h1 := F_plus_le_exp_bound hu
  have h2 := F_minus_le_exp_neg_pi_mul hu
  linarith

lemma integral_exp_mul_half_minus_pi_Ioi5 :
    ∫ u in Ioi (5 : ℝ), Real.exp (u * (1 / 2 - π))
      = Real.exp (5 * (1 / 2 - π)) / (π - 1 / 2) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h_coeff_pos : (0 : ℝ) < π - 1 / 2 := by linarith [Real.pi_gt_three]
  have h_coeff_neg : (1 / 2 - π : ℝ) < 0 := by linarith
  have h_coeff_ne : (1 / 2 - π : ℝ) ≠ 0 := ne_of_lt h_coeff_neg
  have h_pi_minus_half_ne : (π - 1 / 2 : ℝ) ≠ 0 := ne_of_gt h_coeff_pos
  have h_fun :
      (fun u : ℝ => Real.exp (u * (1 / 2 - π)))
      = (fun u : ℝ => Real.exp ((1 / 2 - π) * u)) := by
    ext u; rw [mul_comm]
  rw [h_fun]
  rw [integral_exp_mul_Ioi (a := 1 / 2 - π) (c := 5) h_coeff_neg]
  have h_arg : ((1 : ℝ) / 2 - π) * 5 = 5 * (1 / 2 - π) := by ring
  rw [h_arg]
  rw [neg_div, eq_comm, eq_neg_iff_add_eq_zero, div_add_div _ _ h_pi_minus_half_ne h_coeff_ne]
  rw [div_eq_zero_iff]
  left
  ring

lemma integral_exp_neg_pi_Ioi5 :
    ∫ u in Ioi (5 : ℝ), Real.exp (-π * u) = Real.exp (-5 * π) / π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h_neg : (-π : ℝ) < 0 := by linarith
  have h_neg_ne : (-π : ℝ) ≠ 0 := ne_of_lt h_neg
  have h_pi_ne : (π : ℝ) ≠ 0 := ne_of_gt hπ
  rw [integral_exp_mul_Ioi (a := -π) (c := 5) h_neg]
  have h_arg : (-π * 5 : ℝ) = -5 * π := by ring
  rw [h_arg]
  rw [neg_div, eq_comm, eq_neg_iff_add_eq_zero, div_add_div _ _ h_pi_ne h_neg_ne]
  rw [div_eq_zero_iff]
  left
  ring

lemma integral_tailDominator_Ioi5 :
    ∫ u in Ioi (5 : ℝ), tailDominator u
      = (23 / 22) * Real.exp (-π) * (Real.exp (5 * (1 / 2 - π)) / (π - 1 / 2))
        + (23 / 22) * (Real.exp (-5 * π) / π) := by
  unfold tailDominator
  have h_coeff_pos : (0 : ℝ) < π - 1 / 2 := by linarith [Real.pi_gt_three]
  have h_coeff_neg : (1 / 2 - π : ℝ) < 0 := by linarith
  have h_neg_pi : (-π : ℝ) < 0 := by linarith [Real.pi_pos]
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (u * (1 / 2 - π))) (Ioi (5 : ℝ)) := by
    have h_fun :
        (fun u : ℝ => Real.exp (u * (1 / 2 - π)))
        = (fun u : ℝ => Real.exp ((1 / 2 - π) * u)) := by
      ext u; rw [mul_comm]
    rw [h_fun]
    exact integrableOn_exp_mul_Ioi (a := 1 / 2 - π) (c := 5) h_coeff_neg
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-π * u)) (Ioi (5 : ℝ)) :=
    integrableOn_exp_mul_Ioi (a := -π) (c := 5) h_neg_pi
  have h1c : IntegrableOn
      (fun u : ℝ => (23 / 22 : ℝ) * Real.exp (-π) * Real.exp (u * (1 / 2 - π))) (Ioi (5 : ℝ)) :=
    h1.const_mul ((23 / 22 : ℝ) * Real.exp (-π))
  have h2c : IntegrableOn
      (fun u : ℝ => (23 / 22 : ℝ) * Real.exp (-π * u)) (Ioi (5 : ℝ)) :=
    h2.const_mul (23 / 22)
  rw [MeasureTheory.integral_add h1c h2c]
  congr 1
  · rw [show (fun u : ℝ => (23 / 22 : ℝ) * Real.exp (-π) * Real.exp (u * (1 / 2 - π)))
        = (fun u : ℝ => ((23 / 22 : ℝ) * Real.exp (-π)) * Real.exp (u * (1 / 2 - π))) from rfl]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_exp_mul_half_minus_pi_Ioi5]
  · rw [MeasureTheory.integral_const_mul]
    rw [integral_exp_neg_pi_Ioi5]

lemma integral_tailDominator_Ioi5_le_one :
    ∫ u in Ioi (5 : ℝ), tailDominator u ≤ 1 := by
  rw [integral_tailDominator_Ioi5]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ_gt_3 : (3 : ℝ) < π := Real.pi_gt_three
  have h_coeff_pos : (0 : ℝ) < π - 1 / 2 := by linarith
  have h_exp_neg_pi_le_1 : Real.exp (-π) ≤ 1 := by
    have h : Real.exp (-π) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_zero] at h
  have h_exp_5c_le_1 : Real.exp (5 * (1 / 2 - π)) ≤ 1 := by
    have h : Real.exp (5 * (1 / 2 - π)) ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rwa [Real.exp_zero] at h
  have h_exp_neg5pi_le_1 : Real.exp (-5 * π) ≤ 1 := by
    have h : Real.exp (-5 * π) ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rwa [Real.exp_zero] at h
  have h_exp_neg_pi_pos : 0 < Real.exp (-π) := Real.exp_pos _
  have h_exp_5c_pos : 0 < Real.exp (5 * (1 / 2 - π)) := Real.exp_pos _
  have h_exp_neg5pi_pos : 0 < Real.exp (-5 * π) := Real.exp_pos _
  have h_t1_num_le :
      (23 / 22 : ℝ) * Real.exp (-π) * Real.exp (5 * (1 / 2 - π)) ≤ 23 / 22 := by
    have h_mul : Real.exp (-π) * Real.exp (5 * (1 / 2 - π)) ≤ 1 := by
      calc Real.exp (-π) * Real.exp (5 * (1 / 2 - π))
          ≤ 1 * 1 := by
            apply mul_le_mul h_exp_neg_pi_le_1 h_exp_5c_le_1 h_exp_5c_pos.le (by norm_num)
        _ = 1 := by norm_num
    nlinarith [h_mul]
  have h_t1_le :
      (23 / 22 : ℝ) * Real.exp (-π) * (Real.exp (5 * (1 / 2 - π)) / (π - 1 / 2))
      ≤ (23 / 22) / (π - 1 / 2) := by
    rw [show ((23 / 22 : ℝ) * Real.exp (-π) * (Real.exp (5 * (1 / 2 - π)) / (π - 1 / 2)))
          = ((23 / 22) * Real.exp (-π) * Real.exp (5 * (1 / 2 - π))) / (π - 1 / 2) by ring]
    exact div_le_div_of_nonneg_right h_t1_num_le h_coeff_pos.le
  have h_t2_le :
      (23 / 22 : ℝ) * (Real.exp (-5 * π) / π) ≤ (23 / 22) / π := by
    rw [show ((23 / 22 : ℝ) * (Real.exp (-5 * π) / π)) = ((23/22) * Real.exp (-5*π)) / π by ring]
    apply div_le_div_of_nonneg_right _ hπ.le
    nlinarith [h_exp_neg5pi_le_1]
  have h_pi_minus_half_ge : (5 / 2 : ℝ) ≤ π - 1 / 2 := by linarith
  have h_pi_ge_3 : (3 : ℝ) ≤ π := le_of_lt hπ_gt_3
  have h_inv_1 : (1 : ℝ) / (π - 1 / 2) ≤ 2 / 5 := by
    rw [div_le_div_iff₀ h_coeff_pos (by norm_num : (0:ℝ) < 5)]
    linarith
  have h_inv_2 : (1 : ℝ) / π ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hπ (by norm_num : (0:ℝ) < 3)]
    linarith
  have h_sum_le :
      (23 / 22 : ℝ) / (π - 1 / 2) + (23 / 22) / π ≤ (23 / 22) * (2 / 5) + (23 / 22) * (1 / 3) := by
    have h_a : (23 / 22 : ℝ) / (π - 1 / 2) = (23 / 22) * (1 / (π - 1 / 2)) := by ring
    have h_b : (23 / 22 : ℝ) / π = (23 / 22) * (1 / π) := by ring
    rw [h_a, h_b]
    have h_coeff_nn : (0 : ℝ) ≤ 23 / 22 := by norm_num
    have := mul_le_mul_of_nonneg_left h_inv_1 h_coeff_nn
    have := mul_le_mul_of_nonneg_left h_inv_2 h_coeff_nn
    linarith
  have h_rhs_le_1 : (23 / 22 : ℝ) * (2 / 5) + (23 / 22) * (1 / 3) ≤ 1 := by norm_num
  linarith

theorem nodeR_fourier_plus_at_c81_8_N3_tail_integral_abs_le :
    |∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c81_8_N3 u| ≤ 1 := by
  have h_int := nodeR_fourier_plus_at_c81_8_N3_integrable_Ioi5
  have h_dom_int := tailDominator_integrable_Ioi5
  have h_abs_le_abs :
      |∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c81_8_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_plus_at_c81_8_N3 u| :=
    MeasureTheory.abs_integral_le_integral_abs
  have h_abs_le_dom :
      ∫ u in Ioi (5 : ℝ), |nodeR_fourier_plus_at_c81_8_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := by
    refine MeasureTheory.setIntegral_mono_on h_int.abs h_dom_int measurableSet_Ioi ?_
    intro u hu
    have hu0 : 0 ≤ u := by
      have := mem_Ioi.mp hu; linarith
    have h1 := nodeR_fourier_plus_at_c81_8_N3_abs_le u
    have h2 := F_plus_add_F_minus_le_tailDominator hu0
    linarith
  calc |∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c81_8_N3 u|
      ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_plus_at_c81_8_N3 u| := h_abs_le_abs
    _ ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := h_abs_le_dom
    _ ≤ 1 := integral_tailDominator_Ioi5_le_one

theorem nodeR_fourier_minus_at_c81_8_N3_tail_integral_abs_le :
    |∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c81_8_N3 u| ≤ 1 := by
  have h_int := nodeR_fourier_minus_at_c81_8_N3_integrable_Ioi5
  have h_dom_int := tailDominator_integrable_Ioi5
  have h_abs_le_abs :
      |∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c81_8_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_minus_at_c81_8_N3 u| :=
    MeasureTheory.abs_integral_le_integral_abs
  have h_abs_le_dom :
      ∫ u in Ioi (5 : ℝ), |nodeR_fourier_minus_at_c81_8_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := by
    refine MeasureTheory.setIntegral_mono_on h_int.abs h_dom_int measurableSet_Ioi ?_
    intro u hu
    have hu0 : 0 ≤ u := by
      have := mem_Ioi.mp hu; linarith
    have h1 := nodeR_fourier_minus_at_c81_8_N3_abs_le u
    have h2 := F_plus_add_F_minus_le_tailDominator hu0
    linarith
  calc |∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c81_8_N3 u|
      ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_minus_at_c81_8_N3 u| := h_abs_le_abs
    _ ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := h_abs_le_dom
    _ ≤ 1 := integral_tailDominator_Ioi5_le_one

/-! ## §5 — Tight tail bound: `|∫_{Ioi 5} f| ≤ 1/10⁶` -/

open PrincipiaTractalis.Lambda0TightestBoundsMellin20261014

lemma exp_neg_five_pi_le : Real.exp (-5 * π) ≤ 1 / 6436343 := by
  have h : Real.exp (-5 * π) = (Real.exp (-π)) ^ 5 := by
    rw [← Real.exp_nat_mul (-π) 5]
    congr 1; push_cast; ring
  rw [h]
  have hbase : Real.exp (-π) ≤ 1 / 23 := exp_neg_pi_le_one_twentythird
  have hbase_nn : 0 ≤ Real.exp (-π) := (Real.exp_pos _).le
  have hpow : (Real.exp (-π)) ^ 5 ≤ (1 / 23 : ℝ) ^ 5 :=
    pow_le_pow_left₀ hbase_nn hbase 5
  have hrhs : ((1 : ℝ) / 23) ^ 5 = 1 / 6436343 := by norm_num
  linarith [hpow, hrhs.le]

lemma exp_neg_pi_mul_exp_5_half_sub_pi_le :
    Real.exp (-π) * Real.exp (5 * (1 / 2 - π)) ≤ 1 / 6436343 := by
  have h_combine :
      Real.exp (-π) * Real.exp (5 * (1 / 2 - π))
        = Real.exp (5 / 2 - 6 * π) := by
    rw [← Real.exp_add]
    congr 1; ring
  rw [h_combine]
  have hπ_ge : (5 / 2 : ℝ) ≤ π := by
    have hπ : (3.14 : ℝ) < π := Real.pi_gt_d2
    linarith
  have h_arg_le : (5 / 2 - 6 * π : ℝ) ≤ -5 * π := by linarith
  have h_exp_mono : Real.exp (5 / 2 - 6 * π) ≤ Real.exp (-5 * π) :=
    Real.exp_le_exp.mpr h_arg_le
  exact h_exp_mono.trans exp_neg_five_pi_le

lemma integral_tailDominator_Ioi5_le_tight :
    ∫ u in Ioi (5 : ℝ), tailDominator u ≤ 12 / 10 ^ 8 := by
  rw [integral_tailDominator_Ioi5]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ_d2 : (3.14 : ℝ) < π := Real.pi_gt_d2
  have h_coeff_pos : (0 : ℝ) < π - 1 / 2 := by linarith
  have h_exp_neg_pi_pos : 0 < Real.exp (-π) := Real.exp_pos _
  have h_exp_5c_pos : 0 < Real.exp (5 * (1 / 2 - π)) := Real.exp_pos _
  have h_exp_neg5pi_pos : 0 < Real.exp (-5 * π) := Real.exp_pos _
  have h_exp5pi_le : Real.exp (-5 * π) ≤ 1 / 6436343 := exp_neg_five_pi_le
  have h_combined_le :
      Real.exp (-π) * Real.exp (5 * (1 / 2 - π)) ≤ 1 / 6436343 :=
    exp_neg_pi_mul_exp_5_half_sub_pi_le
  have h_pi_minus_half_ge : (132 / 50 : ℝ) ≤ π - 1 / 2 := by linarith
  have h_pi_ge : (157 / 50 : ℝ) ≤ π := by linarith
  have h_t1_le :
      (23 / 22 : ℝ) * Real.exp (-π) * (Real.exp (5 * (1 / 2 - π)) / (π - 1 / 2))
        ≤ (23 / 22) * (1 / 6436343) / (132 / 50) := by
    have h_rewrite :
        (23 / 22 : ℝ) * Real.exp (-π) * (Real.exp (5 * (1 / 2 - π)) / (π - 1 / 2))
          = (23 / 22) * (Real.exp (-π) * Real.exp (5 * (1 / 2 - π))) / (π - 1 / 2) := by
      ring
    rw [h_rewrite]
    have h_num_nn : 0 ≤ (23 / 22 : ℝ) * (Real.exp (-π) * Real.exp (5 * (1 / 2 - π))) := by
      have := mul_pos h_exp_neg_pi_pos h_exp_5c_pos
      positivity
    have h_num_le :
        (23 / 22 : ℝ) * (Real.exp (-π) * Real.exp (5 * (1 / 2 - π)))
          ≤ (23 / 22) * (1 / 6436343) := by
      have h_coeff_nn : (0 : ℝ) ≤ 23 / 22 := by norm_num
      exact mul_le_mul_of_nonneg_left h_combined_le h_coeff_nn
    have h_denom_pos : (0 : ℝ) < 132 / 50 := by norm_num
    have h_inv_le : (1 : ℝ) / (π - 1 / 2) ≤ 1 / (132 / 50) :=
      one_div_le_one_div_of_le h_denom_pos h_pi_minus_half_ge
    have h_rhs_pos : (0 : ℝ) < 132 / 50 := h_denom_pos
    have h_num_rhs_nn : 0 ≤ (23 / 22 : ℝ) * (1 / 6436343) := by norm_num
    calc (23 / 22 : ℝ) * (Real.exp (-π) * Real.exp (5 * (1 / 2 - π))) / (π - 1 / 2)
        = (23 / 22) * (Real.exp (-π) * Real.exp (5 * (1 / 2 - π))) * (1 / (π - 1 / 2)) := by
            rw [div_eq_mul_one_div]
      _ ≤ (23 / 22) * (1 / 6436343) * (1 / (π - 1 / 2)) := by
            apply mul_le_mul_of_nonneg_right h_num_le
            exact div_nonneg (by norm_num) h_coeff_pos.le
      _ ≤ (23 / 22) * (1 / 6436343) * (1 / (132 / 50)) := by
            apply mul_le_mul_of_nonneg_left h_inv_le h_num_rhs_nn
      _ = (23 / 22) * (1 / 6436343) / (132 / 50) := by ring
  have h_t2_le :
      (23 / 22 : ℝ) * (Real.exp (-5 * π) / π)
        ≤ (23 / 22) * (1 / 6436343) / (157 / 50) := by
    have h_rewrite :
        (23 / 22 : ℝ) * (Real.exp (-5 * π) / π)
          = (23 / 22) * Real.exp (-5 * π) / π := by ring
    rw [h_rewrite]
    have h_num_le :
        (23 / 22 : ℝ) * Real.exp (-5 * π) ≤ (23 / 22) * (1 / 6436343) := by
      have h_coeff_nn : (0 : ℝ) ≤ 23 / 22 := by norm_num
      exact mul_le_mul_of_nonneg_left h_exp5pi_le h_coeff_nn
    have h_denom_pos : (0 : ℝ) < 157 / 50 := by norm_num
    have h_inv_le : (1 : ℝ) / π ≤ 1 / (157 / 50) :=
      one_div_le_one_div_of_le h_denom_pos h_pi_ge
    have h_num_rhs_nn : 0 ≤ (23 / 22 : ℝ) * (1 / 6436343) := by norm_num
    have h_num_lhs_nn : 0 ≤ (23 / 22 : ℝ) * Real.exp (-5 * π) :=
      mul_nonneg (by norm_num) h_exp_neg5pi_pos.le
    calc (23 / 22 : ℝ) * Real.exp (-5 * π) / π
        = (23 / 22) * Real.exp (-5 * π) * (1 / π) := by rw [div_eq_mul_one_div]
      _ ≤ (23 / 22) * (1 / 6436343) * (1 / π) := by
            apply mul_le_mul_of_nonneg_right h_num_le
            exact div_nonneg (by norm_num) hπ.le
      _ ≤ (23 / 22) * (1 / 6436343) * (1 / (157 / 50)) := by
            apply mul_le_mul_of_nonneg_left h_inv_le h_num_rhs_nn
      _ = (23 / 22) * (1 / 6436343) / (157 / 50) := by ring
  have h_rhs1 : (23 / 22 : ℝ) * (1 / 6436343) / (132 / 50)
                = 1150 / (2904 * 6436343) := by norm_num
  have h_rhs2 : (23 / 22 : ℝ) * (1 / 6436343) / (157 / 50)
                = 1150 / (3454 * 6436343) := by norm_num
  have h_sum_le_rat :
      (23 / 22 : ℝ) * Real.exp (-π) * (Real.exp (5 * (1 / 2 - π)) / (π - 1 / 2))
        + (23 / 22) * (Real.exp (-5 * π) / π)
      ≤ 1150 / (2904 * 6436343) + 1150 / (3454 * 6436343) := by
    have h1 := h_t1_le
    have h2 := h_t2_le
    rw [h_rhs1] at h1
    rw [h_rhs2] at h2
    linarith
  have h_rat_le : (1150 : ℝ) / (2904 * 6436343) + 1150 / (3454 * 6436343) ≤ 12 / 10 ^ 8 := by
    norm_num
  linarith

theorem nodeR_fourier_plus_at_c81_8_N3_tail_integral_abs_le_tight :
    |∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c81_8_N3 u| ≤ 12 / 10 ^ 8 := by
  have h_int := nodeR_fourier_plus_at_c81_8_N3_integrable_Ioi5
  have h_dom_int := tailDominator_integrable_Ioi5
  have h_abs_le_abs :
      |∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c81_8_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_plus_at_c81_8_N3 u| :=
    MeasureTheory.abs_integral_le_integral_abs
  have h_abs_le_dom :
      ∫ u in Ioi (5 : ℝ), |nodeR_fourier_plus_at_c81_8_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := by
    refine MeasureTheory.setIntegral_mono_on h_int.abs h_dom_int measurableSet_Ioi ?_
    intro u hu
    have hu0 : 0 ≤ u := by
      have := mem_Ioi.mp hu; linarith
    have h1 := nodeR_fourier_plus_at_c81_8_N3_abs_le u
    have h2 := F_plus_add_F_minus_le_tailDominator hu0
    linarith
  calc |∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c81_8_N3 u|
      ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_plus_at_c81_8_N3 u| := h_abs_le_abs
    _ ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := h_abs_le_dom
    _ ≤ 12 / 10 ^ 8 := integral_tailDominator_Ioi5_le_tight

theorem nodeR_fourier_minus_at_c81_8_N3_tail_integral_abs_le_tight :
    |∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c81_8_N3 u| ≤ 12 / 10 ^ 8 := by
  have h_int := nodeR_fourier_minus_at_c81_8_N3_integrable_Ioi5
  have h_dom_int := tailDominator_integrable_Ioi5
  have h_abs_le_abs :
      |∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c81_8_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_minus_at_c81_8_N3 u| :=
    MeasureTheory.abs_integral_le_integral_abs
  have h_abs_le_dom :
      ∫ u in Ioi (5 : ℝ), |nodeR_fourier_minus_at_c81_8_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := by
    refine MeasureTheory.setIntegral_mono_on h_int.abs h_dom_int measurableSet_Ioi ?_
    intro u hu
    have hu0 : 0 ≤ u := by
      have := mem_Ioi.mp hu; linarith
    have h1 := nodeR_fourier_minus_at_c81_8_N3_abs_le u
    have h2 := F_plus_add_F_minus_le_tailDominator hu0
    linarith
  calc |∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c81_8_N3 u|
      ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_minus_at_c81_8_N3 u| := h_abs_le_abs
    _ ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := h_abs_le_dom
    _ ≤ 12 / 10 ^ 8 := integral_tailDominator_Ioi5_le_tight

/-! ## §Axiom check -/

#print axioms omega_N3_at_exp_eq_partial_sum
#print axioms omega_N3_at_exp_le_omega_exp
#print axioms omega_N3_at_exp_nonneg
#print axioms nodeR_fourier_plus_at_c81_8_N3_abs_le
#print axioms nodeR_fourier_minus_at_c81_8_N3_abs_le
#print axioms F_plus_integrable_Ioi5
#print axioms F_minus_integrable_Ioi5
#print axioms F_plus_add_F_minus_integrable_Ioi5
#print axioms nodeR_fourier_plus_at_c81_8_N3_integrable_Ioi5
#print axioms nodeR_fourier_minus_at_c81_8_N3_integrable_Ioi5
#print axioms tailDominator_integrable_Ioi
#print axioms tailDominator_integrable_Ioi5
#print axioms F_plus_add_F_minus_le_tailDominator
#print axioms integral_exp_mul_half_minus_pi_Ioi5
#print axioms integral_exp_neg_pi_Ioi5
#print axioms integral_tailDominator_Ioi5
#print axioms integral_tailDominator_Ioi5_le_one
#print axioms nodeR_fourier_plus_at_c81_8_N3_tail_integral_abs_le
#print axioms nodeR_fourier_minus_at_c81_8_N3_tail_integral_abs_le
#print axioms exp_neg_five_pi_le
#print axioms exp_neg_pi_mul_exp_5_half_sub_pi_le
#print axioms integral_tailDominator_Ioi5_le_tight
#print axioms nodeR_fourier_plus_at_c81_8_N3_tail_integral_abs_le_tight
#print axioms nodeR_fourier_minus_at_c81_8_N3_tail_integral_abs_le_tight

end AnalyticTailBound
end FourierPanels_c81_8
end PrincipiaTractalis
