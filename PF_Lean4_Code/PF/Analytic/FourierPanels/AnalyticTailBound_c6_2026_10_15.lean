/-
# PF.Analytic.FourierPanels.AnalyticTailBound_c6_2026_10_15

**Analytic tail-bound companion** to the finite-segment Fourier panel pack.

The r120-style panel pack certifies `∫_0^U nodeR_fourier_±_at_c6_N3 u du`
on a finite segment via per-panel `Interval` bricks.  To close the full
`Re Λ₀(1 + 6i)` and `Im Λ₀(1 + 6i)` Mellin integrals we also need an
analytic bound on `∫_U^∞ nodeR_fourier_±_at_c6_N3 u du`.

**Truncation point.** `U = 5` (matching the r120 case and the Agent B/F
prototypes).

**Strategy.** For every `u ≥ 0`,

  `|nodeR_fourier_plus_at_c6_N3 u|  ≤ F_plus u + F_minus u`
  `|nodeR_fourier_minus_at_c6_N3 u| ≤ F_plus u + F_minus u`

because `omega_N3_at_exp u ≤ omega (exp u)` (the N = 3 truncation is a
partial sum of the nonneg `omega` series) and `|cos|, |sin| ≤ 1`.  Then
`F_plus` and `F_minus` are integrable on `Ioi 0`
(`F_plus_integrable_Ioi`, `F_minus_integrable_Ioi` from
`OmegaDerivativeBounds_2026_10_15`), and so on `Ioi 5` by `mono_set`.

We prove both:

* `IntegrableOn (fun u => nodeR_fourier_±_at_c6_N3 u) (Ioi 5)`
* `|∫ u in Ioi 5, nodeR_fourier_±_at_c6_N3 u| ≤ 1`

The explicit bound of `1` is intentionally very loose — the actual
magnitude at `u = 5` is around `exp(-π · e^5) ≈ 10^{-203}`.  All we need
for the Mellin integral is the lemma to *exist* kernel-clean.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/
import PF.Analytic.FourierPanels.CoreDefs_c6_2026_10_15
import PF.Analytic.OmegaDerivativeBounds_2026_10_15
import PF.Analytic.FourierPanels.Seg01Range_c6_2026_10_15

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c6
namespace AnalyticTailBound

open Real MeasureTheory Set Topology Filter
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaDerivativeBounds20261015
open scoped Real

/-! ## §1 — `omega_N3_at_exp u ≤ omega (exp u)`

`omega_N3_at_exp u = exp(-π·e^u) + exp(-4π·e^u) + exp(-9π·e^u)` is the
sum of the first three terms of the nonneg series defining
`omega (exp u) = ∑' n, exp(-π·(n+1)²·exp u)`, so it is a partial sum.
-/

/-- The N = 3 truncation is a partial sum of `omega`: it equals
`∑ n ∈ Finset.range 3, exp(-π · (n+1)² · exp u)`. -/
lemma omega_N3_at_exp_eq_partial_sum (u : ℝ) :
    omega_N3_at_exp u =
      ∑ n ∈ Finset.range 3, Real.exp (-π * ((n : ℝ) + 1) ^ 2 * Real.exp u) := by
  unfold omega_N3_at_exp
  simp [Finset.sum_range_succ]
  ring_nf

/-- Pointwise: `omega_N3_at_exp u ≤ omega (exp u)` for every real `u`. -/
theorem omega_N3_at_exp_le_omega_exp (u : ℝ) :
    omega_N3_at_exp u ≤ omega (Real.exp u) := by
  have hu_pos : 0 < Real.exp u := Real.exp_pos u
  rw [omega_N3_at_exp_eq_partial_sum]
  -- omega(exp u) = ∑' n, exp(-π(n+1)²·exp u); partial sum ≤ tsum (nonneg terms).
  have hterm_nn : ∀ n : ℕ, 0 ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * Real.exp u) :=
    fun _ => (Real.exp_pos _).le
  have hsum := summable_omega hu_pos
  exact hsum.sum_le_tsum (Finset.range 3) (fun n _ => hterm_nn n)

/-- `0 ≤ omega_N3_at_exp u` for all `u`. -/
lemma omega_N3_at_exp_nonneg (u : ℝ) : 0 ≤ omega_N3_at_exp u := by
  unfold omega_N3_at_exp
  have h1 : 0 ≤ Real.exp (-(π * Real.exp u)) := (Real.exp_pos _).le
  have h2 : 0 ≤ Real.exp (-(4 * π * Real.exp u)) := (Real.exp_pos _).le
  have h3 : 0 ≤ Real.exp (-(9 * π * Real.exp u)) := (Real.exp_pos _).le
  linarith

/-! ## §2 — Pointwise bound on `nodeR_fourier_±_at_c6_N3` -/

/-- Pointwise bound: `|nodeR_fourier_plus_at_c6_N3 u| ≤ F_plus u + F_minus u`
for every `u`.  Uses `omega_N3_at_exp u ≤ omega (exp u) = F_minus u`,
`exp(u·0.5) · omega_N3_at_exp u ≤ exp(u/2) · omega(exp u) = F_plus u`
(since `u * 0.5 = u / 2`), and `|cos(3u)| ≤ 1`. -/
theorem nodeR_fourier_plus_at_c6_N3_abs_le (u : ℝ) :
    |nodeR_fourier_plus_at_c6_N3 u| ≤ F_plus u + F_minus u := by
  unfold nodeR_fourier_plus_at_c6_N3 F_plus F_minus
  have h_half : u * (0.5 : ℝ) = u / 2 := by ring
  rw [h_half]
  have h_cos : |Real.cos (3 * u)| ≤ 1 := Real.abs_cos_le_one _
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
  calc (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * |Real.cos (3 * u)|
      ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * 1 :=
        mul_le_mul_of_nonneg_left h_cos h_both_nn
    _ = Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by ring
    _ ≤ Real.exp (u / 2) * omega (Real.exp u) + omega (Real.exp u) := by
        linarith

/-- Pointwise bound: `|nodeR_fourier_minus_at_c6_N3 u| ≤ F_plus u + F_minus u`.
Same structure as the `plus` bound.  Note the SUB-expression
`exp(u·0.5)·ω_N3 − ω_N3` need not be nonneg, so we work via `|a − b| ≤ a + b`
(both ≥ 0). -/
theorem nodeR_fourier_minus_at_c6_N3_abs_le (u : ℝ) :
    |nodeR_fourier_minus_at_c6_N3 u| ≤ F_plus u + F_minus u := by
  unfold nodeR_fourier_minus_at_c6_N3 F_plus F_minus
  have h_half : u * (0.5 : ℝ) = u / 2 := by ring
  rw [h_half]
  have h_sin : |Real.sin (3 * u)| ≤ 1 := Real.abs_sin_le_one _
  have h_omega_N3_nn : 0 ≤ omega_N3_at_exp u := omega_N3_at_exp_nonneg u
  have h_exp_half_pos : 0 < Real.exp (u / 2) := Real.exp_pos _
  rw [abs_mul]
  -- |A - B| ≤ |A| + |B| = A + B when A, B ≥ 0
  have h_A_nn : 0 ≤ Real.exp (u / 2) * omega_N3_at_exp u :=
    mul_nonneg h_exp_half_pos.le h_omega_N3_nn
  have h_abs_sub_le :
      |Real.exp (u / 2) * omega_N3_at_exp u - omega_N3_at_exp u|
      ≤ Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by
    have := abs_sub (Real.exp (u / 2) * omega_N3_at_exp u) (omega_N3_at_exp u)
    -- abs_sub : |a - b| ≤ |a| + |b|
    rw [abs_of_nonneg h_A_nn, abs_of_nonneg h_omega_N3_nn] at this
    exact this
  have h_omega_N3_le : omega_N3_at_exp u ≤ omega (Real.exp u) :=
    omega_N3_at_exp_le_omega_exp u
  have h_plus_le :
      Real.exp (u / 2) * omega_N3_at_exp u ≤ Real.exp (u / 2) * omega (Real.exp u) :=
    mul_le_mul_of_nonneg_left h_omega_N3_le h_exp_half_pos.le
  calc |Real.exp (u / 2) * omega_N3_at_exp u - omega_N3_at_exp u| * |Real.sin (3 * u)|
      ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * |Real.sin (3 * u)| := by
        apply mul_le_mul_of_nonneg_right h_abs_sub_le
        exact abs_nonneg _
    _ ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * 1 := by
        apply mul_le_mul_of_nonneg_left h_sin
        linarith
    _ = Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by ring
    _ ≤ Real.exp (u / 2) * omega (Real.exp u) + omega (Real.exp u) := by
        linarith

/-! ## §3 — Integrability on `Ioi 5`

`F_plus` and `F_minus` are integrable on `Ioi 0`.  By `mono_set` they are
integrable on `Ioi 5` (since `Ioi 5 ⊆ Ioi 0`).  Combined with the
pointwise bound and continuity of the N = 3 node functions
(`nodeR_fourier_±_at_c6_N3_continuous` from Seg01Range), we get
integrability of the N = 3 node functions on `Ioi 5`.
-/

/-- `F_plus` integrable on `Ioi 5`. -/
lemma F_plus_integrable_Ioi5 : IntegrableOn F_plus (Ioi (5 : ℝ)) :=
  F_plus_integrable_Ioi.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 5))

/-- `F_minus` integrable on `Ioi 5`. -/
lemma F_minus_integrable_Ioi5 : IntegrableOn F_minus (Ioi (5 : ℝ)) :=
  F_minus_integrable_Ioi.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 5))

/-- Dominating function `fun u => F_plus u + F_minus u` is integrable on `Ioi 5`. -/
lemma F_plus_add_F_minus_integrable_Ioi5 :
    IntegrableOn (fun u : ℝ => F_plus u + F_minus u) (Ioi (5 : ℝ)) :=
  F_plus_integrable_Ioi5.add F_minus_integrable_Ioi5

/-- **`nodeR_fourier_plus_at_c6_N3` is integrable on `Ioi 5`.** -/
theorem nodeR_fourier_plus_at_c6_N3_integrable_Ioi5 :
    IntegrableOn (fun u : ℝ => nodeR_fourier_plus_at_c6_N3 u) (Ioi (5 : ℝ)) := by
  have h_dom := F_plus_add_F_minus_integrable_Ioi5
  have h_meas : AEStronglyMeasurable
      (fun u : ℝ => nodeR_fourier_plus_at_c6_N3 u)
      (volume.restrict (Ioi (5 : ℝ))) :=
    (Seg01Range.nodeR_fourier_plus_at_c6_N3_continuous).aestronglyMeasurable.restrict
  refine h_dom.mono' h_meas ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (5 : ℝ)))]
    with u hu
  have hu0 : 0 ≤ u := by
    have : (5 : ℝ) < u := mem_Ioi.mp hu
    linarith
  rw [Real.norm_eq_abs]
  exact nodeR_fourier_plus_at_c6_N3_abs_le u

/-- **`nodeR_fourier_minus_at_c6_N3` is integrable on `Ioi 5`.** -/
theorem nodeR_fourier_minus_at_c6_N3_integrable_Ioi5 :
    IntegrableOn (fun u : ℝ => nodeR_fourier_minus_at_c6_N3 u) (Ioi (5 : ℝ)) := by
  have h_dom := F_plus_add_F_minus_integrable_Ioi5
  have h_meas : AEStronglyMeasurable
      (fun u : ℝ => nodeR_fourier_minus_at_c6_N3 u)
      (volume.restrict (Ioi (5 : ℝ))) :=
    (Seg01Range.nodeR_fourier_minus_at_c6_N3_continuous).aestronglyMeasurable.restrict
  refine h_dom.mono' h_meas ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (5 : ℝ)))]
    with u hu
  have hu0 : 0 ≤ u := by
    have : (5 : ℝ) < u := mem_Ioi.mp hu
    linarith
  rw [Real.norm_eq_abs]
  exact nodeR_fourier_minus_at_c6_N3_abs_le u

/-! ## §4 — Tail integral bound: `|∫_{Ioi 5} f| ≤ 1`

The actual magnitude is tiny (`≈ 10^{-203}`); we prove a very loose
bound of `1` using

  `|∫_{Ioi 5} f| ≤ ∫_{Ioi 5} |f| ≤ ∫_{Ioi 5} (F_plus + F_minus)`

and the explicit integrable dominator bound `F_plus + F_minus
≤ (23/22)·exp(-π)·exp(u·(1/2-π)) + (23/22)·exp(-π·u)`.  Both pieces
integrate to small positive numbers; the sum is well below `1`.
-/

/-- A clean integrable dominator built from the two exponential bounds
`F_plus_le_exp_bound` and `F_minus_le_exp_neg_pi_mul`. -/
noncomputable def tailDominator (u : ℝ) : ℝ :=
  (23 / 22 : ℝ) * Real.exp (-π) * Real.exp (u * (1 / 2 - π))
    + (23 / 22 : ℝ) * Real.exp (-π * u)

/-- `tailDominator` is integrable on `Ioi 0` (hence on `Ioi 5`). -/
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

/-- `tailDominator` integrable on `Ioi 5`. -/
lemma tailDominator_integrable_Ioi5 : IntegrableOn tailDominator (Ioi (5 : ℝ)) :=
  tailDominator_integrable_Ioi.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 5))

/-- `F_plus u + F_minus u ≤ tailDominator u` for `u ≥ 0`. -/
lemma F_plus_add_F_minus_le_tailDominator {u : ℝ} (hu : 0 ≤ u) :
    F_plus u + F_minus u ≤ tailDominator u := by
  unfold tailDominator
  have h1 := F_plus_le_exp_bound hu
  have h2 := F_minus_le_exp_neg_pi_mul hu
  linarith

/-! Compute an explicit upper bound on `∫_{Ioi 5} tailDominator`. -/

/-- `∫_{Ioi 5} exp(u·(1/2 - π)) du = exp(5·(1/2 - π))/(π - 1/2)`. -/
lemma integral_exp_mul_half_minus_pi_Ioi5 :
    ∫ u in Ioi (5 : ℝ), Real.exp (u * (1 / 2 - π))
      = Real.exp (5 * (1 / 2 - π)) / (π - 1 / 2) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h_coeff_pos : (0 : ℝ) < π - 1 / 2 := by linarith [Real.pi_gt_three]
  have h_coeff_neg : (1 / 2 - π : ℝ) < 0 := by linarith
  have h_coeff_ne : (1 / 2 - π : ℝ) ≠ 0 := ne_of_lt h_coeff_neg
  have h_pi_minus_half_ne : (π - 1 / 2 : ℝ) ≠ 0 := ne_of_gt h_coeff_pos
  -- Convert u · c = c · u
  have h_fun :
      (fun u : ℝ => Real.exp (u * (1 / 2 - π)))
      = (fun u : ℝ => Real.exp ((1 / 2 - π) * u)) := by
    ext u; rw [mul_comm]
  rw [h_fun]
  -- Use integral_exp_mul_Ioi : ∫ u in Ioi c, exp (a * u) = -exp(a·c)/a
  rw [integral_exp_mul_Ioi (a := 1 / 2 - π) (c := 5) h_coeff_neg]
  -- Goal: -(exp((1/2 - π)·5) / (1/2 - π)) = exp(5·(1/2 - π))/(π - 1/2)
  have h_arg : ((1 : ℝ) / 2 - π) * 5 = 5 * (1 / 2 - π) := by ring
  rw [h_arg]
  -- Multiply both sides by (1/2 - π)·(π - 1/2) via div_eq_div_iff.
  rw [neg_div, eq_comm, eq_neg_iff_add_eq_zero, div_add_div _ _ h_pi_minus_half_ne h_coeff_ne]
  rw [div_eq_zero_iff]
  left
  ring

/-- `∫_{Ioi 5} exp(-π·u) du = exp(-5π)/π`. -/
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

/-- Explicit value of `∫_{Ioi 5} tailDominator`. -/
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

/-- Numerical upper bound: the explicit tail-dominator integral is `≤ 1`. -/
lemma integral_tailDominator_Ioi5_le_one :
    ∫ u in Ioi (5 : ℝ), tailDominator u ≤ 1 := by
  rw [integral_tailDominator_Ioi5]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ_gt_3 : (3 : ℝ) < π := Real.pi_gt_three
  have h_coeff_pos : (0 : ℝ) < π - 1 / 2 := by linarith
  -- Both terms are positive and tiny.
  -- Term 1 bound: (23/22)·exp(-π)·exp(5·(1/2 - π))/(π - 1/2)
  --   ≤ (23/22)·1·1/(π - 1/2) ≤ (23/22)·1/2.5 ≤ 1 (since exp(-π) ≤ 1, exp(5·(1/2-π)) ≤ 1)
  -- Term 2 bound: (23/22)·exp(-5π)/π ≤ (23/22)·1/3 ≤ 1
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
  -- Term 1: (23/22) * exp(-π) * exp(5·(1/2 - π)) / (π - 1/2)
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
  -- Term 2: (23/22) * exp(-5π) / π ≤ (23/22) / π
  have h_t2_le :
      (23 / 22 : ℝ) * (Real.exp (-5 * π) / π) ≤ (23 / 22) / π := by
    rw [show ((23 / 22 : ℝ) * (Real.exp (-5 * π) / π)) = ((23/22) * Real.exp (-5*π)) / π by ring]
    apply div_le_div_of_nonneg_right _ hπ.le
    nlinarith [h_exp_neg5pi_le_1]
  -- Combine: (23/22)/(π - 1/2) + (23/22)/π ≤ 1
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

/-- **The tail integral is bounded in absolute value by `1`.**  Loose bound;
actual value `≈ 10^{-203}`. -/
theorem nodeR_fourier_plus_at_c6_N3_tail_integral_abs_le :
    |∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c6_N3 u| ≤ 1 := by
  have h_int := nodeR_fourier_plus_at_c6_N3_integrable_Ioi5
  have h_dom_int := tailDominator_integrable_Ioi5
  -- |∫ f| ≤ ∫ |f| ≤ ∫ tailDominator (via pointwise bound on Ioi 5)
  have h_abs_le_abs :
      |∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c6_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_plus_at_c6_N3 u| :=
    MeasureTheory.abs_integral_le_integral_abs
  have h_abs_le_dom :
      ∫ u in Ioi (5 : ℝ), |nodeR_fourier_plus_at_c6_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := by
    refine MeasureTheory.setIntegral_mono_on h_int.abs h_dom_int measurableSet_Ioi ?_
    intro u hu
    have hu0 : 0 ≤ u := by
      have := mem_Ioi.mp hu; linarith
    have h1 := nodeR_fourier_plus_at_c6_N3_abs_le u
    have h2 := F_plus_add_F_minus_le_tailDominator hu0
    linarith
  calc |∫ u in Ioi (5 : ℝ), nodeR_fourier_plus_at_c6_N3 u|
      ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_plus_at_c6_N3 u| := h_abs_le_abs
    _ ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := h_abs_le_dom
    _ ≤ 1 := integral_tailDominator_Ioi5_le_one

/-- **The tail integral is bounded in absolute value by `1`.**  Loose bound;
actual value `≈ 10^{-203}`. -/
theorem nodeR_fourier_minus_at_c6_N3_tail_integral_abs_le :
    |∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c6_N3 u| ≤ 1 := by
  have h_int := nodeR_fourier_minus_at_c6_N3_integrable_Ioi5
  have h_dom_int := tailDominator_integrable_Ioi5
  have h_abs_le_abs :
      |∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c6_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_minus_at_c6_N3 u| :=
    MeasureTheory.abs_integral_le_integral_abs
  have h_abs_le_dom :
      ∫ u in Ioi (5 : ℝ), |nodeR_fourier_minus_at_c6_N3 u|
        ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := by
    refine MeasureTheory.setIntegral_mono_on h_int.abs h_dom_int measurableSet_Ioi ?_
    intro u hu
    have hu0 : 0 ≤ u := by
      have := mem_Ioi.mp hu; linarith
    have h1 := nodeR_fourier_minus_at_c6_N3_abs_le u
    have h2 := F_plus_add_F_minus_le_tailDominator hu0
    linarith
  calc |∫ u in Ioi (5 : ℝ), nodeR_fourier_minus_at_c6_N3 u|
      ≤ ∫ u in Ioi (5 : ℝ), |nodeR_fourier_minus_at_c6_N3 u| := h_abs_le_abs
    _ ≤ ∫ u in Ioi (5 : ℝ), tailDominator u := h_abs_le_dom
    _ ≤ 1 := integral_tailDominator_Ioi5_le_one

/-! ## §Axiom check -/

#print axioms omega_N3_at_exp_eq_partial_sum
#print axioms omega_N3_at_exp_le_omega_exp
#print axioms omega_N3_at_exp_nonneg
#print axioms nodeR_fourier_plus_at_c6_N3_abs_le
#print axioms nodeR_fourier_minus_at_c6_N3_abs_le
#print axioms F_plus_integrable_Ioi5
#print axioms F_minus_integrable_Ioi5
#print axioms F_plus_add_F_minus_integrable_Ioi5
#print axioms nodeR_fourier_plus_at_c6_N3_integrable_Ioi5
#print axioms nodeR_fourier_minus_at_c6_N3_integrable_Ioi5
#print axioms tailDominator_integrable_Ioi
#print axioms tailDominator_integrable_Ioi5
#print axioms F_plus_add_F_minus_le_tailDominator
#print axioms integral_exp_mul_half_minus_pi_Ioi5
#print axioms integral_exp_neg_pi_Ioi5
#print axioms integral_tailDominator_Ioi5
#print axioms integral_tailDominator_Ioi5_le_one
#print axioms nodeR_fourier_plus_at_c6_N3_tail_integral_abs_le
#print axioms nodeR_fourier_minus_at_c6_N3_tail_integral_abs_le

end AnalyticTailBound
end FourierPanels_c6
end PrincipiaTractalis
