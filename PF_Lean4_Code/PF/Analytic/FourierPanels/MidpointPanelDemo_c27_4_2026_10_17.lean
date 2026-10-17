/-
# PF.Analytic.FourierPanels.MidpointPanelDemo_c27_4_2026_10_17

**Measurement scratch:** a single midpoint-rule-based panel for the sum
`∑ n < 3, fourier_plus_term (27/4) n u` on `u ∈ [0, 1/32]`, instantiating
`XiQuadrature.midpoint_rule_error` with the C² bound from
`abs_fourier_plus_termD2_sum_le`.

**Goal:** count lines-per-panel vs the ~153 lines/panel of the current
range-brick generator (`Seg01Range_c27_4_2026_10_16.lean`).

**Why `∑ fourier_plus_term` rather than `nodeR_fourier_plus_at_c27_4_N3`:**
the CoreDefs identity `nodeR_... = (1/2) · ∑ fourier_plus_term` is a one-line
`unfold + ring` fact; the generator will apply it after the midpoint rule
closes the sum version.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/
import PF.Analytic.FourierPanels.FourierTermC2_2026_10_16
import PF.Analytic.XiQuadrature
import PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14

namespace PrincipiaTractalis
namespace MidpointPanelDemo

open PrincipiaTractalis.FourierTermC2 PrincipiaTractalis.XiQuadrature Real

noncomputable section

/-- The integrand under test: `f(u) = ∑ n<3, fourier_plus_term (27/4) n u`. -/
private noncomputable abbrev f (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 3, fourier_plus_term (27/4) n u

/-- Loose M-bound at `T = 1/32` summed over `n < 3`. True sum ≈ 7.50;
using `3000` as a crudely-provable rational cap, with per-`n` bound
`≤ 1000` via `π ≤ 4`, `A ≤ 36`, `exp(-A) ≤ 1/23`, `exp(1/32) ≤ 2`. -/
private noncomputable abbrev M : ℝ := 3000

/-- **Per-term crude bound**: `fourier_plus_termM (27/4) n (1/32) ≤ 1000`
for each `n ∈ {0, 1, 2}`. -/
private lemma fourier_plus_termM_le_crude (n : ℕ) (hn : n ≤ 2) :
    fourier_plus_termM (27/4) n (1/32) ≤ 1000 := by
  unfold fourier_plus_termM
  have hπ_le : π ≤ 4 := Real.pi_lt_four.le
  have hπ_pos : 0 < π := Real.pi_pos
  have hE_le : Real.exp ((1:ℝ)/64) ≤ 2 :=
    ((Real.exp_le_exp).mpr (by have := Real.log_two_gt_d9; linarith :
      (1:ℝ)/64 ≤ Real.log 2)).trans_eq (Real.exp_log (by norm_num))
  have hT_le : Real.exp ((1:ℝ)/32) ≤ 2 :=
    ((Real.exp_le_exp).mpr (by have := Real.log_two_gt_d9; linarith :
      (1:ℝ)/32 ≤ Real.log 2)).trans_eq (Real.exp_log (by norm_num))
  have hT_ge_one : (1 : ℝ) ≤ Real.exp ((1:ℝ)/32) := Real.one_le_exp (by norm_num)
  have hE_pos : 0 < Real.exp ((1:ℝ)/64) := Real.exp_pos _
  have hT_pos : 0 < Real.exp ((1:ℝ)/32) := Real.exp_pos _
  have h_eneg_pi : Real.exp (-π) ≤ 1/23 :=
    PrincipiaTractalis.Lambda0TightestBoundsMellin20261014.exp_neg_pi_le_one_twentythird
  have hA_pos : 0 ≤ π * ((n:ℝ)+1)^2 := mul_nonneg hπ_pos.le (sq_nonneg _)
  have hA_ge_π : π ≤ π * ((n:ℝ)+1)^2 := by
    have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h1 : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith
    nlinarith
  have hA_le : π * ((n:ℝ)+1)^2 ≤ 36 := by
    have h1 : ((n:ℝ)+1)^2 ≤ 9 := by
      have : (n:ℝ) ≤ 2 := by exact_mod_cast hn
      nlinarith
    nlinarith
  have hB_pos : 0 < Real.exp (-(π * ((n:ℝ)+1)^2)) := Real.exp_pos _
  have hB_le : Real.exp (-(π * ((n:ℝ)+1)^2)) ≤ 1/23 :=
    (Real.exp_le_exp.mpr (by linarith : -(π * ((n:ℝ)+1)^2) ≤ -π)).trans h_eneg_pi
  have habs_c : |((27:ℝ)/4)| = 27/4 := by rw [abs_of_pos]; norm_num
  rw [habs_c, show ((1:ℝ)/32/2 : ℝ) = 1/64 from by norm_num]
  set A := π * ((n:ℝ)+1)^2 with hA_def
  set E := Real.exp ((1:ℝ)/64) with hE_def
  set B := Real.exp (-A) with hB_def
  set T := Real.exp ((1:ℝ)/32) with hT_def
  have hA_ge_π' : π ≤ A := hA_ge_π
  have hAT_ge_one : (1 : ℝ) ≤ A * T := by
    have h1 : (1:ℝ) ≤ A := by linarith [hπ_pos, Real.pi_gt_three]
    have : (1 : ℝ) * 1 ≤ A * T := mul_le_mul h1 hT_ge_one (by norm_num) (by linarith)
    linarith
  -- Product bounds: pre-multiply to help nlinarith.
  have hB_le' : B ≤ (23:ℝ)⁻¹ := by rw [show (23:ℝ)⁻¹ = 1/23 from by norm_num]; exact hB_le
  have hAB_le : A * B ≤ 36/23 := by
    have := mul_le_mul hA_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 36)
    linarith
  have hAB_nn : 0 ≤ A * B := mul_nonneg hA_pos hB_pos.le
  have hEB_le : E * B ≤ 2/23 := by
    have := mul_le_mul hE_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have hEB_nn : 0 ≤ E * B := mul_nonneg hE_pos.le hB_pos.le
  have hAT_le : A * T ≤ 72 := by
    have := mul_le_mul hA_le hT_le hT_pos.le (by norm_num : (0:ℝ) ≤ 36)
    linarith
  have hA2TB_bound : A * (A*T - 1) * B ≤ 36 * 71 / 23 := by
    have h_ATm1_nn : (0:ℝ) ≤ A*T - 1 := by linarith
    have h_ATm1_le : A*T - 1 ≤ 71 := by linarith
    have h_A_ATm1_nn : (0:ℝ) ≤ A * (A*T - 1) := mul_nonneg hA_pos h_ATm1_nn
    have h_A_ATm1_le : A * (A*T - 1) ≤ 36 * 71 := by
      have := mul_le_mul hA_le h_ATm1_le h_ATm1_nn (by norm_num : (0:ℝ) ≤ 36)
      linarith
    have h := mul_le_mul h_A_ATm1_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 36*71)
    calc A * (A*T - 1) * B ≤ 36 * 71 * (1/23) := by linarith
      _ = 36 * 71 / 23 := by ring
  have hA2TB_nn : 0 ≤ A * (A*T - 1) * B := by
    have h_ATm1_nn : (0:ℝ) ≤ A*T - 1 := by linarith
    exact mul_nonneg (mul_nonneg hA_pos h_ATm1_nn) hB_pos.le
  have hEAB_le : E * (A * B) ≤ 2 * (36/23) := by
    have := mul_le_mul hE_le hAB_le hAB_nn (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have hE1AB_le : (E + 1) * (A * B) ≤ 3 * (36/23) := by
    have h1 : E + 1 ≤ 3 := by linarith
    have := mul_le_mul h1 hAB_le hAB_nn (by norm_num : (0:ℝ) ≤ 3)
    linarith
  have hE1_nn : 0 ≤ E + 1 := by linarith
  nlinarith [hAB_le, hAB_nn, hEB_le, hEB_nn, hA2TB_bound, hA2TB_nn,
             hEAB_le, mul_nonneg hE_pos.le hAB_nn,
             hE1AB_le, mul_nonneg hE1_nn hAB_nn,
             hE_le, hE_pos.le, hT_le, hT_pos.le, hB_pos.le, hπ_pos]

/-- The explicit sum-of-M bound: three crude per-term bounds summed. -/
private lemma M_sum_le : ∑ n ∈ Finset.range 3, fourier_plus_termM (27/4) n (1/32) ≤ M := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [fourier_plus_termM_le_crude 0 (by decide),
            fourier_plus_termM_le_crude 1 (by decide),
            fourier_plus_termM_le_crude 2 (by decide)]

/-- Panel `[0, 1/32]`, midpoint `1/64`. **Midpoint-rule integral bound.**

Error term `M · (b-a)³ / 24 = 3000 · (1/32)³ / 24 = 3000 / 786432 = 125/32768`. -/
theorem s01p0_midpoint_integral_bound :
    |(∫ u in (0 : ℝ)..(1/32 : ℝ), f u) - (1/32) * f (1/64)|
      ≤ (3000 : ℝ) / 786432 := by
  have hab : (0 : ℝ) ≤ 1/32 := by norm_num
  have h_f : ∀ u ∈ Set.uIcc (0 : ℝ) (1/32), HasDerivAt f
      (∑ n ∈ Finset.range 3, fourier_plus_termD1 (27/4) n u) u :=
    fun u _ ↦ hasDerivAt_fourier_plus_term_sum (27/4) 3 u
  have h_f' : ∀ u ∈ Set.uIcc (0 : ℝ) (1/32),
      HasDerivAt (fun y ↦ ∑ n ∈ Finset.range 3, fourier_plus_termD1 (27/4) n y)
        (∑ n ∈ Finset.range 3, fourier_plus_termD2 (27/4) n u) u :=
    fun u _ ↦ hasDerivAt_fourier_plus_termD1_sum (27/4) 3 u
  have h_M : ∀ u ∈ Set.uIcc (0 : ℝ) (1/32),
      |∑ n ∈ Finset.range 3, fourier_plus_termD2 (27/4) n u| ≤ M := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact (abs_fourier_plus_termD2_sum_le (27/4) (1/32) 3 hu.1 hu.2).trans M_sum_le
  have h_mid : ((0 : ℝ) + 1/32) / 2 = 1/64 := by norm_num
  have h_mp := midpoint_rule_error hab h_f h_f' h_M
  rw [h_mid] at h_mp
  have h_rhs : M * (1/32 - 0 : ℝ) ^ 3 / 24 = 3000 / 786432 := by
    show (3000 : ℝ) * (1/32 - 0) ^ 3 / 24 = 3000 / 786432
    norm_num
  linarith [h_rhs]

end
end MidpointPanelDemo
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.MidpointPanelDemo.fourier_plus_termM_le_crude
#print axioms PrincipiaTractalis.MidpointPanelDemo.M_sum_le
#print axioms PrincipiaTractalis.MidpointPanelDemo.s01p0_midpoint_integral_bound
