/-
# PF.Analytic.FourierPanels.ResidueBound_c25_4_three_halves_to_5_2026_10_16

**Residue bound** between the panel pack cutoff `u = 3/2` and the
analytic tail cutoff `u = 5` for the `c = 49/8` pilot.

Mirror of `ResidueBound_c6_three_halves_to_5_2026_10_15.lean`. The
uniform-over-interval argument is c-independent: we use
`|cos|, |sin| ≤ 1`.

**Strategy.** Loose uniform-over-interval bound. For `u ≥ 0`,

  `|nodeR_fourier_±_at_c25_4_N3 u| ≤ (exp(u/2) + 1) · (3 · exp(-π · exp u))`

On `u ∈ [3/2, 5]`:
* `exp(u/2) + 1 ≤ 22`.
* `exp(-π · exp u) ≤ exp(-4π) ≤ 1/279841`.
* So `|f u| ≤ 66/279841` on `[3/2, 5]`, giving
  `|∫_(3/2)^5 f| ≤ (66/279841) · (7/2) = 231/279841 < 1/10³`.

Three-axiom bar: every top-level declaration prints exactly
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/
import PF.Analytic.FourierPanels.CoreDefs_c25_4_2026_10_16
import PF.Analytic.FourierPanels.Seg01Range_c25_4_2026_10_16
import PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c25_4
namespace ResidueBound

open Real MeasureTheory Set
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.Lambda0TightestBoundsMellin20261014
open scoped Real

/-! ## §1 — Pointwise bound: `|f u| ≤ (exp(u/2) + 1) · 3 · exp(-π · exp u)` -/

lemma omega_N3_at_exp_le_three_exp (u : ℝ) :
    omega_N3_at_exp u ≤ 3 * Real.exp (-(π * Real.exp u)) := by
  unfold omega_N3_at_exp
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_exp_u_pos : (0 : ℝ) < Real.exp u := Real.exp_pos _
  have h_prod_nn : (0 : ℝ) ≤ π * Real.exp u := le_of_lt (mul_pos hπ_pos h_exp_u_pos)
  have h2 : Real.exp (-(4 * π * Real.exp u)) ≤ Real.exp (-(π * Real.exp u)) := by
    apply Real.exp_le_exp.mpr
    have : π * Real.exp u ≤ 4 * π * Real.exp u := by nlinarith
    linarith
  have h3 : Real.exp (-(9 * π * Real.exp u)) ≤ Real.exp (-(π * Real.exp u)) := by
    apply Real.exp_le_exp.mpr
    have : π * Real.exp u ≤ 9 * π * Real.exp u := by nlinarith
    linarith
  linarith

lemma nodeR_fourier_plus_at_c25_4_N3_abs_le_mul_exp (u : ℝ) :
    |nodeR_fourier_plus_at_c25_4_N3 u|
      ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) := by
  unfold nodeR_fourier_plus_at_c25_4_N3
  have h_half : u * (0.5 : ℝ) = u / 2 := by ring
  rw [h_half]
  have h_cos : |Real.cos ((3.125 : ℝ) * u)| ≤ 1 := Real.abs_cos_le_one _
  have h_omega_nn : 0 ≤ omega_N3_at_exp u := by
    unfold omega_N3_at_exp
    have h1 : 0 ≤ Real.exp (-(π * Real.exp u)) := (Real.exp_pos _).le
    have h2 : 0 ≤ Real.exp (-(4 * π * Real.exp u)) := (Real.exp_pos _).le
    have h3 : 0 ≤ Real.exp (-(9 * π * Real.exp u)) := (Real.exp_pos _).le
    linarith
  have h_exp_half_pos : 0 < Real.exp (u / 2) := Real.exp_pos _
  have h_factor_nn :
      0 ≤ Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by
    have := mul_nonneg h_exp_half_pos.le h_omega_nn
    linarith
  rw [abs_mul]
  have h_abs_factor :
      |Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u|
        = Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u :=
    abs_of_nonneg h_factor_nn
  rw [h_abs_factor]
  have h_omega_le : omega_N3_at_exp u ≤ 3 * Real.exp (-(π * Real.exp u)) :=
    omega_N3_at_exp_le_three_exp u
  have h_factor_le :
      Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u
        ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) := by
    have h_exp_mul :
        Real.exp (u / 2) * omega_N3_at_exp u
          ≤ Real.exp (u / 2) * (3 * Real.exp (-(π * Real.exp u))) :=
      mul_le_mul_of_nonneg_left h_omega_le h_exp_half_pos.le
    nlinarith [h_exp_mul, h_omega_le, h_exp_half_pos.le]
  calc (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * |Real.cos ((3.125 : ℝ) * u)|
      ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * 1 :=
        mul_le_mul_of_nonneg_left h_cos h_factor_nn
    _ = Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by ring
    _ ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) := h_factor_le

lemma nodeR_fourier_minus_at_c25_4_N3_abs_le_mul_exp (u : ℝ) :
    |nodeR_fourier_minus_at_c25_4_N3 u|
      ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) := by
  unfold nodeR_fourier_minus_at_c25_4_N3
  have h_half : u * (0.5 : ℝ) = u / 2 := by ring
  rw [h_half]
  have h_sin : |Real.sin ((3.125 : ℝ) * u)| ≤ 1 := Real.abs_sin_le_one _
  have h_omega_nn : 0 ≤ omega_N3_at_exp u := by
    unfold omega_N3_at_exp
    have h1 : 0 ≤ Real.exp (-(π * Real.exp u)) := (Real.exp_pos _).le
    have h2 : 0 ≤ Real.exp (-(4 * π * Real.exp u)) := (Real.exp_pos _).le
    have h3 : 0 ≤ Real.exp (-(9 * π * Real.exp u)) := (Real.exp_pos _).le
    linarith
  have h_exp_half_pos : 0 < Real.exp (u / 2) := Real.exp_pos _
  rw [abs_mul]
  have h_A_nn : 0 ≤ Real.exp (u / 2) * omega_N3_at_exp u :=
    mul_nonneg h_exp_half_pos.le h_omega_nn
  have h_abs_sub_le :
      |Real.exp (u / 2) * omega_N3_at_exp u - omega_N3_at_exp u|
        ≤ Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by
    have := abs_sub (Real.exp (u / 2) * omega_N3_at_exp u) (omega_N3_at_exp u)
    rw [abs_of_nonneg h_A_nn, abs_of_nonneg h_omega_nn] at this
    exact this
  have h_omega_le : omega_N3_at_exp u ≤ 3 * Real.exp (-(π * Real.exp u)) :=
    omega_N3_at_exp_le_three_exp u
  have h_factor_nn :
      0 ≤ Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by
    linarith
  have h_factor_le :
      Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u
        ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) := by
    have h_exp_mul :
        Real.exp (u / 2) * omega_N3_at_exp u
          ≤ Real.exp (u / 2) * (3 * Real.exp (-(π * Real.exp u))) :=
      mul_le_mul_of_nonneg_left h_omega_le h_exp_half_pos.le
    nlinarith [h_exp_mul, h_omega_le, h_exp_half_pos.le]
  calc |Real.exp (u / 2) * omega_N3_at_exp u - omega_N3_at_exp u| * |Real.sin ((3.125 : ℝ) * u)|
      ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * |Real.sin ((3.125 : ℝ) * u)| := by
        apply mul_le_mul_of_nonneg_right h_abs_sub_le
        exact abs_nonneg _
    _ ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * 1 := by
        apply mul_le_mul_of_nonneg_left h_sin h_factor_nn
    _ = Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by ring
    _ ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) := h_factor_le

/-! ## §2 — Numerical constants on `[3/2, 5]` -/

lemma exp_one_ge_five_halves : (5 / 2 : ℝ) ≤ Real.exp 1 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num)
  have : (1 + 1 + (1 : ℝ) ^ 2 / 2) = 5 / 2 := by norm_num
  linarith

lemma exp_half_ge_thirteen_eighths : (13 / 8 : ℝ) ≤ Real.exp (1 / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
  have : (1 + (1 / 2 : ℝ) + (1 / 2 : ℝ) ^ 2 / 2) = 13 / 8 := by norm_num
  linarith

lemma exp_three_halves_ge : (65 / 16 : ℝ) ≤ Real.exp (3 / 2) := by
  have h_split : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]; congr 1; norm_num
  rw [h_split]
  have h1 := exp_one_ge_five_halves
  have h2 := exp_half_ge_thirteen_eighths
  have h1_pos : (0 : ℝ) < 5 / 2 := by norm_num
  have h2_pos : (0 : ℝ) < 13 / 8 := by norm_num
  have h_prod : (5 / 2 : ℝ) * (13 / 8) ≤ Real.exp 1 * Real.exp (1 / 2) := by
    apply mul_le_mul h1 h2 h2_pos.le (le_trans h1_pos.le h1)
  have h_eq : (5 / 2 : ℝ) * (13 / 8) = 65 / 16 := by norm_num
  linarith

lemma exp_three_halves_ge_four : (4 : ℝ) ≤ Real.exp (3 / 2) := by
  have h := exp_three_halves_ge
  linarith

lemma exp_three_le_twentyone : Real.exp 3 ≤ 21 := by
  have h_one_lt : Real.exp 1 < 2.72 := by
    have h := Real.exp_one_lt_d9
    linarith
  have h_one_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have h_cube : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num]
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [h_cube]
  have h_le : (Real.exp 1) ^ 3 ≤ (2.72 : ℝ) ^ 3 :=
    pow_le_pow_left₀ h_one_pos.le h_one_lt.le 3
  have h_rhs : (2.72 : ℝ) ^ 3 ≤ 21 := by norm_num
  linarith

lemma exp_half_u_le_exp_three {u : ℝ} (hu : u ≤ 5) : Real.exp (u / 2) ≤ Real.exp 3 := by
  apply Real.exp_le_exp.mpr
  linarith

lemma exp_half_u_plus_one_le_twentytwo {u : ℝ} (hu : u ≤ 5) :
    Real.exp (u / 2) + 1 ≤ 22 := by
  have h1 := exp_half_u_le_exp_three hu
  have h2 := exp_three_le_twentyone
  linarith

lemma pi_mul_exp_u_ge_four_pi {u : ℝ} (hu : 3 / 2 ≤ u) : 4 * π ≤ π * Real.exp u := by
  have h_mono : Real.exp (3 / 2) ≤ Real.exp u := Real.exp_le_exp.mpr hu
  have h_three_halves : (4 : ℝ) ≤ Real.exp (3 / 2) := exp_three_halves_ge_four
  have h_eu : (4 : ℝ) ≤ Real.exp u := le_trans h_three_halves h_mono
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_mul : (4 : ℝ) * π ≤ Real.exp u * π :=
    mul_le_mul_of_nonneg_right h_eu hπ_pos.le
  linarith

lemma exp_neg_pi_exp_u_le {u : ℝ} (hu : 3 / 2 ≤ u) :
    Real.exp (-(π * Real.exp u)) ≤ Real.exp (-(4 * π)) := by
  apply Real.exp_le_exp.mpr
  have h := pi_mul_exp_u_ge_four_pi hu
  linarith

lemma exp_neg_four_pi_le : Real.exp (-(4 * π)) ≤ 1 / 279841 := by
  have h_eq : Real.exp (-(4 * π)) = (Real.exp (-π)) ^ 4 := by
    rw [← Real.exp_nat_mul (-π) 4]
    congr 1; push_cast; ring
  rw [h_eq]
  have h_base := exp_neg_pi_le_one_twentythird
  have h_base_nn : 0 ≤ Real.exp (-π) := (Real.exp_pos _).le
  have h_pow : (Real.exp (-π)) ^ 4 ≤ (1 / 23 : ℝ) ^ 4 :=
    pow_le_pow_left₀ h_base_nn h_base 4
  have h_rhs : ((1 : ℝ) / 23) ^ 4 = 1 / 279841 := by norm_num
  linarith

/-! ## §3 — Uniform pointwise bound on `[3/2, 5]`. -/

lemma nodeR_fourier_plus_at_c25_4_N3_abs_uniform_le
    {u : ℝ} (hu_lo : 3 / 2 ≤ u) (hu_hi : u ≤ 5) :
    |nodeR_fourier_plus_at_c25_4_N3 u| ≤ 66 / 279841 := by
  have h1 := nodeR_fourier_plus_at_c25_4_N3_abs_le_mul_exp u
  have h_a : Real.exp (u / 2) + 1 ≤ 22 := exp_half_u_plus_one_le_twentytwo hu_hi
  have h_a_pos : 0 < Real.exp (u / 2) + 1 := by positivity
  have h_b : Real.exp (-(π * Real.exp u)) ≤ Real.exp (-(4 * π)) :=
    exp_neg_pi_exp_u_le hu_lo
  have h_c : Real.exp (-(4 * π)) ≤ 1 / 279841 := exp_neg_four_pi_le
  have h_b_pos : 0 < Real.exp (-(π * Real.exp u)) := Real.exp_pos _
  have h_bc : Real.exp (-(π * Real.exp u)) ≤ 1 / 279841 := le_trans h_b h_c
  have h_rhs_le :
      (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) ≤ 22 * (3 * (1 / 279841)) := by
    have h_three_pos : (0 : ℝ) < 3 := by norm_num
    have h_three_bc_nn : (0 : ℝ) ≤ 3 * Real.exp (-(π * Real.exp u)) :=
      mul_nonneg h_three_pos.le h_b_pos.le
    have h_three_bc_le : 3 * Real.exp (-(π * Real.exp u)) ≤ 3 * (1 / 279841) :=
      mul_le_mul_of_nonneg_left h_bc h_three_pos.le
    have h_three_rhs_nn : (0 : ℝ) ≤ 3 * (1 / 279841) := by norm_num
    calc (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u)))
        ≤ 22 * (3 * Real.exp (-(π * Real.exp u))) :=
          mul_le_mul_of_nonneg_right h_a h_three_bc_nn
      _ ≤ 22 * (3 * (1 / 279841)) :=
          mul_le_mul_of_nonneg_left h_three_bc_le (by norm_num : (0 : ℝ) ≤ 22)
  have h_rhs_eq : (22 : ℝ) * (3 * (1 / 279841)) = 66 / 279841 := by norm_num
  linarith

lemma nodeR_fourier_minus_at_c25_4_N3_abs_uniform_le
    {u : ℝ} (hu_lo : 3 / 2 ≤ u) (hu_hi : u ≤ 5) :
    |nodeR_fourier_minus_at_c25_4_N3 u| ≤ 66 / 279841 := by
  have h1 := nodeR_fourier_minus_at_c25_4_N3_abs_le_mul_exp u
  have h_a : Real.exp (u / 2) + 1 ≤ 22 := exp_half_u_plus_one_le_twentytwo hu_hi
  have h_b : Real.exp (-(π * Real.exp u)) ≤ Real.exp (-(4 * π)) :=
    exp_neg_pi_exp_u_le hu_lo
  have h_c : Real.exp (-(4 * π)) ≤ 1 / 279841 := exp_neg_four_pi_le
  have h_b_pos : 0 < Real.exp (-(π * Real.exp u)) := Real.exp_pos _
  have h_bc : Real.exp (-(π * Real.exp u)) ≤ 1 / 279841 := le_trans h_b h_c
  have h_rhs_le :
      (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) ≤ 22 * (3 * (1 / 279841)) := by
    have h_three_pos : (0 : ℝ) < 3 := by norm_num
    have h_three_bc_nn : (0 : ℝ) ≤ 3 * Real.exp (-(π * Real.exp u)) :=
      mul_nonneg h_three_pos.le h_b_pos.le
    have h_three_bc_le : 3 * Real.exp (-(π * Real.exp u)) ≤ 3 * (1 / 279841) :=
      mul_le_mul_of_nonneg_left h_bc h_three_pos.le
    calc (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u)))
        ≤ 22 * (3 * Real.exp (-(π * Real.exp u))) :=
          mul_le_mul_of_nonneg_right h_a h_three_bc_nn
      _ ≤ 22 * (3 * (1 / 279841)) :=
          mul_le_mul_of_nonneg_left h_three_bc_le (by norm_num : (0 : ℝ) ≤ 22)
  have h_rhs_eq : (22 : ℝ) * (3 * (1 / 279841)) = 66 / 279841 := by norm_num
  linarith

/-! ## §4 — Residue integral bound. -/

theorem nodeR_fourier_plus_at_c25_4_N3_residue_three_halves_to_5_abs_le :
    |∫ u in (3/2 : ℝ)..(5 : ℝ), nodeR_fourier_plus_at_c25_4_N3 u| ≤ (1 / 10 ^ 3 : ℝ) := by
  have h_bound :
      ‖∫ u in (3/2 : ℝ)..(5 : ℝ), nodeR_fourier_plus_at_c25_4_N3 u‖
        ≤ (66 / 279841 : ℝ) * |5 - 3/2| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (3/2 : ℝ) ≤ 5)] at hu
    have hu_lo : 3 / 2 ≤ u := le_of_lt hu.1
    have hu_hi : u ≤ 5 := hu.2
    rw [Real.norm_eq_abs]
    exact nodeR_fourier_plus_at_c25_4_N3_abs_uniform_le hu_lo hu_hi
  have h_abs_sub : |(5 : ℝ) - 3/2| = 7/2 := by
    rw [show ((5 : ℝ) - 3/2) = 7/2 by norm_num]
    exact abs_of_pos (by norm_num : (0 : ℝ) < 7/2)
  rw [h_abs_sub] at h_bound
  have h_prod : (66 / 279841 : ℝ) * (7 / 2) = 231 / 279841 := by norm_num
  rw [h_prod] at h_bound
  rw [Real.norm_eq_abs] at h_bound
  have h_final : (231 : ℝ) / 279841 ≤ 1 / 10 ^ 3 := by norm_num
  linarith

theorem nodeR_fourier_minus_at_c25_4_N3_residue_three_halves_to_5_abs_le :
    |∫ u in (3/2 : ℝ)..(5 : ℝ), nodeR_fourier_minus_at_c25_4_N3 u| ≤ (1 / 10 ^ 3 : ℝ) := by
  have h_bound :
      ‖∫ u in (3/2 : ℝ)..(5 : ℝ), nodeR_fourier_minus_at_c25_4_N3 u‖
        ≤ (66 / 279841 : ℝ) * |5 - 3/2| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (3/2 : ℝ) ≤ 5)] at hu
    have hu_lo : 3 / 2 ≤ u := le_of_lt hu.1
    have hu_hi : u ≤ 5 := hu.2
    rw [Real.norm_eq_abs]
    exact nodeR_fourier_minus_at_c25_4_N3_abs_uniform_le hu_lo hu_hi
  have h_abs_sub : |(5 : ℝ) - 3/2| = 7/2 := by
    rw [show ((5 : ℝ) - 3/2) = 7/2 by norm_num]
    exact abs_of_pos (by norm_num : (0 : ℝ) < 7/2)
  rw [h_abs_sub] at h_bound
  have h_prod : (66 / 279841 : ℝ) * (7 / 2) = 231 / 279841 := by norm_num
  rw [h_prod] at h_bound
  rw [Real.norm_eq_abs] at h_bound
  have h_final : (231 : ℝ) / 279841 ≤ 1 / 10 ^ 3 := by norm_num
  linarith

/-! ## §Axiom check -/

#print axioms omega_N3_at_exp_le_three_exp
#print axioms nodeR_fourier_plus_at_c25_4_N3_abs_le_mul_exp
#print axioms nodeR_fourier_minus_at_c25_4_N3_abs_le_mul_exp
#print axioms exp_one_ge_five_halves
#print axioms exp_half_ge_thirteen_eighths
#print axioms exp_three_halves_ge
#print axioms exp_three_halves_ge_four
#print axioms exp_three_le_twentyone
#print axioms exp_half_u_le_exp_three
#print axioms exp_half_u_plus_one_le_twentytwo
#print axioms pi_mul_exp_u_ge_four_pi
#print axioms exp_neg_pi_exp_u_le
#print axioms exp_neg_four_pi_le
#print axioms nodeR_fourier_plus_at_c25_4_N3_abs_uniform_le
#print axioms nodeR_fourier_minus_at_c25_4_N3_abs_uniform_le
#print axioms nodeR_fourier_plus_at_c25_4_N3_residue_three_halves_to_5_abs_le
#print axioms nodeR_fourier_minus_at_c25_4_N3_residue_three_halves_to_5_abs_le

end ResidueBound
end FourierPanels_c25_4
end PrincipiaTractalis
