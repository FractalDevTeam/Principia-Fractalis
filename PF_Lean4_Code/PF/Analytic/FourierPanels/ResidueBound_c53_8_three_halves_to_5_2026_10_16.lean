/-
# PF.Analytic.FourierPanels.ResidueBound_c53_8_three_halves_to_5_2026_10_16

**Residue bound** between the panel pack cutoff `u = 3/2` and the
analytic tail cutoff `u = 5` for the `c = 53/8` pilot.

Mirror of `ResidueBound_c6_three_halves_to_5_2026_10_15.lean`. The
uniform-over-interval argument is c-independent: we use
`|cos|, |sin| ≤ 1`.

**Strategy.** Monotone-product endpoint-tight bound. For `u ∈ [3/2, 5]`,

  `|nodeR_fourier_±_at_c53_8_N3 u| ≤ (exp(u/2) + 1) · (3 · exp(-π · exp u))`

Both factors are peaked at `u = 3/2` (the product is antitone on `[3/2, ∞)`):

* `(exp(u/2) + 1) ≤ 2 · exp(u/2)` on `u ≥ 0` (via `1 ≤ exp(u/2)`).
* `h(u) := u/2 − π · exp u` is antitone on `[3/2, ∞)`: using `exp u ≥
    exp(3/2) + exp(3/2) · (u − 3/2)` (`add_one_le_exp` shifted),
    `h(u) − h(3/2) ≤ (u − 3/2) · (1/2 − π · exp(3/2)) ≤ 0` because
    `π · exp(3/2) ≥ 14 > 1/2`.
* Hence `exp(u/2 − π · exp u) ≤ exp(3/4 − π · exp(3/2))
    = exp(3/4) · exp(−π · exp(3/2)) ≤ 2.72 · (1/10⁶) = 272/10⁸`
    (using `exp(3/4) ≤ exp 1 ≤ 2.72` and the c=13/2 result
    `exp(−π · exp(3/2)) ≤ 1/10⁶`).
* Combined: `(exp(u/2) + 1) · exp(−π · exp u) ≤ 2 · 272/10⁸ = 544/10⁸`.
* Pointwise: `|f u| ≤ 3 · 544/10⁸ = 1632/10⁸ ≈ 1.63·10⁻⁵` on `[3/2, 5]`.
* Integral: `|∫_(3/2)^5 f| ≤ (1632/10⁸) · (7/2) = 5712/10⁸ ≈ 5.71·10⁻⁵`
  (required for the c=53/8 Gate-1 budget — the c=13/2 bound `231/10⁶` is
  insufficient as c² grows from `169/4` to `2809/64`).

The exp-factor tightening `exp(−π · exp u) ≤ 1/10⁶` is inherited from the
c=13/2 pilot (same majorant, same endpoint evaluation). The new tightening
here is the growth-factor side: `(exp(u/2) + 1)` was previously loosened
to `22` across the whole interval `[3/2, 5]`; via the monotone-product
argument we now use its tight bound at `u = 3/2`, scaled by the standard
`(exp(x) + 1) ≤ 2 · exp(x)` for `x ≥ 0`. No new mathematics — same
family of exp-monotonicity + convexity facts.

Three-axiom bar: every top-level declaration prints exactly
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/
import PF.Analytic.FourierPanels.CoreDefs_c53_8_2026_10_16
import PF.Analytic.FourierPanels.Seg01Range_c53_8_2026_10_16
import PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c53_8
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

lemma nodeR_fourier_plus_at_c53_8_N3_abs_le_mul_exp (u : ℝ) :
    |nodeR_fourier_plus_at_c53_8_N3 u|
      ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) := by
  unfold nodeR_fourier_plus_at_c53_8_N3
  have h_half : u * (0.5 : ℝ) = u / 2 := by ring
  rw [h_half]
  have h_cos : |Real.cos ((3.3125 : ℝ) * u)| ≤ 1 := Real.abs_cos_le_one _
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
  calc (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * |Real.cos ((3.3125 : ℝ) * u)|
      ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * 1 :=
        mul_le_mul_of_nonneg_left h_cos h_factor_nn
    _ = Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u := by ring
    _ ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) := h_factor_le

lemma nodeR_fourier_minus_at_c53_8_N3_abs_le_mul_exp (u : ℝ) :
    |nodeR_fourier_minus_at_c53_8_N3 u|
      ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) := by
  unfold nodeR_fourier_minus_at_c53_8_N3
  have h_half : u * (0.5 : ℝ) = u / 2 := by ring
  rw [h_half]
  have h_sin : |Real.sin ((3.3125 : ℝ) * u)| ≤ 1 := Real.abs_sin_le_one _
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
  calc |Real.exp (u / 2) * omega_N3_at_exp u - omega_N3_at_exp u| * |Real.sin ((3.3125 : ℝ) * u)|
      ≤ (Real.exp (u / 2) * omega_N3_at_exp u + omega_N3_at_exp u) * |Real.sin ((3.3125 : ℝ) * u)| := by
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

/-! ### Endpoint-tight exp lemmas for the c=53/8 pilot.
Legion's finding 2026-10-16: `exp(-π · exp u) ≤ exp(-14) ≤ 1/10⁶` on `[3/2, ∞)`
is a strict tightening of the loose `exp(-4π) ≤ 1/279841` used in prior pilots.
Needed to meet the Gate-1 budget at `c = 53/8`.
-/

/-- `exp 3 ≥ 20` via `exp 1 ≥ 2.7182818283` (`Real.exp_one_gt_d9`) and `(2.718)^3 ≥ 20`. -/
lemma exp_three_ge_twenty : (20 : ℝ) ≤ Real.exp 3 := by
  have h_one_gt : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h_one_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have h_cube : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num]
    rw [Real.exp_add, Real.exp_add]; ring
  rw [h_cube]
  have h_le : (2.7182818283 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h_one_gt.le 3
  have h_decimal : (20 : ℝ) ≤ (2.7182818283 : ℝ) ^ 3 := by norm_num
  linarith

/-- `exp(3/2) ≥ 447/100 = 4.47` via `exp(3/2)² = exp 3 ≥ 20` and `(447/100)² = 19.9809 ≤ 20`. -/
lemma exp_three_halves_ge_tight : (447 / 100 : ℝ) ≤ Real.exp (3 / 2) := by
  have h3 : (20 : ℝ) ≤ Real.exp 3 := exp_three_ge_twenty
  have h_sq : Real.exp (3 / 2) * Real.exp (3 / 2) = Real.exp 3 := by
    rw [← Real.exp_add]; norm_num
  have h_pos : (0 : ℝ) < Real.exp (3 / 2) := Real.exp_pos _
  nlinarith [h3, h_sq, h_pos]

/-- `14 ≤ π · exp(3/2)` via `π > 3.14` and `exp(3/2) ≥ 4.47` ⇒ `π·exp(3/2) ≥ 14.0358`. -/
lemma pi_mul_exp_three_halves_ge_fourteen : (14 : ℝ) ≤ π * Real.exp (3 / 2) := by
  have hπ : (3.14 : ℝ) < π := Real.pi_gt_d2
  have h_exp : (447 / 100 : ℝ) ≤ Real.exp (3 / 2) := exp_three_halves_ge_tight
  have h_pos : (0 : ℝ) < Real.exp (3 / 2) := Real.exp_pos _
  nlinarith [hπ, h_exp, h_pos]

/-- `14 ≤ π · exp u` on `[3/2, ∞)` via `exp u ≥ exp(3/2)` and `π·exp(3/2) ≥ 14`. -/
lemma pi_mul_exp_u_ge_fourteen {u : ℝ} (hu : 3 / 2 ≤ u) : (14 : ℝ) ≤ π * Real.exp u := by
  have h_mono : Real.exp (3 / 2) ≤ Real.exp u := Real.exp_le_exp.mpr hu
  have h_14 : (14 : ℝ) ≤ π * Real.exp (3 / 2) := pi_mul_exp_three_halves_ge_fourteen
  have hπ_pos : (0 : ℝ) < π := Real.pi_pos
  have h_mul : π * Real.exp (3 / 2) ≤ π * Real.exp u :=
    mul_le_mul_of_nonneg_left h_mono hπ_pos.le
  linarith

/-- `exp(-(π · exp u)) ≤ exp(-14)` on `[3/2, ∞)`. -/
lemma exp_neg_pi_exp_u_le_tight {u : ℝ} (hu : 3 / 2 ≤ u) :
    Real.exp (-(π * Real.exp u)) ≤ Real.exp (-14) := by
  apply Real.exp_le_exp.mpr
  have h := pi_mul_exp_u_ge_fourteen hu
  linarith

/-- `exp 14 ≥ 10⁶` via `exp 1 ≥ 2.7` and `(2.7)^14 ≈ 1.09·10⁶ > 10⁶`. -/
lemma exp_fourteen_ge_million : (10 ^ 6 : ℝ) ≤ Real.exp 14 := by
  have h_one_gt : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have h_one_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have h_14_eq : Real.exp 14 = (Real.exp 1) ^ 14 := by
    rw [← Real.exp_nat_mul 1 14]
    congr 1; push_cast; ring
  rw [h_14_eq]
  have h_le : (2.7 : ℝ) ^ 14 ≤ (Real.exp 1) ^ 14 :=
    pow_le_pow_left₀ (by norm_num) h_one_gt.le 14
  have h_decimal : (10 ^ 6 : ℝ) ≤ (2.7 : ℝ) ^ 14 := by norm_num
  linarith

/-- `exp(-14) ≤ 1/10⁶`. -/
lemma exp_neg_fourteen_le : Real.exp (-14) ≤ 1 / 10 ^ 6 := by
  have h := exp_fourteen_ge_million
  have h_pos : (0 : ℝ) < Real.exp 14 := Real.exp_pos _
  have h_ten_pos : (0 : ℝ) < (10 : ℝ) ^ 6 := by norm_num
  rw [Real.exp_neg, show (1 : ℝ) / 10 ^ 6 = (10 ^ 6 : ℝ)⁻¹ by field_simp]
  exact inv_anti₀ h_ten_pos h

/-! ### Monotone-product lemmas for the c=53/8 pilot's tighter residue bound. -/

/-- `(exp(u/2) + 1) ≤ 2 · exp(u/2)` for `u ≥ 0`, from `1 ≤ exp(u/2)`. -/
lemma exp_half_u_plus_one_le_two_exp_half_u {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (u / 2) + 1 ≤ 2 * Real.exp (u / 2) := by
  have h : (1 : ℝ) ≤ Real.exp (u / 2) := Real.one_le_exp (by linarith)
  linarith

/-- Convexity lower bound: `exp u ≥ exp(3/2) · (1 + (u - 3/2))` for all u. -/
lemma exp_u_ge_shifted (u : ℝ) :
    Real.exp u ≥ Real.exp (3 / 2) * (1 + (u - 3 / 2)) := by
  have h_eq : Real.exp u = Real.exp (3 / 2) * Real.exp (u - 3 / 2) := by
    rw [← Real.exp_add]
    congr 1; ring
  have h_shifted : 1 + (u - 3 / 2) ≤ Real.exp (u - 3 / 2) := by
    have := Real.add_one_le_exp (u - 3 / 2)
    linarith
  have h_pos : (0 : ℝ) ≤ Real.exp (3 / 2) := (Real.exp_pos _).le
  rw [h_eq]
  exact mul_le_mul_of_nonneg_left h_shifted h_pos

/-- `h(u) := u/2 - π · exp u` is antitone on `[3/2, ∞)`: for `u ≥ 3/2`,
`h(u) ≤ h(3/2) = 3/4 - π · exp(3/2)`. -/
lemma h_antitone_three_halves {u : ℝ} (hu : 3 / 2 ≤ u) :
    u / 2 - π * Real.exp u ≤ 3 / 4 - π * Real.exp (3 / 2) := by
  have h_shifted : Real.exp u ≥ Real.exp (3 / 2) * (1 + (u - 3 / 2)) := exp_u_ge_shifted u
  have h_14 : (14 : ℝ) ≤ π * Real.exp (3 / 2) := pi_mul_exp_three_halves_ge_fourteen
  have h_pi_pos : (0 : ℝ) < π := Real.pi_pos
  have h_exp_15_pos : (0 : ℝ) < Real.exp (3 / 2) := Real.exp_pos _
  have h_u_shift : (0 : ℝ) ≤ u - 3 / 2 := by linarith
  nlinarith [h_shifted, h_14, h_pi_pos, h_exp_15_pos, h_u_shift]

/-- `exp(3/4) ≤ 272/100`, via `exp(3/4) ≤ exp 1 ≤ 2.72`. -/
lemma exp_three_quarters_le_272 : Real.exp (3 / 4) ≤ 272 / 100 := by
  have h1 : Real.exp (3 / 4) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  linarith

/-- Combined: `exp(3/4 - π·exp(3/2)) ≤ 272/10⁸`. -/
lemma exp_h_three_halves_le : Real.exp (3 / 4 - π * Real.exp (3 / 2)) ≤ 272 / 10 ^ 8 := by
  have h_split : Real.exp (3 / 4 - π * Real.exp (3 / 2))
      = Real.exp (3 / 4) * Real.exp (-(π * Real.exp (3 / 2))) := by
    rw [show (3 / 4 - π * Real.exp (3 / 2) : ℝ) = 3 / 4 + (-(π * Real.exp (3 / 2))) from by ring,
        Real.exp_add]
  rw [h_split]
  have h_exp34 : Real.exp (3 / 4) ≤ 272 / 100 := exp_three_quarters_le_272
  have h_exp_neg : Real.exp (-(π * Real.exp (3 / 2))) ≤ 1 / 10 ^ 6 := by
    have h_neg_le : -(π * Real.exp (3 / 2)) ≤ -14 := by
      have := pi_mul_exp_three_halves_ge_fourteen; linarith
    have h_mono : Real.exp (-(π * Real.exp (3 / 2))) ≤ Real.exp (-14) :=
      Real.exp_le_exp.mpr h_neg_le
    linarith [exp_neg_fourteen_le]
  have h_pos_exp34 : (0 : ℝ) ≤ Real.exp (3 / 4) := (Real.exp_pos _).le
  have h_pos_exp_neg : (0 : ℝ) ≤ Real.exp (-(π * Real.exp (3 / 2))) := (Real.exp_pos _).le
  have h_pos_272 : (0 : ℝ) ≤ 272 / 100 := by norm_num
  have h_prod_bound : Real.exp (3 / 4) * Real.exp (-(π * Real.exp (3 / 2)))
      ≤ (272 / 100) * (1 / 10 ^ 6) := by
    calc Real.exp (3 / 4) * Real.exp (-(π * Real.exp (3 / 2)))
        ≤ (272 / 100) * Real.exp (-(π * Real.exp (3 / 2))) :=
          mul_le_mul_of_nonneg_right h_exp34 h_pos_exp_neg
      _ ≤ (272 / 100) * (1 / 10 ^ 6) :=
          mul_le_mul_of_nonneg_left h_exp_neg h_pos_272
  have h_prod_eq : (272 / 100 : ℝ) * (1 / 10 ^ 6) = 272 / 10 ^ 8 := by norm_num
  linarith

/-- Monotone-product bound: `exp(u/2) · exp(-π·exp u) ≤ 272/10⁸` on `[3/2, 5]`. -/
lemma exp_half_u_mul_exp_neg_pi_exp_u_le {u : ℝ} (hu_lo : 3 / 2 ≤ u) (hu_hi : u ≤ 5) :
    Real.exp (u / 2) * Real.exp (-(π * Real.exp u)) ≤ 272 / 10 ^ 8 := by
  have h_combine : Real.exp (u / 2) * Real.exp (-(π * Real.exp u))
      = Real.exp (u / 2 - π * Real.exp u) := by
    rw [show (u / 2 - π * Real.exp u : ℝ) = u / 2 + (-(π * Real.exp u)) from by ring,
        Real.exp_add]
  rw [h_combine]
  have h_antit : u / 2 - π * Real.exp u ≤ 3 / 4 - π * Real.exp (3 / 2) :=
    h_antitone_three_halves hu_lo
  have h_mono : Real.exp (u / 2 - π * Real.exp u) ≤ Real.exp (3 / 4 - π * Real.exp (3 / 2)) :=
    Real.exp_le_exp.mpr h_antit
  linarith [exp_h_three_halves_le]

/-- Full monotone-product bound: `(exp(u/2) + 1) · exp(-π·exp u) ≤ 544/10⁸` on `[3/2, 5]`. -/
lemma prod_tight_bound {u : ℝ} (hu_lo : 3 / 2 ≤ u) (hu_hi : u ≤ 5) :
    (Real.exp (u / 2) + 1) * Real.exp (-(π * Real.exp u)) ≤ 544 / 10 ^ 8 := by
  have h_two : Real.exp (u / 2) + 1 ≤ 2 * Real.exp (u / 2) :=
    exp_half_u_plus_one_le_two_exp_half_u (by linarith)
  have h_pos_neg_exp : (0 : ℝ) ≤ Real.exp (-(π * Real.exp u)) := (Real.exp_pos _).le
  have h_prod : Real.exp (u / 2) * Real.exp (-(π * Real.exp u)) ≤ 272 / 10 ^ 8 :=
    exp_half_u_mul_exp_neg_pi_exp_u_le hu_lo hu_hi
  calc (Real.exp (u / 2) + 1) * Real.exp (-(π * Real.exp u))
      ≤ (2 * Real.exp (u / 2)) * Real.exp (-(π * Real.exp u)) :=
        mul_le_mul_of_nonneg_right h_two h_pos_neg_exp
    _ = 2 * (Real.exp (u / 2) * Real.exp (-(π * Real.exp u))) := by ring
    _ ≤ 2 * (272 / 10 ^ 8) := by
        have h_two_pos : (0 : ℝ) ≤ 2 := by norm_num
        exact mul_le_mul_of_nonneg_left h_prod h_two_pos
    _ = 544 / 10 ^ 8 := by norm_num

/-! ## §3 — Uniform pointwise bound on `[3/2, 5]`. -/

lemma nodeR_fourier_plus_at_c53_8_N3_abs_uniform_le
    {u : ℝ} (hu_lo : 3 / 2 ≤ u) (hu_hi : u ≤ 5) :
    |nodeR_fourier_plus_at_c53_8_N3 u| ≤ 1632 / 10 ^ 8 := by
  have h1 := nodeR_fourier_plus_at_c53_8_N3_abs_le_mul_exp u
  have h_prod : (Real.exp (u / 2) + 1) * Real.exp (-(π * Real.exp u)) ≤ 544 / 10 ^ 8 :=
    prod_tight_bound hu_lo hu_hi
  have h_rhs_le :
      (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) ≤ 3 * (544 / 10 ^ 8) := by
    have h_eq : (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u)))
        = 3 * ((Real.exp (u / 2) + 1) * Real.exp (-(π * Real.exp u))) := by ring
    rw [h_eq]
    exact mul_le_mul_of_nonneg_left h_prod (by norm_num : (0 : ℝ) ≤ 3)
  have h_rhs_eq : (3 : ℝ) * (544 / 10 ^ 8) = 1632 / 10 ^ 8 := by norm_num
  linarith

lemma nodeR_fourier_minus_at_c53_8_N3_abs_uniform_le
    {u : ℝ} (hu_lo : 3 / 2 ≤ u) (hu_hi : u ≤ 5) :
    |nodeR_fourier_minus_at_c53_8_N3 u| ≤ 1632 / 10 ^ 8 := by
  have h1 := nodeR_fourier_minus_at_c53_8_N3_abs_le_mul_exp u
  have h_prod : (Real.exp (u / 2) + 1) * Real.exp (-(π * Real.exp u)) ≤ 544 / 10 ^ 8 :=
    prod_tight_bound hu_lo hu_hi
  have h_rhs_le :
      (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u))) ≤ 3 * (544 / 10 ^ 8) := by
    have h_eq : (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u)))
        = 3 * ((Real.exp (u / 2) + 1) * Real.exp (-(π * Real.exp u))) := by ring
    rw [h_eq]
    exact mul_le_mul_of_nonneg_left h_prod (by norm_num : (0 : ℝ) ≤ 3)
  have h_rhs_eq : (3 : ℝ) * (544 / 10 ^ 8) = 1632 / 10 ^ 8 := by norm_num
  linarith

/-! ## §4 — Residue integral bound. -/

theorem nodeR_fourier_plus_at_c53_8_N3_residue_three_halves_to_5_abs_le :
    |∫ u in (3/2 : ℝ)..(5 : ℝ), nodeR_fourier_plus_at_c53_8_N3 u| ≤ (5712 / 10 ^ 8 : ℝ) := by
  have h_bound :
      ‖∫ u in (3/2 : ℝ)..(5 : ℝ), nodeR_fourier_plus_at_c53_8_N3 u‖
        ≤ (1632 / 10 ^ 8 : ℝ) * |5 - 3/2| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (3/2 : ℝ) ≤ 5)] at hu
    have hu_lo : 3 / 2 ≤ u := le_of_lt hu.1
    have hu_hi : u ≤ 5 := hu.2
    rw [Real.norm_eq_abs]
    exact nodeR_fourier_plus_at_c53_8_N3_abs_uniform_le hu_lo hu_hi
  have h_abs_sub : |(5 : ℝ) - 3/2| = 7/2 := by
    rw [show ((5 : ℝ) - 3/2) = 7/2 by norm_num]
    exact abs_of_pos (by norm_num : (0 : ℝ) < 7/2)
  rw [h_abs_sub] at h_bound
  have h_prod : (1632 / 10 ^ 8 : ℝ) * (7 / 2) = 5712 / 10 ^ 8 := by norm_num
  rw [h_prod] at h_bound
  rw [Real.norm_eq_abs] at h_bound
  linarith

theorem nodeR_fourier_minus_at_c53_8_N3_residue_three_halves_to_5_abs_le :
    |∫ u in (3/2 : ℝ)..(5 : ℝ), nodeR_fourier_minus_at_c53_8_N3 u| ≤ (5712 / 10 ^ 8 : ℝ) := by
  have h_bound :
      ‖∫ u in (3/2 : ℝ)..(5 : ℝ), nodeR_fourier_minus_at_c53_8_N3 u‖
        ≤ (1632 / 10 ^ 8 : ℝ) * |5 - 3/2| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (3/2 : ℝ) ≤ 5)] at hu
    have hu_lo : 3 / 2 ≤ u := le_of_lt hu.1
    have hu_hi : u ≤ 5 := hu.2
    rw [Real.norm_eq_abs]
    exact nodeR_fourier_minus_at_c53_8_N3_abs_uniform_le hu_lo hu_hi
  have h_abs_sub : |(5 : ℝ) - 3/2| = 7/2 := by
    rw [show ((5 : ℝ) - 3/2) = 7/2 by norm_num]
    exact abs_of_pos (by norm_num : (0 : ℝ) < 7/2)
  rw [h_abs_sub] at h_bound
  have h_prod : (1632 / 10 ^ 8 : ℝ) * (7 / 2) = 5712 / 10 ^ 8 := by norm_num
  rw [h_prod] at h_bound
  rw [Real.norm_eq_abs] at h_bound
  linarith

/-! ## §Axiom check -/

#print axioms omega_N3_at_exp_le_three_exp
#print axioms nodeR_fourier_plus_at_c53_8_N3_abs_le_mul_exp
#print axioms nodeR_fourier_minus_at_c53_8_N3_abs_le_mul_exp
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
#print axioms exp_three_ge_twenty
#print axioms exp_three_halves_ge_tight
#print axioms pi_mul_exp_three_halves_ge_fourteen
#print axioms pi_mul_exp_u_ge_fourteen
#print axioms exp_neg_pi_exp_u_le_tight
#print axioms exp_fourteen_ge_million
#print axioms exp_neg_fourteen_le
#print axioms exp_half_u_plus_one_le_two_exp_half_u
#print axioms exp_u_ge_shifted
#print axioms h_antitone_three_halves
#print axioms exp_three_quarters_le_272
#print axioms exp_h_three_halves_le
#print axioms exp_half_u_mul_exp_neg_pi_exp_u_le
#print axioms prod_tight_bound
#print axioms nodeR_fourier_plus_at_c53_8_N3_abs_uniform_le
#print axioms nodeR_fourier_minus_at_c53_8_N3_abs_uniform_le
#print axioms nodeR_fourier_plus_at_c53_8_N3_residue_three_halves_to_5_abs_le
#print axioms nodeR_fourier_minus_at_c53_8_N3_residue_three_halves_to_5_abs_le

end ResidueBound
end FourierPanels_c53_8
end PrincipiaTractalis
