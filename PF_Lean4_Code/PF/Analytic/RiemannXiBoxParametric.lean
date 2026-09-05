/-
# PF.Analytic.RiemannXiBoxParametric

σ-parametric amplitude layer for the r331b top-edge boxes.

Box 0's `box0_pow_sum_tight_lb/ub`, `box0_a1_range`, `box0_a2_range`,
`box0_a_pow_bounds` are stated only for `σ ∈ [1/2, 9/16]`.  Their PROOFS are
already generic: `box0_pow_sum_tight_lb` never uses its σ hypotheses (pure
AM-GM), and `box0_pow_sum_tight_ub` is the exponent-monotonicity identity
`(u^δ - 1)(u^a - u^(-3/2-b)) ≥ 0` with box-0 endpoints substituted.

This module lifts exactly those two facts to free exponents, then instantiates
them at arbitrary box endpoints `σ_lo ≤ σ ≤ σ_hi` with `1/2 ≤ σ_lo`.  Nothing
else is generalized: the C²/M machinery (`abs_thetaPowCosSumD2_le`) is already
parametric in `a t p1 p2 L`.

Conjugate identity used throughout:
  `(1 - σ)/2 - 1 = -(3/2) - (σ/2 - 1)`
so the amplitude is `A(σ,u) = u^a + u^(-(3/2) - a)` with `a = σ/2 - 1`, and the
product of the two powers is `u^(-3/2)`, independent of σ.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b

namespace PrincipiaTractalis.RiemannXiBoxParametric

open scoped Real
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes

/-! ## §P.0 — the conjugate-exponent identity -/

/-- `(1-σ)/2 - 1 = -(3/2) - (σ/2 - 1)`. -/
theorem conj_exp (σ : ℝ) : (1 - σ) / 2 - 1 = -(3 / 2 : ℝ) - (σ / 2 - 1) := by
  ring

/-! ## §P.1 — exponent monotonicity of the amplitude, free exponents -/

/-- **Amplitude sum is monotone in the exponent.**  For `u ≥ 1`, `a ≤ b` and
`a + b ≥ -3/2`,
`u^a + u^(-3/2-a) ≤ u^b + u^(-3/2-b)`.

Generalises `box0_pow_sum_tight_ub`; same `(u^δ - 1)(u^a - u^(-3/2-b)) ≥ 0`
identity, with the box-0 endpoints replaced by free `a`, `b`. -/
theorem pow_sum_mono {u a b : ℝ} (hu : 1 ≤ u) (hab : a ≤ b)
    (hsum : -(3 / 2 : ℝ) ≤ a + b) :
    u ^ a + u ^ (-(3 / 2 : ℝ) - a) ≤ u ^ b + u ^ (-(3 / 2 : ℝ) - b) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  set δ := b - a with hδ_def
  have hδ_nn : 0 ≤ δ := by rw [hδ_def]; linarith
  have h_a_ge : -(3 / 2 : ℝ) - b ≤ a := by linarith
  have h_uδ_ge_one : 1 ≤ u ^ δ := by
    have h0 : u ^ (0 : ℝ) = 1 := Real.rpow_zero u
    rw [← h0]
    exact Real.rpow_le_rpow_of_exponent_le hu hδ_nn
  have h_pw_ge : u ^ (-(3 / 2 : ℝ) - b) ≤ u ^ a :=
    Real.rpow_le_rpow_of_exponent_le hu h_a_ge
  have h_ub_eq : u ^ b = u ^ a * u ^ δ := by
    have h_exp : b = a + δ := by rw [hδ_def]; ring
    rw [h_exp, Real.rpow_add hu0]
  have h_uconj_eq : u ^ (-(3 / 2 : ℝ) - a) = u ^ (-(3 / 2 : ℝ) - b) * u ^ δ := by
    have h_exp : -(3 / 2 : ℝ) - a = (-(3 / 2 : ℝ) - b) + δ := by rw [hδ_def]; ring
    rw [h_exp, Real.rpow_add hu0]
  rw [h_ub_eq, h_uconj_eq]
  have h_diff_nn : 0 ≤ u ^ δ - 1 := by linarith
  have h_pw_diff_nn : 0 ≤ u ^ a - u ^ (-(3 / 2 : ℝ) - b) := by linarith
  nlinarith [mul_nonneg h_diff_nn h_pw_diff_nn]

/-- **Amplitude difference is monotone in the exponent** — termwise, no
cancellation needed. -/
theorem pow_diff_mono {u a b : ℝ} (hu : 1 ≤ u) (hab : a ≤ b) :
    u ^ a - u ^ (-(3 / 2 : ℝ) - a) ≤ u ^ b - u ^ (-(3 / 2 : ℝ) - b) := by
  have h1 : u ^ a ≤ u ^ b := Real.rpow_le_rpow_of_exponent_le hu hab
  have h2 : u ^ (-(3 / 2 : ℝ) - b) ≤ u ^ (-(3 / 2 : ℝ) - a) :=
    Real.rpow_le_rpow_of_exponent_le hu (by linarith)
  linarith

/-! ## §P.2 — box-parametric amplitude enclosures -/

variable {σ σlo σhi u : ℝ}

/-- σ-uniform amplitude LOWER bound on a box, evaluated at `σ_lo`. -/
theorem box_pow_sum_lb (hu : 1 ≤ u) (hlo : (1 : ℝ) / 2 ≤ σlo)
    (h0 : σlo ≤ σ) :
    u ^ (σlo / 2 - 1) + u ^ ((1 - σlo) / 2 - 1)
      ≤ u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1) := by
  rw [conj_exp σlo, conj_exp σ]
  exact pow_sum_mono hu (by linarith) (by linarith)

/-- σ-uniform amplitude UPPER bound on a box, evaluated at `σ_hi`. -/
theorem box_pow_sum_ub (hu : 1 ≤ u) (hlo : (1 : ℝ) / 2 ≤ σ)
    (h1 : σ ≤ σhi) :
    u ^ (σ / 2 - 1) + u ^ ((1 - σ) / 2 - 1)
      ≤ u ^ (σhi / 2 - 1) + u ^ ((1 - σhi) / 2 - 1) := by
  rw [conj_exp σ, conj_exp σhi]
  exact pow_sum_mono hu (by linarith) (by linarith)

/-- σ-uniform amplitude-difference LOWER bound, evaluated at `σ_lo`. -/
theorem box_pow_diff_lb (hu : 1 ≤ u) (h0 : σlo ≤ σ) :
    u ^ (σlo / 2 - 1) - u ^ ((1 - σlo) / 2 - 1)
      ≤ u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1) := by
  rw [conj_exp σlo, conj_exp σ]
  exact pow_diff_mono hu (by linarith)

/-- σ-uniform amplitude-difference UPPER bound, evaluated at `σ_hi`. -/
theorem box_pow_diff_ub (hu : 1 ≤ u) (h1 : σ ≤ σhi) :
    u ^ (σ / 2 - 1) - u ^ ((1 - σ) / 2 - 1)
      ≤ u ^ (σhi / 2 - 1) - u ^ ((1 - σhi) / 2 - 1) := by
  rw [conj_exp σ, conj_exp σhi]
  exact pow_diff_mono hu (by linarith)

/-! ## §P.3 — box-parametric exponent ranges and `p1`/`p2` -/

/-- Both exponents `a₁ = σ/2-1` and `a₂ = (1-σ)/2-1` lie in
`[-(1+σ_hi)/2, σ_hi/2 - 1]` for `σ ∈ [σ_lo, σ_hi]`, `1/2 ≤ σ_lo`, `σ_hi ≤ 1`. -/
theorem box_a1_range (hlo : (1 : ℝ) / 2 ≤ σlo) (h0 : σlo ≤ σ) (h1 : σ ≤ σhi) :
    -((1 + σhi) / 2) ≤ σ / 2 - 1 ∧ σ / 2 - 1 ≤ σhi / 2 - 1 :=
  ⟨by linarith, by linarith⟩

theorem box_a2_range (hlo : (1 : ℝ) / 2 ≤ σlo) (h0 : σlo ≤ σ) (h1 : σ ≤ σhi) :
    -((1 + σhi) / 2) ≤ (1 - σ) / 2 - 1 ∧ (1 - σ) / 2 - 1 ≤ σhi / 2 - 1 := by
  constructor
  · linarith
  · linarith

/-- `a ∈ [-(1+σ_hi)/2, σ_hi/2 - 1]` with `σ_hi ≤ 1` gives `a ≤ 0`,
`|a| ≤ (1+σ_hi)/2`, and `|a(a-1)| ≤ p2` for `p2 = ((1+σ_hi)/2)·((1+σ_hi)/2 + 1)`. -/
theorem box_a_pow_bounds {a : ℝ} (hσhi : σhi ≤ 1) (hσhi0 : (1 : ℝ) / 2 ≤ σhi)
    (h_lo : -((1 + σhi) / 2) ≤ a) (h_hi : a ≤ σhi / 2 - 1) :
    a ≤ 0 ∧ |a| ≤ (1 + σhi) / 2 ∧
      |a * (a - 1)| ≤ ((1 + σhi) / 2) * ((1 + σhi) / 2 + 1) := by
  have ha_neg : a < 0 := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [abs_le]; exact ⟨by linarith, by linarith⟩
  · have ha1_neg : a - 1 < 0 := by linarith
    have h_prod_pos : 0 < a * (a - 1) := mul_pos_of_neg_of_neg ha_neg ha1_neg
    rw [abs_of_pos h_prod_pos]
    nlinarith [h_lo, h_hi, sq_nonneg (a + (1 + σhi) / 2)]

/-! ## §P.4 — box-parametric uniform C² bounds

Mirrors `abs_realThetaRe/ImIntegrandND2_le_box0` with `p1 = (1+σ_hi)/2`,
`p2 = p1(p1+1)` instead of box-0's `25/32`, `1425/1024`.  At `σ_hi = 9/16`
these reduce to exactly the box-0 constants. -/

theorem abs_realThetaReIntegrandND2_le_box {p1 p2 : ℝ}
    (hp1 : (1 + σhi) / 2 ≤ p1) (hp2 : ((1 + σhi) / 2) * ((1 + σhi) / 2 + 1) ≤ p2)
    (hσhi1 : σhi ≤ 1) (hσhi0 : (1 : ℝ) / 2 ≤ σhi) (hlo : (1 : ℝ) / 2 ≤ σlo)
    (h0 : σlo ≤ σ) (h1 : σ ≤ σhi)
    {L : ℝ} (hL : 1 ≤ L) (N : ℕ) {u : ℝ} (hu : L ≤ u) :
    |realThetaReIntegrandND2 N σ 15 u|
      ≤ 2 * ∑ n ∈ Finset.range N, thetaPowTermM 15 p1 p2 L n := by
  have ⟨ha1_lo, ha1_hi⟩ := box_a1_range (σlo := σlo) (σhi := σhi) hlo h0 h1
  have ⟨ha2_lo, ha2_hi⟩ := box_a2_range (σlo := σlo) (σhi := σhi) hlo h0 h1
  have ⟨ha1_np, ha1_p1, ha1_p2⟩ :=
    box_a_pow_bounds (σhi := σhi) hσhi1 hσhi0 ha1_lo ha1_hi
  have ⟨ha2_np, ha2_p1, ha2_p2⟩ :=
    box_a_pow_bounds (σhi := σhi) hσhi1 hσhi0 ha2_lo ha2_hi
  have hb1 := abs_thetaPowCosSumD2_le (t := 15) (p1 := p1) (p2 := p2) ha1_np
    (le_trans ha1_p1 hp1) (le_trans ha1_p2 hp2) N hL hu
  have hb2 := abs_thetaPowCosSumD2_le (t := 15) (p1 := p1) (p2 := p2) ha2_np
    (le_trans ha2_p1 hp1) (le_trans ha2_p2 hp2) N hL hu
  unfold realThetaReIntegrandND2
  calc |thetaPowCosSumD2 (σ / 2 - 1) 15 N u
          + thetaPowCosSumD2 ((1 - σ) / 2 - 1) 15 N u|
      ≤ |thetaPowCosSumD2 (σ / 2 - 1) 15 N u|
        + |thetaPowCosSumD2 ((1 - σ) / 2 - 1) 15 N u| := abs_add _ _
    _ ≤ _ + _ := add_le_add hb1 hb2
    _ = 2 * ∑ n ∈ Finset.range N, thetaPowTermM 15 p1 p2 L n := by ring

theorem abs_realThetaImIntegrandND2_le_box {p1 p2 : ℝ}
    (hp1 : (1 + σhi) / 2 ≤ p1) (hp2 : ((1 + σhi) / 2) * ((1 + σhi) / 2 + 1) ≤ p2)
    (hσhi1 : σhi ≤ 1) (hσhi0 : (1 : ℝ) / 2 ≤ σhi) (hlo : (1 : ℝ) / 2 ≤ σlo)
    (h0 : σlo ≤ σ) (h1 : σ ≤ σhi)
    {L : ℝ} (hL : 1 ≤ L) (N : ℕ) {u : ℝ} (hu : L ≤ u) :
    |realThetaImIntegrandND2 N σ 15 u|
      ≤ 2 * ∑ n ∈ Finset.range N, thetaPowTermM 15 p1 p2 L n := by
  have ⟨ha1_lo, ha1_hi⟩ := box_a1_range (σlo := σlo) (σhi := σhi) hlo h0 h1
  have ⟨ha2_lo, ha2_hi⟩ := box_a2_range (σlo := σlo) (σhi := σhi) hlo h0 h1
  have ⟨ha1_np, ha1_p1, ha1_p2⟩ :=
    box_a_pow_bounds (σhi := σhi) hσhi1 hσhi0 ha1_lo ha1_hi
  have ⟨ha2_np, ha2_p1, ha2_p2⟩ :=
    box_a_pow_bounds (σhi := σhi) hσhi1 hσhi0 ha2_lo ha2_hi
  have hb1 := abs_thetaPowSinSumD2_le (t := 15) (p1 := p1) (p2 := p2) ha1_np
    (le_trans ha1_p1 hp1) (le_trans ha1_p2 hp2) N hL hu
  have hb2 := abs_thetaPowSinSumD2_le (t := 15) (p1 := p1) (p2 := p2) ha2_np
    (le_trans ha2_p1 hp1) (le_trans ha2_p2 hp2) N hL hu
  unfold realThetaImIntegrandND2
  calc |thetaPowSinSumD2 (σ / 2 - 1) 15 N u
          - thetaPowSinSumD2 ((1 - σ) / 2 - 1) 15 N u|
      ≤ |thetaPowSinSumD2 (σ / 2 - 1) 15 N u|
        + |thetaPowSinSumD2 ((1 - σ) / 2 - 1) 15 N u| := abs_sub _ _
    _ ≤ _ + _ := add_le_add hb1 hb2
    _ = 2 * ∑ n ∈ Finset.range N, thetaPowTermM 15 p1 p2 L n := by ring

/-! ## §P.5 — box-parametric composite-midpoint error wrappers -/

theorem box_re_midpoint_error_on_segment {L U : ℝ} {n : ℕ} (N : ℕ) {p1 p2 : ℝ}
    (hp1 : (1 + σhi) / 2 ≤ p1) (hp2 : ((1 + σhi) / 2) * ((1 + σhi) / 2 + 1) ≤ p2)
    (hσhi1 : σhi ≤ 1) (hσhi0 : (1 : ℝ) / 2 ≤ σhi) (hlo : (1 : ℝ) / 2 ≤ σlo)
    (hσ0 : σlo ≤ σ) (hσ1 : σ ≤ σhi)
    (hL : 1 ≤ L) (hLU : L ≤ U) (hn : 0 < n) :
    |(∫ u in L..U, realThetaReIntegrandN N σ 15 u)
       - (U - L) / n
         * ∑ i ∈ Finset.range n,
             realThetaReIntegrandN N σ 15 (L + (U - L) / n * (i + 1/2))|
      ≤ (2 * ∑ n' ∈ Finset.range N, thetaPowTermM 15 p1 p2 L n')
        * (U - L) ^ 3 / (24 * n ^ 2) := by
  refine PrincipiaTractalis.XiQuadrature.composite_midpoint_error
    (f := fun u => realThetaReIntegrandN N σ 15 u)
    (f' := fun u => realThetaReIntegrandND1 N σ 15 u)
    (f'' := fun u => realThetaReIntegrandND2 N σ 15 u)
    hn hLU ?_ ?_ ?_
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans hL hx.1)
    exact hasDerivAt_realThetaReIntegrandN N σ 15 hx_pos
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans hL hx.1)
    exact hasDerivAt_realThetaReIntegrandND1 N σ 15 hx_pos
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    exact abs_realThetaReIntegrandND2_le_box (σlo := σlo) (σhi := σhi)
      (p1 := p1) (p2 := p2) hp1 hp2 hσhi1 hσhi0 hlo hσ0 hσ1 hL N hx.1

theorem box_im_midpoint_error_on_segment {L U : ℝ} {n : ℕ} (N : ℕ) {p1 p2 : ℝ}
    (hp1 : (1 + σhi) / 2 ≤ p1) (hp2 : ((1 + σhi) / 2) * ((1 + σhi) / 2 + 1) ≤ p2)
    (hσhi1 : σhi ≤ 1) (hσhi0 : (1 : ℝ) / 2 ≤ σhi) (hlo : (1 : ℝ) / 2 ≤ σlo)
    (hσ0 : σlo ≤ σ) (hσ1 : σ ≤ σhi)
    (hL : 1 ≤ L) (hLU : L ≤ U) (hn : 0 < n) :
    |(∫ u in L..U, realThetaImIntegrandN N σ 15 u)
       - (U - L) / n
         * ∑ i ∈ Finset.range n,
             realThetaImIntegrandN N σ 15 (L + (U - L) / n * (i + 1/2))|
      ≤ (2 * ∑ n' ∈ Finset.range N, thetaPowTermM 15 p1 p2 L n')
        * (U - L) ^ 3 / (24 * n ^ 2) := by
  refine PrincipiaTractalis.XiQuadrature.composite_midpoint_error
    (f := fun u => realThetaImIntegrandN N σ 15 u)
    (f' := fun u => realThetaImIntegrandND1 N σ 15 u)
    (f'' := fun u => realThetaImIntegrandND2 N σ 15 u)
    hn hLU ?_ ?_ ?_
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans hL hx.1)
    exact hasDerivAt_realThetaImIntegrandN N σ 15 hx_pos
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one (le_trans hL hx.1)
    exact hasDerivAt_realThetaImIntegrandND1 N σ 15 hx_pos
  · intro x hx
    rw [Set.uIcc_of_le hLU] at hx
    exact abs_realThetaImIntegrandND2_le_box (σlo := σlo) (σhi := σhi)
      (p1 := p1) (p2 := p2) hp1 hp2 hσhi1 hσhi0 hlo hσ0 hσ1 hL N hx.1

end PrincipiaTractalis.RiemannXiBoxParametric
