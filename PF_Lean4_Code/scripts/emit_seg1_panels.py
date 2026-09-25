#!/usr/bin/env python3
"""
emit_seg1_panels.py — mass-emit Stage-1 production node theorems.

For each node i=3..22 in segment [3/2, 25/16], u_i = (1105 + 2i)/736:
  - Compute mpmath dps=100 numerical Astar·C·W and Dstar·S·W
  - Choose outward rational RE_LO_i and IM_HI_i (or IM_LO_i for neg-sin)
  - Emit Lean node theorem in production exact-endpoint architecture

Panels: P2=[3,4,5], P3=[6,7,8], P4=[9,10,11], P5=[12,13,14],
        P6=[15,16,17], P7=[18,19,20], P8=[21,22].

Nodes 0-6: positive sin
Nodes 7-22: negative sin
"""
import mpmath as mp
from fractions import Fraction

mp.mp.dps = 100
PI = mp.pi

def compute_node(i):
    u = Fraction(1105 + 2*i, 736)
    u_mp = mp.mpf(u.numerator) / u.denominator
    p23 = mp.power(u_mp, -mp.mpf(23)/32)
    p25 = mp.power(u_mp, -mp.mpf(25)/32)
    log_u = mp.log(u_mp)
    c = mp.cos(mp.mpf(15)/2 * log_u)
    s = mp.sin(mp.mpf(15)/2 * log_u)
    om = mp.exp(-PI*u_mp) + mp.exp(-4*PI*u_mp) + mp.exp(-9*PI*u_mp)
    re_adv = (p23 + p25) * c * om
    im_adv = (p23 - p25) * s * om
    sin_pos = (s > 0)
    return u, u_mp, c, s, re_adv, im_adv, sin_pos

def outward_lo(x, digits=5):
    """Floor toward -∞ with `digits` after decimal point.  Returns Fraction."""
    scale = 10**digits
    return Fraction(int(mp.floor(x * scale)), scale)

def outward_hi(x, digits=7):
    """Ceil toward +∞ with `digits` after decimal point.  Returns Fraction."""
    scale = 10**digits
    return Fraction(int(mp.ceil(x * scale)), scale)

def emit_positive_sin_node(i):
    u, u_mp, c, s, re_adv, im_adv, sin_pos = compute_node(i)
    assert sin_pos, f"expected positive sin at i={i}, got s={float(s)}"
    RE_LO = outward_lo(re_adv, 5)  # 5 digits
    IM_HI = outward_hi(im_adv, 7)  # 7 digits
    u_str = f"{u.numerator}/{u.denominator}"
    u_rat_str = f"({u.numerator} : ℚ)/{u.denominator}"
    re_lo_str = f"({RE_LO.numerator}/{RE_LO.denominator} : ℝ)"
    im_hi_str = f"({IM_HI.numerator}/{IM_HI.denominator} : ℝ)"
    re_lo_i_str = f"({RE_LO.numerator}/{RE_LO.denominator} : _root_.Interval)"
    im_hi_i_str = f"({IM_HI.numerator}/{IM_HI.denominator} : _root_.Interval)"
    return f"""
/-! ## Node {i} at u = {u_str} — positive sin -/

private theorem u{i}_cos_np : Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) ≤ 0 := by
  have hlt : Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) < (0 : ℝ) := by
    refine _root_.Interval.approx_lt
      (_root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
          (_root_.Interval.ofRat ({u_rat_str}))))
      ((0 : _root_.Interval))
      (Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
      (0 : ℝ)
      (_root_.Interval.mem_approx_cos (by approx))
      (by approx)
      ?_
    decide +kernel
  linarith

private theorem u{i}_sin_nn : (0 : ℝ) ≤ Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) := by
  refine _root_.Interval.approx_le
    ((0 : _root_.Interval))
    (_root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str}))))
    (0 : ℝ)
    (Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (by approx)
    (_root_.Interval.mem_approx_sin (by approx))
    ?_
  decide +kernel

private theorem u{i}_re_adverse_ge :
    {re_lo_str}
      ≤ (({u_str} : ℝ) ^ (-(23/32 : ℝ)) + ({u_str} : ℝ) ^ (-(25/32 : ℝ)))
        * Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))
        * omegaPartial 3 ({u_str} : ℝ) := by
  have hu0 : (0 : ℝ) < ({u_str} : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine _root_.Interval.approx_le
    {re_lo_i_str}
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})) * _root_.Interval.ofRat (23/32)))
      + _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ({u_rat_str})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat_str})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat_str})))))
    {re_lo_str}
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel

private theorem u{i}_im_adverse_le :
    (({u_str} : ℝ) ^ (-(23/32 : ℝ)) - ({u_str} : ℝ) ^ (-(25/32 : ℝ)))
      * Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ))
      * omegaPartial 3 ({u_str} : ℝ)
      ≤ {im_hi_str} := by
  have hu0 : (0 : ℝ) < ({u_str} : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine le_of_lt <| _root_.Interval.approx_lt
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})) * _root_.Interval.ofRat (23/32)))
      - _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ({u_rat_str})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat_str})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat_str})))))
    {im_hi_i_str}
    _
    {im_hi_str}
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel

theorem node_{i}_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    {re_lo_str} ≤ realThetaReIntegrandN 3 σ 15 ({u_str} : ℝ)
    ∧ realThetaReIntegrandN 3 σ 15 ({u_str} : ℝ) ≤ 0
    ∧ (0 : ℝ) ≤ realThetaImIntegrandN 3 σ 15 ({u_str} : ℝ)
    ∧ realThetaImIntegrandN 3 σ 15 ({u_str} : ℝ) ≤ {im_hi_str} := by
  have hu1 : (1 : ℝ) ≤ ({u_str} : ℝ) := by norm_num
  have hA_nn : (0 : ℝ) ≤ ({u_str} : ℝ)^(σ/2 - 1) + ({u_str} : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_sum_nonneg σ hu1
  have hA_hi : ({u_str} : ℝ)^(σ/2 - 1) + ({u_str} : ℝ)^((1-σ)/2 - 1)
      ≤ ({u_str} : ℝ)^(-(23/32 : ℝ)) + ({u_str} : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_sum_tight_ub hu1 hσ0 hσ1
  have hD_nn : (0 : ℝ) ≤ ({u_str} : ℝ)^(σ/2 - 1) - ({u_str} : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_diff_nonneg hσ0 hu1
  have hD_hi : ({u_str} : ℝ)^(σ/2 - 1) - ({u_str} : ℝ)^((1-σ)/2 - 1)
      ≤ ({u_str} : ℝ)^(-(23/32 : ℝ)) - ({u_str} : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_diff_ub hσ0 hσ1 hu1
  have hW_nn : (0 : ℝ) ≤ omegaPartial 3 ({u_str} : ℝ) := omegaPartial_nonneg_here 3 _
  have hAstar_nn : (0 : ℝ) ≤ ({u_str} : ℝ)^(-(23/32 : ℝ)) + ({u_str} : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_sum_nonneg (9/16 : ℝ) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h; exact h
  have hDstar_nn : (0 : ℝ) ≤ ({u_str} : ℝ)^(-(23/32 : ℝ)) - ({u_str} : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_diff_nonneg (σ := 9/16) (by norm_num) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h; exact h
  have hC_np : Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) ≤ 0 := u{i}_cos_np
  have hS_nn : (0 : ℝ) ≤ Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) := u{i}_sin_nn
  have hRe := re_scalar_bounds_cos_neg
    (A_lo := 0)
    (A_hi := ({u_str} : ℝ)^(-(23/32 : ℝ)) + ({u_str} : ℝ)^(-(25/32 : ℝ)))
    (C_lo := Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (C_hi := 0) (W_lo := 0) (W_hi := omegaPartial 3 ({u_str} : ℝ))
    (le_refl 0) hAstar_nn hC_np hC_np (le_refl 0)
    (le_refl 0) hW_nn
    hA_nn hA_hi (le_refl _) hC_np hW_nn (le_refl _)
  have hIm := im_scalar_bounds_sin_nonneg
    (D_lo := 0)
    (D_hi := ({u_str} : ℝ)^(-(23/32 : ℝ)) - ({u_str} : ℝ)^(-(25/32 : ℝ)))
    (S_lo := 0)
    (S_hi := Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (W_lo := 0) (W_hi := omegaPartial 3 ({u_str} : ℝ))
    (le_refl 0) hDstar_nn (le_refl 0) hS_nn (le_refl 0) hW_nn
    hD_nn hD_hi hS_nn (le_refl _) hW_nn (le_refl _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold realThetaReIntegrandN
    linarith [hRe.1, u{i}_re_adverse_ge]
  · unfold realThetaReIntegrandN
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith [hRe.2]
  · unfold realThetaImIntegrandN
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith [hIm.1]
  · unfold realThetaImIntegrandN
    linarith [hIm.2, u{i}_im_adverse_le]
"""

def emit_negative_sin_node(i):
    u, u_mp, c, s, re_adv, im_adv, sin_pos = compute_node(i)
    assert not sin_pos, f"expected negative sin at i={i}, got s={float(s)}"
    RE_LO = outward_lo(re_adv, 5)
    # For negative sin: im_adv is positive (Dstar>0, S<0, W>0 → im_adv < 0)
    # Wait: Dstar > 0, S < 0, W > 0 → im_adv < 0. Actually im_adv = Dstar*S*W < 0.
    # IM_LO_i ≤ im_adv < 0, so IM_LO_i is negative.
    # We want: outward LOWER means MORE NEGATIVE
    IM_LO = outward_lo(im_adv, 7)  # floor → more negative
    u_str = f"{u.numerator}/{u.denominator}"
    u_rat_str = f"({u.numerator} : ℚ)/{u.denominator}"
    re_lo_str = f"({RE_LO.numerator}/{RE_LO.denominator} : ℝ)"
    im_lo_str = f"({IM_LO.numerator}/{IM_LO.denominator} : ℝ)"
    re_lo_i_str = f"({RE_LO.numerator}/{RE_LO.denominator} : _root_.Interval)"
    im_lo_i_str = f"({IM_LO.numerator}/{IM_LO.denominator} : _root_.Interval)"
    return f"""
/-! ## Node {i} at u = {u_str} — negative sin -/

private theorem u{i}_cos_np : Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) ≤ 0 := by
  have hlt : Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) < (0 : ℝ) := by
    refine _root_.Interval.approx_lt
      (_root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
          (_root_.Interval.ofRat ({u_rat_str}))))
      ((0 : _root_.Interval))
      (Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
      (0 : ℝ)
      (_root_.Interval.mem_approx_cos (by approx))
      (by approx)
      ?_
    decide +kernel
  linarith

private theorem u{i}_sin_np : Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) ≤ 0 := by
  have hlt : Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) < (0 : ℝ) := by
    refine _root_.Interval.approx_lt
      (_root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
          (_root_.Interval.ofRat ({u_rat_str}))))
      ((0 : _root_.Interval))
      (Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
      (0 : ℝ)
      (_root_.Interval.mem_approx_sin (by approx))
      (by approx)
      ?_
    decide +kernel
  linarith

private theorem u{i}_re_adverse_ge :
    {re_lo_str}
      ≤ (({u_str} : ℝ) ^ (-(23/32 : ℝ)) + ({u_str} : ℝ) ^ (-(25/32 : ℝ)))
        * Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))
        * omegaPartial 3 ({u_str} : ℝ) := by
  have hu0 : (0 : ℝ) < ({u_str} : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine _root_.Interval.approx_le
    {re_lo_i_str}
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})) * _root_.Interval.ofRat (23/32)))
      + _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ({u_rat_str})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat_str})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat_str})))))
    {re_lo_str}
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel

private theorem u{i}_im_adverse_ge :
    {im_lo_str}
      ≤ (({u_str} : ℝ) ^ (-(23/32 : ℝ)) - ({u_str} : ℝ) ^ (-(25/32 : ℝ)))
        * Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ))
        * omegaPartial 3 ({u_str} : ℝ) := by
  have hu0 : (0 : ℝ) < ({u_str} : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine _root_.Interval.approx_le
    {im_lo_i_str}
    ((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})) * _root_.Interval.ofRat (23/32)))
      - _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat_str})))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ({u_rat_str})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat_str})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat_str})))))
    {im_lo_str}
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel

theorem node_{i}_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    {re_lo_str} ≤ realThetaReIntegrandN 3 σ 15 ({u_str} : ℝ)
    ∧ realThetaReIntegrandN 3 σ 15 ({u_str} : ℝ) ≤ 0
    ∧ {im_lo_str} ≤ realThetaImIntegrandN 3 σ 15 ({u_str} : ℝ)
    ∧ realThetaImIntegrandN 3 σ 15 ({u_str} : ℝ) ≤ 0 := by
  have hu1 : (1 : ℝ) ≤ ({u_str} : ℝ) := by norm_num
  have hA_nn : (0 : ℝ) ≤ ({u_str} : ℝ)^(σ/2 - 1) + ({u_str} : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_sum_nonneg σ hu1
  have hA_hi : ({u_str} : ℝ)^(σ/2 - 1) + ({u_str} : ℝ)^((1-σ)/2 - 1)
      ≤ ({u_str} : ℝ)^(-(23/32 : ℝ)) + ({u_str} : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_sum_tight_ub hu1 hσ0 hσ1
  have hD_nn : (0 : ℝ) ≤ ({u_str} : ℝ)^(σ/2 - 1) - ({u_str} : ℝ)^((1-σ)/2 - 1) :=
    box0_pow_diff_nonneg hσ0 hu1
  have hD_hi : ({u_str} : ℝ)^(σ/2 - 1) - ({u_str} : ℝ)^((1-σ)/2 - 1)
      ≤ ({u_str} : ℝ)^(-(23/32 : ℝ)) - ({u_str} : ℝ)^(-(25/32 : ℝ)) :=
    box0_pow_diff_ub hσ0 hσ1 hu1
  have hW_nn : (0 : ℝ) ≤ omegaPartial 3 ({u_str} : ℝ) := omegaPartial_nonneg_here 3 _
  have hAstar_nn : (0 : ℝ) ≤ ({u_str} : ℝ)^(-(23/32 : ℝ)) + ({u_str} : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_sum_nonneg (9/16 : ℝ) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h; exact h
  have hDstar_nn : (0 : ℝ) ≤ ({u_str} : ℝ)^(-(23/32 : ℝ)) - ({u_str} : ℝ)^(-(25/32 : ℝ)) := by
    have h := box0_pow_diff_nonneg (σ := 9/16) (by norm_num) hu1
    have eq1 : ((9 : ℝ)/16)/2 - 1 = -(23/32 : ℝ) := by norm_num
    have eq2 : (1 - (9 : ℝ)/16)/2 - 1 = -(25/32 : ℝ) := by norm_num
    rw [eq1, eq2] at h; exact h
  have hC_np : Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) ≤ 0 := u{i}_cos_np
  have hS_np : Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) ≤ 0 := u{i}_sin_np
  have hRe := re_scalar_bounds_cos_neg
    (A_lo := 0)
    (A_hi := ({u_str} : ℝ)^(-(23/32 : ℝ)) + ({u_str} : ℝ)^(-(25/32 : ℝ)))
    (C_lo := Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (C_hi := 0) (W_lo := 0) (W_hi := omegaPartial 3 ({u_str} : ℝ))
    (le_refl 0) hAstar_nn hC_np hC_np (le_refl 0)
    (le_refl 0) hW_nn
    hA_nn hA_hi (le_refl _) hC_np hW_nn (le_refl _)
  have hIm := im_scalar_bounds_sin_neg
    (D_lo := 0)
    (D_hi := ({u_str} : ℝ)^(-(23/32 : ℝ)) - ({u_str} : ℝ)^(-(25/32 : ℝ)))
    (S_lo := Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (S_hi := 0) (W_lo := 0) (W_hi := omegaPartial 3 ({u_str} : ℝ))
    (le_refl 0) hDstar_nn hS_np hS_np (le_refl 0)
    (le_refl 0) hW_nn
    hD_nn hD_hi (le_refl _) hS_np hW_nn (le_refl _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold realThetaReIntegrandN
    linarith [hRe.1, u{i}_re_adverse_ge]
  · unfold realThetaReIntegrandN
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith [hRe.2]
  · unfold realThetaImIntegrandN
    linarith [hIm.1, u{i}_im_adverse_ge]
  · unfold realThetaImIntegrandN
    have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num
    linarith [hIm.2]
"""

# Emit each P file
PANELS = {
    'Seg1P2': [3, 4, 5],
    'Seg1P3': [6, 7, 8],
    'Seg1P4': [9, 10, 11],
    'Seg1P5': [12, 13, 14],
    'Seg1P6': [15, 16, 17],
    'Seg1P7': [18, 19, 20],
    'Seg1P8': [21, 22],
}

HEADER = """/-
# PF.Analytic.RiemannXiBox0Panels.{name}

AUTO-GENERATED by scripts/emit_seg1_panels.py.
Production exact-endpoint architecture per r331b Stage-1 directive.
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import Interval.Interval.Conversion
import Interval.Interval.Exp
import Interval.Interval.Log
import Interval.Interval.Sincos
import Interval.Interval.Pi
import Interval.Interval.Order
import Interval.Interval.Mul
import Interval.Tactic.Approx

namespace PrincipiaTractalis.RiemannXiBox0Panels.{name}

open scoped Real
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes
open PrincipiaTractalis.XiQuadrature

private theorem rpow_neg_eq_exp {{x a : ℝ}} (hx : 0 < x) :
    x ^ (-a) = Real.exp (-(Real.log x * a)) := by
  rw [Real.rpow_def_of_pos hx]; ring_nf

private theorem omegaPartial_3_closed {{u : ℝ}} :
    omegaPartial 3 u = Real.exp (-(π * u)) + Real.exp (-(π * 4 * u))
      + Real.exp (-(π * 9 * u)) := by
  unfold omegaPartial
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, one_pow]
  ring_nf
"""

FOOTER = "\nend PrincipiaTractalis.RiemannXiBox0Panels.{name}\n"

import os
out_dir = "PF/Analytic/RiemannXiBox0Panels"
os.makedirs(out_dir, exist_ok=True)

for panel_name, indices in PANELS.items():
    body = HEADER.format(name=panel_name)
    for i in indices:
        if i <= 6:
            body += emit_positive_sin_node(i)
        else:
            body += emit_negative_sin_node(i)
    body += FOOTER.format(name=panel_name)
    with open(f"{out_dir}/{panel_name}.lean", "w") as f:
        f.write(body)
    print(f"Emitted {panel_name}.lean with nodes {indices}")

print("Done.")
