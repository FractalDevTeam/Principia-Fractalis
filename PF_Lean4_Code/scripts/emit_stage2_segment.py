#!/usr/bin/env python3
"""
emit_stage2_segment.py — parameterized OPT-40-TIGHT segment generator.

For each segment (idx, L, U, n, MHI), emit two Lean files:
  * PF/Analytic/RiemannXiBox0Panels/Seg{idx:02d}.lean
  * PF/Numerics/Box0Seg{idx:02d}M.lean

Per-node dispatch on (cos_sign, sin_sign) ∈ {nn, np} × {nn, np}
where nn = "≥ 0" (nonneg) and np = "≤ 0" (nonpos).

Segment 17 (L=3/2, U=25/16, n=23) is the Stage-1 reference; skipped by default.
"""
import mpmath as mp
from fractions import Fraction as F
import os
import sys

mp.mp.dps = 100
PI = mp.pi

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from opt40tight import SEGMENTS


# ==============================================================================
# Numerical helpers
# ==============================================================================

def outward_lo(x, digits):
    scale = 10 ** digits
    return F(int(mp.floor(x * scale)), scale)


def outward_hi(x, digits):
    scale = 10 ** digits
    return F(int(mp.ceil(x * scale)), scale)


def compute_node(u_frac):
    """Return (c, s, re_adv, im_adv) using mpmath."""
    u_mp = mp.mpf(u_frac.numerator) / u_frac.denominator
    p23 = mp.power(u_mp, -mp.mpf(23) / 32)
    p25 = mp.power(u_mp, -mp.mpf(25) / 32)
    log_u = mp.log(u_mp)
    c = mp.cos(mp.mpf(15) / 2 * log_u)
    s = mp.sin(mp.mpf(15) / 2 * log_u)
    om = mp.exp(-PI * u_mp) + mp.exp(-4 * PI * u_mp) + mp.exp(-9 * PI * u_mp)
    re_adv = (p23 + p25) * c * om
    im_adv = (p23 - p25) * s * om
    return c, s, re_adv, im_adv


DIGITS_RE_LO = 10   # r331b rework: Re lower-bound node rounding (was 5, vacuous)


def compute_node_tight_lo(u_frac):
    """Tight sigma-uniform Re lower-bound product at a node: 2*u^(-3/4)*cos*omega.

    A_lo = 2*u^(-3/4) is box0_pow_sum_tight_lb (valid u>=1, sigma in [1/2,9/16]).
    Only used at cos>=0 nodes, where A_lo*C_lo*W_lo is the adverse-LOW product.
    """
    u_mp = mp.mpf(u_frac.numerator) / u_frac.denominator
    p34 = mp.power(u_mp, -mp.mpf(3) / 4)
    log_u = mp.log(u_mp)
    c = mp.cos(mp.mpf(15) / 2 * log_u)
    om = mp.exp(-PI * u_mp) + mp.exp(-4 * PI * u_mp) + mp.exp(-9 * PI * u_mp)
    return 2 * p34 * c * om


class NodeLedgerMismatch(AssertionError):
    """Raised when node-emission and segment-ledger bounds disagree."""


def canonical_node_bounds(u_frac, cos_sign, sin_sign):
    """THE single source of truth for a node's four rational bounds.

    Both the node emitter (emit_node) and the segment ledger
    (emit_segment_file) MUST obtain bounds from here, so the constant
    proved in Lean and the constant summed into the segment endpoint can
    never diverge.

    Re, cos<0 : lower = outward_lo(Astar*C*W, 5)      [Astar upper-bound arch]
                upper = 0
    Re, cos>=0: lower = outward_lo(2u^(-3/4)*C*W, 10) [tight lower arch]
                upper = outward_hi(Astar*C*W, 5)
    Im         : unchanged architecture.
    All lower bounds use outward_lo (floor) -> round DOWN toward/past truth.
    All upper bounds use outward_hi (ceil)  -> round UP  toward/past truth.
    """
    c_mp, s_mp, re_adv, im_adv = compute_node(u_frac)
    if cos_sign == 'np':
        assert c_mp <= 0
        # r331b rework: 5 digits here loses ~1.06e-5 over the 260 cos<0 nodes
        # and makes Box 0 fail by -1.06e-5.  DIGITS_RE_LO=10 recovers it.
        re_lo = outward_lo(re_adv, DIGITS_RE_LO)
        re_hi = F(0)
    else:
        assert c_mp >= 0
        re_lo = outward_lo(compute_node_tight_lo(u_frac), DIGITS_RE_LO)
        re_hi = outward_hi(re_adv, 5)
    if sin_sign == 'nn':
        assert s_mp >= 0
        im_lo = F(0)
        im_hi = outward_hi(im_adv, 7)
    else:
        assert s_mp <= 0
        im_lo = outward_lo(im_adv, 7)
        im_hi = F(0)
    return re_lo, re_hi, im_lo, im_hi


def rat_R(f):
    return f"({f.numerator}/{f.denominator} : ℝ)"


def rat_I(f):
    return f"({f.numerator}/{f.denominator} : _root_.Interval)"


def rat_Q(f):
    return f"({f.numerator} : ℚ)/{f.denominator}"


# ==============================================================================
# Sign-specific lemma bodies (cos ± / sin ±)
# ==============================================================================

def _cos_lemma(idx, u_str, u_rat, cos_sign):
    """cos_sign ∈ {'np', 'nn'}."""
    if cos_sign == 'np':
        return f"""
private theorem u{idx}_cos_np : Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) ≤ 0 := by
  have hlt : Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) < (0 : ℝ) := by
    refine _root_.Interval.approx_lt
      (_root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
          (_root_.Interval.ofRat ({u_rat}))))
      ((0 : _root_.Interval))
      (Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
      (0 : ℝ)
      (_root_.Interval.mem_approx_cos (by approx))
      (by approx)
      ?_
    decide +kernel
  linarith
"""
    else:  # 'nn'
        return f"""
private theorem u{idx}_cos_nn : (0 : ℝ) ≤ Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) := by
  refine _root_.Interval.approx_le
    ((0 : _root_.Interval))
    (_root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat}))))
    (0 : ℝ)
    (Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (by approx)
    (_root_.Interval.mem_approx_cos (by approx))
    ?_
  decide +kernel
"""


def _sin_lemma(idx, u_str, u_rat, sin_sign):
    if sin_sign == 'np':
        return f"""
private theorem u{idx}_sin_np : Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) ≤ 0 := by
  have hlt : Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) < (0 : ℝ) := by
    refine _root_.Interval.approx_lt
      (_root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
          (_root_.Interval.ofRat ({u_rat}))))
      ((0 : _root_.Interval))
      (Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
      (0 : ℝ)
      (_root_.Interval.mem_approx_sin (by approx))
      (by approx)
      ?_
    decide +kernel
  linarith
"""
    else:  # 'nn'
        return f"""
private theorem u{idx}_sin_nn : (0 : ℝ) ≤ Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) := by
  refine _root_.Interval.approx_le
    ((0 : _root_.Interval))
    (_root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat}))))
    (0 : ℝ)
    (Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (by approx)
    (_root_.Interval.mem_approx_sin (by approx))
    ?_
  decide +kernel
"""


def _re_adverse_lemma(idx, u_str, u_rat, cos_sign, re_lo=None, re_hi=None):
    """Emit `u{idx}_re_adverse_ge` (cos_np) or `u{idx}_re_adverse_le` (cos_nn)."""
    plus_expr = f"""(({u_str} : ℝ) ^ (-(23/32 : ℝ)) + ({u_str} : ℝ) ^ (-(25/32 : ℝ)))
        * Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))
        * omegaPartial 3 ({u_str} : ℝ)"""
    plus_interval = f"""((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat})) * _root_.Interval.ofRat (23/32)))
      + _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat})) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat})))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ({u_rat})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat})))))"""
    if cos_sign == 'np':
        # Astar*C*W ≤ 0.  Lower bound RE_LO ≤ Astar*C*W.
        return f"""
private theorem u{idx}_re_adverse_ge :
    {rat_R(re_lo)}
      ≤ {plus_expr} := by
  have hu0 : (0 : ℝ) < ({u_str} : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine _root_.Interval.approx_le
    {rat_I(re_lo)}
    {plus_interval}
    {rat_R(re_lo)}
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel
"""
    else:
        # Astar*C*W ≥ 0.  Upper bound Astar*C*W ≤ RE_HI.
        return f"""
private theorem u{idx}_re_adverse_le :
    {plus_expr}
      ≤ {rat_R(re_hi)} := by
  have hu0 : (0 : ℝ) < ({u_str} : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine le_of_lt <| _root_.Interval.approx_lt
    {plus_interval}
    {rat_I(re_hi)}
    _
    {rat_R(re_hi)}
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel
"""


def _re_tight_lemma(idx, u_str, u_rat, re_lo):
    """Emit `u{idx}_re_tight_ge`: RE_LO <= 2*u^(-3/4) * cos * omega  (cos>=0 nodes).

    RE_LO is outward-rounded DOWN (floor) toward the true value, so the
    inequality is the certified adverse-LOW direction.
    """
    tight_expr = f"""(2 * ({u_str} : ℝ) ^ (-(3/4 : ℝ)))
        * Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))
        * omegaPartial 3 ({u_str} : ℝ)"""
    tight_interval = f"""((2 : _root_.Interval) * _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat})) * _root_.Interval.ofRat (3/4)))
     * _root_.Interval.cos ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat})))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ({u_rat})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat})))))"""
    return f"""
private theorem u{idx}_re_tight_ge :
    {rat_R(re_lo)}
      ≤ {tight_expr} := by
  have hu0 : (0 : ℝ) < ({u_str} : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine _root_.Interval.approx_le
    {rat_I(re_lo)}
    {tight_interval}
    {rat_R(re_lo)}
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel
"""


def _im_adverse_lemma(idx, u_str, u_rat, sin_sign, im_lo=None, im_hi=None):
    """Emit `u{idx}_im_adverse_le` (sin_nn) or `u{idx}_im_adverse_ge` (sin_np)."""
    diff_expr = f"""(({u_str} : ℝ) ^ (-(23/32 : ℝ)) - ({u_str} : ℝ) ^ (-(25/32 : ℝ)))
      * Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ))
      * omegaPartial 3 ({u_str} : ℝ)"""
    diff_interval = f"""((_root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat})) * _root_.Interval.ofRat (23/32)))
      - _root_.Interval.exp (-(_root_.Interval.log
        (_root_.Interval.ofRat ({u_rat})) * _root_.Interval.ofRat (25/32))))
     * _root_.Interval.sin ((15/2 : _root_.Interval) * _root_.Interval.log
        (_root_.Interval.ofRat ({u_rat})))
     * (_root_.Interval.exp (-(_root_.Interval.pi *
          _root_.Interval.ofRat ({u_rat})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat})))
        + _root_.Interval.exp (-(_root_.Interval.pi * (9 : _root_.Interval) *
          _root_.Interval.ofRat ({u_rat})))))"""
    if sin_sign == 'nn':
        # Dstar*S*W ≥ 0.  Upper bound Dstar*S*W ≤ IM_HI.
        return f"""
private theorem u{idx}_im_adverse_le :
    {diff_expr}
      ≤ {rat_R(im_hi)} := by
  have hu0 : (0 : ℝ) < ({u_str} : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine le_of_lt <| _root_.Interval.approx_lt
    {diff_interval}
    {rat_I(im_hi)}
    _
    {rat_R(im_hi)}
    ?_
    (by approx)
    ?_
  · approx
  · decide +kernel
"""
    else:
        # Dstar*S*W ≤ 0.  Lower bound IM_LO ≤ Dstar*S*W.
        return f"""
private theorem u{idx}_im_adverse_ge :
    {rat_R(im_lo)}
      ≤ {diff_expr} := by
  have hu0 : (0 : ℝ) < ({u_str} : ℝ) := by norm_num
  rw [rpow_neg_eq_exp hu0, rpow_neg_eq_exp hu0, omegaPartial_3_closed]
  refine _root_.Interval.approx_le
    {rat_I(im_lo)}
    {diff_interval}
    {rat_R(im_lo)}
    _
    (by approx)
    ?_
    ?_
  · approx
  · decide +kernel
"""


# ==============================================================================
# Node theorem body — dispatch on (cos_sign, sin_sign)
# ==============================================================================

def emit_node(idx, u, cos_sign, sin_sign):
    """Return (source_text, (re_lo, re_hi, im_lo, im_hi))."""
    c_mp, s_mp, re_adv, im_adv = compute_node(u)

    # Bounds come from the ONE canonical computation (never inline here).
    re_lo, re_hi, im_lo, im_hi = canonical_node_bounds(u, cos_sign, sin_sign)

    u_str = f"{u.numerator}/{u.denominator}"
    u_rat = rat_Q(u)

    # Prelim lemmas
    cos_lem = _cos_lemma(idx, u_str, u_rat, cos_sign)
    sin_lem = _sin_lemma(idx, u_str, u_rat, sin_sign)
    re_adv_lem = _re_adverse_lemma(idx, u_str, u_rat, cos_sign,
                                    re_lo=re_lo, re_hi=re_hi)
    if cos_sign == 'nn':
        re_adv_lem = re_adv_lem + _re_tight_lemma(idx, u_str, u_rat, re_lo)
    im_adv_lem = _im_adverse_lemma(idx, u_str, u_rat, sin_sign,
                                    im_lo=im_lo, im_hi=im_hi)

    # Node bounds statement + proof
    if cos_sign == 'np':
        re_lo_bnd = rat_R(re_lo)
        re_hi_bnd = "0"
    else:
        re_lo_bnd = rat_R(re_lo)
        re_hi_bnd = rat_R(re_hi)

    if sin_sign == 'nn':
        im_lo_bnd = "(0 : ℝ)"
        im_hi_bnd = rat_R(im_hi)
    else:
        im_lo_bnd = rat_R(im_lo)
        im_hi_bnd = "0"

    # Choose sign consumers
    if cos_sign == 'np':
        re_consumer = _re_consumer_cos_np(u_str, idx)
        # After re_scalar_bounds_cos_neg: A_hi*C_lo*W_hi ≤ ReN_atomic ∧ ReN ≤ 0
        # ReN unfolds to Astar*C*W approx (via u{idx}_re_adverse_ge for lower)
        re_lo_proof = f"linarith [hRe.1, u{idx}_re_adverse_ge]"
        re_hi_proof = ("have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num\n"
                       "    linarith [hRe.2]")
    else:  # cos_nn
        re_consumer = _re_consumer_cos_nn(u_str, idx)
        # After re_scalar_bounds_cos_nonneg: 0 ≤ ReN ∧ ReN ≤ A_hi*C_hi*W_hi
        re_lo_proof = (
            f"have hAlo : 2 * ({u_str} : ℝ)^(-(3/4 : ℝ))\n"
            f"        ≤ ({u_str} : ℝ)^(σ/2 - 1) + ({u_str} : ℝ)^((1-σ)/2 - 1) :=\n"
            f"      box0_pow_sum_tight_lb hu1 hσ0 hσ1\n"
            f"    have hCW : (0 : ℝ) ≤ Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))\n"
            f"        * omegaPartial 3 ({u_str} : ℝ) := mul_nonneg hC hW_nn\n"
            f"    have hchain : 2 * ({u_str} : ℝ)^(-(3/4 : ℝ))\n"
            f"          * Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))\n"
            f"          * omegaPartial 3 ({u_str} : ℝ)\n"
            f"        ≤ (({u_str} : ℝ)^(σ/2 - 1) + ({u_str} : ℝ)^((1-σ)/2 - 1))\n"
            f"          * Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))\n"
            f"          * omegaPartial 3 ({u_str} : ℝ) := by\n"
            f"      calc 2 * ({u_str} : ℝ)^(-(3/4 : ℝ))\n"
            f"            * Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))\n"
            f"            * omegaPartial 3 ({u_str} : ℝ)\n"
            f"          = 2 * ({u_str} : ℝ)^(-(3/4 : ℝ))\n"
            f"            * (Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))\n"
            f"              * omegaPartial 3 ({u_str} : ℝ)) := by ring\n"
            f"        _ ≤ (({u_str} : ℝ)^(σ/2 - 1) + ({u_str} : ℝ)^((1-σ)/2 - 1))\n"
            f"            * (Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))\n"
            f"              * omegaPartial 3 ({u_str} : ℝ)) :=\n"
            f"          mul_le_mul_of_nonneg_right hAlo hCW\n"
            f"        _ = (({u_str} : ℝ)^(σ/2 - 1) + ({u_str} : ℝ)^((1-σ)/2 - 1))\n"
            f"            * Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ))\n"
            f"            * omegaPartial 3 ({u_str} : ℝ) := by ring\n"
            f"    linarith [u{idx}_re_tight_ge, hchain]"
        )
        re_hi_proof = f"linarith [hRe.2, u{idx}_re_adverse_le]"

    if sin_sign == 'nn':
        im_consumer = _im_consumer_sin_nn(u_str, idx)
        im_lo_proof = "have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num\n    linarith [hIm.1]"
        im_hi_proof = f"linarith [hIm.2, u{idx}_im_adverse_le]"
    else:  # sin_np
        im_consumer = _im_consumer_sin_np(u_str, idx)
        im_lo_proof = f"linarith [hIm.1, u{idx}_im_adverse_ge]"
        im_hi_proof = ("have h2 : (0 : ℝ) * 0 * 0 = 0 := by norm_num\n"
                       "    linarith [hIm.2]")

    # cos/sin hypothesis name
    cos_hyp = f"u{idx}_cos_np" if cos_sign == 'np' else f"u{idx}_cos_nn"
    sin_hyp = f"u{idx}_sin_np" if sin_sign == 'np' else f"u{idx}_sin_nn"
    cos_type = "≤ 0" if cos_sign == 'np' else "≥ 0"
    sin_type = "≤ 0" if sin_sign == 'np' else "≥ 0"

    node_thm = f"""
theorem node_{idx}_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({re_lo_bnd}) ≤ realThetaReIntegrandN 3 σ 15 ({u_str} : ℝ)
    ∧ realThetaReIntegrandN 3 σ 15 ({u_str} : ℝ) ≤ ({re_hi_bnd})
    ∧ ({im_lo_bnd}) ≤ realThetaImIntegrandN 3 σ 15 ({u_str} : ℝ)
    ∧ realThetaImIntegrandN 3 σ 15 ({u_str} : ℝ) ≤ ({im_hi_bnd}) := by
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
  have hC : Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) {cos_type} := {cos_hyp}
  have hS : Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)) {sin_type} := {sin_hyp}
{re_consumer}
{im_consumer}
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold realThetaReIntegrandN
    {re_lo_proof}
  · unfold realThetaReIntegrandN
    {re_hi_proof}
  · unfold realThetaImIntegrandN
    {im_lo_proof}
  · unfold realThetaImIntegrandN
    {im_hi_proof}
"""

    source = "\n".join([
        f"/-! ## Node {idx} at u = {u_str} — cos {cos_sign}, sin {sin_sign} -/",
        cos_lem, sin_lem, re_adv_lem, im_adv_lem, node_thm
    ])

    return source, (re_lo, re_hi, im_lo, im_hi, cos_sign, sin_sign)


def _re_consumer_cos_np(u_str, idx):
    """cos ≤ 0 case: re_scalar_bounds_cos_neg."""
    return f"""  have hRe := re_scalar_bounds_cos_neg
    (A_lo := 0)
    (A_hi := ({u_str} : ℝ)^(-(23/32 : ℝ)) + ({u_str} : ℝ)^(-(25/32 : ℝ)))
    (C_lo := Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (C_hi := 0) (W_lo := 0) (W_hi := omegaPartial 3 ({u_str} : ℝ))
    (le_refl 0) hAstar_nn hC hC (le_refl 0)
    (le_refl 0) hW_nn
    hA_nn hA_hi (le_refl _) hC hW_nn (le_refl _)"""


def _re_consumer_cos_nn(u_str, idx):
    """cos ≥ 0 case: re_scalar_bounds_cos_nonneg."""
    return f"""  have hRe := re_scalar_bounds_cos_nonneg
    (A_lo := 0)
    (A_hi := ({u_str} : ℝ)^(-(23/32 : ℝ)) + ({u_str} : ℝ)^(-(25/32 : ℝ)))
    (C_lo := 0)
    (C_hi := Real.cos ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (W_lo := 0) (W_hi := omegaPartial 3 ({u_str} : ℝ))
    (le_refl 0) hAstar_nn (le_refl 0) hC
    (le_refl 0) hW_nn
    hA_nn hA_hi hC (le_refl _) hW_nn (le_refl _)"""


def _im_consumer_sin_nn(u_str, idx):
    """sin ≥ 0 case: im_scalar_bounds_sin_nonneg."""
    return f"""  have hIm := im_scalar_bounds_sin_nonneg
    (D_lo := 0)
    (D_hi := ({u_str} : ℝ)^(-(23/32 : ℝ)) - ({u_str} : ℝ)^(-(25/32 : ℝ)))
    (S_lo := 0)
    (S_hi := Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (W_lo := 0) (W_hi := omegaPartial 3 ({u_str} : ℝ))
    (le_refl 0) hDstar_nn (le_refl 0) hS
    (le_refl 0) hW_nn
    hD_nn hD_hi hS (le_refl _) hW_nn (le_refl _)"""


def _im_consumer_sin_np(u_str, idx):
    """sin ≤ 0 case: im_scalar_bounds_sin_neg."""
    return f"""  have hIm := im_scalar_bounds_sin_neg
    (D_lo := 0)
    (D_hi := ({u_str} : ℝ)^(-(23/32 : ℝ)) - ({u_str} : ℝ)^(-(25/32 : ℝ)))
    (S_lo := Real.sin ((15/2 : ℝ) * Real.log ({u_str} : ℝ)))
    (S_hi := 0) (W_lo := 0) (W_hi := omegaPartial 3 ({u_str} : ℝ))
    (le_refl 0) hDstar_nn hS hS (le_refl 0)
    (le_refl 0) hW_nn
    hD_nn hD_hi (le_refl _) hS hW_nn (le_refl _)"""


# ==============================================================================
# M certificate emission (unchanged from prior version)
# ==============================================================================

def compute_T_bounds(L):
    """T_n(L) = exp(-π·(n+1)²·L) · (78705/1024 + (n+1)⁴·π² + (n+1)²·(265/16)·π)"""
    L_mp = mp.mpf(L.numerator) / L.denominator
    consts = [78705 / mp.mpf(1024) + (n + 1)**4 * PI**2
              + (n + 1)**2 * mp.mpf(265) / 16 * PI for n in range(3)]
    T = [mp.exp(-PI * (n + 1)**2 * L_mp) * consts[n] for n in range(3)]
    bounds = []
    for t in T:
        if t < 1e-30:
            bounds.append(F(1, 10**30))
            continue
        target = float(t) * 1.10
        denom = 10
        while target * denom < 1:
            denom *= 10
        denom *= 100
        num = int(target * denom) + 1
        bounds.append(F(num, denom))
    return T, bounds


def pi_mult_real(e):
    """Real-side expression for pi * e (see patch 7 rendering policy)."""
    if e == 1:
        return "\u03c0"
    if e.denominator == 1:
        return f"\u03c0 * {e.numerator}"
    return f"\u03c0 * ({e.numerator}/{e.denominator})"


def pi_mult_interval(e):
    """Interval mirror for pi * e, restricted to forms `approx` can discharge."""
    if e == 1:
        return "_root_.Interval.pi"
    if e.denominator == 1:
        return f"_root_.Interval.pi * ({e.numerator} : _root_.Interval)"
    return ("_root_.Interval.pi * _root_.Interval.ofRat "
            f"({e.numerator}/{e.denominator})")


def rat_lean(f):
    # ALWAYS keep the explicit denominator.  A bare integer literal makes the
    # mirror `Interval.ofRat (4)`, which `approx` cannot discharge; the
    # division form `Interval.ofRat (4/1)` is the shape it handles.
    # Affects the integer-L segments 1, 25, 33, 37.
    return f"{f.numerator}/{f.denominator}"


def emit_M_certificate(idx, L, MHI):
    T, bounds = compute_T_bounds(L)
    B0, B1, B2 = bounds
    sum_2 = 2 * (B0 + B1 + B2)
    assert sum_2 <= MHI, f"Seg{idx}: 2·(B0+B1+B2)={sum_2} > MHI={MHI}"

    L_str = f"{L.numerator}/{L.denominator}"
    ns = f"Box0Seg{idx:02d}M"

    def exp_coef(n):
        return F(n + 1)**2 * L
    e0, e1, e2 = exp_coef(0), exp_coef(1), exp_coef(2)
    e0_re, e1_re, e2_re = (pi_mult_real(e0), pi_mult_real(e1),
                           pi_mult_real(e2))
    e0_iv, e1_iv, e2_iv = (pi_mult_interval(e0), pi_mult_interval(e1),
                           pi_mult_interval(e2))

    return f"""/-
# PF.Numerics.{ns}

M certificate for OPT-40-TIGHT segment {idx}:  L = {L}, MHI = {MHI}.
Auto-generated by scripts/emit_stage2_segment.py.

T_0 ≈ {float(T[0]):.4e}   B0 = {B0}
T_1 ≈ {float(T[1]):.4e}   B1 = {B1}
T_2 ≈ {float(T[2]):.4e}   B2 = {B2}
2·(B0+B1+B2) = {sum_2} ≤ {MHI}

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import Interval.Interval.Conversion
import Interval.Interval.Exp
import Interval.Interval.Pi
import Interval.Interval.Order
import Interval.Interval.Mul
import Interval.Tactic.Approx

namespace PrincipiaTractalis.{ns}

open scoped Real
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes

theorem seg{idx}_T0_closed :
    thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) 0
      = Real.exp (-({e0_re})) * ((78705/1024 : ℝ) + π * π + (265/16 : ℝ) * π) := by
  unfold thetaPowTermM
  have h_abs : |(15 : ℝ)| = 15 := by rw [abs_of_pos]; norm_num
  simp only [Nat.cast_zero, zero_add, h_abs, one_pow]
  ring

theorem seg{idx}_T1_closed :
    thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) 1
      = Real.exp (-({e1_re})) * ((78705/1024 : ℝ) + 16 * (π * π) + (265/4 : ℝ) * π) := by
  unfold thetaPowTermM
  have h_abs : |(15 : ℝ)| = 15 := by rw [abs_of_pos]; norm_num
  simp only [Nat.cast_one, h_abs]
  ring

theorem seg{idx}_T2_closed :
    thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) 2
      = Real.exp (-({e2_re})) * ((78705/1024 : ℝ) + 81 * (π * π) + (2385/16 : ℝ) * π) := by
  unfold thetaPowTermM
  have h_abs : |(15 : ℝ)| = 15 := by rw [abs_of_pos]; norm_num
  simp only [Nat.cast_ofNat, h_abs]
  ring

noncomputable def T0_mirror : _root_.Interval :=
  _root_.Interval.exp (-({e0_iv})) *
    (_root_.Interval.ofRat (78705/1024)
     + _root_.Interval.pi * _root_.Interval.pi
     + _root_.Interval.ofRat (265/16) * _root_.Interval.pi)

noncomputable def T1_mirror : _root_.Interval :=
  _root_.Interval.exp (-({e1_iv})) *
    (_root_.Interval.ofRat (78705/1024)
     + (16 : _root_.Interval) * (_root_.Interval.pi * _root_.Interval.pi)
     + _root_.Interval.ofRat (265/4) * _root_.Interval.pi)

noncomputable def T2_mirror : _root_.Interval :=
  _root_.Interval.exp (-({e2_iv})) *
    (_root_.Interval.ofRat (78705/1024)
     + (81 : _root_.Interval) * (_root_.Interval.pi * _root_.Interval.pi)
     + _root_.Interval.ofRat (2385/16) * _root_.Interval.pi)

theorem seg{idx}_T0_lt : thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) 0 < {rat_R(B0)} := by
  rw [seg{idx}_T0_closed]
  refine _root_.Interval.approx_lt
    T0_mirror
    {rat_I(B0)}
    (Real.exp (-({e0_re})) * ((78705/1024 : ℝ) + π * π + (265/16 : ℝ) * π))
    {rat_R(B0)}
    ?_
    (by approx)
    ?_
  · unfold T0_mirror
    approx
  · decide +kernel

theorem seg{idx}_T1_lt : thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) 1 < {rat_R(B1)} := by
  rw [seg{idx}_T1_closed]
  refine _root_.Interval.approx_lt
    T1_mirror
    {rat_I(B1)}
    (Real.exp (-({e1_re})) * ((78705/1024 : ℝ) + 16 * (π * π) + (265/4 : ℝ) * π))
    {rat_R(B1)}
    ?_
    (by approx)
    ?_
  · unfold T1_mirror
    approx
  · decide +kernel

theorem seg{idx}_T2_lt : thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) 2 < {rat_R(B2)} := by
  rw [seg{idx}_T2_closed]
  refine _root_.Interval.approx_lt
    T2_mirror
    {rat_I(B2)}
    (Real.exp (-({e2_re})) * ((78705/1024 : ℝ) + 81 * (π * π) + (2385/16 : ℝ) * π))
    {rat_R(B2)}
    ?_
    (by approx)
    ?_
  · unfold T2_mirror
    approx
  · decide +kernel

theorem seg{idx}_M_expand :
    2 * ∑ n ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) n
      = 2 * (thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) 0
             + thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) 1
             + thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) 2) := by
  simp [Finset.sum_range_succ]

theorem box0_seg{idx}_M_le_MHI :
    2 * ∑ n ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) n
      ≤ {rat_R(MHI)} := by
  rw [seg{idx}_M_expand]
  have h0 := seg{idx}_T0_lt
  have h1 := seg{idx}_T1_lt
  have h2 := seg{idx}_T2_lt
  linarith

end PrincipiaTractalis.{ns}
"""


# ==============================================================================
# Panel file emission (3 nodes per file, matches Stage-1's Seg1P1..P8 pattern)
# ==============================================================================

PANEL_SIZE = 3


def _panel_partition(n):
    """Split range(n) into contiguous chunks of size ≤ PANEL_SIZE.
    Returns list of (panel_num, [k, k+1, ...]) starting from panel_num=1."""
    panels = []
    p = 1
    for start in range(0, n, PANEL_SIZE):
        panels.append((p, list(range(start, min(start + PANEL_SIZE, n)))))
        p += 1
    return panels


def emit_panel_file(idx, panel_num, node_data_list):
    """Emit one PF/Analytic/RiemannXiBox0Panels/Seg{idx:02d}P{panel_num}.lean.

    node_data_list : list of (k, u, cos_sign, sin_sign, re_lo, re_hi, im_lo, im_hi)
    """
    ns = f"Seg{idx:02d}P{panel_num}"

    # Emit all node theorems in this panel
    node_blocks = []
    node_summary = []
    for k, u, cos_sign, sin_sign, re_lo, re_hi, im_lo, im_hi in node_data_list:
        code, emitted = emit_node(k, u, cos_sign, sin_sign)
        # MANDATORY self-check: the constant proved in Lean (emitted) must be
        # bit-identical to the constant summed into the segment ledger.
        e_re_lo, e_re_hi, e_im_lo, e_im_hi = emitted[0], emitted[1], emitted[2], emitted[3]
        if (e_re_lo, e_re_hi, e_im_lo, e_im_hi) != (re_lo, re_hi, im_lo, im_hi):
            raise NodeLedgerMismatch(
                "Seg%02d node %d: emitted %s != ledger %s"
                % (idx, k, (e_re_lo, e_re_hi, e_im_lo, e_im_hi),
                   (re_lo, re_hi, im_lo, im_hi)))
        node_blocks.append(code)
        node_summary.append((k, u, re_lo, re_hi, im_lo, im_hi))

    # Chunk sums for this panel
    re_lo_sum = sum(nd[2] for nd in node_summary)
    re_hi_sum = sum(nd[3] for nd in node_summary)
    im_lo_sum = sum(nd[4] for nd in node_summary)
    im_hi_sum = sum(nd[5] for nd in node_summary)

    # Raw sum expressions over this panel's nodes
    def raw_expr(func_name):
        return " + ".join(
            f"{func_name} 3 σ 15 ({u.numerator}/{u.denominator} : ℝ)"
            for _, u, _, _, _, _ in node_summary)
    raw_re = raw_expr("realThetaReIntegrandN")
    raw_im = raw_expr("realThetaImIntegrandN")

    node_hyps = "".join(
        f"  have h{k} := node_{k}_bounds σ hσ0 hσ1\n" for k, *_ in node_summary)
    re_lo_terms = ", ".join(f"h{k}.1" for k, *_ in node_summary)
    re_hi_terms = ", ".join(f"h{k}.2.1" for k, *_ in node_summary)
    im_lo_terms = ", ".join(f"h{k}.2.2.1" for k, *_ in node_summary)
    im_hi_terms = ", ".join(f"h{k}.2.2.2" for k, *_ in node_summary)

    node_indices = [nd[0] for nd in node_summary]
    return f"""/-
# PF.Analytic.RiemannXiBox0Panels.{ns}

Panel {panel_num} of Segment {idx}: nodes {node_indices}.
Auto-generated by scripts/emit_stage2_segment.py.
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

namespace PrincipiaTractalis.RiemannXiBox0Panels.{ns}

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

{''.join(node_blocks)}

/-! ## Panel {panel_num} chunk sum -/

theorem seg{idx}_p{panel_num}_chunk_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({rat_R(re_lo_sum)}) ≤ {raw_re}
    ∧ {raw_re} ≤ ({rat_R(re_hi_sum)})
    ∧ ({rat_R(im_lo_sum)}) ≤ {raw_im}
    ∧ {raw_im} ≤ ({rat_R(im_hi_sum)}) := by
{node_hyps}  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [{re_lo_terms}]
  · linarith [{re_hi_terms}]
  · linarith [{im_lo_terms}]
  · linarith [{im_hi_terms}]

end PrincipiaTractalis.RiemannXiBox0Panels.{ns}
"""


# ==============================================================================
# Segment assembly emission (top-level, imports panels)
# ==============================================================================

def emit_segment_file(idx, L, U, n, MHI):
    """Emit SegNPK.lean panel files (returned as dict) + SegN.lean assembly.
    Returns (assembly_source, {panel_num: panel_source, ...})."""
    delta = U - L
    h = delta / n
    midpoints = [L + F(2 * k + 1, 2 * n) * delta for k in range(n)]

    # Per-node data (compute signs and bounds)
    per_node_data = []   # list of (k, u, cos_sign, sin_sign, re_lo, re_hi, im_lo, im_hi)
    for k, u in enumerate(midpoints):
        c_mp, s_mp, re_adv, im_adv = compute_node(u)
        cos_sign = 'nn' if c_mp >= 0 else 'np'
        sin_sign = 'nn' if s_mp >= 0 else 'np'
        re_lo, re_hi, im_lo, im_hi = canonical_node_bounds(u, cos_sign, sin_sign)
        per_node_data.append((k, u, cos_sign, sin_sign, re_lo, re_hi, im_lo, im_hi))

    # Split into panels
    panel_partition = _panel_partition(n)
    panel_sources = {}
    panel_meta = []  # list of (panel_num, [node indices in panel], per-panel chunk sums)
    for p_num, node_ks in panel_partition:
        panel_nodes = [per_node_data[k] for k in node_ks]
        panel_sources[p_num] = emit_panel_file(idx, p_num, panel_nodes)
        p_re_lo = sum(nd[4] for nd in panel_nodes)
        p_re_hi = sum(nd[5] for nd in panel_nodes)
        p_im_lo = sum(nd[6] for nd in panel_nodes)
        p_im_hi = sum(nd[7] for nd in panel_nodes)
        panel_meta.append((p_num, node_ks, p_re_lo, p_re_hi, p_im_lo, p_im_hi))

    # Overall chunk sums across all nodes (mixed-sign aware)
    re_lo_sum = sum(nd[4] for nd in per_node_data)
    re_hi_sum = sum(nd[5] for nd in per_node_data)
    im_lo_sum = sum(nd[6] for nd in per_node_data)
    im_hi_sum = sum(nd[7] for nd in per_node_data)

    L_str = f"{L.numerator}/{L.denominator}"
    U_str = f"{U.numerator}/{U.denominator}"

    def raw_expr(func_name):
        return "\n        + ".join(
            f"{func_name} 3 σ 15 ({u.numerator}/{u.denominator} : ℝ)"
            for u in midpoints)
    raw_re = raw_expr("realThetaReIntegrandN")
    raw_im = raw_expr("realThetaImIntegrandN")

    E_SEG = MHI * delta**3 / (24 * n * n)
    RE_INT_LO = re_lo_sum * h - E_SEG
    RE_INT_HI = re_hi_sum * h + E_SEG
    IM_INT_LO = im_lo_sum * h - E_SEG
    IM_INT_HI = im_hi_sum * h + E_SEG

    def _kexpr(k):
        # k = 0 ONLY: the closing simp set contains zero_add, which
        # normalises ((0 : R) + 1/2) to 1/2 BEFORE e0 can fire.  An e0
        # stated with (0 + 1/2) therefore never matches (linter: "e0 is
        # unused") and the sum-equality goal is left unsolved.
        return "(1/2)" if k == 0 else f"(({k} : ℝ) + 1/2)"

    per_k_arg_eqs = "\n".join(
        f"  have e{k} : (({L_str} : ℝ) + ({U_str} - {L_str}) / {n} * {_kexpr(k)}) "
        f"= ({midpoints[k].numerator}/{midpoints[k].denominator} : ℝ) := by norm_num"
        for k in range(n))
    per_k_eqs = ", ".join(f"e{k}" for k in range(n))

    ns = f"Seg{idx:02d}"
    M_ns = f"Box0Seg{idx:02d}M"

    # Panel imports
    panel_imports = "\n".join(
        f"import PF.Analytic.RiemannXiBox0Panels.Seg{idx:02d}P{p_num}"
        for p_num, _, _, _, _, _ in panel_meta)
    panel_opens = "\n".join(
        f"open PrincipiaTractalis.RiemannXiBox0Panels.Seg{idx:02d}P{p_num}"
        for p_num, _, _, _, _, _ in panel_meta)

    # Chunk aggregation: sum panel chunk bounds via linarith
    panel_chunk_hyps = "".join(
        f"  have hp{p_num} := seg{idx}_p{p_num}_chunk_bounds σ hσ0 hσ1\n"
        for p_num, _, _, _, _, _ in panel_meta)
    p_re_lo_terms = ", ".join(f"(hp{p_num}).1" for p_num, *_ in panel_meta)
    p_re_hi_terms = ", ".join(f"(hp{p_num}).2.1" for p_num, *_ in panel_meta)
    p_im_lo_terms = ", ".join(f"(hp{p_num}).2.2.1" for p_num, *_ in panel_meta)
    p_im_hi_terms = ", ".join(f"(hp{p_num}).2.2.2" for p_num, *_ in panel_meta)

    assembly = f"""/-
# PF.Analytic.RiemannXiBox0Panels.{ns}

OPT-40-TIGHT Stage-2 segment {idx}: L={L} U={U} n={n} MHI={MHI}.
Auto-generated by scripts/emit_stage2_segment.py.

Split into {len(panel_meta)} panel modules (Seg{idx:02d}P1..P{len(panel_meta)}) for
per-file Interval-computation memory bounds.

  RE_LO_SUM = {re_lo_sum}     RE_HI_SUM = {re_hi_sum}
  IM_LO_SUM = {im_lo_sum}     IM_HI_SUM = {im_hi_sum}
  E_SEG     = {E_SEG} ≈ {float(E_SEG):.4e}
  RE_INT_LO = {RE_INT_LO} ≈ {float(RE_INT_LO):.4e}
  RE_INT_HI = {RE_INT_HI} ≈ {float(RE_INT_HI):.4e}
  IM_INT_LO = {IM_INT_LO} ≈ {float(IM_INT_LO):.4e}
  IM_INT_HI = {IM_INT_HI} ≈ {float(IM_INT_HI):.4e}

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import PF.Numerics.{M_ns}
{panel_imports}

namespace PrincipiaTractalis.RiemannXiBox0Panels.{ns}

open scoped Real BigOperators
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes
open PrincipiaTractalis.{M_ns}
open PrincipiaTractalis.XiQuadrature
{panel_opens}

/-! ## Chunk sum (aggregated from all panels) -/

theorem seg{idx}_chunk_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({rat_R(re_lo_sum)}) ≤ {raw_re}
    ∧ {raw_re} ≤ ({rat_R(re_hi_sum)})
    ∧ ({rat_R(im_lo_sum)}) ≤ {raw_im}
    ∧ {raw_im} ≤ ({rat_R(im_hi_sum)}) := by
{panel_chunk_hyps}  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [{p_re_lo_terms}]
  · linarith [{p_re_hi_terms}]
  · linarith [{p_im_lo_terms}]
  · linarith [{p_im_hi_terms}]

/-! ## Midpoint sum equality -/

theorem seg{idx}_re_midpoint_sum_eq_raw (σ : ℝ) :
    (∑ i ∈ Finset.range {n}, realThetaReIntegrandN 3 σ 15
       (({L_str} : ℝ) + ({U_str} - {L_str}) / {n} * ((i : ℝ) + 1/2)))
    = {raw_re} := by
{per_k_arg_eqs}
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
             {per_k_eqs}]

theorem seg{idx}_im_midpoint_sum_eq_raw (σ : ℝ) :
    (∑ i ∈ Finset.range {n}, realThetaImIntegrandN 3 σ 15
       (({L_str} : ℝ) + ({U_str} - {L_str}) / {n} * ((i : ℝ) + 1/2)))
    = {raw_im} := by
{per_k_arg_eqs}
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
             {per_k_eqs}]

/-! ## Midpoint sum bounds -/

theorem seg{idx}_re_midpoint_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({rat_R(re_lo_sum)}) ≤ (∑ i ∈ Finset.range {n}, realThetaReIntegrandN 3 σ 15
        (({L_str} : ℝ) + ({U_str} - {L_str}) / {n} * ((i : ℝ) + 1/2))) := by
  rw [seg{idx}_re_midpoint_sum_eq_raw]
  linarith [(seg{idx}_chunk_bounds σ hσ0 hσ1).1]

theorem seg{idx}_re_midpoint_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∑ i ∈ Finset.range {n}, realThetaReIntegrandN 3 σ 15
        (({L_str} : ℝ) + ({U_str} - {L_str}) / {n} * ((i : ℝ) + 1/2))) ≤ ({rat_R(re_hi_sum)}) := by
  rw [seg{idx}_re_midpoint_sum_eq_raw]
  linarith [(seg{idx}_chunk_bounds σ hσ0 hσ1).2.1]

theorem seg{idx}_im_midpoint_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({rat_R(im_lo_sum)}) ≤ (∑ i ∈ Finset.range {n}, realThetaImIntegrandN 3 σ 15
        (({L_str} : ℝ) + ({U_str} - {L_str}) / {n} * ((i : ℝ) + 1/2))) := by
  rw [seg{idx}_im_midpoint_sum_eq_raw]
  linarith [(seg{idx}_chunk_bounds σ hσ0 hσ1).2.2.1]

theorem seg{idx}_im_midpoint_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∑ i ∈ Finset.range {n}, realThetaImIntegrandN 3 σ 15
        (({L_str} : ℝ) + ({U_str} - {L_str}) / {n} * ((i : ℝ) + 1/2))) ≤ ({rat_R(im_hi_sum)}) := by
  rw [seg{idx}_im_midpoint_sum_eq_raw]
  linarith [(seg{idx}_chunk_bounds σ hσ0 hσ1).2.2.2]

/-! ## Stage-2 segment-integral bounds via midpoint error + M ≤ MHI -/

private lemma seg{idx}_error_bound_le :
    (2 * ∑ n' ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) n')
      * (({U_str} : ℝ) - {L_str}) ^ 3 / (24 * ({n} : ℕ) ^ 2)
      ≤ ({rat_R(E_SEG)}) := by
  have hM := box0_seg{idx}_M_le_MHI
  set M := 2 * ∑ n' ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) ({L_str}) n' with hM_def
  have hassoc : M * (({U_str} : ℝ) - {L_str}) ^ 3 / (24 * ({n} : ℕ) ^ 2)
              = M * ((({U_str} : ℝ) - {L_str}) ^ 3 / (24 * ({n} : ℕ) ^ 2)) := by ring
  rw [hassoc]
  have hf : (({U_str} : ℝ) - {L_str}) ^ 3 / (24 * ({n} : ℕ) ^ 2)
          = ({rat_R(delta**3 / (24 * n * n))}) := by push_cast; norm_num
  rw [hf]
  have hpos : (0 : ℝ) < {rat_R(delta**3 / (24 * n * n))} := by norm_num
  calc M * ({rat_R(delta**3 / (24 * n * n))})
        ≤ ({rat_R(MHI)}) * ({rat_R(delta**3 / (24 * n * n))}) :=
          mul_le_mul_of_nonneg_right hM (le_of_lt hpos)
    _ = ({rat_R(E_SEG)}) := by norm_num

theorem box0_seg{idx}_re_integral_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({rat_R(RE_INT_LO)}) ≤ ∫ u in ({L_str} : ℝ)..{U_str}, realThetaReIntegrandN 3 σ 15 u := by
  have hL : (1 : ℝ) ≤ {L_str} := by norm_num
  have hLU : ({L_str} : ℝ) ≤ {U_str} := by norm_num
  have hn : 0 < ({n} : ℕ) := by decide
  have herr := box0_re_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg{idx}_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg{idx}_re_midpoint_sum_lower σ hσ0 hσ1
  have hscale : (({U_str} : ℝ) - {L_str}) / ({n} : ℕ) = ({rat_R(h)}) := by push_cast; norm_num
  rw [hscale] at habs
  linarith [habs.1, hmid]

theorem box0_seg{idx}_re_integral_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∫ u in ({L_str} : ℝ)..{U_str}, realThetaReIntegrandN 3 σ 15 u) ≤ ({rat_R(RE_INT_HI)}) := by
  have hL : (1 : ℝ) ≤ {L_str} := by norm_num
  have hLU : ({L_str} : ℝ) ≤ {U_str} := by norm_num
  have hn : 0 < ({n} : ℕ) := by decide
  have herr := box0_re_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg{idx}_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg{idx}_re_midpoint_sum_upper σ hσ0 hσ1
  have hscale : (({U_str} : ℝ) - {L_str}) / ({n} : ℕ) = ({rat_R(h)}) := by push_cast; norm_num
  rw [hscale] at habs
  linarith [habs.2, hmid]

theorem box0_seg{idx}_im_integral_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({rat_R(IM_INT_LO)}) ≤ ∫ u in ({L_str} : ℝ)..{U_str}, realThetaImIntegrandN 3 σ 15 u := by
  have hL : (1 : ℝ) ≤ {L_str} := by norm_num
  have hLU : ({L_str} : ℝ) ≤ {U_str} := by norm_num
  have hn : 0 < ({n} : ℕ) := by decide
  have herr := box0_im_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg{idx}_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg{idx}_im_midpoint_sum_lower σ hσ0 hσ1
  have hscale : (({U_str} : ℝ) - {L_str}) / ({n} : ℕ) = ({rat_R(h)}) := by push_cast; norm_num
  rw [hscale] at habs
  linarith [habs.1, hmid]

theorem box0_seg{idx}_im_integral_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∫ u in ({L_str} : ℝ)..{U_str}, realThetaImIntegrandN 3 σ 15 u) ≤ ({rat_R(IM_INT_HI)}) := by
  have hL : (1 : ℝ) ≤ {L_str} := by norm_num
  have hLU : ({L_str} : ℝ) ≤ {U_str} := by norm_num
  have hn : 0 < ({n} : ℕ) := by decide
  have herr := box0_im_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg{idx}_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg{idx}_im_midpoint_sum_upper σ hσ0 hσ1
  have hscale : (({U_str} : ℝ) - {L_str}) / ({n} : ℕ) = ({rat_R(h)}) := by push_cast; norm_num
  rw [hscale] at habs
  linarith [habs.2, hmid]

end PrincipiaTractalis.RiemannXiBox0Panels.{ns}
"""
    return assembly, panel_sources


# ==============================================================================
# Driver
# ==============================================================================

def emit_all_segments(indices, panels_dir="PF/Analytic/RiemannXiBox0Panels",
                       m_dir="PF/Numerics"):
    os.makedirs(panels_dir, exist_ok=True)
    os.makedirs(m_dir, exist_ok=True)
    for idx in indices:
        spec = next(s for s in SEGMENTS if s['idx'] == idx)
        L, U, n, MHI = spec['L'], spec['U'], spec['n'], spec['MHI']
        m_path = os.path.join(m_dir, f"Box0Seg{idx:02d}M.lean")
        with open(m_path, "w") as f:
            f.write(emit_M_certificate(idx, L, MHI))
        assembly, panel_sources = emit_segment_file(idx, L, U, n, MHI)
        panel_paths = []
        for p_num, source in panel_sources.items():
            p_path = os.path.join(panels_dir, f"Seg{idx:02d}P{p_num}.lean")
            with open(p_path, "w") as f:
                f.write(source)
            panel_paths.append(p_path)
        seg_path = os.path.join(panels_dir, f"Seg{idx:02d}.lean")
        with open(seg_path, "w") as f:
            f.write(assembly)
        print(f"Seg{idx:02d}: L={L} U={U} n={n} MHI={MHI} → "
              f"{len(panel_sources)} panels + assembly + M cert")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        indices = [int(x) for x in sys.argv[1:]]
    else:
        indices = [2]
    emit_all_segments(indices)
