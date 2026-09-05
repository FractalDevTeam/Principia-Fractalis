#!/usr/bin/env python3
"""
emit_seg1_assembly.py — generate PF/Analytic/RiemannXiBox0Panels/Seg1.lean.

Assembles P1..P8 chunk theorems into:
  * raw exact-rational segment sum bounds (linarith over 8 chunks)
  * midpoint-form Finset sum bounds (via per-index arg equality + expansion)
  * midpoint-scaled integral bounds via box0_re/im_midpoint_error_on_segment
    + box0_seg1_M_le_three

Endpoints (Stage-1):
  RE_INT_LO = -39964981/54169600000    ≈ -7.378e-4
  RE_INT_HI = 1/17334272               ≈ +5.77e-8
  IM_INT_LO = -974941/1354240000000    ≈ -7.199e-7
  IM_INT_HI = 61257/270848000000       ≈ +2.262e-7
"""
from fractions import Fraction as F

# Chunk totals extracted from Seg1P{1..8}.lean chunk theorems.
CHUNKS = {
    1: {'nodes': [0, 1, 2],
        're_lo': F(-3907, 100000), 'im_lo': F(0), 'im_hi': F(402, 10000000)},
    2: {'nodes': [3, 4, 5],
        're_lo': F(-1901, 50000), 'im_lo': F(0), 'im_hi': F(197, 10000000)},
    3: {'nodes': [6, 7, 8],
        're_lo': F(-1847, 50000), 'im_lo': F(-3, 1250000), 'im_hi': F(21, 10000000)},
    4: {'nodes': [9, 10, 11],
        're_lo': F(-112, 3125), 'im_lo': F(-39, 2000000), 'im_hi': F(0)},
    5: {'nodes': [12, 13, 14],
        're_lo': F(-347, 10000), 'im_lo': F(-189, 5000000), 'im_hi': F(0)},
    6: {'nodes': [15, 16, 17],
        're_lo': F(-839, 25000), 'im_lo': F(-69, 1250000), 'im_hi': F(0)},
    7: {'nodes': [18, 19, 20],
        're_lo': F(-81, 2500), 'im_lo': F(-9, 125000), 'im_hi': F(0)},
    8: {'nodes': [21, 22],
        're_lo': F(-419, 20000), 'im_lo': F(-71, 1250000), 'im_hi': F(0)},
}
N_NODES = 23  # nodes 0..22

# Totals
SEG_RE_LO = sum(c['re_lo'] for c in CHUNKS.values())     # -6787/25000
SEG_IM_LO = sum(c['im_lo'] for c in CHUNKS.values())     # -2437/10000000
SEG_IM_HI = sum(c['im_hi'] for c in CHUNKS.values())     # 31/500000
E_SEG = F(1, 17334272)
H = F(1, 368)   # midpoint step = (U-L)/n = (1/16)/23 = 1/368

# Integral endpoints
RE_INT_LO = SEG_RE_LO * H - E_SEG
RE_INT_HI = F(0) + E_SEG
IM_INT_LO = SEG_IM_LO * H - E_SEG
IM_INT_HI = SEG_IM_HI * H + E_SEG


def u_val(i):
    """u_i = (1105 + 2i)/736 as a Fraction."""
    return F(1105 + 2 * i, 736)


def rat(f):
    return f"({f.numerator}/{f.denominator} : ℝ)"


def raw_re_sum():
    return " + ".join(
        f"realThetaReIntegrandN 3 σ 15 (({1105 + 2*i}/736 : ℝ))"
        for i in range(N_NODES))


def raw_im_sum():
    return " + ".join(
        f"realThetaImIntegrandN 3 σ 15 (({1105 + 2*i}/736 : ℝ))"
        for i in range(N_NODES))


def chunk_re_expr(chunk_num):
    nodes = CHUNKS[chunk_num]['nodes']
    return " + ".join(
        f"realThetaReIntegrandN 3 σ 15 (({1105 + 2*i}/736 : ℝ))"
        for i in nodes)


def chunk_im_expr(chunk_num):
    nodes = CHUNKS[chunk_num]['nodes']
    return " + ".join(
        f"realThetaImIntegrandN 3 σ 15 (({1105 + 2*i}/736 : ℝ))"
        for i in nodes)


HEADER = f"""/-
# PF.Analytic.RiemannXiBox0Panels.Seg1

Stage-1 assembly for r331b Box-0: combines P1..P8 chunk theorems into
raw exact-rational segment sum bounds and midpoint-scaled integral
bounds via `box0_re/im_midpoint_error_on_segment` + `box0_seg1_M_le_three`.

Segment: `[L, U] = [3/2, 25/16]`, `n = 23` midpoints, step `h = 1/368`.
M certificate: `box0_seg1_M_le_three` (kernel-clean, prior landing).
Midpoint error: `E_SEG = M · (U-L)^3 / (24 · n^2) ≤ 3/(4096·12696) = 1/17334272`.

Stage-1 endpoints:
* `RE_INT_LO = {RE_INT_LO}`  ≈ {float(RE_INT_LO):.4e}
* `RE_INT_HI = {RE_INT_HI}`  ≈ {float(RE_INT_HI):.4e}
* `IM_INT_LO = {IM_INT_LO}`  ≈ {float(IM_INT_LO):.4e}
* `IM_INT_HI = {IM_INT_HI}`  ≈ {float(IM_INT_HI):.4e}

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import PF.Numerics.Box0Seg1MPrototype
import PF.Analytic.RiemannXiBox0Panels.Seg1P1
import PF.Analytic.RiemannXiBox0Panels.Seg1P2
import PF.Analytic.RiemannXiBox0Panels.Seg1P3
import PF.Analytic.RiemannXiBox0Panels.Seg1P4
import PF.Analytic.RiemannXiBox0Panels.Seg1P5
import PF.Analytic.RiemannXiBox0Panels.Seg1P6
import PF.Analytic.RiemannXiBox0Panels.Seg1P7
import PF.Analytic.RiemannXiBox0Panels.Seg1P8

namespace PrincipiaTractalis.RiemannXiBox0Panels.Seg1

open scoped Real BigOperators
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes
open PrincipiaTractalis.Box0Seg1MPrototype
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P1
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P2
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P3
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P4
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P5
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P6
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P7
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P8
"""


def emit_raw_bounds():
    """Four theorems: seg1_re_sum_{lower,upper}, seg1_im_sum_{lower,upper}."""
    re_sum = raw_re_sum()
    im_sum = raw_im_sum()
    hyps = "".join(f"  have h{k} := seg1_p{k}_chunk_bounds σ hσ0 hσ1\n"
                   for k in range(1, 9))
    re_lower_terms = ", ".join(f"h{k}.1" for k in range(1, 9))
    re_upper_terms = ", ".join(f"h{k}.2.1" for k in range(1, 9))
    im_lower_terms = ", ".join(f"h{k}.2.2.1" for k in range(1, 9))
    im_upper_terms = ", ".join(f"h{k}.2.2.2" for k in range(1, 9))

    return f"""
/-! ## §1 — Raw exact-rational segment sum bounds (chunks + linarith) -/

theorem seg1_re_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    {rat(SEG_RE_LO)}
      ≤ {re_sum} := by
{hyps}  linarith [{re_lower_terms}]

theorem seg1_re_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    {re_sum}
      ≤ (0 : ℝ) := by
{hyps}  linarith [{re_upper_terms}]

theorem seg1_im_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    {rat(SEG_IM_LO)}
      ≤ {im_sum} := by
{hyps}  linarith [{im_lower_terms}]

theorem seg1_im_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    {im_sum}
      ≤ {rat(SEG_IM_HI)} := by
{hyps}  linarith [{im_upper_terms}]
"""


def emit_arg_reduction_lemmas():
    """Generic argument reduction + per-index bound tables."""
    # Extract per-node bounds from the emitter's compute_node output.
    # Since we're not running mpmath here, we hardcode from the emitted files.
    # For chunk sums we already know totals; for per-node we regenerate here.
    from decimal import Decimal
    # Node data extracted from what the emitter produced (via inspection).
    # Table: (i, re_lo_num, re_lo_den, im_lo_num, im_lo_den, im_hi_num, im_hi_den, sign)
    # sign 'pos' means (im_lo=0, im_hi=IM_HI positive); 'neg' means (im_lo=IM_LO neg, im_hi=0).
    # We'll parse from the Seg1P*.lean files.
    import re, os
    node_data = {}
    for panel, indices in [('Seg1P1', [0,1,2]), ('Seg1P2', [3,4,5]),
                            ('Seg1P3', [6,7,8]), ('Seg1P4', [9,10,11]),
                            ('Seg1P5', [12,13,14]), ('Seg1P6', [15,16,17]),
                            ('Seg1P7', [18,19,20]), ('Seg1P8', [21,22])]:
        path = f"PF/Analytic/RiemannXiBox0Panels/{panel}.lean"
        with open(path) as f:
            text = f.read()
        for i in indices:
            m = re.search(rf"theorem node_{i}_bounds .*?(?=theorem |\Z)",
                          text, re.DOTALL)
            block = m.group(0)
            m_re = re.search(r"\((-?\d+)/(\d+)\s*:\s*ℝ\)\s*≤\s*realThetaReIntegrandN",
                             block)
            re_lo = (int(m_re.group(1)), int(m_re.group(2)))
            if f"u{i}_sin_nn" in block:
                sign = 'pos'
                m_im = re.search(r"realThetaImIntegrandN\s+3\s+σ\s+15\s+"
                                 r"\(\d+/\d+\s*:\s*ℝ\)\s*≤\s*\((-?\d+)/(\d+)\s*:\s*ℝ\)",
                                 block)
                im_lo = (0, 1)
                im_hi = (int(m_im.group(1)), int(m_im.group(2)))
            else:
                sign = 'neg'
                m_im = re.search(r"\((-?\d+)/(\d+)\s*:\s*ℝ\)\s*≤\s*realThetaImIntegrandN",
                                 block)
                im_lo = (int(m_im.group(1)), int(m_im.group(2)))
                im_hi = (0, 1)
            node_data[i] = {'re_lo': re_lo, 'im_lo': im_lo, 'im_hi': im_hi,
                            'sign': sign}

    # Store for downstream use
    global NODE_DATA
    NODE_DATA = node_data

    out = ["""
/-! ## §2 — Argument reduction + per-index bound extraction -/

/-- Generic midpoint argument reduction: `L + (U-L)/n·(k+1/2) = (1105+2k)/736`. -/
private lemma mid_arg_eq_u (k : ℕ) :
    ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((k : ℝ) + 1/2))
    = ((1105 + 2 * k : ℕ) : ℝ)/736 := by
  push_cast; ring

/-- Per-index literal-form reduction: `((1105 + 2*k : ℕ) : ℝ)/736 = (1105+2k)/736`
where the RHS is a numeric ℝ literal. -/
"""]
    for k in range(N_NODES):
        u = 1105 + 2 * k
        out.append(f"""private lemma u_eq_{k} : (((1105 + 2 * {k} : ℕ) : ℝ)/736) = ({u}/736 : ℝ) := by
  norm_num
""")
    return "".join(out)


def emit_midpoint_sum_eq():
    """Prove Finset.range 23 midpoint sum equals raw 23-term sum via
    per-index rewrites + full sum expansion."""
    rhs_re = "\n      + ".join(
        f"realThetaReIntegrandN 3 σ 15 (({1105 + 2*i}/736 : ℝ))"
        for i in range(N_NODES))
    rhs_im = rhs_re.replace("realThetaReIntegrandN", "realThetaImIntegrandN")
    u_eqs = ", ".join(f"u_eq_{k}" for k in range(N_NODES))

    return f"""
/-! ## §3 — Midpoint-form Finset sum equals raw 23-term sum -/

theorem seg1_re_midpoint_sum_eq_raw (σ : ℝ) :
    (∑ i ∈ Finset.range 23, realThetaReIntegrandN 3 σ 15
       ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((i : ℝ) + 1/2)))
    = {rhs_re} := by
  simp_rw [mid_arg_eq_u]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             {u_eqs}]

theorem seg1_im_midpoint_sum_eq_raw (σ : ℝ) :
    (∑ i ∈ Finset.range 23, realThetaImIntegrandN 3 σ 15
       ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((i : ℝ) + 1/2)))
    = {rhs_im} := by
  simp_rw [mid_arg_eq_u]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             {u_eqs}]
"""


def emit_midpoint_sum_bounds():
    """Bounds on Finset.range 23 midpoint sums (composition of eq + raw bounds)."""
    lhs_re = ("∑ i ∈ Finset.range 23, realThetaReIntegrandN 3 σ 15\n"
              "        ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((i : ℝ) + 1/2))")
    lhs_im = lhs_re.replace("realThetaReIntegrandN", "realThetaImIntegrandN")

    return f"""
/-! ## §4 — Midpoint sum bounds (composition of §1 and §3) -/

theorem seg1_re_midpoint_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    {rat(SEG_RE_LO)}
      ≤ ({lhs_re}) := by
  rw [seg1_re_midpoint_sum_eq_raw]; exact seg1_re_sum_lower σ hσ0 hσ1

theorem seg1_re_midpoint_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({lhs_re}) ≤ (0 : ℝ) := by
  rw [seg1_re_midpoint_sum_eq_raw]; exact seg1_re_sum_upper σ hσ0 hσ1

theorem seg1_im_midpoint_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    {rat(SEG_IM_LO)}
      ≤ ({lhs_im}) := by
  rw [seg1_im_midpoint_sum_eq_raw]; exact seg1_im_sum_lower σ hσ0 hσ1

theorem seg1_im_midpoint_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({lhs_im}) ≤ {rat(SEG_IM_HI)} := by
  rw [seg1_im_midpoint_sum_eq_raw]; exact seg1_im_sum_upper σ hσ0 hσ1
"""


def emit_integral_theorems():
    """Four Stage-1 integral theorems via midpoint error + M ≤ 3."""
    return f"""
/-! ## §5 — Stage-1 integral bounds via midpoint error + M ≤ 3 -/

/-- Numeric shape of the midpoint sum with `(U-L)/n = 1/368`. -/
private lemma midpoint_scale_eq : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := by
  push_cast; norm_num

/-- Numeric bound on midpoint error: `M·(U-L)³/(24·n²) ≤ 1/17334272`. -/
private lemma seg1_error_bound_le :
    (2 * ∑ n' ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) (3/2) n')
      * ((25/16 : ℝ) - 3/2) ^ 3 / (24 * (23 : ℕ) ^ 2)
      ≤ (1/17334272 : ℝ) := by
  have hM := box0_seg1_M_le_three
  set M := 2 * ∑ n' ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) (3/2) n' with hM_def
  -- Re-associate: M * X^3 / Y = M * (X^3 / Y)
  have hassoc : M * ((25/16 : ℝ) - 3/2) ^ 3 / (24 * (23 : ℕ) ^ 2)
              = M * (((25/16 : ℝ) - 3/2) ^ 3 / (24 * (23 : ℕ) ^ 2)) := by ring
  rw [hassoc]
  have hf : ((25/16 : ℝ) - 3/2) ^ 3 / (24 * (23 : ℕ) ^ 2) = (1/52002816 : ℝ) := by
    push_cast; norm_num
  rw [hf]
  have hpos : (0 : ℝ) < 1/52002816 := by norm_num
  calc M * (1/52002816 : ℝ)
        ≤ 3 * (1/52002816 : ℝ) := mul_le_mul_of_nonneg_right hM (le_of_lt hpos)
    _ = (1/17334272 : ℝ) := by norm_num

/-- ★ Stage-1 REAL integral lower bound. -/
theorem box0_seg1_re_integral_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({rat(RE_INT_LO)}) ≤ ∫ u in (3/2 : ℝ)..(25/16), realThetaReIntegrandN 3 σ 15 u := by
  have hL : (1 : ℝ) ≤ 3/2 := by norm_num
  have hLU : (3/2 : ℝ) ≤ 25/16 := by norm_num
  have hn : 0 < (23 : ℕ) := by decide
  have herr := box0_re_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg1_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  -- habs.1: -(1/17334272) ≤ integral - midpoint_sum
  -- habs.2: integral - midpoint_sum ≤ 1/17334272
  have hmid := seg1_re_midpoint_sum_lower σ hσ0 hσ1
  have hscale : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := midpoint_scale_eq
  rw [hscale] at habs
  linarith [habs.1, hmid]

/-- ★ Stage-1 REAL integral upper bound. -/
theorem box0_seg1_re_integral_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∫ u in (3/2 : ℝ)..(25/16), realThetaReIntegrandN 3 σ 15 u) ≤ {rat(RE_INT_HI)} := by
  have hL : (1 : ℝ) ≤ 3/2 := by norm_num
  have hLU : (3/2 : ℝ) ≤ 25/16 := by norm_num
  have hn : 0 < (23 : ℕ) := by decide
  have herr := box0_re_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg1_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg1_re_midpoint_sum_upper σ hσ0 hσ1
  have hscale : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := midpoint_scale_eq
  rw [hscale] at habs
  linarith [habs.2, hmid]

/-- ★ Stage-1 IMAG integral lower bound. -/
theorem box0_seg1_im_integral_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({rat(IM_INT_LO)}) ≤ ∫ u in (3/2 : ℝ)..(25/16), realThetaImIntegrandN 3 σ 15 u := by
  have hL : (1 : ℝ) ≤ 3/2 := by norm_num
  have hLU : (3/2 : ℝ) ≤ 25/16 := by norm_num
  have hn : 0 < (23 : ℕ) := by decide
  have herr := box0_im_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg1_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg1_im_midpoint_sum_lower σ hσ0 hσ1
  have hscale : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := midpoint_scale_eq
  rw [hscale] at habs
  linarith [habs.1, hmid]

/-- ★ Stage-1 IMAG integral upper bound. -/
theorem box0_seg1_im_integral_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∫ u in (3/2 : ℝ)..(25/16), realThetaImIntegrandN 3 σ 15 u) ≤ {rat(IM_INT_HI)} := by
  have hL : (1 : ℝ) ≤ 3/2 := by norm_num
  have hLU : (3/2 : ℝ) ≤ 25/16 := by norm_num
  have hn : 0 < (23 : ℕ) := by decide
  have herr := box0_im_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg1_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg1_im_midpoint_sum_upper σ hσ0 hσ1
  have hscale : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := midpoint_scale_eq
  rw [hscale] at habs
  linarith [habs.2, hmid]
"""


FOOTER = "\nend PrincipiaTractalis.RiemannXiBox0Panels.Seg1\n"


def main():
    body = HEADER
    body += emit_raw_bounds()
    body += emit_arg_reduction_lemmas()
    body += emit_midpoint_sum_eq()
    body += emit_midpoint_sum_bounds()
    body += emit_integral_theorems()
    body += FOOTER
    path = "PF/Analytic/RiemannXiBox0Panels/Seg1.lean"
    with open(path, "w") as f:
        f.write(body)
    print(f"Wrote {path} ({len(body)} bytes)")
    print(f"RE_INT_LO = {RE_INT_LO}")
    print(f"RE_INT_HI = {RE_INT_HI}")
    print(f"IM_INT_LO = {IM_INT_LO}")
    print(f"IM_INT_HI = {IM_INT_HI}")


if __name__ == "__main__":
    main()
