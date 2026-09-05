#!/usr/bin/env python3
"""
append_seg1_chunks.py — parse existing Seg1P{2..8}.lean, append chunk theorem.

Chunk theorem: pure arithmetic (linarith) sum of the emitted node theorems.
Idempotent: skips files that already have a `seg1_p{n}_chunk_bounds` theorem.

Sign convention:
  positive-sin node → (RE_LO ≤ ReN ≤ 0) ∧ (0 ≤ ImN ≤ IM_HI)
  negative-sin node → (RE_LO ≤ ReN ≤ 0) ∧ (IM_LO ≤ ImN ≤ 0)

Chunk Im lower = Σ IM_LO_i over negative-sin nodes
Chunk Im upper = Σ IM_HI_i over positive-sin nodes
Chunk Re lower = Σ RE_LO_i over all nodes; Re upper = 0.
"""
import os
import re
from fractions import Fraction

PANELS = {
    'Seg1P2': [3, 4, 5],
    'Seg1P3': [6, 7, 8],
    'Seg1P4': [9, 10, 11],
    'Seg1P5': [12, 13, 14],
    'Seg1P6': [15, 16, 17],
    'Seg1P7': [18, 19, 20],
    'Seg1P8': [21, 22],
}

OUT_DIR = "PF/Analytic/RiemannXiBox0Panels"


def parse_node(text, i):
    """
    Return dict {u_num, u_den, re_lo: Fraction, im_lo: Fraction, im_hi: Fraction,
                 sign: 'pos' or 'neg'} for node i, from full file text.
    """
    # Locate the theorem block: theorem node_{i}_bounds ... := by
    m = re.search(rf"theorem node_{i}_bounds .*?(?=theorem |end Principia)",
                  text, re.DOTALL)
    if not m:
        raise ValueError(f"node_{i}_bounds not found")
    block = m.group(0)

    # RE_LO: first line has "(-NN/DD : ℝ) ≤ realThetaReIntegrandN"
    m1 = re.search(r"\((-?\d+)/(\d+)\s*:\s*ℝ\)\s*≤\s*realThetaReIntegrandN", block)
    if not m1:
        raise ValueError(f"RE_LO not found in node {i}")
    re_lo = Fraction(int(m1.group(1)), int(m1.group(2)))

    # u: u = (num/den), take from "realThetaReIntegrandN 3 σ 15 (NUM/DEN : ℝ)"
    m_u = re.search(r"realThetaReIntegrandN\s+3\s+σ\s+15\s+\((\d+)/(\d+)\s*:\s*ℝ\)",
                    block)
    if not m_u:
        raise ValueError(f"u not found in node {i}")
    u_num, u_den = int(m_u.group(1)), int(m_u.group(2))

    # Detect positive vs negative sin: search for "u{i}_sin_nn" (positive)
    # or "u{i}_sin_np" (negative) — as emitted.
    is_pos = f"u{i}_sin_nn" in block
    is_neg = f"u{i}_sin_np" in block
    if is_pos == is_neg:
        raise ValueError(f"cannot resolve sin sign for node {i}")
    sign = 'pos' if is_pos else 'neg'

    # Im bound: for pos-sin, IM_HI matches `realThetaImIntegrandN ... ≤ (N/D : ℝ)`;
    # for neg-sin, IM_LO matches `(N/D : ℝ) ≤ realThetaImIntegrandN`.
    if sign == 'pos':
        m_im = re.search(r"realThetaImIntegrandN\s+3\s+σ\s+15\s+\(\d+/\d+\s*:\s*ℝ\)\s*"
                         r"≤\s*\((-?\d+)/(\d+)\s*:\s*ℝ\)", block)
        if not m_im:
            raise ValueError(f"IM_HI not found in pos-sin node {i}")
        im_lo = Fraction(0)
        im_hi = Fraction(int(m_im.group(1)), int(m_im.group(2)))
    else:
        m_im = re.search(r"\((-?\d+)/(\d+)\s*:\s*ℝ\)\s*≤\s*realThetaImIntegrandN", block)
        if not m_im:
            raise ValueError(f"IM_LO not found in neg-sin node {i}")
        im_lo = Fraction(int(m_im.group(1)), int(m_im.group(2)))
        im_hi = Fraction(0)

    return {
        'i': i,
        'u_num': u_num, 'u_den': u_den,
        're_lo': re_lo,
        'im_lo': im_lo, 'im_hi': im_hi,
        'sign': sign,
    }


def frac_lean(f):
    """Render a Fraction as Lean 'num/den' with negatives kept in numerator."""
    return f"{f.numerator}/{f.denominator}"


def chunk_theorem(panel_num, nodes):
    """Return Lean chunk theorem source."""
    re_sum = sum(n['re_lo'] for n in nodes)
    im_lo_sum = sum(n['im_lo'] for n in nodes)
    im_hi_sum = sum(n['im_hi'] for n in nodes)

    # Build ReN sum expression: A + B + C
    re_expr = "\n        + ".join(
        f"realThetaReIntegrandN 3 σ 15 ({n['u_num']}/{n['u_den']} : ℝ)"
        for n in nodes)
    im_expr = "\n        + ".join(
        f"realThetaImIntegrandN 3 σ 15 ({n['u_num']}/{n['u_den']} : ℝ)"
        for n in nodes)

    # Hypothesis names + linarith conjunctions
    hyps = ""
    for n in nodes:
        hyps += f"  have h{n['i']} := node_{n['i']}_bounds σ hσ0 hσ1\n"

    re_lower_terms = ", ".join(f"h{n['i']}.1" for n in nodes)
    re_upper_terms = ", ".join(f"h{n['i']}.2.1" for n in nodes)
    im_lower_terms = ", ".join(f"h{n['i']}.2.2.1" for n in nodes)
    im_upper_terms = ", ".join(f"h{n['i']}.2.2.2" for n in nodes)

    return f"""
/-! ## P{panel_num} chunk sum: nodes {[n['i'] for n in nodes]} (production) -/

theorem seg1_p{panel_num}_chunk_bounds (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ({frac_lean(re_sum)} : ℝ)
      ≤ {re_expr}
    ∧ {re_expr} ≤ 0
    ∧ ({frac_lean(im_lo_sum)} : ℝ)
      ≤ {im_expr}
    ∧ {im_expr} ≤ ({frac_lean(im_hi_sum)} : ℝ) := by
{hyps}  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [{re_lower_terms}]
  · linarith [{re_upper_terms}]
  · linarith [{im_lower_terms}]
  · linarith [{im_upper_terms}]
"""


def main():
    for panel_name, indices in PANELS.items():
        path = os.path.join(OUT_DIR, f"{panel_name}.lean")
        with open(path, "r") as f:
            text = f.read()

        p_num = int(panel_name.replace("Seg1P", ""))
        chunk_name = f"seg1_p{p_num}_chunk_bounds"
        if chunk_name in text:
            print(f"{panel_name}: chunk theorem already present — skip")
            continue

        nodes = [parse_node(text, i) for i in indices]
        chunk_src = chunk_theorem(p_num, nodes)

        # Insert before the final `end PrincipiaTractalis...` line.
        end_marker = f"end PrincipiaTractalis.RiemannXiBox0Panels.{panel_name}"
        if end_marker not in text:
            raise ValueError(f"end marker not found in {panel_name}")
        new_text = text.replace(end_marker, chunk_src + "\n" + end_marker)

        with open(path, "w") as f:
            f.write(new_text)

        re_sum = sum(n['re_lo'] for n in nodes)
        im_lo = sum(n['im_lo'] for n in nodes)
        im_hi = sum(n['im_hi'] for n in nodes)
        print(f"{panel_name}: appended chunk. "
              f"RE_LO={re_sum} IM_LO={im_lo} IM_HI={im_hi}")


if __name__ == "__main__":
    main()
