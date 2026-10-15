#!/usr/bin/env python3
"""
gen_fourier_panels_c6.py — M2 pointwise panel generator for `Re Λ₀(1+6i)` /
`Im Λ₀(1+6i)` at c = 6, N = 3 truncation of `omega(e^u)`.

SCIENTIFIC ROLE
---------------
This script produces CANDIDATE rational enclosure bounds `[L_k, U_k]` on

    nodeR_fourier_plus_at_c6_N3(u_mid_k)   and
    nodeR_fourier_minus_at_c6_N3(u_mid_k)

at panel midpoints `u_mid_k` across one segment covering `u ∈ [0, 1/4]`
with 8 uniform panels of width `1/32`.  The emitted values become premises
of Lean theorems of the shape

    theorem s01p<k>_plus_lo  : (L_plus_k  : ℝ) ≤ nodeR_fourier_plus_at_c6_N3  <u_mid_k>
    theorem s01p<k>_plus_hi  :                   nodeR_fourier_plus_at_c6_N3  <u_mid_k>  ≤ (U_plus_k  : ℝ)
    theorem s01p<k>_minus_lo : (L_minus_k : ℝ) ≤ nodeR_fourier_minus_at_c6_N3 <u_mid_k>
    theorem s01p<k>_minus_hi :                   nodeR_fourier_minus_at_c6_N3 <u_mid_k> ≤ (U_minus_k : ℝ)

which are discharged inside Lean by the vendored interval engine plus
`decide +kernel` using `Interval.approx_le` against the N=3 interval mirror
`nodeI_fourier_plus_at_c6` / `nodeI_fourier_minus_at_c6` defined in
`PF/Analytic/FourierPanels/CoreDefs_c6_2026_10_15.lean`.

THIS SCRIPT IS NOT PART OF THE PROOF.  Every emitted L / U is a candidate
whose correctness is established solely by the Lean kernel.

ROUNDING POLICY
---------------
Working precision: exact Fraction arithmetic with outward rounding to
1/10^30 at each accumulation step (plenty of headroom for the interval
engine's decimal-parse widening).

Emitted precision: 10 decimal digits.
Direction: lower bounds floor toward -∞ with an extra -1 ULP of 10^-10
safety; upper bounds ceil toward +∞ with an extra +1 ULP of 10^-10
safety.  This matches the r120 safety discipline (gen_r120_panels_t15.py).

N = 3 TRUNCATION
----------------
We enclose ONLY the N=3-truncated omega:

    omega_N3(exp u) := exp(-π·exp u) + exp(-4π·exp u) + exp(-9π·exp u)

which matches the Lean definition `omega_N3_at_exp`.  The full omega tail
(n ≥ 4 terms) is positive, so for the real functions
`F_plus(u) = exp(u/2)·omega(exp u)` and `F_minus(u) = omega(exp u)` we have
truncated < full.  BUT: `nodeR_fourier_plus_at_c6_N3` and
`nodeR_fourier_minus_at_c6_N3` as defined in `CoreDefs_c6_2026_10_15.lean`
use the TRUNCATED omega directly, so our enclosure here is for THAT
truncated real function, not the full F_plus/F_minus.  Correct.

The relationship truncated-vs-full is a separate (not-yet-landed) tail-bound
lemma to be addressed in M3.

Usage:
    python3 gen_fourier_panels_c6.py             # emit Lean + report
    python3 gen_fourier_panels_c6.py --dry-run   # print report only
"""
import argparse
import os
import sys
from fractions import Fraction

# ---------------------------------------------------------------------------
# Fraction-only outward-rounded interval arithmetic
# (vendored from /tmp/panel_c6_v1.py, Agent B)
# ---------------------------------------------------------------------------
ROUND_DIGITS = 30
ROUND_DENOM = 10 ** ROUND_DIGITS


def round_down(f):
    """Round Fraction f DOWN to nearest multiple of 1/ROUND_DENOM."""
    num = f.numerator * ROUND_DENOM
    den = f.denominator
    q = num // den   # floor
    return Fraction(q, ROUND_DENOM)


def round_up(f):
    """Round Fraction f UP to nearest multiple of 1/ROUND_DENOM."""
    num = f.numerator * ROUND_DENOM
    den = f.denominator
    q = -((-num) // den)   # ceiling
    return Fraction(q, ROUND_DENOM)


class I:
    """Closed interval of Fractions.  All ops conservative (outward)."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        if not isinstance(lo, Fraction):
            lo = Fraction(lo)
        if not isinstance(hi, Fraction):
            hi = Fraction(hi)
        assert lo <= hi, f"empty interval: lo={lo} > hi={hi}"
        self.lo = lo
        self.hi = hi

    def __repr__(self):
        return f"[{float(self.lo):.6e}, {float(self.hi):.6e}]"

    def width(self):
        return self.hi - self.lo

    def __add__(self, o):
        if isinstance(o, I):
            return I(self.lo + o.lo, self.hi + o.hi)
        o = Fraction(o)
        return I(self.lo + o, self.hi + o)

    def __radd__(self, o):
        return self.__add__(o)

    def __sub__(self, o):
        if isinstance(o, I):
            return I(self.lo - o.hi, self.hi - o.lo)
        o = Fraction(o)
        return I(self.lo - o, self.hi - o)

    def __rsub__(self, o):
        o = Fraction(o)
        return I(o - self.hi, o - self.lo)

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __mul__(self, o):
        if not isinstance(o, I):
            o = Fraction(o)
            if o >= 0:
                return I(self.lo * o, self.hi * o)
            return I(self.hi * o, self.lo * o)
        p = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return I(min(p), max(p))

    def __rmul__(self, o):
        return self.__mul__(o)

    @staticmethod
    def point(x):
        f = Fraction(x)
        return I(f, f)

    def rounded(self):
        """Widen to common denom ROUND_DENOM: lo DOWN, hi UP.  Soundness preserved."""
        return I(round_down(self.lo), round_up(self.hi))


# Rational enclosure of pi (same as Agent B's /tmp/panel_c6_v1.py)
# pi to 30 digits: 3.141592653589793238462643383279...
PI_LO = Fraction(3141592653589793238462643383, 10**27)
PI_HI = Fraction(3141592653589793238462643384, 10**27)
PI = I(PI_LO, PI_HI)


# ---------------------------------------------------------------------------
# exp(-x) for x >= 0 as rational enclosure
# ---------------------------------------------------------------------------
def _exp_neg_point(x_frac, series_terms=50):
    """Return I enclosing exp(-x) for a single Fraction x >= 0."""
    assert x_frac >= 0
    xmax = x_frac
    k = 0
    cur = xmax
    while cur > 1:
        cur = cur / 2
        k += 1
    m = 2**k
    xs = Fraction(x_frac) / m if m > 1 else Fraction(x_frac)
    N = series_terms
    S = I(Fraction(1), Fraction(1))  # j=0 term
    term_pt = Fraction(1)
    for j in range(1, N):
        term_pt = term_pt * (-xs) / Fraction(j)
        term_lo = round_down(term_pt)
        term_hi = round_up(term_pt)
        S = (S + I(term_lo, term_hi)).rounded()
    N_fact = 1
    for i in range(1, N + 1):
        N_fact *= i
    R = xs ** N / Fraction(N_fact)
    lo = round_down(S.lo - R)
    hi = round_up(S.hi + R)
    if lo < 0:
        lo = Fraction(0)
    if hi > 1:
        hi = Fraction(1)
    exp_neg_xs = I(lo, hi)
    result = I(1, 1)
    base = exp_neg_xs
    kk = m
    while kk > 0:
        if kk & 1:
            result = (result * base).rounded()
        kk >>= 1
        if kk:
            base = (base * base).rounded()
    if result.lo < 0:
        result = I(Fraction(0), result.hi)
    if result.hi > 1:
        result = I(result.lo, Fraction(1))
    return result


def exp_neg_interval(x_interval, series_terms=50):
    """Return I enclosing exp(-x) for x in x_interval, x_interval.lo >= 0.
    exp(-x) is monotone decreasing."""
    assert x_interval.lo >= 0
    lo_enc = _exp_neg_point(x_interval.hi, series_terms=series_terms)
    hi_enc = _exp_neg_point(x_interval.lo, series_terms=series_terms)
    return I(lo_enc.lo, hi_enc.hi)


def exp_pos_interval(u_interval, series_terms=50):
    """Return I enclosing e^u for u in u_interval, u_interval.lo >= 0."""
    assert u_interval.lo >= 0
    neg = exp_neg_interval(u_interval, series_terms=series_terms)
    if neg.lo <= 0:
        raise RuntimeError(f"exp_neg returned non-positive lower bound: {neg}")
    return I(Fraction(1) / neg.hi, Fraction(1) / neg.lo)


# ---------------------------------------------------------------------------
# cos / sin on intervals (same style as /tmp/panel_c6_v1.py)
# ---------------------------------------------------------------------------
def _cos_point(y_frac, series_terms=40):
    y = abs(Fraction(y_frac))
    y2 = y * y
    N = series_terms
    S = I(Fraction(1), Fraction(1))
    term_pt = Fraction(1)
    sign = 1
    for k in range(1, N):
        denom = (2*k - 1) * (2*k)
        term_pt = term_pt * y2 / Fraction(denom)
        sign = -sign
        signed = sign * term_pt
        lo = round_down(signed)
        hi = round_up(signed)
        S = (S + I(lo, hi)).rounded()
    fact_2N = 1
    for i in range(1, 2*N + 1):
        fact_2N *= i
    R = y ** (2*N) / Fraction(fact_2N)
    lo = round_down(S.lo - R)
    hi = round_up(S.hi + R)
    if lo < -1:
        lo = Fraction(-1)
    if hi > 1:
        hi = Fraction(1)
    return I(lo, hi)


def _sin_point(y_frac, series_terms=40):
    y = Fraction(y_frac)
    neg = (y < 0)
    yy = abs(y)
    y2 = yy * yy
    N = series_terms
    term_pt = yy
    lo0 = round_down(term_pt); hi0 = round_up(term_pt)
    S = I(lo0, hi0)
    sign = 1
    for k in range(1, N):
        denom = (2*k) * (2*k + 1)
        term_pt = term_pt * y2 / Fraction(denom)
        sign = -sign
        signed = sign * term_pt
        lo = round_down(signed); hi = round_up(signed)
        S = (S + I(lo, hi)).rounded()
    fact_2N1 = 1
    for i in range(1, 2*N + 2):
        fact_2N1 *= i
    R = yy ** (2*N + 1) / Fraction(fact_2N1)
    lo = round_down(S.lo - R)
    hi = round_up(S.hi + R)
    if lo < -1:
        lo = Fraction(-1)
    if hi > 1:
        hi = Fraction(1)
    out = I(lo, hi)
    if neg:
        out = I(-out.hi, -out.lo)
    return out


# ---------------------------------------------------------------------------
# N = 3 TRUNCATION of omega(e^u)
# omega_N3(exp u) = exp(-pi * exp u) + exp(-4 pi * exp u) + exp(-9 pi * exp u)
# ---------------------------------------------------------------------------
def omega_N3_interval(x_interval, series_terms=50):
    """Return I enclosing omega_N3(x) = exp(-pi x) + exp(-4 pi x) + exp(-9 pi x)
    for x in x_interval, x_interval.lo > 0.

    Matches the Lean definition `omega_N3_at_exp u` for `x = exp u`."""
    assert x_interval.lo > 0
    pi_x   = (PI * x_interval).rounded()
    pi4_x  = (I.point(4) * pi_x).rounded()
    pi9_x  = (I.point(9) * pi_x).rounded()
    t1 = exp_neg_interval(pi_x,  series_terms=series_terms)
    t2 = exp_neg_interval(pi4_x, series_terms=series_terms)
    t3 = exp_neg_interval(pi9_x, series_terms=series_terms)
    return (t1 + t2 + t3).rounded()


# ---------------------------------------------------------------------------
# nodeR_fourier_plus_at_c6_N3 at a POINT u = u_mid (represented as a tight interval)
# nodeR_fourier_plus_at_c6_N3  u = (exp(u/2) * omega_N3(exp u) + omega_N3(exp u)) * cos(3 u)
# nodeR_fourier_minus_at_c6_N3 u = (exp(u/2) * omega_N3(exp u) - omega_N3(exp u)) * sin(3 u)
# ---------------------------------------------------------------------------
def node_bounds_at_point(u_frac, series_terms=50):
    """Compute (R_plus_interval, R_minus_interval) at u = u_frac (exact Fraction).

    Matches Lean definitions `nodeR_fourier_plus_at_c6_N3` / `..._minus_...`
    with `omega(e^u)` replaced by `omega_N3(e^u)`."""
    u_pt = I.point(u_frac)
    # exp(u)
    exp_u = exp_pos_interval(u_pt, series_terms=series_terms)
    # exp(u * 0.5) = exp(u/2)
    u_half = I.point(u_frac * Fraction(1, 2))
    exp_u_half = exp_pos_interval(u_half, series_terms=series_terms)
    # omega_N3(exp u)
    om = omega_N3_interval(exp_u, series_terms=series_terms)
    # F_plus_truncated = exp(u/2) * om
    Fp = (exp_u_half * om).rounded()
    # F_minus_truncated = om  (as the Lean def shows: nodeR = (exp(u/2)*om + om)*cos(3u))
    Fm = om
    # Angle 3 u = c*u/2 at c = 6
    three_u = I.point(Fraction(3) * u_frac)
    cos_3u = _cos_point(Fraction(3) * u_frac, series_terms=series_terms)
    sin_3u = _sin_point(Fraction(3) * u_frac, series_terms=series_terms)
    R_plus  = ((Fp + Fm) * cos_3u).rounded()
    R_minus = ((Fp - Fm) * sin_3u).rounded()
    return R_plus, R_minus


# ---------------------------------------------------------------------------
# Safety-backed emission at 10 decimal digits
# ---------------------------------------------------------------------------
def floor10_int(x_frac):
    """Return floor(x_frac * 10^10) as an exact Python int.  Direction: toward -∞."""
    scale = 10 ** 10
    num = x_frac.numerator * scale
    den = x_frac.denominator
    return num // den   # Python // floors toward -∞


def ceil10_int(x_frac):
    """Return ceil(x_frac * 10^10) as an exact Python int.  Direction: toward +∞."""
    scale = 10 ** 10
    num = x_frac.numerator * scale
    den = x_frac.denominator
    return -((-num) // den)


def emit_lower_bound(x_frac):
    """Rational L ≤ x_frac at 10 digits, with -1 ULP of 10^-10 safety backoff.

    So L_emitted = floor10(x_frac) / 10^10 - 10^-10.
    This matches r120's safety discipline."""
    n = floor10_int(x_frac) - 1
    return Fraction(n, 10 ** 10)


def emit_upper_bound(x_frac):
    """Rational U ≥ x_frac at 10 digits, with +1 ULP of 10^-10 safety backoff.

    So U_emitted = ceil10(x_frac) / 10^10 + 10^-10."""
    n = ceil10_int(x_frac) + 1
    return Fraction(n, 10 ** 10)


def frac_to_lean_decimal(q):
    """Emit a Python Fraction as an exact terminating decimal literal."""
    if q == 0:
        return "0"
    sign = '-' if q < 0 else ''
    q = abs(q)
    denom = q.denominator
    d = denom
    twos = 0
    while d % 2 == 0:
        d //= 2
        twos += 1
    fives = 0
    while d % 5 == 0:
        d //= 5
        fives += 1
    if d != 1:
        raise ValueError(f"non-terminating decimal for {q}")
    digits = max(twos, fives)
    scaled = q.numerator * (10 ** digits) // denom
    s = str(scaled).zfill(digits + 1)
    if digits == 0:
        return sign + s
    return sign + s[:-digits] + '.' + s[-digits:]


# ---------------------------------------------------------------------------
# M2 panel geometry: ONE segment on u ∈ [0, 1/4] with 8 uniform panels
# of width 1/32.  Midpoints are at (k + 1/2) · 1/32 for k = 0, ..., 7.
# ---------------------------------------------------------------------------
SEG_LO = Fraction(0)
SEG_HI = Fraction(1, 4)
N_PANELS = 8
PANEL_WIDTH = (SEG_HI - SEG_LO) / N_PANELS   # = 1/32

def panel_midpoint(k):
    """u_mid_k = SEG_LO + (k + 1/2) * width  for k = 0..N-1."""
    return SEG_LO + (Fraction(k) + Fraction(1, 2)) * PANEL_WIDTH


# ---------------------------------------------------------------------------
# Lean emitter
# ---------------------------------------------------------------------------
LEAN_HEADER = """/-
# PF.Analytic.FourierPanels.Seg01_c6_2026_10_15

M2 pointwise panel certificate — generated by
`scripts/gen_fourier_panels_c6.py` (Fraction interval arithmetic, outward
rounding to 1/10^30, emitted at 10 decimal digits with ±1 ULP safety backoff).

THIS FILE IS AUTO-GENERATED.  Regenerate via:
    python3 PF_Lean4_Code/scripts/gen_fourier_panels_c6.py

Scope: ONE segment covering `u ∈ [0, 1/4]` with 8 uniform panels of width
`1/32`.  Each panel contributes 4 bricks (plus_lo, plus_hi, minus_lo,
minus_hi), each closed by `Interval.approx_le` + `decide +kernel` against
the N = 3 interval mirrors `nodeI_fourier_plus_at_c6` /
`nodeI_fourier_minus_at_c6` from `CoreDefs_c6_2026_10_15.lean`.

Three-axiom bar: every brick prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/
"""


def emit_lean_file(bricks, path):
    """Emit the Lean module."""
    body = LEAN_HEADER
    body += "import PF.Analytic.FourierPanels.CoreDefs_c6_2026_10_15\n\n"
    body += "set_option autoImplicit false\n\n"
    body += "namespace PrincipiaTractalis\n"
    body += "namespace FourierPanels_c6\n"
    body += "namespace Seg01\n\n"
    body += "set_option maxRecDepth 4000000\n\n"
    for k, u_mid, L_plus, U_plus, L_minus, U_minus in bricks:
        u_mid_s   = frac_to_lean_decimal(u_mid)
        L_plus_s  = frac_to_lean_decimal(L_plus)
        U_plus_s  = frac_to_lean_decimal(U_plus)
        L_minus_s = frac_to_lean_decimal(L_minus)
        U_minus_s = frac_to_lean_decimal(U_minus)

        # plus_lo
        body += (
            f"theorem s01p{k}_plus_lo : ({L_plus_s} : ℝ)\n"
            f"    ≤ nodeR_fourier_plus_at_c6_N3 ({u_mid_s} : ℝ) := by\n"
            f"  refine _root_.Interval.approx_le\n"
            f"    (({L_plus_s} : _root_.Interval))\n"
            f"    (nodeI_fourier_plus_at_c6 ({u_mid_s} : _root_.Interval))\n"
            f"    ({L_plus_s} : ℝ)\n"
            f"    (nodeR_fourier_plus_at_c6_N3 ({u_mid_s} : ℝ))\n"
            f"    (by approx)\n"
            f"    (nodeR_fourier_plus_at_c6_N3_mem_approx\n"
            f"      (u := ({u_mid_s} : ℝ)) (U := ({u_mid_s} : _root_.Interval)) (by approx))\n"
            f"    ?_\n"
            f"  decide +kernel\n\n"
        )
        # plus_hi
        body += (
            f"theorem s01p{k}_plus_hi :\n"
            f"    nodeR_fourier_plus_at_c6_N3 ({u_mid_s} : ℝ) ≤ ({U_plus_s} : ℝ) := by\n"
            f"  refine _root_.Interval.approx_le\n"
            f"    (nodeI_fourier_plus_at_c6 ({u_mid_s} : _root_.Interval))\n"
            f"    (({U_plus_s} : _root_.Interval))\n"
            f"    (nodeR_fourier_plus_at_c6_N3 ({u_mid_s} : ℝ))\n"
            f"    ({U_plus_s} : ℝ)\n"
            f"    (nodeR_fourier_plus_at_c6_N3_mem_approx\n"
            f"      (u := ({u_mid_s} : ℝ)) (U := ({u_mid_s} : _root_.Interval)) (by approx))\n"
            f"    (by approx)\n"
            f"    ?_\n"
            f"  decide +kernel\n\n"
        )
        # minus_lo
        body += (
            f"theorem s01p{k}_minus_lo : ({L_minus_s} : ℝ)\n"
            f"    ≤ nodeR_fourier_minus_at_c6_N3 ({u_mid_s} : ℝ) := by\n"
            f"  refine _root_.Interval.approx_le\n"
            f"    (({L_minus_s} : _root_.Interval))\n"
            f"    (nodeI_fourier_minus_at_c6 ({u_mid_s} : _root_.Interval))\n"
            f"    ({L_minus_s} : ℝ)\n"
            f"    (nodeR_fourier_minus_at_c6_N3 ({u_mid_s} : ℝ))\n"
            f"    (by approx)\n"
            f"    (nodeR_fourier_minus_at_c6_N3_mem_approx\n"
            f"      (u := ({u_mid_s} : ℝ)) (U := ({u_mid_s} : _root_.Interval)) (by approx))\n"
            f"    ?_\n"
            f"  decide +kernel\n\n"
        )
        # minus_hi
        body += (
            f"theorem s01p{k}_minus_hi :\n"
            f"    nodeR_fourier_minus_at_c6_N3 ({u_mid_s} : ℝ) ≤ ({U_minus_s} : ℝ) := by\n"
            f"  refine _root_.Interval.approx_le\n"
            f"    (nodeI_fourier_minus_at_c6 ({u_mid_s} : _root_.Interval))\n"
            f"    (({U_minus_s} : _root_.Interval))\n"
            f"    (nodeR_fourier_minus_at_c6_N3 ({u_mid_s} : ℝ))\n"
            f"    ({U_minus_s} : ℝ)\n"
            f"    (nodeR_fourier_minus_at_c6_N3_mem_approx\n"
            f"      (u := ({u_mid_s} : ℝ)) (U := ({u_mid_s} : _root_.Interval)) (by approx))\n"
            f"    (by approx)\n"
            f"    ?_\n"
            f"  decide +kernel\n\n"
        )

    # Axiom-check prints at the end
    for k, _u, _lp, _up, _lm, _um in bricks:
        body += f"#print axioms s01p{k}_plus_lo\n"
        body += f"#print axioms s01p{k}_plus_hi\n"
        body += f"#print axioms s01p{k}_minus_lo\n"
        body += f"#print axioms s01p{k}_minus_hi\n"

    body += "\nend Seg01\n"
    body += "end FourierPanels_c6\n"
    body += "end PrincipiaTractalis\n"
    with open(path, 'w') as f:
        f.write(body)


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dry-run', action='store_true',
                        help="print audit, do not write Lean file")
    parser.add_argument('--out', default=None,
                        help="output Lean file path")
    args = parser.parse_args()

    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_lean_dir = os.path.abspath(os.path.join(script_dir, '..', 'PF', 'Analytic'))
    out_dir = os.path.join(repo_lean_dir, 'FourierPanels')
    out_path = args.out or os.path.join(out_dir, 'Seg01_c6_2026_10_15.lean')

    print("gen_fourier_panels_c6.py :: M2 pointwise panel generator")
    print(f"  segment: u in [{frac_to_lean_decimal(SEG_LO)}, {frac_to_lean_decimal(SEG_HI)}]")
    print(f"  n_panels: {N_PANELS}, panel width: {frac_to_lean_decimal(PANEL_WIDTH)}")
    print(f"  N = 3 truncation of omega(exp u)")
    print(f"  Fraction interval arithmetic (round outward to 1/10^{ROUND_DIGITS})")
    print(f"  Emitted precision: 10 decimal digits")
    print(f"  Safety backoff: ±1 ULP of 10^-10")
    print()

    audit_lines = []
    audit_lines.append(
        f"{'k':<3} {'u_mid':<10} "
        f"{'R+ true-lo':<17} {'R+ true-hi':<17} {'L_plus':<17} {'U_plus':<17} "
        f"{'R- true-lo':<17} {'R- true-hi':<17} {'L_minus':<17} {'U_minus':<17}"
    )
    audit_lines.append("-" * 180)

    bricks = []
    for k in range(N_PANELS):
        u_mid = panel_midpoint(k)
        R_plus, R_minus = node_bounds_at_point(u_mid, series_terms=50)
        L_plus  = emit_lower_bound(R_plus.lo)
        U_plus  = emit_upper_bound(R_plus.hi)
        L_minus = emit_lower_bound(R_minus.lo)
        U_minus = emit_upper_bound(R_minus.hi)
        # sanity checks
        assert L_plus <= R_plus.lo, f"panel {k}: L_plus ({float(L_plus):.12f}) > R_plus.lo ({float(R_plus.lo):.12f})"
        assert R_plus.hi <= U_plus, f"panel {k}: R_plus.hi > U_plus"
        assert L_minus <= R_minus.lo, f"panel {k}: L_minus > R_minus.lo"
        assert R_minus.hi <= U_minus, f"panel {k}: R_minus.hi > U_minus"
        bricks.append((k, u_mid, L_plus, U_plus, L_minus, U_minus))
        audit_lines.append(
            f"{k:<3} {float(u_mid):<10.6f} "
            f"{float(R_plus.lo):<17.12f} {float(R_plus.hi):<17.12f} "
            f"{float(L_plus):<17.10f} {float(U_plus):<17.10f} "
            f"{float(R_minus.lo):<17.12f} {float(R_minus.hi):<17.12f} "
            f"{float(L_minus):<17.10f} {float(U_minus):<17.10f}"
        )

    print("Per-panel enclosures (chunk-table audit):")
    for line in audit_lines:
        print(line)
    print()

    # Slack audit: how much headroom each L / U has vs. the certified true-value interval
    print("Slack analysis (how far each emitted bound is from the Fraction-interval true value):")
    print(f"{'k':<3}  {'slack L_plus (R+.lo - L+)':<30}  {'slack U_plus (U+ - R+.hi)':<30}  "
          f"{'slack L_minus (R-.lo - L-)':<30}  {'slack U_minus (U- - R-.hi)':<30}")
    for k, u_mid, L_plus, U_plus, L_minus, U_minus in bricks:
        R_plus, R_minus = node_bounds_at_point(u_mid, series_terms=50)
        s_Lp = R_plus.lo  - L_plus
        s_Up = U_plus     - R_plus.hi
        s_Lm = R_minus.lo - L_minus
        s_Um = U_minus    - R_minus.hi
        print(f"{k:<3}  {float(s_Lp):<30.3e}  {float(s_Up):<30.3e}  "
              f"{float(s_Lm):<30.3e}  {float(s_Um):<30.3e}")

    if args.dry_run:
        print("\n[dry-run] not writing Lean file.")
        return

    os.makedirs(out_dir, exist_ok=True)
    emit_lean_file(bricks, out_path)
    print(f"\nWrote {len(bricks) * 4} brick theorems to {out_path}")


if __name__ == "__main__":
    main()
