#!/usr/bin/env python3
"""
gen_fourier_panels_c6_v3.py — M2.5 panel-RANGE generator for
`Re Λ₀(1+6i)` / `Im Λ₀(1+6i)` at c = 6, N = 3 truncation of `omega(e^u)`.

CHANGES FROM v2
---------------
v2's `cos_interval` / `sin_interval` take a cheap monotone shortcut:
    cos(y) on [a,b] with y ∈ [0, 3/4] ⊂ [0, π/2] → cos is monotone decreasing
    sin(y) on [a,b] with y ∈ [0, 3/4] ⊂ [0, π/2] → sin is monotone increasing

That shortcut is only sound for `|y| ≤ 1` (equivalently, u ≤ 1/3), and v2
asserts this. For Segment 1 (u ∈ [0, 1/4], 3u ∈ [0, 3/4]) the shortcut is
fine. But for ANY segment past the first — in particular Segment 2
(u ∈ [1/4, 1/2], 3u ∈ [3/4, 3/2]) — the argument crosses π/2 ≈ 1.5708 and
the shortcut becomes UNSOUND.

v3 replaces `cos_interval` and `sin_interval` with sound versions that work
for ARBITRARY rational argument intervals.

STRATEGY (critical-point enumeration)
-------------------------------------
On `[a, b]`:

  * cos has critical points at y = kπ, k ∈ ℤ, where cos(kπ) = (-1)^k.
  * sin has critical points at y = (k+1/2)π, k ∈ ℤ, where sin((k+1/2)π) = (-1)^k.

Algorithm for cos on [a, b]:
  1. Evaluate cos at the two endpoints via Agent B's `_cos_point` (Taylor +
     Lagrange).
  2. Enumerate every integer k such that the rational enclosure
     [k·PI_LO, k·PI_HI] (for k ≥ 0; mirrored for k < 0) could overlap [a, b].
     For each such k, include cos(kπ) = (-1)^k as a candidate value (exact).
  3. Range = [min, max] over endpoints + critical-point values.

Analog for sin with half-integer multiples. Because π is irrational we use
the rational enclosure PI_LO ≤ π ≤ PI_HI; "could overlap" is tested with
outward-rounded arithmetic → conservative (sound) but tight for our panels.

This is strictly more general than v2's shortcut and gives the same answer
on monotone sub-intervals (regression tested on Segment 1 — matches v2
exactly to 10 digits).

CORE PRIMITIVES (unchanged from v2 / Agent B)
---------------------------------------------
  * `I` = Fraction interval arithmetic with outward rounding to 1/10^30.
  * `_exp_neg_point` + `exp_neg_interval` for exp(-x) on x ≥ 0.
  * `exp_pos_interval` for e^u, u ≥ 0, via reciprocal of exp_neg.
  * `_cos_point` + `_sin_point` from Agent B — Taylor series with Lagrange
    remainder, valid for ANY rational argument (not just |y| ≤ 1).
  * `omega_N3_interval` — N = 3 truncation of omega(exp u).

Three-axiom bar (downstream): `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no floating-point-as-proof. Pure `Fraction`
arithmetic.

Usage:
    python3 gen_fourier_panels_c6_v3.py              # emit Lean + report
    python3 gen_fourier_panels_c6_v3.py --dry-run    # print report only
    python3 gen_fourier_panels_c6_v3.py --test-seg2  # test u ∈ [1/4, 1/2]
    python3 gen_fourier_panels_c6_v3.py --test-pi6   # test π/6 crossing
"""
import argparse
import os
import sys
from fractions import Fraction

# ---------------------------------------------------------------------------
# Fraction-only outward-rounded interval arithmetic (verbatim from v2)
# ---------------------------------------------------------------------------
ROUND_DIGITS = 30
ROUND_DENOM = 10 ** ROUND_DIGITS


def round_down(f):
    num = f.numerator * ROUND_DENOM
    den = f.denominator
    q = num // den
    return Fraction(q, ROUND_DENOM)


def round_up(f):
    num = f.numerator * ROUND_DENOM
    den = f.denominator
    q = -((-num) // den)
    return Fraction(q, ROUND_DENOM)


class I:
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
        return I(round_down(self.lo), round_up(self.hi))


# Rational enclosure of pi to 30 digits
PI_LO = Fraction(3141592653589793238462643383, 10**27)
PI_HI = Fraction(3141592653589793238462643384, 10**27)
PI = I(PI_LO, PI_HI)


def _exp_neg_point(x_frac, series_terms=50):
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
    S = I(Fraction(1), Fraction(1))
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
    assert x_interval.lo >= 0
    lo_enc = _exp_neg_point(x_interval.hi, series_terms=series_terms)
    hi_enc = _exp_neg_point(x_interval.lo, series_terms=series_terms)
    return I(lo_enc.lo, hi_enc.hi)


def exp_pos_interval(u_interval, series_terms=50):
    assert u_interval.lo >= 0
    neg = exp_neg_interval(u_interval, series_terms=series_terms)
    if neg.lo <= 0:
        raise RuntimeError(f"exp_neg returned non-positive lower bound: {neg}")
    return I(Fraction(1) / neg.hi, Fraction(1) / neg.lo)


# ---------------------------------------------------------------------------
# Agent B's _cos_point / _sin_point (Taylor + Lagrange, works for ANY argument)
# ---------------------------------------------------------------------------
def _cos_point(y_frac, series_terms=40):
    """Enclose cos(y) for a single Fraction y via Taylor series + Lagrange.
    cos is even so compute at |y|. Valid for ANY rational y."""
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
    """Enclose sin(y) for a single Fraction y via Taylor series + Lagrange.
    Valid for ANY rational y."""
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
# v3 CORE: sound cos/sin interval enclosure via critical-point enumeration
# ---------------------------------------------------------------------------
# For cos on [a, b]:
#   extrema inside the interval are at y = k*pi, k integer, with value (-1)^k.
# For sin on [a, b]:
#   extrema inside the interval are at y = (k + 1/2)*pi, k integer, with
#   value (-1)^k.
#
# Soundness note: because pi is irrational we only know PI_LO <= pi <= PI_HI.
# For a candidate k we test whether k*pi could lie in [a, b]:
#   - if k >= 0: k*pi ranges over [k*PI_LO, k*PI_HI]. Candidate overlaps
#     [a, b] iff k*PI_LO <= b and k*PI_HI >= a.
#   - if k <  0: k*pi ranges over [k*PI_HI, k*PI_LO] (reversed since k < 0).
#     Candidate overlaps [a, b] iff k*PI_HI <= b and k*PI_LO >= a.
# If the test is positive we include the exact extremum value in the range.
# This is CONSERVATIVE (we may include an extremum that's actually just
# outside the interval) but SOUND, and the extra width is tiny: at most
# |k| * (PI_HI - PI_LO) = |k| * 10^-27 of slack per candidate boundary.
# ---------------------------------------------------------------------------

def _k_pi_overlaps(k, a, b):
    """Return True if k*pi could lie in [a, b] using the PI_LO/PI_HI enclosure."""
    if k == 0:
        return a <= 0 <= b
    if k > 0:
        lo = Fraction(k) * PI_LO
        hi = Fraction(k) * PI_HI
    else:
        # k < 0: k*PI_HI < k*PI_LO
        lo = Fraction(k) * PI_HI
        hi = Fraction(k) * PI_LO
    # overlap iff lo <= b and hi >= a
    return lo <= b and hi >= a


def _half_k_pi_overlaps(k, a, b):
    """Return True if (k + 1/2)*pi could lie in [a, b]."""
    coef = Fraction(2*k + 1, 2)
    if coef == 0:
        # Only possible if k = -1/2 which isn't integer; skip. (2k+1 is odd ≠ 0)
        return False
    if coef > 0:
        lo = coef * PI_LO
        hi = coef * PI_HI
    else:
        lo = coef * PI_HI
        hi = coef * PI_LO
    return lo <= b and hi >= a


def _k_range_for_cos(a, b):
    """Enumerate integers k such that k*pi could lie in [a, b].
    Returns a (possibly empty) list of integer k values."""
    # k*pi in [a, b] roughly means k in [a/pi, b/pi]. Using PI_LO/PI_HI:
    # a/PI_HI <= k <= b/PI_LO conservatively.
    # Add ±1 for safety at boundaries.
    if PI_LO <= 0:
        raise RuntimeError("PI_LO must be positive")
    if a <= 0 and b >= 0:
        k_lo = int((a / PI_LO)) - 1  # a <= 0: a/PI_LO <= 0
        k_hi = int((b / PI_LO)) + 1
    elif a > 0:
        k_lo = int((a / PI_HI)) - 1
        k_hi = int((b / PI_LO)) + 1
    else:  # b < 0
        k_lo = int((a / PI_LO)) - 1
        k_hi = int((b / PI_HI)) + 1
    out = []
    for k in range(k_lo, k_hi + 1):
        if _k_pi_overlaps(k, a, b):
            out.append(k)
    return out


def _half_k_range_for_sin(a, b):
    """Enumerate integers k such that (k+1/2)*pi could lie in [a, b]."""
    # (k+1/2)*pi in [a,b] → k+1/2 in [a/pi, b/pi] → k in [a/pi - 1/2, b/pi - 1/2].
    # Scan a wide-enough window.
    if a <= 0 and b >= 0:
        k_lo = int((a / PI_LO)) - 2
        k_hi = int((b / PI_LO)) + 2
    elif a > 0:
        k_lo = int((a / PI_HI)) - 2
        k_hi = int((b / PI_LO)) + 2
    else:
        k_lo = int((a / PI_LO)) - 2
        k_hi = int((b / PI_HI)) + 2
    out = []
    for k in range(k_lo, k_hi + 1):
        if _half_k_pi_overlaps(k, a, b):
            out.append(k)
    return out


def cos_interval(y_interval, series_terms=40):
    """Enclose cos(y) for y in y_interval. SOUND for ANY rational interval.

    Strategy: endpoint values via `_cos_point`, plus exact extremum values
    (-1)^k at any k*pi that could lie inside [a, b]. Take min/max.
    """
    a = y_interval.lo
    b = y_interval.hi
    cos_a = _cos_point(a, series_terms=series_terms)
    cos_b = _cos_point(b, series_terms=series_terms)
    lo = min(cos_a.lo, cos_b.lo)
    hi = max(cos_a.hi, cos_b.hi)
    for k in _k_range_for_cos(a, b):
        # cos(k*pi) = (-1)^k, exact
        v = Fraction(1) if (k % 2 == 0) else Fraction(-1)
        if v < lo:
            lo = v
        if v > hi:
            hi = v
    if lo < -1:
        lo = Fraction(-1)
    if hi > 1:
        hi = Fraction(1)
    return I(lo, hi)


def sin_interval(y_interval, series_terms=40):
    """Enclose sin(y) for y in y_interval. SOUND for ANY rational interval.

    Strategy: endpoint values via `_sin_point`, plus exact extremum values
    (-1)^k at any (k + 1/2)*pi that could lie inside [a, b]. Take min/max.
    """
    a = y_interval.lo
    b = y_interval.hi
    sin_a = _sin_point(a, series_terms=series_terms)
    sin_b = _sin_point(b, series_terms=series_terms)
    lo = min(sin_a.lo, sin_b.lo)
    hi = max(sin_a.hi, sin_b.hi)
    for k in _half_k_range_for_sin(a, b):
        # sin((k + 1/2)*pi) = (-1)^k, exact
        v = Fraction(1) if (k % 2 == 0) else Fraction(-1)
        if v < lo:
            lo = v
        if v > hi:
            hi = v
    if lo < -1:
        lo = Fraction(-1)
    if hi > 1:
        hi = Fraction(1)
    return I(lo, hi)


# ---------------------------------------------------------------------------
# omega_N3_interval, node_bounds_on_interval — unchanged from v2
# ---------------------------------------------------------------------------
def omega_N3_interval(x_interval, series_terms=50):
    """Enclose omega_N3(x) = exp(-pi x) + exp(-4 pi x) + exp(-9 pi x)."""
    assert x_interval.lo > 0
    pi_x   = (PI * x_interval).rounded()
    pi4_x  = (I.point(4) * pi_x).rounded()
    pi9_x  = (I.point(9) * pi_x).rounded()
    t1 = exp_neg_interval(pi_x,  series_terms=series_terms)
    t2 = exp_neg_interval(pi4_x, series_terms=series_terms)
    t3 = exp_neg_interval(pi9_x, series_terms=series_terms)
    return (t1 + t2 + t3).rounded()


def node_bounds_on_interval(u_interval, series_terms=50):
    """Compute (R_plus_interval, R_minus_interval) for u ∈ u_interval."""
    exp_u = exp_pos_interval(u_interval, series_terms=series_terms)
    u_half = I(u_interval.lo * Fraction(1, 2), u_interval.hi * Fraction(1, 2))
    exp_u_half = exp_pos_interval(u_half, series_terms=series_terms)
    om = omega_N3_interval(exp_u, series_terms=series_terms)
    Fp = (exp_u_half * om).rounded()
    Fm = om
    three_u = I(Fraction(3) * u_interval.lo, Fraction(3) * u_interval.hi)
    cos_3u = cos_interval(three_u, series_terms=series_terms)
    sin_3u = sin_interval(three_u, series_terms=series_terms)
    R_plus  = ((Fp + Fm) * cos_3u).rounded()
    R_minus = ((Fp - Fm) * sin_3u).rounded()
    return R_plus, R_minus


# ---------------------------------------------------------------------------
# Safety-backed emission at 10 decimal digits (same as v2)
# ---------------------------------------------------------------------------
def floor10_int(x_frac):
    scale = 10 ** 10
    num = x_frac.numerator * scale
    den = x_frac.denominator
    return num // den


def ceil10_int(x_frac):
    scale = 10 ** 10
    num = x_frac.numerator * scale
    den = x_frac.denominator
    return -((-num) // den)


def emit_lower_bound(x_frac):
    n = floor10_int(x_frac) - 1
    return Fraction(n, 10 ** 10)


def emit_upper_bound(x_frac):
    n = ceil10_int(x_frac) + 1
    return Fraction(n, 10 ** 10)


def frac_to_lean_decimal(q):
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
# M2.5 panel geometry: same as v2 — ONE segment u ∈ [0, 1/4], 8 panels of 1/32
# ---------------------------------------------------------------------------
SEG_LO = Fraction(0)
SEG_HI = Fraction(1, 4)
N_PANELS = 8
PANEL_WIDTH = (SEG_HI - SEG_LO) / N_PANELS   # = 1/32


def panel_endpoints(k):
    a = SEG_LO + Fraction(k) * PANEL_WIDTH
    b = SEG_LO + Fraction(k + 1) * PANEL_WIDTH
    return a, b


# ---------------------------------------------------------------------------
# Lean emitter — unchanged from v2 (soundness lives in Python; emission format
# of range bricks + integral bounds is identical).
# ---------------------------------------------------------------------------
LEAN_HEADER = """/-
# PF.Analytic.FourierPanels.Seg01Range_c6_2026_10_15

**M2.5 panel-RANGE certificate** — generated by
`scripts/gen_fourier_panels_c6_v3.py` (Fraction interval arithmetic, outward
rounding to 1/10^30, emitted at 10 decimal digits with ±1 ULP safety backoff).

THIS FILE IS AUTO-GENERATED.  Regenerate via:
    python3 PF_Lean4_Code/scripts/gen_fourier_panels_c6_v3.py

Scope: ONE segment covering `u ∈ [0, 1/4]` with 8 uniform panels of width
`1/32`.  Each panel contributes 4 range bricks (plus_lo, plus_hi, minus_lo,
minus_hi) PLUS 2 integral-bound theorems (plus_integral, minus_integral),
giving 48 top-level declarations total.

v3 note: `cos_interval` / `sin_interval` are now sound for ARBITRARY rational
argument intervals (critical-point enumeration + endpoint evaluation). On
Segment 1 where the argument 3u ∈ [0, 3/4] ⊂ [0, π/2] is monotone, v3's
output matches v2 to 10 digits — this file is bit-identical to the v2 output
for the Seg01 range.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/
"""


LEAN_PREAMBLE = r"""import PF.Analytic.FourierPanels.CoreDefs_c6_2026_10_15
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c6
namespace Seg01Range

open scoped Real
open MeasureTheory

set_option maxRecDepth 4000000

/-! ## §1 — Helper: range-interval membership from Icc + endpoint intervals -/

/-- If `a ∈ approx A` and `b ∈ approx B`, then every `u ∈ Icc a b` is in
    `approx (A ∪ B)`. Immediate from `Interval.mem_approx_of_monotone'`
    applied to the identity (monotone) function. -/
lemma mem_approx_union_of_Icc
    {a b : ℝ} {A B : _root_.Interval}
    (hA : a ∈ approx A) (hB : b ∈ approx B)
    {u : ℝ} (hu : u ∈ Set.Icc a b) :
    u ∈ approx (A ∪ B) := by
  have hmono : MonotoneOn (fun x : ℝ => x) (Set.Icc a b) :=
    fun _ _ _ _ hxy => hxy
  exact _root_.Interval.mem_approx_of_monotone' (f := fun x => x) hmono hu A B hA hB

/-! ## §2 — Continuity of the N = 3 node functions -/

/-- `omega_N3_at_exp` is continuous. -/
theorem omega_N3_at_exp_continuous : Continuous omega_N3_at_exp := by
  unfold omega_N3_at_exp
  refine Continuous.add (Continuous.add ?_ ?_) ?_
  · exact Real.continuous_exp.comp (continuous_neg.comp
      (continuous_const.mul Real.continuous_exp))
  · exact Real.continuous_exp.comp (continuous_neg.comp
      ((continuous_const.mul continuous_const).mul Real.continuous_exp))
  · exact Real.continuous_exp.comp (continuous_neg.comp
      ((continuous_const.mul continuous_const).mul Real.continuous_exp))

/-- `nodeR_fourier_plus_at_c6_N3` is continuous. -/
theorem nodeR_fourier_plus_at_c6_N3_continuous :
    Continuous nodeR_fourier_plus_at_c6_N3 := by
  unfold nodeR_fourier_plus_at_c6_N3
  refine Continuous.mul (Continuous.add ?_ omega_N3_at_exp_continuous)
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul
    omega_N3_at_exp_continuous

/-- `nodeR_fourier_minus_at_c6_N3` is continuous. -/
theorem nodeR_fourier_minus_at_c6_N3_continuous :
    Continuous nodeR_fourier_minus_at_c6_N3 := by
  unfold nodeR_fourier_minus_at_c6_N3
  refine Continuous.mul (Continuous.sub ?_ omega_N3_at_exp_continuous)
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul
    omega_N3_at_exp_continuous

/-- IntervalIntegrability for the plus node function. -/
theorem nodeR_fourier_plus_at_c6_N3_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable nodeR_fourier_plus_at_c6_N3 MeasureTheory.volume a b :=
  nodeR_fourier_plus_at_c6_N3_continuous.intervalIntegrable a b

/-- IntervalIntegrability for the minus node function. -/
theorem nodeR_fourier_minus_at_c6_N3_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable nodeR_fourier_minus_at_c6_N3 MeasureTheory.volume a b :=
  nodeR_fourier_minus_at_c6_N3_continuous.intervalIntegrable a b

"""


def emit_panel_block(k, a, b, L_plus, U_plus, L_minus, U_minus):
    a_s = frac_to_lean_decimal(a)
    b_s = frac_to_lean_decimal(b)
    width = b - a
    width_s = frac_to_lean_decimal(width)
    L_plus_s  = frac_to_lean_decimal(L_plus)
    U_plus_s  = frac_to_lean_decimal(U_plus)
    L_minus_s = frac_to_lean_decimal(L_minus)
    U_minus_s = frac_to_lean_decimal(U_minus)

    out = ""
    out += f"/-! ## §3.{k} — Panel {k}: u ∈ Icc {a_s} {b_s} -/\n\n"
    out += (
        f"theorem s01p{k}_plus_range_lo (u : ℝ) (hu : u ∈ Set.Icc ({a_s} : ℝ) ({b_s} : ℝ)) :\n"
        f"    ({L_plus_s} : ℝ) ≤ nodeR_fourier_plus_at_c6_N3 u := by\n"
        f"  have hU : u ∈ approx\n"
        f"    ((({a_s} : _root_.Interval)) ∪ (({b_s} : _root_.Interval))) :=\n"
        f"    mem_approx_union_of_Icc (by approx) (by approx) hu\n"
        f"  refine _root_.Interval.approx_le\n"
        f"    (({L_plus_s} : _root_.Interval))\n"
        f"    (nodeI_fourier_plus_at_c6\n"
        f"      (({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)))\n"
        f"    ({L_plus_s} : ℝ)\n"
        f"    (nodeR_fourier_plus_at_c6_N3 u)\n"
        f"    (by approx)\n"
        f"    (nodeR_fourier_plus_at_c6_N3_mem_approx\n"
        f"      (u := u)\n"
        f"      (U := ({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)) hU)\n"
        f"    ?_\n"
        f"  decide +kernel\n\n"
    )
    out += (
        f"theorem s01p{k}_plus_range_hi (u : ℝ) (hu : u ∈ Set.Icc ({a_s} : ℝ) ({b_s} : ℝ)) :\n"
        f"    nodeR_fourier_plus_at_c6_N3 u ≤ ({U_plus_s} : ℝ) := by\n"
        f"  have hU : u ∈ approx\n"
        f"    ((({a_s} : _root_.Interval)) ∪ (({b_s} : _root_.Interval))) :=\n"
        f"    mem_approx_union_of_Icc (by approx) (by approx) hu\n"
        f"  refine _root_.Interval.approx_le\n"
        f"    (nodeI_fourier_plus_at_c6\n"
        f"      (({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)))\n"
        f"    (({U_plus_s} : _root_.Interval))\n"
        f"    (nodeR_fourier_plus_at_c6_N3 u)\n"
        f"    ({U_plus_s} : ℝ)\n"
        f"    (nodeR_fourier_plus_at_c6_N3_mem_approx\n"
        f"      (u := u)\n"
        f"      (U := ({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)) hU)\n"
        f"    (by approx)\n"
        f"    ?_\n"
        f"  decide +kernel\n\n"
    )
    out += (
        f"theorem s01p{k}_minus_range_lo (u : ℝ) (hu : u ∈ Set.Icc ({a_s} : ℝ) ({b_s} : ℝ)) :\n"
        f"    ({L_minus_s} : ℝ) ≤ nodeR_fourier_minus_at_c6_N3 u := by\n"
        f"  have hU : u ∈ approx\n"
        f"    ((({a_s} : _root_.Interval)) ∪ (({b_s} : _root_.Interval))) :=\n"
        f"    mem_approx_union_of_Icc (by approx) (by approx) hu\n"
        f"  refine _root_.Interval.approx_le\n"
        f"    (({L_minus_s} : _root_.Interval))\n"
        f"    (nodeI_fourier_minus_at_c6\n"
        f"      (({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)))\n"
        f"    ({L_minus_s} : ℝ)\n"
        f"    (nodeR_fourier_minus_at_c6_N3 u)\n"
        f"    (by approx)\n"
        f"    (nodeR_fourier_minus_at_c6_N3_mem_approx\n"
        f"      (u := u)\n"
        f"      (U := ({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)) hU)\n"
        f"    ?_\n"
        f"  decide +kernel\n\n"
    )
    out += (
        f"theorem s01p{k}_minus_range_hi (u : ℝ) (hu : u ∈ Set.Icc ({a_s} : ℝ) ({b_s} : ℝ)) :\n"
        f"    nodeR_fourier_minus_at_c6_N3 u ≤ ({U_minus_s} : ℝ) := by\n"
        f"  have hU : u ∈ approx\n"
        f"    ((({a_s} : _root_.Interval)) ∪ (({b_s} : _root_.Interval))) :=\n"
        f"    mem_approx_union_of_Icc (by approx) (by approx) hu\n"
        f"  refine _root_.Interval.approx_le\n"
        f"    (nodeI_fourier_minus_at_c6\n"
        f"      (({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)))\n"
        f"    (({U_minus_s} : _root_.Interval))\n"
        f"    (nodeR_fourier_minus_at_c6_N3 u)\n"
        f"    ({U_minus_s} : ℝ)\n"
        f"    (nodeR_fourier_minus_at_c6_N3_mem_approx\n"
        f"      (u := u)\n"
        f"      (U := ({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)) hU)\n"
        f"    (by approx)\n"
        f"    ?_\n"
        f"  decide +kernel\n\n"
    )
    out += (
        f"theorem s01p{k}_plus_integral_bound :\n"
        f"    ({width_s} : ℝ) * ({L_plus_s} : ℝ)\n"
        f"      ≤ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), nodeR_fourier_plus_at_c6_N3 u)\n"
        f"    ∧ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), nodeR_fourier_plus_at_c6_N3 u)\n"
        f"      ≤ ({width_s} : ℝ) * ({U_plus_s} : ℝ) := by\n"
        f"  have hab : ({a_s} : ℝ) ≤ ({b_s} : ℝ) := by norm_num\n"
        f"  have hwidth : ({b_s} : ℝ) - ({a_s} : ℝ) = ({width_s} : ℝ) := by norm_num\n"
        f"  have hint_const_lo : (∫ _ in ({a_s} : ℝ)..({b_s} : ℝ), ({L_plus_s} : ℝ))\n"
        f"      = ({width_s} : ℝ) * ({L_plus_s} : ℝ) := by\n"
        f"    rw [intervalIntegral.integral_const, smul_eq_mul, hwidth]\n"
        f"  have hint_const_hi : (∫ _ in ({a_s} : ℝ)..({b_s} : ℝ), ({U_plus_s} : ℝ))\n"
        f"      = ({width_s} : ℝ) * ({U_plus_s} : ℝ) := by\n"
        f"    rw [intervalIntegral.integral_const, smul_eq_mul, hwidth]\n"
        f"  refine ⟨?_, ?_⟩\n"
        f"  · rw [← hint_const_lo]\n"
        f"    refine intervalIntegral.integral_mono_on hab\n"
        f"      (intervalIntegral.intervalIntegrable_const)\n"
        f"      (nodeR_fourier_plus_at_c6_N3_intervalIntegrable _ _)\n"
        f"      ?_\n"
        f"    intro u hu\n"
        f"    exact s01p{k}_plus_range_lo u hu\n"
        f"  · rw [← hint_const_hi]\n"
        f"    refine intervalIntegral.integral_mono_on hab\n"
        f"      (nodeR_fourier_plus_at_c6_N3_intervalIntegrable _ _)\n"
        f"      (intervalIntegral.intervalIntegrable_const)\n"
        f"      ?_\n"
        f"    intro u hu\n"
        f"    exact s01p{k}_plus_range_hi u hu\n\n"
    )
    out += (
        f"theorem s01p{k}_minus_integral_bound :\n"
        f"    ({width_s} : ℝ) * ({L_minus_s} : ℝ)\n"
        f"      ≤ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), nodeR_fourier_minus_at_c6_N3 u)\n"
        f"    ∧ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), nodeR_fourier_minus_at_c6_N3 u)\n"
        f"      ≤ ({width_s} : ℝ) * ({U_minus_s} : ℝ) := by\n"
        f"  have hab : ({a_s} : ℝ) ≤ ({b_s} : ℝ) := by norm_num\n"
        f"  have hwidth : ({b_s} : ℝ) - ({a_s} : ℝ) = ({width_s} : ℝ) := by norm_num\n"
        f"  have hint_const_lo : (∫ _ in ({a_s} : ℝ)..({b_s} : ℝ), ({L_minus_s} : ℝ))\n"
        f"      = ({width_s} : ℝ) * ({L_minus_s} : ℝ) := by\n"
        f"    rw [intervalIntegral.integral_const, smul_eq_mul, hwidth]\n"
        f"  have hint_const_hi : (∫ _ in ({a_s} : ℝ)..({b_s} : ℝ), ({U_minus_s} : ℝ))\n"
        f"      = ({width_s} : ℝ) * ({U_minus_s} : ℝ) := by\n"
        f"    rw [intervalIntegral.integral_const, smul_eq_mul, hwidth]\n"
        f"  refine ⟨?_, ?_⟩\n"
        f"  · rw [← hint_const_lo]\n"
        f"    refine intervalIntegral.integral_mono_on hab\n"
        f"      (intervalIntegral.intervalIntegrable_const)\n"
        f"      (nodeR_fourier_minus_at_c6_N3_intervalIntegrable _ _)\n"
        f"      ?_\n"
        f"    intro u hu\n"
        f"    exact s01p{k}_minus_range_lo u hu\n"
        f"  · rw [← hint_const_hi]\n"
        f"    refine intervalIntegral.integral_mono_on hab\n"
        f"      (nodeR_fourier_minus_at_c6_N3_intervalIntegrable _ _)\n"
        f"      (intervalIntegral.intervalIntegrable_const)\n"
        f"      ?_\n"
        f"    intro u hu\n"
        f"    exact s01p{k}_minus_range_hi u hu\n\n"
    )
    return out


def emit_lean_file(bricks, path):
    body = LEAN_HEADER
    body += LEAN_PREAMBLE
    for k, a, b, L_plus, U_plus, L_minus, U_minus in bricks:
        body += emit_panel_block(k, a, b, L_plus, U_plus, L_minus, U_minus)

    body += "/-! ## §Axiom check -/\n\n"
    body += "#print axioms mem_approx_union_of_Icc\n"
    body += "#print axioms omega_N3_at_exp_continuous\n"
    body += "#print axioms nodeR_fourier_plus_at_c6_N3_continuous\n"
    body += "#print axioms nodeR_fourier_minus_at_c6_N3_continuous\n"
    body += "#print axioms nodeR_fourier_plus_at_c6_N3_intervalIntegrable\n"
    body += "#print axioms nodeR_fourier_minus_at_c6_N3_intervalIntegrable\n"
    for k, _a, _b, _lp, _up, _lm, _um in bricks:
        body += f"#print axioms s01p{k}_plus_range_lo\n"
        body += f"#print axioms s01p{k}_plus_range_hi\n"
        body += f"#print axioms s01p{k}_minus_range_lo\n"
        body += f"#print axioms s01p{k}_minus_range_hi\n"
        body += f"#print axioms s01p{k}_plus_integral_bound\n"
        body += f"#print axioms s01p{k}_minus_integral_bound\n"

    body += "\nend Seg01Range\n"
    body += "end FourierPanels_c6\n"
    body += "end PrincipiaTractalis\n"
    with open(path, 'w') as f:
        f.write(body)


# ---------------------------------------------------------------------------
# Testing helpers
# ---------------------------------------------------------------------------
def _run_seg01():
    """Standard Seg01 run: u ∈ [0, 1/4], 8 panels. Returns bricks + audit list."""
    audit = []
    bricks = []
    for k in range(N_PANELS):
        a, b = panel_endpoints(k)
        panel_U = I(a, b)
        R_plus, R_minus = node_bounds_on_interval(panel_U, series_terms=50)
        L_plus  = emit_lower_bound(R_plus.lo)
        U_plus  = emit_upper_bound(R_plus.hi)
        L_minus = emit_lower_bound(R_minus.lo)
        U_minus = emit_upper_bound(R_minus.hi)
        assert L_plus <= R_plus.lo, f"panel {k}: L_plus > R_plus.lo"
        assert R_plus.hi <= U_plus, f"panel {k}: R_plus.hi > U_plus"
        assert L_minus <= R_minus.lo, f"panel {k}: L_minus > R_minus.lo"
        assert R_minus.hi <= U_minus, f"panel {k}: R_minus.hi > U_minus"
        bricks.append((k, a, b, L_plus, U_plus, L_minus, U_minus))
        audit.append((k, a, b, R_plus, R_minus, L_plus, U_plus, L_minus, U_minus))
    return bricks, audit


def _run_segment_range(u_lo, u_hi, n_panels):
    """Run panels on an arbitrary segment [u_lo, u_hi] with n_panels uniform panels.
    Returns list of (k, a, b, R_plus, R_minus, L_plus, U_plus, L_minus, U_minus)."""
    seg_lo = Fraction(u_lo)
    seg_hi = Fraction(u_hi)
    width = (seg_hi - seg_lo) / n_panels
    out = []
    for k in range(n_panels):
        a = seg_lo + Fraction(k) * width
        b = seg_lo + Fraction(k + 1) * width
        panel_U = I(a, b)
        R_plus, R_minus = node_bounds_on_interval(panel_U, series_terms=50)
        L_plus  = emit_lower_bound(R_plus.lo)
        U_plus  = emit_upper_bound(R_plus.hi)
        L_minus = emit_lower_bound(R_minus.lo)
        U_minus = emit_upper_bound(R_minus.hi)
        out.append((k, a, b, R_plus, R_minus, L_plus, U_plus, L_minus, U_minus))
    return out


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--dry-run', action='store_true')
    parser.add_argument('--out', default=None)
    parser.add_argument('--test-seg2', action='store_true',
                        help="test u ∈ [1/4, 1/2] (Segment 2 regime)")
    parser.add_argument('--test-pi6', action='store_true',
                        help="test u in a window straddling π/6 (cos(3u) = 0)")
    parser.add_argument('--all-tests', action='store_true',
                        help="run every test, no Lean emission")
    args = parser.parse_args()

    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_lean_dir = os.path.abspath(os.path.join(script_dir, '..', 'PF', 'Analytic'))
    out_dir = os.path.join(repo_lean_dir, 'FourierPanels')
    out_path = args.out or os.path.join(out_dir, 'Seg01Range_c6_2026_10_15.lean')

    print("gen_fourier_panels_c6_v3.py :: M2.5 panel-RANGE generator (sound cos/sin)")
    print(f"  Fraction interval arithmetic (round outward to 1/10^{ROUND_DIGITS})")
    print(f"  cos_interval / sin_interval: critical-point enumeration (SOUND for any argument)")
    print()

    # --- Seg01 primary run (regression check vs v2) ---
    print("=" * 90)
    print("Seg01 (u ∈ [0, 1/4], 8 panels, PANEL_WIDTH = 1/32)")
    print("=" * 90)
    bricks, audit = _run_seg01()
    hdr = (f"{'k':<3} {'a_k':<10} {'b_k':<10} "
           f"{'R+ lo':<17} {'R+ hi':<17} {'L_plus':<17} {'U_plus':<17} "
           f"{'R- lo':<17} {'R- hi':<17} {'L_minus':<17} {'U_minus':<17}")
    print(hdr)
    print("-" * len(hdr))
    for (k, a, b, R_plus, R_minus, L_plus, U_plus, L_minus, U_minus) in audit:
        print(f"{k:<3} {float(a):<10.6f} {float(b):<10.6f} "
              f"{float(R_plus.lo):<17.12f} {float(R_plus.hi):<17.12f} "
              f"{float(L_plus):<17.10f} {float(U_plus):<17.10f} "
              f"{float(R_minus.lo):<17.12f} {float(R_minus.hi):<17.12f} "
              f"{float(L_minus):<17.10f} {float(U_minus):<17.10f}")
    print()
    width = PANEL_WIDTH
    sum_L_plus  = sum(L_plus  * width for _, _, _, L_plus, _, _, _ in bricks)
    sum_U_plus  = sum(U_plus  * width for _, _, _, _, U_plus, _, _ in bricks)
    sum_L_minus = sum(L_minus * width for _, _, _, _, _, L_minus, _ in bricks)
    sum_U_minus = sum(U_minus * width for _, _, _, _, _, _, U_minus in bricks)
    print(f"Aggregate integral bounds on u ∈ [0, 1/4]:")
    print(f"  ∫ (F+ + F-) cos(3u) du ∈ [{float(sum_L_plus):.10f}, {float(sum_U_plus):.10f}] "
          f"(width = {float(sum_U_plus - sum_L_plus):.3e})")
    print(f"  ∫ (F+ - F-) sin(3u) du ∈ [{float(sum_L_minus):.10f}, {float(sum_U_minus):.10f}] "
          f"(width = {float(sum_U_minus - sum_L_minus):.3e})")
    print()

    # --- Test Seg2 (u ∈ [1/4, 1/2]) ---
    if args.test_seg2 or args.all_tests:
        print("=" * 90)
        print("TEST --test-seg2: u ∈ [1/4, 1/2], 8 panels (3u ∈ [3/4, 3/2]; crosses π/2)")
        print("=" * 90)
        rows = _run_segment_range(Fraction(1,4), Fraction(1,2), 8)
        print(hdr)
        print("-" * len(hdr))
        for (k, a, b, R_plus, R_minus, L_plus, U_plus, L_minus, U_minus) in rows:
            print(f"{k:<3} {float(a):<10.6f} {float(b):<10.6f} "
                  f"{float(R_plus.lo):<17.12f} {float(R_plus.hi):<17.12f} "
                  f"{float(L_plus):<17.10f} {float(U_plus):<17.10f} "
                  f"{float(R_minus.lo):<17.12f} {float(R_minus.hi):<17.12f} "
                  f"{float(L_minus):<17.10f} {float(U_minus):<17.10f}")
        w = (Fraction(1,2) - Fraction(1,4)) / 8  # = 1/32
        sL_plus  = sum(L_plus  * w for _, _, _, _, _, L_plus, _, _, _ in rows)
        sU_plus  = sum(U_plus  * w for _, _, _, _, _, _, U_plus, _, _ in rows)
        sL_minus = sum(L_minus * w for _, _, _, _, _, _, _, L_minus, _ in rows)
        sU_minus = sum(U_minus * w for _, _, _, _, _, _, _, _, U_minus in rows)
        print()
        print(f"Aggregate integral bounds on u ∈ [1/4, 1/2]:")
        print(f"  ∫ (F+ + F-) cos(3u) du ∈ [{float(sL_plus):.10f}, {float(sU_plus):.10f}]")
        print(f"  ∫ (F+ - F-) sin(3u) du ∈ [{float(sL_minus):.10f}, {float(sU_minus):.10f}]")
        print()

    # --- Test π/6 crossing (cos(3u) crosses zero at u = π/6) ---
    if args.test_pi6 or args.all_tests:
        print("=" * 90)
        print("TEST --test-pi6: single panel u ∈ [π/6 - 1/100, π/6 + 1/100]")
        print("  cos(3u) crosses zero at u = π/6 (3u = π/2). Expected cos_3u enclosure")
        print("  of width O(1/100) × 3 = O(3/100) spanning zero.")
        print("=" * 90)
        # π/6 is irrational; we use PI_LO/6 and PI_HI/6 as the enclosure
        # Build a RATIONAL window:
        #   a = PI_LO/6 - 1/100,  b = PI_HI/6 + 1/100
        # This conservatively encloses [π/6 - 1/100, π/6 + 1/100].
        a_pi6 = PI_LO / 6 - Fraction(1, 100)
        b_pi6 = PI_HI / 6 + Fraction(1, 100)
        print(f"  Panel: u ∈ [{float(a_pi6):.10f}, {float(b_pi6):.10f}]  "
              f"(width = {float(b_pi6 - a_pi6):.6f})")
        print(f"  3u    ∈ [{float(3*a_pi6):.10f}, {float(3*b_pi6):.10f}]  "
              f"(crosses π/2 ≈ 1.5707963267948966)")
        panel_U = I(a_pi6, b_pi6)
        # Direct cos/sin enclosure for diagnostic
        three_u = I(Fraction(3) * panel_U.lo, Fraction(3) * panel_U.hi)
        c_enc = cos_interval(three_u, series_terms=50)
        s_enc = sin_interval(three_u, series_terms=50)
        print(f"  cos(3u) ∈ [{float(c_enc.lo):.12e}, {float(c_enc.hi):.12e}]")
        print(f"  sin(3u) ∈ [{float(s_enc.lo):.12e}, {float(s_enc.hi):.12e}]")
        R_plus, R_minus = node_bounds_on_interval(panel_U, series_terms=50)
        print(f"  R_plus  ∈ [{float(R_plus.lo):.12e}, {float(R_plus.hi):.12e}]")
        print(f"  R_minus ∈ [{float(R_minus.lo):.12e}, {float(R_minus.hi):.12e}]")
        print()

    # --- Default: emit Lean (if --all-tests or test flags, skip emit) ---
    if args.dry_run or args.all_tests or args.test_seg2 or args.test_pi6:
        print("[test / dry-run] not writing Lean file.")
        return

    os.makedirs(out_dir, exist_ok=True)
    emit_lean_file(bricks, out_path)
    print(f"Wrote {len(bricks) * 6} declarations to {out_path}")


if __name__ == "__main__":
    main()
