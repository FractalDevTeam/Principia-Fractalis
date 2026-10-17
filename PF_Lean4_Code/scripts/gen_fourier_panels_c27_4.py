#!/usr/bin/env python3
"""
gen_fourier_panels_c27_4.py — M2.5 panel-RANGE generator for
`Re Λ₀(1 + (27/4)i)` / `Im Λ₀(1 + (27/4)i)` at c = 27/4, N = 3 truncation of
`omega(e^u)`.

This is the c=27/4 analog of the c=25/4 generator. The ONLY
mathematical differences from that generator:
  * The cosine/sine argument is `(c/2)*u = (27/8)*u`
    (c=25/4 used `(25/8)*u`).
  * The emitted Lean file uses the `*_at_c27_4_N3` names and imports
    `CoreDefs_c27_4_2026_10_16.lean`.

Everything else (Fraction interval arithmetic, outward rounding to 1/10^30,
critical-point enumeration for cos/sin, panel geometry of width 1/32,
10-digit emission with ±1 ULP safety back-off, three-axiom-bar emission
format) is bit-identical to the c=25/4 generator.

Three-axiom bar (downstream): `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no floating-point-as-proof. Pure `Fraction`
arithmetic.

Usage:
    python3 gen_fourier_panels_c27_4.py --seg 1    # emit Seg01Range for u ∈ [0, 1/4]
    python3 gen_fourier_panels_c27_4.py --seg 2    # emit Seg02Range for u ∈ [1/4, 1/2]
    ...
    python3 gen_fourier_panels_c27_4.py --seg 6    # emit Seg06Range for u ∈ [5/4, 3/2]
    python3 gen_fourier_panels_c27_4.py --seg 3 --dry-run   # print report only
"""
import argparse
import os
import sys
from fractions import Fraction

# ---------------------------------------------------------------------------
# Fraction-only outward-rounded interval arithmetic (verbatim from v3)
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
# _cos_point / _sin_point: Taylor + Lagrange, works for ANY rational argument
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
# Sound cos/sin interval enclosure via critical-point enumeration (v3 core)
# ---------------------------------------------------------------------------
def _k_pi_overlaps(k, a, b):
    if k == 0:
        return a <= 0 <= b
    if k > 0:
        lo = Fraction(k) * PI_LO
        hi = Fraction(k) * PI_HI
    else:
        lo = Fraction(k) * PI_HI
        hi = Fraction(k) * PI_LO
    return lo <= b and hi >= a


def _half_k_pi_overlaps(k, a, b):
    coef = Fraction(2*k + 1, 2)
    if coef == 0:
        return False
    if coef > 0:
        lo = coef * PI_LO
        hi = coef * PI_HI
    else:
        lo = coef * PI_HI
        hi = coef * PI_LO
    return lo <= b and hi >= a


def _k_range_for_cos(a, b):
    if PI_LO <= 0:
        raise RuntimeError("PI_LO must be positive")
    if a <= 0 and b >= 0:
        k_lo = int((a / PI_LO)) - 1
        k_hi = int((b / PI_LO)) + 1
    elif a > 0:
        k_lo = int((a / PI_HI)) - 1
        k_hi = int((b / PI_LO)) + 1
    else:
        k_lo = int((a / PI_LO)) - 1
        k_hi = int((b / PI_HI)) + 1
    out = []
    for k in range(k_lo, k_hi + 1):
        if _k_pi_overlaps(k, a, b):
            out.append(k)
    return out


def _half_k_range_for_sin(a, b):
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
    a = y_interval.lo
    b = y_interval.hi
    cos_a = _cos_point(a, series_terms=series_terms)
    cos_b = _cos_point(b, series_terms=series_terms)
    lo = min(cos_a.lo, cos_b.lo)
    hi = max(cos_a.hi, cos_b.hi)
    for k in _k_range_for_cos(a, b):
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
    a = y_interval.lo
    b = y_interval.hi
    sin_a = _sin_point(a, series_terms=series_terms)
    sin_b = _sin_point(b, series_terms=series_terms)
    lo = min(sin_a.lo, sin_b.lo)
    hi = max(sin_a.hi, sin_b.hi)
    for k in _half_k_range_for_sin(a, b):
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
# c=27/4 parameters
# ---------------------------------------------------------------------------
C_VALUE = Fraction(27, 4)             # c
C_HALF  = Fraction(27, 8)            # c/2 — multiplier in cos((c/2)*u), sin((c/2)*u)


def omega_N3_interval(x_interval, series_terms=50):
    assert x_interval.lo > 0
    pi_x   = (PI * x_interval).rounded()
    pi4_x  = (I.point(4) * pi_x).rounded()
    pi9_x  = (I.point(9) * pi_x).rounded()
    t1 = exp_neg_interval(pi_x,  series_terms=series_terms)
    t2 = exp_neg_interval(pi4_x, series_terms=series_terms)
    t3 = exp_neg_interval(pi9_x, series_terms=series_terms)
    return (t1 + t2 + t3).rounded()


def node_bounds_on_interval(u_interval, series_terms=50):
    """Compute (R_plus_interval, R_minus_interval, cos_cu, sin_cu) for u ∈ u_interval at c=27/4.

    R_plus  = (F_plus + F_minus) * cos((c/2)*u)   with F_plus = exp(u/2)*omega, F_minus = omega
    R_minus = (F_plus - F_minus) * sin((c/2)*u)
    c/2 = 27/8.
    """
    exp_u = exp_pos_interval(u_interval, series_terms=series_terms)
    u_half = I(u_interval.lo * Fraction(1, 2), u_interval.hi * Fraction(1, 2))
    exp_u_half = exp_pos_interval(u_half, series_terms=series_terms)
    om = omega_N3_interval(exp_u, series_terms=series_terms)
    Fp = (exp_u_half * om).rounded()
    Fm = om
    cu = I(C_HALF * u_interval.lo, C_HALF * u_interval.hi)
    cos_cu = cos_interval(cu, series_terms=series_terms)
    sin_cu = sin_interval(cu, series_terms=series_terms)
    R_plus  = ((Fp + Fm) * cos_cu).rounded()
    R_minus = ((Fp - Fm) * sin_cu).rounded()
    return R_plus, R_minus, cos_cu, sin_cu


# ---------------------------------------------------------------------------
# Safety-backed emission at 10 decimal digits
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
# Segment geometry: 6 segments, each width 1/4, 8 panels of width 1/32.
# ---------------------------------------------------------------------------
SEGMENTS = {
    1: (Fraction(0,   1), Fraction(1,  4)),
    2: (Fraction(1,   4), Fraction(1,  2)),
    3: (Fraction(1,   2), Fraction(3,  4)),
    4: (Fraction(3,   4), Fraction(1,  1)),
    5: (Fraction(1,   1), Fraction(5,  4)),
    6: (Fraction(5,   4), Fraction(3,  2)),
}
N_PANELS = 8


def panel_endpoints(seg_lo, seg_hi, k):
    width = (seg_hi - seg_lo) / N_PANELS
    a = seg_lo + Fraction(k) * width
    b = seg_lo + Fraction(k + 1) * width
    return a, b


# ---------------------------------------------------------------------------
# Lean emitter
# ---------------------------------------------------------------------------
def seg_file_name(seg_idx):
    return f"Seg0{seg_idx}Range_c27_4_2026_10_16.lean"


def seg_namespace(seg_idx):
    return f"Seg0{seg_idx}Range"


def seg_prefix(seg_idx):
    return f"s0{seg_idx}p"


def seg_file_header(seg_idx, seg_lo, seg_hi):
    lo_s = frac_to_lean_decimal(seg_lo)
    hi_s = frac_to_lean_decimal(seg_hi)
    ns = seg_namespace(seg_idx)
    return f"""/-
# PF.Analytic.FourierPanels.{ns}_c27_4_2026_10_16

**M2.5 panel-RANGE certificate** at `c = 27/4` — generated by
`scripts/gen_fourier_panels_c27_4.py` (Fraction interval arithmetic, outward
rounding to 1/10^30, emitted at 10 decimal digits with ±1 ULP safety backoff).

THIS FILE IS AUTO-GENERATED.  Regenerate via:
    python3 PF_Lean4_Code/scripts/gen_fourier_panels_c27_4.py --seg {seg_idx}

Scope: ONE segment covering `u ∈ [{lo_s}, {hi_s}]` with 8 uniform panels of
width `1/32`.  Each panel contributes 4 range bricks (plus_lo, plus_hi,
minus_lo, minus_hi) PLUS 2 integral-bound theorems (plus_integral,
minus_integral), giving 48 panel declarations + 6 header declarations = 54
top-level declarations total.

The range bricks use `U := (a_k : _root_.Interval) ∪ (b_k : _root_.Interval)`
(the hull of the two endpoints), evaluate `nodeI_fourier_±_at_c27_4 U` on it,
and bound both ends by `Interval.approx_le` + `decide +kernel`.  The
range membership `∀ u ∈ Icc a_k b_k, u ∈ approx U` is discharged via
helper `mem_approx_union_of_Icc` from the convexity of `approx (A ∪ B)`.

The integral-bound theorems apply `intervalIntegral.integral_mono_on` with
the range bricks + continuity-based integrability to produce
    (b_k - a_k) * L_k  ≤  ∫_[a_k, b_k] f du  ≤  (b_k - a_k) * U_k.

c=27/4 note: the cos/sin argument is `(c/2)·u = (27/8)·u`. The first cos
zero of `cos((27/8)·u)` is at `u = 8π/51 ≈ 0.4928`, which falls inside
Seg02's range [1/4, 1/2]. The first non-trivial sin zero is at
`u = 16π/51 ≈ 0.9856`, which falls inside Seg04's range [3/4, 1]. Segments
whose panels cross these zeros can have `L_plus` or `L_minus` negative; the
generator emits `[L, U]` with `L < 0 < U` in that regime, and v3's
critical-point enumeration is sound for arbitrary rational intervals.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/
"""


def seg_preamble(seg_idx):
    ns = seg_namespace(seg_idx)
    return f"""import PF.Analytic.FourierPanels.CoreDefs_c27_4_2026_10_16
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c27_4
namespace {ns}

open scoped Real
open MeasureTheory

set_option maxRecDepth 4000000

/-! ## §1 — Helper: range-interval membership from Icc + endpoint intervals -/

/-- If `a ∈ approx A` and `b ∈ approx B`, then every `u ∈ Icc a b` is in
    `approx (A ∪ B)`. Immediate from `Interval.mem_approx_of_monotone'`
    applied to the identity (monotone) function. -/
lemma mem_approx_union_of_Icc
    {{a b : ℝ}} {{A B : _root_.Interval}}
    (hA : a ∈ approx A) (hB : b ∈ approx B)
    {{u : ℝ}} (hu : u ∈ Set.Icc a b) :
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

/-- `nodeR_fourier_plus_at_c27_4_N3` is continuous. -/
theorem nodeR_fourier_plus_at_c27_4_N3_continuous :
    Continuous nodeR_fourier_plus_at_c27_4_N3 := by
  unfold nodeR_fourier_plus_at_c27_4_N3
  refine Continuous.mul (Continuous.add ?_ omega_N3_at_exp_continuous)
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul
    omega_N3_at_exp_continuous

/-- `nodeR_fourier_minus_at_c27_4_N3` is continuous. -/
theorem nodeR_fourier_minus_at_c27_4_N3_continuous :
    Continuous nodeR_fourier_minus_at_c27_4_N3 := by
  unfold nodeR_fourier_minus_at_c27_4_N3
  refine Continuous.mul (Continuous.sub ?_ omega_N3_at_exp_continuous)
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  exact (Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul
    omega_N3_at_exp_continuous

/-- IntervalIntegrability for the plus node function. -/
theorem nodeR_fourier_plus_at_c27_4_N3_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable nodeR_fourier_plus_at_c27_4_N3 MeasureTheory.volume a b :=
  nodeR_fourier_plus_at_c27_4_N3_continuous.intervalIntegrable a b

/-- IntervalIntegrability for the minus node function. -/
theorem nodeR_fourier_minus_at_c27_4_N3_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable nodeR_fourier_minus_at_c27_4_N3 MeasureTheory.volume a b :=
  nodeR_fourier_minus_at_c27_4_N3_continuous.intervalIntegrable a b

"""


def emit_panel_block(seg_idx, k, a, b, L_plus, U_plus, L_minus, U_minus):
    prefix = seg_prefix(seg_idx)
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
        f"theorem {prefix}{k}_plus_range_lo (u : ℝ) (hu : u ∈ Set.Icc ({a_s} : ℝ) ({b_s} : ℝ)) :\n"
        f"    ({L_plus_s} : ℝ) ≤ nodeR_fourier_plus_at_c27_4_N3 u := by\n"
        f"  have hU : u ∈ approx\n"
        f"    ((({a_s} : _root_.Interval)) ∪ (({b_s} : _root_.Interval))) :=\n"
        f"    mem_approx_union_of_Icc (by approx) (by approx) hu\n"
        f"  refine _root_.Interval.approx_le\n"
        f"    (({L_plus_s} : _root_.Interval))\n"
        f"    (nodeI_fourier_plus_at_c27_4\n"
        f"      (({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)))\n"
        f"    ({L_plus_s} : ℝ)\n"
        f"    (nodeR_fourier_plus_at_c27_4_N3 u)\n"
        f"    (by approx)\n"
        f"    (nodeR_fourier_plus_at_c27_4_N3_mem_approx\n"
        f"      (u := u)\n"
        f"      (U := ({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)) hU)\n"
        f"    ?_\n"
        f"  decide +kernel\n\n"
    )
    out += (
        f"theorem {prefix}{k}_plus_range_hi (u : ℝ) (hu : u ∈ Set.Icc ({a_s} : ℝ) ({b_s} : ℝ)) :\n"
        f"    nodeR_fourier_plus_at_c27_4_N3 u ≤ ({U_plus_s} : ℝ) := by\n"
        f"  have hU : u ∈ approx\n"
        f"    ((({a_s} : _root_.Interval)) ∪ (({b_s} : _root_.Interval))) :=\n"
        f"    mem_approx_union_of_Icc (by approx) (by approx) hu\n"
        f"  refine _root_.Interval.approx_le\n"
        f"    (nodeI_fourier_plus_at_c27_4\n"
        f"      (({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)))\n"
        f"    (({U_plus_s} : _root_.Interval))\n"
        f"    (nodeR_fourier_plus_at_c27_4_N3 u)\n"
        f"    ({U_plus_s} : ℝ)\n"
        f"    (nodeR_fourier_plus_at_c27_4_N3_mem_approx\n"
        f"      (u := u)\n"
        f"      (U := ({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)) hU)\n"
        f"    (by approx)\n"
        f"    ?_\n"
        f"  decide +kernel\n\n"
    )
    out += (
        f"theorem {prefix}{k}_minus_range_lo (u : ℝ) (hu : u ∈ Set.Icc ({a_s} : ℝ) ({b_s} : ℝ)) :\n"
        f"    ({L_minus_s} : ℝ) ≤ nodeR_fourier_minus_at_c27_4_N3 u := by\n"
        f"  have hU : u ∈ approx\n"
        f"    ((({a_s} : _root_.Interval)) ∪ (({b_s} : _root_.Interval))) :=\n"
        f"    mem_approx_union_of_Icc (by approx) (by approx) hu\n"
        f"  refine _root_.Interval.approx_le\n"
        f"    (({L_minus_s} : _root_.Interval))\n"
        f"    (nodeI_fourier_minus_at_c27_4\n"
        f"      (({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)))\n"
        f"    ({L_minus_s} : ℝ)\n"
        f"    (nodeR_fourier_minus_at_c27_4_N3 u)\n"
        f"    (by approx)\n"
        f"    (nodeR_fourier_minus_at_c27_4_N3_mem_approx\n"
        f"      (u := u)\n"
        f"      (U := ({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)) hU)\n"
        f"    ?_\n"
        f"  decide +kernel\n\n"
    )
    out += (
        f"theorem {prefix}{k}_minus_range_hi (u : ℝ) (hu : u ∈ Set.Icc ({a_s} : ℝ) ({b_s} : ℝ)) :\n"
        f"    nodeR_fourier_minus_at_c27_4_N3 u ≤ ({U_minus_s} : ℝ) := by\n"
        f"  have hU : u ∈ approx\n"
        f"    ((({a_s} : _root_.Interval)) ∪ (({b_s} : _root_.Interval))) :=\n"
        f"    mem_approx_union_of_Icc (by approx) (by approx) hu\n"
        f"  refine _root_.Interval.approx_le\n"
        f"    (nodeI_fourier_minus_at_c27_4\n"
        f"      (({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)))\n"
        f"    (({U_minus_s} : _root_.Interval))\n"
        f"    (nodeR_fourier_minus_at_c27_4_N3 u)\n"
        f"    ({U_minus_s} : ℝ)\n"
        f"    (nodeR_fourier_minus_at_c27_4_N3_mem_approx\n"
        f"      (u := u)\n"
        f"      (U := ({a_s} : _root_.Interval) ∪ ({b_s} : _root_.Interval)) hU)\n"
        f"    (by approx)\n"
        f"    ?_\n"
        f"  decide +kernel\n\n"
    )
    out += (
        f"theorem {prefix}{k}_plus_integral_bound :\n"
        f"    ({width_s} : ℝ) * ({L_plus_s} : ℝ)\n"
        f"      ≤ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), nodeR_fourier_plus_at_c27_4_N3 u)\n"
        f"    ∧ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), nodeR_fourier_plus_at_c27_4_N3 u)\n"
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
        f"      (nodeR_fourier_plus_at_c27_4_N3_intervalIntegrable _ _)\n"
        f"      ?_\n"
        f"    intro u hu\n"
        f"    exact {prefix}{k}_plus_range_lo u hu\n"
        f"  · rw [← hint_const_hi]\n"
        f"    refine intervalIntegral.integral_mono_on hab\n"
        f"      (nodeR_fourier_plus_at_c27_4_N3_intervalIntegrable _ _)\n"
        f"      (intervalIntegral.intervalIntegrable_const)\n"
        f"      ?_\n"
        f"    intro u hu\n"
        f"    exact {prefix}{k}_plus_range_hi u hu\n\n"
    )
    out += (
        f"theorem {prefix}{k}_minus_integral_bound :\n"
        f"    ({width_s} : ℝ) * ({L_minus_s} : ℝ)\n"
        f"      ≤ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), nodeR_fourier_minus_at_c27_4_N3 u)\n"
        f"    ∧ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), nodeR_fourier_minus_at_c27_4_N3 u)\n"
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
        f"      (nodeR_fourier_minus_at_c27_4_N3_intervalIntegrable _ _)\n"
        f"      ?_\n"
        f"    intro u hu\n"
        f"    exact {prefix}{k}_minus_range_lo u hu\n"
        f"  · rw [← hint_const_hi]\n"
        f"    refine intervalIntegral.integral_mono_on hab\n"
        f"      (nodeR_fourier_minus_at_c27_4_N3_intervalIntegrable _ _)\n"
        f"      (intervalIntegral.intervalIntegrable_const)\n"
        f"      ?_\n"
        f"    intro u hu\n"
        f"    exact {prefix}{k}_minus_range_hi u hu\n\n"
    )
    return out


def emit_lean_file(seg_idx, seg_lo, seg_hi, bricks, path):
    body = seg_file_header(seg_idx, seg_lo, seg_hi)
    body += seg_preamble(seg_idx)
    for k, a, b, L_plus, U_plus, L_minus, U_minus in bricks:
        body += emit_panel_block(seg_idx, k, a, b, L_plus, U_plus, L_minus, U_minus)

    prefix = seg_prefix(seg_idx)
    ns = seg_namespace(seg_idx)
    body += "/-! ## §Axiom check -/\n\n"
    body += "#print axioms mem_approx_union_of_Icc\n"
    body += "#print axioms omega_N3_at_exp_continuous\n"
    body += "#print axioms nodeR_fourier_plus_at_c27_4_N3_continuous\n"
    body += "#print axioms nodeR_fourier_minus_at_c27_4_N3_continuous\n"
    body += "#print axioms nodeR_fourier_plus_at_c27_4_N3_intervalIntegrable\n"
    body += "#print axioms nodeR_fourier_minus_at_c27_4_N3_intervalIntegrable\n"
    for k, _a, _b, _lp, _up, _lm, _um in bricks:
        body += f"#print axioms {prefix}{k}_plus_range_lo\n"
        body += f"#print axioms {prefix}{k}_plus_range_hi\n"
        body += f"#print axioms {prefix}{k}_minus_range_lo\n"
        body += f"#print axioms {prefix}{k}_minus_range_hi\n"
        body += f"#print axioms {prefix}{k}_plus_integral_bound\n"
        body += f"#print axioms {prefix}{k}_minus_integral_bound\n"

    body += f"\nend {ns}\n"
    body += "end FourierPanels_c27_4\n"
    body += "end PrincipiaTractalis\n"
    with open(path, 'w') as f:
        f.write(body)


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------
def run_segment(seg_idx):
    seg_lo, seg_hi = SEGMENTS[seg_idx]
    audit = []
    bricks = []
    width = (seg_hi - seg_lo) / N_PANELS
    for k in range(N_PANELS):
        a, b = panel_endpoints(seg_lo, seg_hi, k)
        panel_U = I(a, b)
        R_plus, R_minus, cos_cu, sin_cu = node_bounds_on_interval(panel_U, series_terms=50)
        L_plus  = emit_lower_bound(R_plus.lo)
        U_plus  = emit_upper_bound(R_plus.hi)
        L_minus = emit_lower_bound(R_minus.lo)
        U_minus = emit_upper_bound(R_minus.hi)
        assert L_plus <= R_plus.lo, f"panel {k}: L_plus > R_plus.lo"
        assert R_plus.hi <= U_plus, f"panel {k}: R_plus.hi > U_plus"
        assert L_minus <= R_minus.lo, f"panel {k}: L_minus > R_minus.lo"
        assert R_minus.hi <= U_minus, f"panel {k}: R_minus.hi > U_minus"
        bricks.append((k, a, b, L_plus, U_plus, L_minus, U_minus))
        audit.append((k, a, b, R_plus, R_minus, L_plus, U_plus, L_minus, U_minus, cos_cu, sin_cu))
    return bricks, audit, seg_lo, seg_hi, width


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seg', type=int, required=True, choices=[1,2,3,4,5,6])
    parser.add_argument('--dry-run', action='store_true')
    parser.add_argument('--out', default=None)
    args = parser.parse_args()

    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_lean_dir = os.path.abspath(os.path.join(script_dir, '..', 'PF', 'Analytic'))
    out_dir = os.path.join(repo_lean_dir, 'FourierPanels')
    out_path = args.out or os.path.join(out_dir, seg_file_name(args.seg))

    print(f"gen_fourier_panels_c27_4.py :: Segment {args.seg} at c = 27/4")
    print(f"  cos/sin argument multiplier c/2 = 27/8 = {float(C_HALF):.6f}")
    print(f"  Fraction interval arithmetic (round outward to 1/10^{ROUND_DIGITS})")
    print()

    bricks, audit, seg_lo, seg_hi, width = run_segment(args.seg)
    print("=" * 100)
    print(f"Seg0{args.seg} (u ∈ [{float(seg_lo):.6f}, {float(seg_hi):.6f}], 8 panels, PANEL_WIDTH = 1/32)")
    print("=" * 100)
    hdr = (f"{'k':<3} {'a_k':<10} {'b_k':<10} "
           f"{'R+ lo':<18} {'R+ hi':<18} "
           f"{'R- lo':<18} {'R- hi':<18} "
           f"{'cos lo':<13} {'cos hi':<13} {'sin lo':<13} {'sin hi':<13}")
    print(hdr)
    print("-" * len(hdr))
    for row in audit:
        (k, a, b, R_plus, R_minus, L_plus, U_plus, L_minus, U_minus, cos_cu, sin_cu) = row
        print(f"{k:<3} {float(a):<10.6f} {float(b):<10.6f} "
              f"{float(R_plus.lo):<18.12f} {float(R_plus.hi):<18.12f} "
              f"{float(R_minus.lo):<18.12f} {float(R_minus.hi):<18.12f} "
              f"{float(cos_cu.lo):<13.8f} {float(cos_cu.hi):<13.8f} "
              f"{float(sin_cu.lo):<13.8f} {float(sin_cu.hi):<13.8f}")
    print()
    sum_L_plus  = sum(bricks[i][3] * width for i in range(N_PANELS))
    sum_U_plus  = sum(bricks[i][4] * width for i in range(N_PANELS))
    sum_L_minus = sum(bricks[i][5] * width for i in range(N_PANELS))
    sum_U_minus = sum(bricks[i][6] * width for i in range(N_PANELS))
    print(f"Aggregate integral bounds on u ∈ [{float(seg_lo):.6f}, {float(seg_hi):.6f}]:")
    print(f"  ∫ nodeR_fourier_plus_at_c27_4_N3 du  ∈ [{float(sum_L_plus):.10f}, {float(sum_U_plus):.10f}] "
          f"(width = {float(sum_U_plus - sum_L_plus):.3e})")
    print(f"  ∫ nodeR_fourier_minus_at_c27_4_N3 du ∈ [{float(sum_L_minus):.10f}, {float(sum_U_minus):.10f}] "
          f"(width = {float(sum_U_minus - sum_L_minus):.3e})")
    print()

    if args.dry_run:
        print("[dry-run] not writing Lean file.")
        return

    os.makedirs(out_dir, exist_ok=True)
    emit_lean_file(args.seg, seg_lo, seg_hi, bricks, out_path)
    print(f"Wrote {len(bricks) * 6 + 6} declarations to {out_path}")


if __name__ == "__main__":
    main()
