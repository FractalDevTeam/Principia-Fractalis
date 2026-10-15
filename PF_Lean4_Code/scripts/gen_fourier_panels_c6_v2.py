#!/usr/bin/env python3
"""
gen_fourier_panels_c6_v2.py — M2.5 panel-RANGE generator for
`Re Λ₀(1+6i)` / `Im Λ₀(1+6i)` at c = 6, N = 3 truncation of `omega(e^u)`.

SCIENTIFIC ROLE (v2 — RANGE ENCLOSURES)
---------------------------------------
v1 (`gen_fourier_panels_c6.py`) emitted POINTWISE bricks: `L_k ≤ f(u_mid_k) ≤ U_k`.
This is NOT an enclosure of `∫_[a_k, b_k] f du` — only a value at the midpoint.

v2 emits RANGE bricks: `L_k ≤ f(u) ≤ U_k  ∀ u ∈ Icc a_k b_k`.
These DIRECTLY imply the integral bound

    (b_k - a_k) * L_k ≤ ∫_[a_k, b_k] f du ≤ (b_k - a_k) * U_k

via `intervalIntegral.integral_mono_on` + integrability from continuity.

Mechanism in Python: for each panel [a_k, b_k], build an interval
`U = I(a_k, b_k)` (closed interval of Fractions). Evaluate the mirror
expression on `U`: `exp(U)`, `omega_N3(exp U)`, `cos(3·U)`, etc. The result
is a conservative range enclosure of the real function over the whole
panel.

Mechanism in Lean: the panel-brick uses

    U := (a_k : Interval) ∪ (b_k : Interval)

(union of two tight point Intervals, which is a non-point Interval containing
Icc a_k b_k). We prove `∀ u ∈ Icc a_k b_k, u ∈ approx U` via a helper lemma
`mem_approx_union_of_Icc` that follows from `approx_union_left/right` and
the convexity of `approx (A ∪ B) = Icc (min A.lo B.lo) (max A.hi B.hi)`.
Then `nodeR_fourier_plus_at_c6_N3_mem_approx` applied to this `U` gives
the range enclosure.

Then the integral bound follows from `intervalIntegral.integral_mono_on`
+ `intervalIntegral.integral_const` + continuity-from-composition.

Three-axiom bar: `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no `interval` tactic.

ROUNDING / N = 3 TRUNCATION
---------------------------
Same as v1: Fraction interval arithmetic with outward rounding to 1/10^30;
emission at 10 decimal digits with ±1 ULP safety backoff; N=3 omega
truncation `exp(-π·x) + exp(-4π·x) + exp(-9π·x)`.

Usage:
    python3 gen_fourier_panels_c6_v2.py             # emit Lean + report
    python3 gen_fourier_panels_c6_v2.py --dry-run   # print report only
"""
import argparse
import os
import sys
from fractions import Fraction

# ---------------------------------------------------------------------------
# Fraction-only outward-rounded interval arithmetic (same as v1)
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


def _cos_point(y_frac, series_terms=40):
    """Enclose cos(y) for a single Fraction y via Taylor series."""
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


def cos_interval(y_interval, series_terms=40):
    """Enclose cos(y) for y in y_interval.
    On [0, π], cos is monotone decreasing. For our range y ∈ [0, 3/4] (since
    u ∈ [0, 1/4] gives 3u ∈ [0, 3/4] < π/2 < π), we have
       cos(y_interval) ⊆ [cos(y_interval.hi), cos(y_interval.lo)].
    Validate: y_interval.lo ≥ 0 and y_interval.hi ≤ π is required for the
    simple monotone trick to be sound."""
    assert y_interval.lo >= 0
    # π_LO ~ 3.1415, so 1 < π; our panels are u ∈ [0, 1/4], 3u ∈ [0, 3/4]
    assert y_interval.hi <= 1, f"cos_interval expects y ≤ 1 (we're in [0, 3/4] here), got {y_interval}"
    cos_hi_enc = _cos_point(y_interval.hi, series_terms=series_terms)
    cos_lo_enc = _cos_point(y_interval.lo, series_terms=series_terms)
    # The enclosure of cos(y) for y in [a, b] with cos monotone-decreasing:
    #   lower bound = cos(b).lo  (from the enclosure of cos at the hi endpoint)
    #   upper bound = cos(a).hi  (from the enclosure of cos at the lo endpoint)
    return I(cos_hi_enc.lo, cos_lo_enc.hi)


def sin_interval(y_interval, series_terms=40):
    """Enclose sin(y) for y in y_interval.
    On [0, π/2], sin is monotone increasing. For y ∈ [0, 3/4] ⊂ [0, π/2],
       sin(y_interval) ⊆ [sin(y_interval.lo), sin(y_interval.hi)]."""
    assert y_interval.lo >= 0
    assert y_interval.hi <= 1, f"sin_interval expects y ≤ 1 (we're in [0, 3/4]), got {y_interval}"
    sin_lo_enc = _sin_point(y_interval.lo, series_terms=series_terms)
    sin_hi_enc = _sin_point(y_interval.hi, series_terms=series_terms)
    return I(sin_lo_enc.lo, sin_hi_enc.hi)


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
    """Compute (R_plus_interval, R_minus_interval) for u ∈ u_interval,
    where u_interval encloses a panel [a_k, b_k].

    Returns R_plus, R_minus such that
        nodeR_fourier_plus_at_c6_N3  u ∈ R_plus   ∀ u ∈ u_interval
        nodeR_fourier_minus_at_c6_N3 u ∈ R_minus  ∀ u ∈ u_interval
    """
    # exp(u) over the full range
    exp_u = exp_pos_interval(u_interval, series_terms=series_terms)
    # exp(u/2) over the full range
    u_half = I(u_interval.lo * Fraction(1, 2), u_interval.hi * Fraction(1, 2))
    exp_u_half = exp_pos_interval(u_half, series_terms=series_terms)
    # omega_N3(exp u) over the full range
    om = omega_N3_interval(exp_u, series_terms=series_terms)
    # F_plus = exp(u/2) * om, F_minus = om
    Fp = (exp_u_half * om).rounded()
    Fm = om
    # 3u over the full range
    three_u = I(Fraction(3) * u_interval.lo, Fraction(3) * u_interval.hi)
    cos_3u = cos_interval(three_u, series_terms=series_terms)
    sin_3u = sin_interval(three_u, series_terms=series_terms)
    # (Fp + Fm) * cos(3u) and (Fp - Fm) * sin(3u)
    R_plus  = ((Fp + Fm) * cos_3u).rounded()
    R_minus = ((Fp - Fm) * sin_3u).rounded()
    return R_plus, R_minus


# ---------------------------------------------------------------------------
# Safety-backed emission at 10 decimal digits (same as v1)
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
# M2.5 panel geometry: same as v1 — ONE segment u ∈ [0, 1/4], 8 panels of 1/32
# ---------------------------------------------------------------------------
SEG_LO = Fraction(0)
SEG_HI = Fraction(1, 4)
N_PANELS = 8
PANEL_WIDTH = (SEG_HI - SEG_LO) / N_PANELS   # = 1/32


def panel_endpoints(k):
    """Panel k runs from a_k = k * PANEL_WIDTH to b_k = (k+1) * PANEL_WIDTH."""
    a = SEG_LO + Fraction(k) * PANEL_WIDTH
    b = SEG_LO + Fraction(k + 1) * PANEL_WIDTH
    return a, b


# ---------------------------------------------------------------------------
# Lean emitter — M2.5 range bricks + integral-bound theorems
# ---------------------------------------------------------------------------
LEAN_HEADER = """/-
# PF.Analytic.FourierPanels.Seg01Range_c6_2026_10_15

**M2.5 panel-RANGE certificate** — generated by
`scripts/gen_fourier_panels_c6_v2.py` (Fraction interval arithmetic, outward
rounding to 1/10^30, emitted at 10 decimal digits with ±1 ULP safety backoff).

THIS FILE IS AUTO-GENERATED.  Regenerate via:
    python3 PF_Lean4_Code/scripts/gen_fourier_panels_c6_v2.py

Scope: ONE segment covering `u ∈ [0, 1/4]` with 8 uniform panels of width
`1/32`.  Each panel contributes 4 range bricks (plus_lo, plus_hi, minus_lo,
minus_hi) PLUS 2 integral-bound theorems (plus_integral, minus_integral),
giving 48 top-level declarations total.

The range bricks use `U := (a_k : _root_.Interval) ∪ (b_k : _root_.Interval)`
(the hull of the two endpoints), evaluate `nodeI_fourier_±_at_c6 U` on it,
and bound both ends by `Interval.approx_le` + `decide +kernel`.  The
range membership `∀ u ∈ Icc a_k b_k, u ∈ approx U` is discharged via
helper `mem_approx_union_of_Icc` from the convexity of `approx (A ∪ B)`.

The integral-bound theorems apply `intervalIntegral.integral_mono_on` with
the range bricks + continuity-based integrability to produce
    (b_k - a_k) * L_k  ≤  ∫_[a_k, b_k] f du  ≤  (b_k - a_k) * U_k.

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
    """Emit the 4 range bricks + 2 integral bounds for panel k."""
    a_s = frac_to_lean_decimal(a)
    b_s = frac_to_lean_decimal(b)
    width = b - a
    width_s = frac_to_lean_decimal(width)
    L_plus_s  = frac_to_lean_decimal(L_plus)
    U_plus_s  = frac_to_lean_decimal(U_plus)
    L_minus_s = frac_to_lean_decimal(L_minus)
    U_minus_s = frac_to_lean_decimal(U_minus)

    out = ""
    # §3.k.1 — plus_lo range brick: ∀ u ∈ Icc a b, L ≤ f(u)
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
    # plus_hi range brick: ∀ u ∈ Icc a b, f(u) ≤ U
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
    # minus_lo range brick
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
    # minus_hi range brick
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
    # plus_integral: (b - a) * L_plus ≤ ∫ ≤ (b - a) * U_plus
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
    # minus_integral
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

    # Axiom-check prints at the end
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
    out_path = args.out or os.path.join(out_dir, 'Seg01Range_c6_2026_10_15.lean')

    print("gen_fourier_panels_c6_v2.py :: M2.5 panel-RANGE generator")
    print(f"  segment: u in [{frac_to_lean_decimal(SEG_LO)}, {frac_to_lean_decimal(SEG_HI)}]")
    print(f"  n_panels: {N_PANELS}, panel width: {frac_to_lean_decimal(PANEL_WIDTH)}")
    print(f"  N = 3 truncation of omega(exp u)")
    print(f"  Fraction interval arithmetic (round outward to 1/10^{ROUND_DIGITS})")
    print(f"  Emitted precision: 10 decimal digits")
    print(f"  Safety backoff: ±1 ULP of 10^-10")
    print()

    audit_lines = []
    audit_lines.append(
        f"{'k':<3} {'a_k':<10} {'b_k':<10} "
        f"{'R+ range-lo':<17} {'R+ range-hi':<17} {'L_plus':<17} {'U_plus':<17} "
        f"{'R- range-lo':<17} {'R- range-hi':<17} {'L_minus':<17} {'U_minus':<17}"
    )
    audit_lines.append("-" * 200)

    bricks = []
    for k in range(N_PANELS):
        a, b = panel_endpoints(k)
        panel_U = I(a, b)
        R_plus, R_minus = node_bounds_on_interval(panel_U, series_terms=50)
        L_plus  = emit_lower_bound(R_plus.lo)
        U_plus  = emit_upper_bound(R_plus.hi)
        L_minus = emit_lower_bound(R_minus.lo)
        U_minus = emit_upper_bound(R_minus.hi)
        # sanity checks
        assert L_plus <= R_plus.lo, f"panel {k}: L_plus > R_plus.lo"
        assert R_plus.hi <= U_plus, f"panel {k}: R_plus.hi > U_plus"
        assert L_minus <= R_minus.lo, f"panel {k}: L_minus > R_minus.lo"
        assert R_minus.hi <= U_minus, f"panel {k}: R_minus.hi > U_minus"
        bricks.append((k, a, b, L_plus, U_plus, L_minus, U_minus))
        audit_lines.append(
            f"{k:<3} {float(a):<10.6f} {float(b):<10.6f} "
            f"{float(R_plus.lo):<17.12f} {float(R_plus.hi):<17.12f} "
            f"{float(L_plus):<17.10f} {float(U_plus):<17.10f} "
            f"{float(R_minus.lo):<17.12f} {float(R_minus.hi):<17.12f} "
            f"{float(L_minus):<17.10f} {float(U_minus):<17.10f}"
        )

    print("Per-panel RANGE enclosures (chunk-table audit):")
    for line in audit_lines:
        print(line)
    print()

    # Compute aggregate integral bounds across all 8 panels
    print("Aggregate integral bounds across u ∈ [0, 1/4]:")
    width = PANEL_WIDTH
    sum_L_plus  = sum(L_plus  * width for _, _, _, L_plus, _, _, _ in bricks)
    sum_U_plus  = sum(U_plus  * width for _, _, _, _, U_plus, _, _ in bricks)
    sum_L_minus = sum(L_minus * width for _, _, _, _, _, L_minus, _ in bricks)
    sum_U_minus = sum(U_minus * width for _, _, _, _, _, _, U_minus in bricks)
    print(f"  Σ (b-a) * L_plus  ≤ ∫_[0,1/4] (F_plus+F_minus)*cos(3u) du ≤ Σ (b-a) * U_plus")
    print(f"    = [{float(sum_L_plus):.10f}, {float(sum_U_plus):.10f}]")
    print(f"      width = {float(sum_U_plus - sum_L_plus):.3e}")
    print(f"  Σ (b-a) * L_minus ≤ ∫_[0,1/4] (F_plus-F_minus)*sin(3u) du ≤ Σ (b-a) * U_minus")
    print(f"    = [{float(sum_L_minus):.10f}, {float(sum_U_minus):.10f}]")
    print(f"      width = {float(sum_U_minus - sum_L_minus):.3e}")

    if args.dry_run:
        print("\n[dry-run] not writing Lean file.")
        return

    os.makedirs(out_dir, exist_ok=True)
    emit_lean_file(bricks, out_path)
    print(f"\nWrote {len(bricks) * 6} declarations ({len(bricks)*4} range bricks + {len(bricks)*2} integral bounds) to {out_path}")


if __name__ == "__main__":
    main()
