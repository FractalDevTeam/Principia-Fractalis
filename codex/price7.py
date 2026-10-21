#!/usr/bin/env python3
"""
Is prerequisite (2) -- the Tier-B M bound -- actually needed?

The per-segment-optimal ladder wants segment 3 on midpoint from D = 1 and
segment 4 from D = 8. Both are Tier B (T <= 1), which the producer cannot emit:
termM_coarse hardcodes the Tier-A constants, and the Lean M_sum_le lemma is
proved at that tier. Adding a tier is real work, and it needs a new Lean proof.

But the SHIPPED scheme `mmrrrr` (segments 1-2 midpoint, 3-6 range-brick) is
pure Tier A. If raising density on `mmrrrr` alone clears the box criterion
through c = 13, prerequisite (2) is unnecessary and the march needs only
prerequisite (1), parametric density.

The cost is that segments 3-6 then scale as 1/D rather than 1/D^2, so this is
not obviously affordable -- hence measuring rather than assuming. Compares, at
each band boundary and at c = 13:

    mmrrrr  (shipped, Tier A only)   vs   per-segment optimal (needs Tier B)

and reports the density each needs, and what that does to the march cost.
"""
import io
import os
from fractions import Fraction as F

import mpmath as mp

from price_density import ADDON, L0_val, M_of, SEGMENTS

mp.mp.dps = 30
HERE = os.path.dirname(os.path.abspath(__file__))
RG = os.path.join(HERE, "gen", "gen_fourier_panels_c27_4.py")
_g = {"__name__": "_g", "__file__": RG}
exec(compile(io.open(RG, encoding="utf-8").read(), RG, "exec"), _g)
I = _g["I"]
epi, ci, si = _g["exp_pos_interval"], _g["cos_interval"], _g["sin_interval"]
oi = _g["omega_N3_interval"]
ST = 50

_fc = {}


def fcache(a, b):
    k = (a, b)
    if k not in _fc:
        E = epi(I(a * F(1, 2), b * F(1, 2)), series_terms=ST)
        om = oi(epi(I(a, b), series_terms=ST), series_terms=ST)
        Fp = (E * om).rounded()
        _fc[k] = ((Fp + om).rounded(), (Fp - om).rounded())
    return _fc[k]


def seg_ub(c, seg, D, scheme):
    ch = F(c) / 2
    h = F(1, 32 * D)
    lo, hi = SEGMENTS[seg]
    R = Iv = F(0)
    err = F(M_of(c, hi)) * h ** 3 / 24 if scheme == "mid" else 0
    for k in range(8 * D):
        a = lo + k * h
        if scheme == "rng":
            P, Q = fcache(a, a + h)
            cu = I(ch * a, ch * (a + h))
        else:
            m = a + h / 2
            P, Q = fcache(m, m)
            cu = I(ch * m, ch * m)
        R += h * (P * ci(cu, series_terms=ST)).rounded().hi + (err / 2 if err else 0)
        Iv += h * (Q * si(cu, series_terms=ST)).rounded().hi + (err / 2 if err else 0)
    return R, Iv


_mc = {}


def mc_lb_scheme(c, D, scheme):
    """scheme is a 6-char string over {m, r}, segments 1..6."""
    k = (c, D, scheme)
    if k in _mc:
        return _mc[k]
    R = Iv = F(0)
    for i, ch in enumerate(scheme, start=1):
        a, b = seg_ub(c, i, D, "mid" if ch == "m" else "rng")
        R += a
        Iv += b
    cc = mp.mpf(F(c).numerator) / F(c).denominator
    ad = mp.mpf(ADDON.numerator) / ADDON.denominator
    gate = cc ** 2 * (mp.mpf(R.numerator) / R.denominator + ad) \
        + cc * (mp.mpf(Iv.numerator) / Iv.denominator + ad)
    _mc[k] = (1 - gate) / 2
    return _mc[k]


SHIPPED = "mmrrrr"          # Tier A only -- what the producer can emit today
OPT4 = "mmmrrr"             # needs Tier B on segment 3
OPT8 = "mmmmrr"             # needs Tier B on segments 3-4
DLAD = [1, 2, 4, 8, 16, 32, 64]
SAFETY = mp.mpf("1.25")


def need_D(c, r, scheme):
    lr = L0_val(F(c) - F(r)) * F(r)
    need = SAFETY * mp.mpf(lr.numerator) / lr.denominator
    for D in DLAD:
        if mc_lb_scheme(c, D, scheme) > need:
            return D
    return None


if __name__ == "__main__":
    print("=" * 92)
    print("IS THE TIER-B M BOUND NEEDED?   mmrrrr (Tier A only) vs the per-segment "
          "optimum")
    print("=" * 92)
    print(f"{'c':>8} {'r':>7} | {'mmrrrr D':>9} {'Mc_lb':>12} | "
          f"{'optimal D':>10} {'scheme':>8} {'Mc_lb':>12} | {'verdict':>14}")
    ROWS = [(F(41, 4), F(1, 16)), (F(11), F(1, 16)), (F(23, 2), F(1, 32)),
            (F(12), F(1, 32)), (F(25, 2), F(1, 64)), (F(13), F(1, 64))]
    worst = None
    for c, r in ROWS:
        ds = need_D(c, r, SHIPPED)
        opt_best = None
        for sch in (OPT4, OPT8):
            d = need_D(c, r, sch)
            if d is not None and (opt_best is None or d < opt_best[0]):
                opt_best = (d, sch)
        ms = float(mc_lb_scheme(c, ds, SHIPPED)) if ds else float("nan")
        mo = float(mc_lb_scheme(c, opt_best[0], opt_best[1])) if opt_best else float("nan")
        if ds is None:
            v = "TIER B NEEDED"
            worst = worst or (c, r)
        elif opt_best and ds > opt_best[0]:
            v = f"{ds//opt_best[0]}x costlier"
        else:
            v = "no Tier B need"
        print(f"{str(c):>8} {str(r):>7} | {str(ds):>9} {ms:>12.8f} | "
              f"{str(opt_best[0]) if opt_best else '-':>10} "
              f"{opt_best[1] if opt_best else '-':>8} {mo:>12.8f} | {v:>14}")
    print()
    if worst:
        print(f"  mmrrrr runs out at c = {worst[0]} -- Tier B is REQUIRED to finish "
              f"the march.")
    else:
        print("  mmrrrr reaches 13 at every centre tested: prerequisite (2) is NOT")
        print("  required, only prerequisite (1), parametric density.")
        print("  The cost is the density premium in the table above.")
