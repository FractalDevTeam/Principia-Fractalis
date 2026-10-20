#!/usr/bin/env python3
"""
STEP 1, per-segment scheme: is ALL-midpoint the right scheme at high density,
or should segments 5-6 stay range-brick?

At density D the two schemes scale differently per segment:

    midpoint half-width   = M_seg(c) / (196608 D^2)        [closed form]
    range-brick half-width = (excess of sum h*U_k over the true integral) ~ 1/D
                             [measured with the shipped interval arithmetic]

At D = 1 and c = 27/4 the measured per-segment half-widths are

    seg  1      2      3      4      5      6
    rng  2.13e-3 8.78e-4 3.10e-4 9.70e-5 1.59e-5 8.49e-7
    mid  2.44e-4 2.44e-4 3.05e-4 3.05e-4 7.32e-4 7.32e-4

so midpoint wins on 1-3 immediately, on 4 from D ~ 4, on 5 only from D ~ 46,
and on 6 never. Raising density uniformly to 16 therefore pays the midpoint
penalty on segments 5-6 (M is Tier C there: E<=3, expT<=9, so M is large)
where the range brick is three orders of magnitude better.

This prices the PER-SEGMENT optimum against all-midpoint, since the module
count is 6D either way -- the saving shows up as a lower required D.
"""
import io
import os
from fractions import Fraction as F

import mpmath as mp

from price_density import ADDON, L0_val, M_of, SEGMENTS, true_nodes

mp.mp.dps = 30
HERE = os.path.dirname(os.path.abspath(__file__))
RG = os.path.join(HERE, "gen", "gen_fourier_panels_c27_4.py")
_g = {"__name__": "_g", "__file__": RG}
exec(compile(io.open(RG, encoding="utf-8").read(), RG, "exec"), _g)
I = _g["I"]
epi, ci, si = _g["exp_pos_interval"], _g["cos_interval"], _g["sin_interval"]
oi = _g["omega_N3_interval"]
ST = 50


def node_iv(a, b, c_half):
    """(R interval, I interval) of the node integrands over [a,b]."""
    u = I(a, b)
    exp_u = epi(u, series_terms=ST)
    E = epi(I(a * F(1, 2), b * F(1, 2)), series_terms=ST)
    om = oi(exp_u, series_terms=ST)
    Fp = (E * om).rounded()
    cu = I(c_half * a, c_half * b)
    return (((Fp + om) * ci(cu, series_terms=ST)).rounded(),
            ((Fp - om) * si(cu, series_terms=ST)).rounded())


def rng_ub(c, seg, D):
    """sum_k h * U_k for the range brick on this segment at density D."""
    ch = F(c) / 2
    h = F(1, 32 * D)
    lo, hi = SEGMENTS[seg]
    R = Iv = F(0)
    for k in range(8 * D):
        a = lo + k * h
        A, B = node_iv(a, a + h, ch)
        R += h * A.hi
        Iv += h * B.hi
    return R, Iv


def mid_ub(c, seg, D):
    """sum_k (h * U_node(m_k) + err/2) for the midpoint panel at density D."""
    ch = F(c) / 2
    h = F(1, 32 * D)
    lo, hi = SEGMENTS[seg]
    M = M_of(c, hi)
    err = F(M) * h ** 3 / 24
    R = Iv = F(0)
    for k in range(8 * D):
        m = lo + k * h + h / 2
        A, B = node_iv(m, m, ch)
        R += h * A.hi + err / 2
        Iv += h * B.hi + err / 2
    return R, Iv


def seg_true(c, seg):
    ch = mp.mpf(F(c).numerator) / F(c).denominator / 2
    o3 = lambda x: (mp.e ** (-mp.pi * x) + mp.e ** (-4 * mp.pi * x)
                    + mp.e ** (-9 * mp.pi * x))
    lo, hi = SEGMENTS[seg]
    a, b = mp.mpf(lo.numerator) / lo.denominator, mp.mpf(hi.numerator) / hi.denominator
    fR = lambda u: (mp.e ** (u / 2) + 1) * o3(mp.e ** u) * mp.cos(ch * u)
    fI = lambda u: (mp.e ** (u / 2) - 1) * o3(mp.e ** u) * mp.sin(ch * u)
    return mp.quad(fR, [a, b]), mp.quad(fI, [a, b])


C = F(13)
print("=" * 96)
print(f"PER-SEGMENT EXCESS at c = {C}  (sum h*U_k minus the true integral; "
      "this is what Mc_lb pays)")
print("=" * 96)
print(f"{'seg':>4} {'M(13)':>7} | {'D=1 rng':>10} {'D=1 mid':>10} | "
      f"{'D=4 rng':>10} {'D=4 mid':>10} | {'D=16 rng':>10} {'D=16 mid':>10}"
      f" | {'best@16':>8}")
best = {}
tot = {"allmid": {}, "persec": {}, "rng": {}}
for seg in range(1, 7):
    tR, tI = seg_true(C, seg)
    row = {}
    for D in (1, 4, 16):
        rR, rI = rng_ub(C, seg, D)
        mR, mI = mid_ub(C, seg, D)
        row[("rng", D)] = (float(rR) - float(tR), float(rI) - float(tI))
        row[("mid", D)] = (float(mR) - float(tR), float(mI) - float(tI))
    # score by what the gate pays: c^2 * excessR + c * excessI
    cc = float(C)
    sc = lambda e: cc * cc * e[0] + cc * e[1]
    b = min(("rng", "mid"), key=lambda w: sc(row[(w, 16)]))
    best[seg] = b
    print(f"{seg:>4} {M_of(C, SEGMENTS[seg][1]):>7} |"
          f" {sc(row[('rng',1)]):>10.3e} {sc(row[('mid',1)]):>10.3e} |"
          f" {sc(row[('rng',4)]):>10.3e} {sc(row[('mid',4)]):>10.3e} |"
          f" {sc(row[('rng',16)]):>10.3e} {sc(row[('mid',16)]):>10.3e}"
          f" | {b:>8}")
    for D in (1, 4, 16):
        tot["allmid"][D] = tot["allmid"].get(D, 0) + sc(row[("mid", D)])
        tot["rng"][D] = tot["rng"].get(D, 0) + sc(row[("rng", D)])
        w = min(("rng", "mid"), key=lambda w: sc(row[(w, D)]))
        tot["persec"][D] = tot["persec"].get(D, 0) + sc(row[(w, D)])
print()
print(f"  scheme totals (gate cost c^2*dR + c*dI at c = 13):")
print(f"  {'D':>4} {'all-range':>12} {'all-midpoint':>13} {'per-segment':>13}")
for D in (1, 4, 16):
    print(f"  {D:>4} {tot['rng'][D]:>12.4e} {tot['allmid'][D]:>13.4e}"
          f" {tot['persec'][D]:>13.4e}")
print()
print(f"  best scheme per segment at D = 16: "
      f"{ {s: best[s] for s in sorted(best)} }")
print()
ad = float(ADDON)
cc = float(C)
addon_cost = cc * cc * ad + cc * ad
tR, tI = true_nodes(C)
base = 1 - (cc * cc * float(tR) + cc * float(tI)) - addon_cost
print(f"  Mc_lb(13) = (1 - c^2 R - c I - addon - gatecost)/2")
print(f"    perfect enclosure   : {base/2:+.8f}")
for D in (1, 4, 16):
    for name in ("allmid", "persec"):
        print(f"    {name:>7} D = {D:>2}      : "
              f"{(base - tot[name][D])/2:+.8f}")
lr = L0_val(C - F(1, 64)) * F(1, 64)
print(f"  L0*r at r = 1/64    : {float(lr):.8f}  (x1.25 safety = "
      f"{1.25*float(lr):.8f})")
