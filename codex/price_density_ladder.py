#!/usr/bin/env python3
"""
STEP 1, final: the per-segment-optimal ladder, and where each density rung
begins.

price5 established that the SCHEME is a ladder too, not just the density: as D
rises the midpoint/range crossover walks outward through the segments. At
c = 13, measured:

    D = 1  : segs 1-2 midpoint, 3-6 range   (= the shipped hybrid, exactly)
    D = 4  : segs 1-4 midpoint, 5-6 range
    D = 16 : segs 1-4 midpoint, 5-6 range

and per-segment beats all-midpoint by 1.8-2.6x in gate cost at every density.
That matters at the margin: at c = 13, r = 1/64 needs Mc_lb > 0.00188 and
all-midpoint D = 16 gives only 0.00183 (FAIL) while per-segment gives 0.00209
(PASS). So the scheme choice is not cosmetic.

This computes the per-segment-optimal Mc_lb EXACTLY (shipped interval
arithmetic, both schemes per segment, best taken) on the centres that matter,
and reports where each rung of the density ladder starts.
"""
import io
import os
import sys
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

_fc = {}


def fcache(a, b):
    """(Fp+om, Fp-om) over [a,b] -- c-independent, so cached across centres."""
    k = (a, b)
    if k not in _fc:
        u = I(a, b)
        E = epi(I(a * F(1, 2), b * F(1, 2)), series_terms=ST)
        om = oi(epi(u, series_terms=ST), series_terms=ST)
        Fp = (E * om).rounded()
        _fc[k] = ((Fp + om).rounded(), (Fp - om).rounded())
    return _fc[k]


def seg_ub(c, seg, D, scheme):
    """(R_ub, I_ub) for one segment at density D under 'rng' or 'mid'."""
    ch = F(c) / 2
    h = F(1, 32 * D)
    lo, hi = SEGMENTS[seg]
    R = Iv = F(0)
    if scheme == "mid":
        err = F(M_of(c, hi)) * h ** 3 / 24
    for k in range(8 * D):
        a = lo + k * h
        if scheme == "rng":
            P, Q = fcache(a, a + h)
            cu = I(ch * a, ch * (a + h))
            R += h * (P * ci(cu, series_terms=ST)).rounded().hi
            Iv += h * (Q * si(cu, series_terms=ST)).rounded().hi
        else:
            m = a + h / 2
            P, Q = fcache(m, m)
            cu = I(ch * m, ch * m)
            R += h * (P * ci(cu, series_terms=ST)).rounded().hi + err / 2
            Iv += h * (Q * si(cu, series_terms=ST)).rounded().hi + err / 2
    return R, Iv


_sc = {}


def best_enclosure(c, D):
    """Per-segment-optimal (R_ub, I_ub, scheme) at density D."""
    k = (c, D)
    if k in _sc:
        return _sc[k]
    cc = float(c)
    R = Iv = F(0)
    sch = []
    for seg in range(1, 7):
        cand = {}
        for s in ("rng", "mid"):
            cand[s] = seg_ub(c, seg, D, s)
        pick = min(cand, key=lambda s: cc * cc * float(cand[s][0])
                   + cc * float(cand[s][1]))
        R += cand[pick][0]
        Iv += cand[pick][1]
        sch.append(pick[0])
    _sc[k] = (R, Iv, "".join(sch))
    return _sc[k]


def mc_lb_best(c, D):
    R, Iv, sch = best_enclosure(c, D)
    cc = mp.mpf(F(c).numerator) / F(c).denominator
    ad = mp.mpf(ADDON.numerator) / ADDON.denominator
    gate = cc ** 2 * (mp.mpf(R.numerator) / R.denominator + ad) \
        + cc * (mp.mpf(Iv.numerator) / Iv.denominator + ad)
    return (1 - gate) / 2, sch


DLAD = [1, 2, 4, 8, 16, 32]
RLAD = [F(1, 16), F(1, 32), F(1, 64)]
SAFETY = mp.mpf("1.25")
MIN = 7.5

print("=" * 100)
print("PER-SEGMENT-OPTIMAL LADDER: where each density rung begins")
print("=" * 100)
print(f"{'centre c':>10} {'D':>3} {'scheme':>8} {'Mc_lb':>12} | "
      f"{'r=1/16 need':>12} {'1/32':>10} {'1/64':>10} {'best r':>8}")

f = F(109, 16)
boxes = []
while f < 13 and len(boxes) < 200:
    chosen = None
    for r in RLAD:
        c = f + r
        lr = L0_val(c - r) * r
        need = SAFETY * mp.mpf(lr.numerator) / lr.denominator
        for D in DLAD:
            m, sch = mc_lb_best(c, D)
            if m > need:
                cost = 6 * D * MIN
                key = cost / (2.0 * float(r))
                if chosen is None or key < chosen[0]:
                    chosen = (key, c, r, D, m, lr, sch, cost)
                break
    if chosen is None:
        print(f"  STOP at frontier {float(f):.6f}: no (r, D) works")
        break
    _, c, r, D, m, lr, sch, cost = chosen
    boxes.append((c, r, D, m, lr, sch, cost))
    f = c + r

prev = None
tot_h = 0.0
tot_mod = 0
for i, (c, r, D, m, lr, sch, cost) in enumerate(boxes, 1):
    tot_h += cost / 60.0
    tot_mod += 6 * D
    if (D, sch) != prev:
        print(f"{float(c):>10.4f} {D:>3} {sch:>8} {float(m):>12.8f} | "
              f"<- rung starts here, r = {str(r)}, {6*D} modules, "
              f"{cost/60:.2f} h/box")
        prev = (D, sch)
print("-" * 100)
print(f"  {len(boxes)} boxes, frontier {float(f):.6f} "
      f"{'REACHED 13' if f >= 13 else 'SHORT'}")
print(f"  {tot_mod} panel modules, {tot_h:.1f} h serial ({tot_h/24:.1f} days)")
print()
grp = {}
for c, r, D, m, lr, sch, cost in boxes:
    grp.setdefault((D, sch), []).append((float(c), str(r)))
print("  THE LADDER:")
hdr = f"    {'c range':>20} {'D':>3} {'scheme':>8} {'mods':>5} {'h/box':>6} "\
      f"{'boxes':>6} {'r':>14} {'subtotal':>9}"
print(hdr)
for (D, sch) in sorted(grp, key=lambda k: min(x[0] for x in grp[k])):
    cs = [x[0] for x in grp[(D, sch)]]
    rs = sorted(set(x[1] for x in grp[(D, sch)]), key=lambda s: -eval(s))
    n = len(cs)
    print(f"    [{min(cs):>7.4f},{max(cs):>7.4f}] {D:>3} {sch:>8} {6*D:>5}"
          f" {6*D*MIN/60:>6.2f} {n:>6} {','.join(rs):>14}"
          f" {n*6*D*MIN/60:>8.1f}h")
print()
print(f"  TOTAL {tot_h:.0f} h serial = {tot_h/24:.1f} days continuous, "
      f"{tot_mod} new panel modules")
print(f"  vs Rio's ~6 h x boxes = {len(boxes)*6} h  -> ladder is "
      f"{tot_h/(len(boxes)*6):.2f}x of it")
