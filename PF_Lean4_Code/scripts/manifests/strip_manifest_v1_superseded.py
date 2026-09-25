# -*- coding: utf-8 -*-
"""FROZEN EXACT STRIP MANIFEST for sigma in [9/16, 1], all three margins.

Uses the CERTIFIABLE MHI (2 * sum B_n from the verified generator's
compute_T_bounds, post slack fix 1.10 -> 1.0005) -- i.e. exactly what Lean can
prove, not a tight ceiling on the true M.

Margins reported per strip:
  RE      : -1/10000 - max over the certified rectangle of Re xi
  IM_LO   : IM_LO_certified - (-1/10000)      [box-0 convention check only]
  IM_HI   : 1/10000 - IM_HI_certified         [box-0 convention check only]

NOTE on load-bearing status.  The r331a consumer's h_arith obligation is
  forall q2 in [A_im, B_im], ... (1 + p1 p2 - q1 q2)/2 <= M
and since q1 >= 0 the maximum over q2 sits at q2 = A_im = IM_LO.  B_im = IM_HI
therefore only widens a hypothesis range; it never tightens the conclusion.
IM_HI is required for the enclosure to EXIST but is NOT margin-critical.  The
IM_LO/IM_HI columns below are reported against the box-0 +-1/10000 convention
purely for continuity; boxes >= 1 declare the enclosure at their own certified
values, so IM_HI > 1e-4 is harmless there.
"""
import sys
from fractions import Fraction as F
import mpmath as mp

sys.path.insert(0, "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code/scripts")
import emit_box_segment as G
from opt40tight import SEGMENTS

mp.mp.dps = 40
PI = mp.pi
ENV = F(1, 5000000)
TARGET = F(-1, 10000)

NODES = []
for s in sorted(SEGMENTS, key=lambda x: x["idx"]):
    L, U, n = s["L"], s["U"], s["n"]
    d = U - L
    lst = []
    for k in range(n):
        uf = L + F(2 * k + 1, 2 * n) * d
        u = mp.mpf(uf.numerator) / uf.denominator
        lu = mp.log(u)
        lst.append((u, mp.cos(mp.mpf(15) / 2 * lu), mp.sin(mp.mpf(15) / 2 * lu),
                    mp.e ** (-PI * u) + mp.e ** (-4 * PI * u) + mp.e ** (-9 * PI * u)))
    NODES.append((L, U, n, d, d / n, lst))


def certify(slo, shi):
    """Return (RE_LO, IM_LO, IM_HI, E_QUAD) with the CERTIFIABLE MHI."""
    G._set_box(0, slo, shi)          # sets p1/p2/M constants for this box
    e1l, e2l = float(slo / 2 - 1), float((1 - slo) / 2 - 1)
    e1h, e2h = float(shi / 2 - 1), float((1 - shi) / 2 - 1)
    rl = il = ih = F(0)
    eq = F(0)
    for L, U, n, d, h, lst in NODES:
        _T, B = G.compute_T_bounds(L)
        MHI = sum(B) * 2
        ES = MHI * d ** 3 / (24 * n * n)
        eq += ES
        a = c_ = e_ = F(0)
        for u, co, si, om in lst:
            Alo = mp.power(u, e1l) + mp.power(u, e2l)
            Ahi = mp.power(u, e1h) + mp.power(u, e2h)
            Dlo = mp.power(u, e1l) - mp.power(u, e2l)
            Dhi = mp.power(u, e1h) - mp.power(u, e2h)
            a += G.outward_lo((Alo if co >= 0 else Ahi) * co * om, 10)
            if si >= 0:
                c_ += G.outward_lo(Dlo * si * om, 10)
                e_ += G.outward_hi(Dhi * si * om, 10)
            else:
                c_ += G.outward_lo(Dhi * si * om, 10)
                e_ += G.outward_hi(Dlo * si * om, 10)
        rl += a * h - ES
        il += c_ * h - ES
        ih += e_ * h + ES
    return rl - ENV, il - ENV, ih + ENV, eq


def ideal_margin(slo, shi, n=7):
    xs = [slo + (shi - slo) * F(i, n) for i in range(n + 1)]
    reMin = min(mp.re(_lam(x)) for x in xs)
    imMin = min(mp.im(_lam(x)) for x in xs)
    Ahi = mp.mpf(float(shi)) * (mp.mpf(float(shi)) - 1) - 225
    B = (15 * (2 * mp.mpf(float(shi)) - 1) if imMin < 0
         else 15 * (2 * mp.mpf(float(slo)) - 1))
    return mp.mpf(-1) / 10000 - (1 + Ahi * reMin - B * imMin) / 2


def _lam(sig):
    s = mp.mpf(sig.numerator) / sig.denominator + 15j
    return mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s) + 1 / s + 1 / (1 - s)


def margins(slo, shi):
    RE_LO, IM_LO, IM_HI, eq = certify(slo, shi)
    Ahi = shi * (shi - 1) - 225
    B = 15 * (2 * shi - 1) if IM_LO < 0 else 15 * (2 * slo - 1)
    re_m = TARGET - (1 + Ahi * RE_LO - B * IM_LO) / 2
    return re_m, IM_LO - F(-1, 10000), F(1, 10000) - IM_HI, RE_LO, IM_LO, IM_HI, eq


WIDTHS = [F(1, 32), F(1, 64), F(1, 128)]   # directive: coarsest-passing starts at 1/32
FLOOR = F(1, 128)

print("=" * 118)
print("FROZEN STRIP MANIFEST — sigma in [9/16, 1]  (certifiable MHI, 10-digit rounding)")
print("=" * 118)
print("%-4s %-17s %-8s %-14s %-14s %-14s %-14s %s"
      % ("id", "sigma range", "width", "RE margin", "RE_LO", "IM_LO", "IM_HI", "RE ok"))
print("-" * 118)

cur = F(9, 16)
strips = []
guard = 0
while cur < 1 and guard < 300:
    guard += 1
    placed = False
    for w in WIDTHS:
        shi = cur + w
        if shi > 1:
            continue
        rm, imlo_m, imhi_m, RL, IL, IH, eq = margins(cur, shi)
        if rm > 0:
            strips.append(dict(id=len(strips), slo=cur, shi=shi, w=w, re=rm,
                               imlo=imlo_m, imhi=imhi_m, RL=RL, IL=IL, IH=IH, eq=eq))
            print("%-4d [%-7s,%-7s] %-8s %+.6e  %-14.6e %-14.6e %-14.6e %s"
                  % (len(strips) - 1, cur, shi, w, float(rm), float(RL),
                     float(IL), float(IH), "YES"))
            cur = shi
            placed = True
            break
    if not placed:
        shi = min(cur + FLOOR, F(1))
        rm, imlo_m, imhi_m, RL, IL, IH, eq = margins(cur, shi)
        strips.append(dict(id=len(strips), slo=cur, shi=shi, w=FLOOR, re=rm,
                           imlo=imlo_m, imhi=imhi_m, RL=RL, IL=IL, IH=IH, eq=eq))
        print("%-4d [%-7s,%-7s] %-8s %+.6e  %-14.6e %-14.6e %-14.6e ** NO (floor) **"
              % (len(strips) - 1, cur, shi, FLOOR, float(rm), float(RL),
                 float(IL), float(IH)))
        cur = shi

print()
print("=" * 118)
print("GATE B — mechanical assertions")
print("=" * 118)
ok = True


def chk(c, m):
    global ok
    print("  %-4s %s" % ("PASS" if c else "FAIL", m))
    ok &= c


chk(all(isinstance(s["slo"], F) and isinstance(s["shi"], F) for s in strips),
    "all endpoints exact Fractions")
chk(all(s["slo"] < s["shi"] for s in strips), "each strip nonempty")
chk(all(strips[i]["shi"] == strips[i + 1]["slo"] for i in range(len(strips) - 1)),
    "adjacent endpoints equal (no gap, disjoint interiors)")
chk(strips[0]["slo"] == F(9, 16), "starts at exactly 9/16")
chk(strips[-1]["shi"] == F(1), "ends at exactly 1")
chk(sum(s["shi"] - s["slo"] for s in strips) == F(7, 16),
    "total measure exactly 7/16")
chk(all(s["re"] > 0 for s in strips), "every strip RE-margin positive")
print()
print("  union with Box 0 [1/2, 9/16] = [1/2, 1] exactly:",
      "PASS" if strips[0]["slo"] == F(9, 16) else "FAIL")
print()
print("strips: %d   weakest RE margin: %+.6e at strip %d"
      % (len(strips), float(min(s["re"] for s in strips)),
         min(strips, key=lambda s: s["re"])["id"]))
print("estimated build: %.1f h at 8.7 h/strip (%.1f days)"
      % (8.7 * len(strips), 8.7 * len(strips) / 24))
print()
print("GATE B:", "ALL ASSERTIONS PASS" if ok else "FAILED")
