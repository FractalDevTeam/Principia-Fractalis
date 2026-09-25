# -*- coding: utf-8 -*-
"""Corrected strip manifest — drives the EMITTER's own canonical_node_bounds.

Methodology fix: the previous manifest re-implemented the node-bound logic in
the dry-run.  That duplication is exactly what let the Im-zeroing defect hide
(model said D_lo, emitter wrote 0).  This version calls
`emit_box_segment.canonical_node_bounds` directly, so a manifest margin is by
construction what the emitter will produce.

MHI is the CERTIFIABLE 2*sum(B_n) from compute_T_bounds, not a tight ceiling.
"""
import sys, json
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
        lst.append((uf,
                    "nn" if mp.cos(mp.mpf(15) / 2 * lu) >= 0 else "np",
                    "nn" if mp.sin(mp.mpf(15) / 2 * lu) >= 0 else "np"))
    NODES.append((L, U, n, d, d / n, lst))


def certify(slo, shi):
    G._set_box(0, slo, shi)
    rl = rh = il = ih = F(0)
    eq = F(0)
    for L, U, n, d, h, lst in NODES:
        _T, B = G.compute_T_bounds(L)
        MHI = sum(B) * 2
        ES = MHI * d ** 3 / (24 * n * n)
        eq += ES
        a = b = c_ = e_ = F(0)
        for uf, cs, ss in lst:
            rlo, rhi, ilo, ihi = G.canonical_node_bounds(uf, cs, ss)
            a += rlo; b += rhi; c_ += ilo; e_ += ihi
        rl += a * h - ES; rh += b * h + ES
        il += c_ * h - ES; ih += e_ * h + ES
    return rl - ENV, rh + ENV, il - ENV, ih + ENV, eq


def margin(slo, shi):
    RE_LO, RE_HI, IM_LO, IM_HI, eq = certify(slo, shi)
    Ahi = shi * (shi - 1) - 225
    B = 15 * (2 * shi - 1) if IM_LO < 0 else 15 * (2 * slo - 1)
    m = TARGET - (1 + Ahi * RE_LO - B * IM_LO) / 2
    return m, RE_LO, RE_HI, IM_LO, IM_HI, eq, B


WIDTHS = [F(1, 16), F(1, 32), F(1, 64), F(1, 128)]
print("=" * 118)
print("CORRECTED STRIP MANIFEST — emitter-driven (canonical_node_bounds), Im fix applied")
print("=" * 118)
print("%-4s %-17s %-8s %-15s %-14s %-14s %-14s %s"
      % ("id", "sigma range", "width", "RE margin", "RE_LO", "IM_LO", "IM_HI", "B"))
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
        m, RL, RH, IL, IH, eq, B = margin(cur, shi)
        if m > 0:
            strips.append(dict(id=len(strips), slo=str(cur), shi=str(shi), w=str(w),
                               margin=str(m), RE_LO=str(RL), IM_LO=str(IL),
                               IM_HI=str(IH), B=str(B)))
            print("%-4d [%-7s,%-7s] %-8s %+.6e   %-14.6e %-14.6e %-14.6e %s"
                  % (len(strips) - 1, cur, shi, w, float(m), float(RL),
                     float(IL), float(IH), B))
            cur = shi
            placed = True
            break
    if not placed:
        shi = min(cur + F(1, 128), F(1))
        m, RL, RH, IL, IH, eq, B = margin(cur, shi)
        strips.append(dict(id=len(strips), slo=str(cur), shi=str(shi), w="1/128",
                           margin=str(m), RE_LO=str(RL), IM_LO=str(IL),
                           IM_HI=str(IH), B=str(B)))
        print("%-4d [%-7s,%-7s] 1/128    %+.6e   ** FLOOR **" % (len(strips) - 1, cur, shi, float(m)))
        cur = shi

print()
ok = True
def chk(c, m):
    global ok
    print("  %-4s %s" % ("PASS" if c else "FAIL", m)); ok &= c

S = [(F(x["slo"]), F(x["shi"])) for x in strips]
chk(all(a < b for a, b in S), "each strip nonempty")
chk(all(S[i][1] == S[i + 1][0] for i in range(len(S) - 1)), "contiguous, no gap/overlap")
chk(S[0][0] == F(9, 16), "starts at 9/16")
chk(S[-1][1] == F(1), "ends at 1")
chk(sum(b - a for a, b in S) == F(7, 16), "measure exactly 7/16")
chk(all(F(x["margin"]) > 0 for x in strips), "every strip RE-margin positive")
print()
print("strips: %d" % len(strips))
order = sorted(strips, key=lambda x: F(x["margin"]))
print("BUILD ORDER (weakest first):")
for i, x in enumerate(order):
    print("  %2d. strip %-3d [%-7s,%-7s] margin %+.6e"
          % (i + 1, x["id"], x["slo"], x["shi"], float(F(x["margin"]))))
open("/tmp/strip_manifest_v2.json", "w").write(json.dumps(
    dict(strips=strips, order=[x["id"] for x in order]), indent=1))
print()
print("GATE B:", "ALL PASS" if ok else "FAILED")
print("wrote /tmp/strip_manifest_v2.json")
