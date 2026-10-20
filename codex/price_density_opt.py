#!/usr/bin/env python3
"""
STEP 1, optimal schedule: minimum-cost density ladder from the landed frontier
109/16 = 6.8125 to c = 13.

price_density.py priced a GREEDY schedule (min cost per unit advance). This solves the
real problem by dynamic programming over the frontier, so the reported total is
the true minimum for this machinery, not a heuristic's.

It also separates the two cost drivers, which the greedy conflates:

  * GEOMETRY-limited: the box radius obeys L0(c-r)*r < Mc_lb(c) <= Re xi(c),
    and Re xi -> 0 at 13.98838, so near the top r <= Re xi(c)/L0(c) ~ 0.026 no
    matter how good the enclosure is. That sets a FLOOR on the box count that
    no amount of panel density can lower. Computed here as the D -> infinity
    schedule.
  * DENSITY-limited: the extra boxes and the per-box module count needed
    because the enclosure at finite D is worse than perfect.

Reporting both answers Rio's question properly: how much of the march cost is
buying enclosure, and how much is just the geometry of a decaying Re xi.
"""
import heapq
from fractions import Fraction as F

import mpmath as mp

from price_density import (ADDON, DLAD, L0_val, M_of, SEGMENTS, Terr, mc_lb,
                    true_nodes)

mp.mp.dps = 30

SAFETY = mp.mpf("1.25")
MIN_PER_MODULE = 7.5
RLAD = [F(1, 16), F(1, 32), F(1, 64), F(1, 128), F(1, 256)]
GRID = 512                      # frontier grid: multiples of 1/512
START = F(109, 16)
TARGET = F(13)


def mc_lb_inf(c):
    """Mc_lb at perfect enclosure (D -> infinity): Terr = 0."""
    tR, tI = true_nodes(c)
    ad = mp.mpf(ADDON.numerator) / ADDON.denominator
    cc = mp.mpf(F(c).numerator) / F(c).denominator
    return (1 - (cc ** 2 * (tR + ad) + cc * (tI + ad))) / 2


_ok = {}


def min_D(c, r, dlad):
    """Least density in dlad with L0(c-r)*r * SAFETY < Mc_lb(c, D); None if none."""
    key = (c, r, len(dlad))
    if key in _ok:
        return _ok[key]
    lr = L0_val(c - r) * r
    need = SAFETY * mp.mpf(lr.numerator) / lr.denominator
    res = None
    for D in dlad:
        if mc_lb(c, D) > need:
            res = D
            break
    _ok[key] = res
    return res


def solve(dlad, cost_of, label):
    """Dijkstra over frontier positions (units of 1/GRID above START)."""
    N = int((TARGET - START) * GRID)
    INF = float("inf")
    dist = [INF] * (N + 1)
    prev = [None] * (N + 1)
    dist[0] = 0.0
    pq = [(0.0, 0)]
    done = [False] * (N + 1)
    while pq:
        d, i = heapq.heappop(pq)
        if done[i]:
            continue
        done[i] = True
        if i >= N:
            break
        f = START + F(i, GRID)
        for r in RLAD:
            c = f + r
            if r >= c:
                continue
            D = min_D(c, r, dlad)
            if D is None:
                continue
            j = min(N, i + int(2 * r * GRID))
            nd = d + cost_of(D)
            if nd < dist[j]:
                dist[j] = nd
                prev[j] = (i, c, r, D)
                heapq.heappush(pq, (nd, j))
    if dist[N] == INF:
        print(f"  {label}: UNREACHABLE")
        return None
    path = []
    j = N
    while j != 0:
        i, c, r, D = prev[j]
        path.append((c, r, D))
        j = i
    path.reverse()
    return dist[N], path


print("=" * 98)
print("OPTIMAL DENSITY LADDER   109/16 -> 13   (all-midpoint; 6D modules of 8 "
      "panels, 7m30s each)")
print("=" * 98)

tot, path = solve(DLAD, lambda D: 6 * D * MIN_PER_MODULE / 60.0, "real")
print(f"{'#':>4} {'centre c':>12} {'r':>8} {'D':>4} {'Mc_lb':>12} {'L0*r':>11}"
      f" {'ratio':>7} {'mods':>5} {'h/box':>6}")
mods = 0
for i, (c, r, D) in enumerate(path, 1):
    m = mc_lb(c, D)
    lr = L0_val(c - r) * r
    mods += 6 * D
    if i <= 6 or i > len(path) - 8:
        print(f"{i:>4} {str(c):>12} {str(r):>8} {D:>4} {float(m):>12.8f}"
              f" {float(lr):>11.8f} {float(m)/float(lr):>6.1f}x {6*D:>5}"
              f" {6*D*MIN_PER_MODULE/60:>6.2f}")
    elif i == 7:
        print(f"{'':>4} {'...':>12}")
print("-" * 98)
print(f"  OPTIMAL: {len(path)} boxes, {mods} panel modules, {tot:.1f} h serial"
      f"  ({tot/24:.1f} days continuous)")
print()

grp = {}
for c, r, D in path:
    grp.setdefault(D, []).append((float(c), str(r)))
print("  THE LADDER  (centre -> density -> build time):")
for D in sorted(grp):
    cs = [x[0] for x in grp[D]]
    rs = sorted(set(x[1] for x in grp[D]))
    print(f"    c in [{min(cs):>7.4f}, {max(cs):>7.4f}]  D = {D:>2}  "
          f"({6*D:>3} modules, {6*D*MIN_PER_MODULE/60:>5.2f} h/box)  "
          f"{len(cs):>2} boxes, r = {','.join(rs)}  "
          f"=> {len(cs)*6*D*MIN_PER_MODULE/60:>6.1f} h")
print()

# --- the geometry floor: what a PERFECT enclosure would still cost ---------
print("  GEOMETRY FLOOR (D -> infinity, i.e. a perfect panel enclosure):")
mp_inf = {}


def mc_lb_cached_inf(c, D):
    if c not in mp_inf:
        mp_inf[c] = mc_lb_inf(c)
    return mp_inf[c]


import price_density
_real_mc = price_density.mc_lb
price_density.mc_lb = mc_lb_cached_inf
globals()["mc_lb"] = mc_lb_cached_inf
_ok.clear()
tot_inf, path_inf = solve([1], lambda D: 1.0, "floor")
print(f"    {len(path_inf)} boxes minimum -- no enclosure quality can do better.")
rr = {}
for c, r, D in path_inf:
    rr.setdefault(str(r), 0)
    rr[str(r)] += 1
print(f"    radii used: {rr}")
print()
price_density.mc_lb = _real_mc
globals()["mc_lb"] = _real_mc

print(f"  SPLIT: {len(path)} boxes actual vs {len(path_inf)} geometry floor")
print(f"    -> {len(path)-len(path_inf)} extra boxes are density-limited; the "
      f"other {len(path_inf)} are forced by Re xi decaying to 0 at 13.98838.")
print(f"  vs Rio's ~6 h x boxes = {len(path)*6} h : optimal ladder = {tot:.0f} h"
      f"  ({tot/(len(path)*6):.2f}x)")
