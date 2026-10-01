#!/usr/bin/env python3
"""
boundary_search.py — joint boundary + panel-count search for the r331b Box-0 partition.

READ-ONLY. Imports `opt40tight` for geometry, writes only /tmp. Deletes nothing.

CONTEXT

`partition_search.py` optimised the panel allocation n_j with the 40 segment
boundaries held FIXED, and found the hand-tuned OPT-40-TIGHT table is already
within 2.1% of optimal (530 -> 519 panels). So allocation is not where the build
cost hides.

The remaining degree of freedom is the boundaries themselves. Current widths are
dyadic blocks — 1/32 on [1,1.5], 1/16 on [1.5,2], 1/8 on [2,3], 1/4 on [3,5] —
while MHI falls from 13.3 to 1.01e-4 across the range, five orders of magnitude.
Dyadic blocks cannot track that, so there may be real slack.

THEORY

With E = sum_j MHI_j h_j^3 / (24 n_j^2) and n_j proportional to
(MHI_j h_j^3)^(1/3) = MHI_j^(1/3) h_j, substituting back gives

    E  proportional to  ( sum_j MHI_j^(1/3) h_j )^3 / N^2 ,     N = sum_j n_j

so for a FIXED number of segments the quantity to minimise over boundaries is

    W  =  sum_j  MHI_j^(1/3) * h_j            ("cube-root-weighted total variation")

and then N scales as W^(3/2) / sqrt(E). Minimising W over boundary placement with
K segments is the classical equidistribution problem: place cuts so that each
segment carries equal mass of the measure MHI(x)^(1/3) dx. Using MHI_j evaluated
at the segment LEFT endpoint (as the generator does — MHI is a decreasing upper
bound, so left-endpoint evaluation is the conservative choice), W is a Riemann
sum for the integral of M(x)^(1/3).

IMPORTANT LIMITATION, stated up front

The true M(x) is produced by the certifier, and I only have it sampled at the 40
segment left endpoints. To move boundaries I must interpolate. M decays smoothly
and nearly geometrically, so log-linear interpolation is reasonable — but any
allocation this script proposes is an ESTIMATE of the payoff, not a certified
design. If the estimated saving is small, that settles the question and nothing
further is needed. If it is large, it justifies running the real certifier at the
proposed cut points.

Nothing here touches Lean, the generator, or any existing file.
"""
from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
for cand in (HERE, "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code/scripts",
             os.path.expanduser("~/pf-worker/Principia-Fractalis-ACTIVE/PF_Lean4_Code/scripts")):
    if os.path.isfile(os.path.join(cand, "opt40tight.py")):
        sys.path.insert(0, cand)
        break
else:
    print("FATAL: opt40tight.py not found"); raise SystemExit(2)

import opt40tight as G  # read-only


def mhi_for(idx, m_ref):
    ov = getattr(G, "MHI_OVERRIDE", {})
    return ov[idx] if idx in ov else G.m_ceiling(m_ref)


rows = []
for (idx, L, U, n, m_ref) in G.RAW:
    rows.append(dict(idx=idx, L=float(L), U=float(U), n=n,
                     mhi=float(mhi_for(idx, m_ref))))

A = rows[0]["L"]
B = rows[-1]["U"]

# --- log-linear model of M(x) from the 40 left-endpoint samples --------------
xs = [r["L"] for r in rows]
ys = [math.log(r["mhi"]) for r in rows]
xs.append(B)
ys.append(ys[-1] + (ys[-1] - ys[-2]))     # linear extrapolation of log M


def logM(x):
    if x <= xs[0]:
        return ys[0]
    if x >= xs[-1]:
        return ys[-1]
    lo = 0
    hi = len(xs) - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if xs[mid] <= x:
            lo = mid
        else:
            hi = mid
    t = (x - xs[lo]) / (xs[hi] - xs[lo])
    return ys[lo] + t * (ys[hi] - ys[lo])


def M(x):
    return math.exp(logM(x))


def phi(x):
    """Equidistribution density: M(x)^(1/3)."""
    return M(x) ** (1.0 / 3.0)


# cumulative integral of phi on a fine grid
NG = 200001
grid = [A + (B - A) * i / (NG - 1) for i in range(NG)]
cum = [0.0] * NG
for i in range(1, NG):
    cum[i] = cum[i - 1] + 0.5 * (phi(grid[i]) + phi(grid[i - 1])) * (grid[i] - grid[i - 1])
TOT = cum[-1]


def invcum(target):
    lo, hi = 0, NG - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if cum[mid] <= target:
            lo = mid
        else:
            hi = mid
    return grid[lo]


def W_of_boundaries(bs):
    """sum_j M(L_j)^(1/3) * h_j, left-endpoint evaluation (conservative)."""
    return sum(M(bs[j]) ** (1.0 / 3.0) * (bs[j + 1] - bs[j]) for j in range(len(bs) - 1))


def panels_for(bs, budget):
    """Smallest integer allocation meeting the budget, equidistributed."""
    cs = [M(bs[j]) ** (1.0 / 3.0) for j in range(len(bs) - 1)]
    hs = [bs[j + 1] - bs[j] for j in range(len(bs) - 1)]
    cc = [M(bs[j]) * hs[j] ** 3 / 24.0 for j in range(len(bs) - 1)]
    shape = [c ** (1.0 / 3.0) for c in cc]
    s2 = sum(c / (sh ** 2) for c, sh in zip(cc, shape)) / budget
    s = s2 ** 0.5
    alloc = [max(1, math.ceil(s * sh)) for sh in shape]
    def err(a):
        return sum(cc[i] / (a[i] ** 2) for i in range(len(a)))
    improved = True
    while improved:
        improved = False
        for i in sorted(range(len(alloc)), key=lambda i: -alloc[i]):
            if alloc[i] <= 1:
                continue
            alloc[i] -= 1
            if err(alloc) <= budget:
                improved = True
            else:
                alloc[i] += 1
    return alloc, err(alloc)


# --- current baseline --------------------------------------------------------
cur_alloc = [r["n"] for r in rows]
cur_panels = sum(cur_alloc)
cur_err = sum(float(mhi_for(r["idx"], 0)) if False else
              r["mhi"] * (r["U"] - r["L"]) ** 3 / (24.0 * r["n"] ** 2) for r in rows)
cur_bs = [r["L"] for r in rows] + [B]
cur_W = W_of_boundaries(cur_bs)

print("=" * 78)
print("BASELINE  (OPT-40-TIGHT, dyadic boundaries)")
print("=" * 78)
print(f"  segments {len(rows)}   panels {cur_panels}   E {cur_err:.6e}   W {cur_W:.6f}")

budget = cur_err

print()
print("=" * 78)
print("EQUIDISTRIBUTED BOUNDARIES, same error budget, scanning segment count K")
print("=" * 78)
print("     K    W_opt      panels   vs current")
print("  " + "-" * 50)

best = None
results = []
for K in list(range(8, 81, 2)):
    bs = [invcum(TOT * j / K) for j in range(K)] + [B]
    W = W_of_boundaries(bs)
    alloc, e = panels_for(bs, budget)
    N = sum(alloc)
    results.append(dict(K=K, W=W, panels=N, err=e))
    flag = ""
    if best is None or N < best["panels"]:
        best = dict(K=K, W=W, panels=N, err=e, bs=bs, alloc=alloc)
        flag = "  <-- best so far"
    print(f"  {K:4d}  {W:9.6f}  {N:7d}   {N - cur_panels:+6d}{flag}")

print()
print("=" * 78)
print("BEST FOUND")
print("=" * 78)
print(f"  segments      : {best['K']}")
print(f"  panels        : {best['panels']}   (current {cur_panels}, "
      f"delta {best['panels'] - cur_panels:+d})")
print(f"  E             : {best['err']:.6e}  (budget {budget:.6e})")
saved = cur_panels - best["panels"]
print(f"  panels saved  : {saved}  ({100.0 * saved / cur_panels:.1f}%)")

with open("/tmp/boundary_search_result.json", "w") as f:
    json.dump(dict(baseline=dict(panels=cur_panels, err=cur_err, W=cur_W),
                   scan=results,
                   best=dict(K=best["K"], panels=best["panels"], err=best["err"],
                             boundaries=best["bs"], alloc=best["alloc"]),
                   saved=saved,
                   caveat="M(x) log-interpolated from 40 samples; estimate only, "
                          "not a certified design"),
              f, indent=2)
print()
print("  wrote /tmp/boundary_search_result.json")
print()
print("  CAVEAT: M(x) is log-interpolated from 40 certifier samples. This is an")
print("  estimate of the payoff, not a design. A proposed cut set means nothing")
print("  until emit_M_certificate certifies MHI at the new left endpoints and")
print("  the emitted panels build and gate green.")
