#!/usr/bin/env python3
"""
Gamma_0(9): independent float64 sweep of ALL 29 targets at N=64.

WHY THIS EXISTS.  Phase 2 of rh_gamma09.py ran all 29 targets at N=64 in mpmath.
The anomaly pass (rh_gamma09_anomaly.py) re-ran only 4 of them, on the float64
path.  This closes that gap: every one of the 29, both factors, both operators,
controls included, in a separate process from either.

WHY float64 IS LEGITIMATE HERE.  The V4 gate in rh_gamma09_results.txt measured
the float64 determinant error at ~1e-6 of the truncation error (worst
scale-normalized 1.9e-10).  So float64 is a valid HIT DETECTOR.

WHAT float64 CANNOT DO.  At a zero the value is below the float64 floor, so the
DEPTH is not measurable this way: for the target at gamma = -13.7919 this path
gives 2.46e-9 where mpmath at the same N gives 2.58e-10.  Both are ~12 orders
below the control scale, so the hit/no-hit verdict is unaffected, but no depth
claim should be read off this table.  Depths come from the mpmath Phase 2 run.

READS codex/rh_gamma09_targets.txt.  Never regenerates the zeros.
"""
import importlib.util as u
import numpy as np
import sys
import time
import mpmath as mp

HERE = "/home/xluxx/Principia-Fractalis/codex/"
spec = u.spec_from_file_location("g9", HERE + "rh_gamma09.py")
g9 = u.module_from_spec(spec)
sys.argv = ["sweep"]
try:
    spec.loader.exec_module(g9)
except SystemExit:
    pass

N = 64
DELTA = mp.mpf("0.30")       # control offset in t
NEAR = mp.mpf("0.15")        # drop a control landing this close to another target

# ---- targets, read not regenerated -----------------------------------------
gammas = []
for line in open(HERE + "rh_gamma09_targets.txt"):
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    gammas.append(mp.mpf(line.split()[0]))
ts = [g / 2 for g in gammas]
print(f"# {len(gammas)} targets read from rh_gamma09_targets.txt", flush=True)

reps = [("chi", g9.Rep(1)), ("trivial", g9.Rep(0))]
cache = {}


def ev(t, rep):
    key = (mp.nstr(t, 25), id(rep))
    if key not in cache:
        cache[key] = g9.dets(mp.mpc(mp.mpf(1) / 4, t), N, rep)
    return cache[key]


def controls(t):
    out = []
    for d in (-DELTA, +DELTA):
        c = t + d
        if all(abs(c - o) > NEAR for o in ts):
            out.append(c)
    return out


t0 = time.time()
summary = {}
for label, rep in reps:
    print(f"\n## operator: Gamma_0(9) {label},  N={N}, float64", flush=True)
    print("| gamma | t | |det(1-PL)| | ctrl gm | ratio(-) | |det(1+PL)| | ctrl gm | ratio(+) |",
          flush=True)
    print("|---|---|---|---|---|---|---|---|", flush=True)
    hits_m = hits_p = 0
    rmin_m = rmax_m = None
    for g, t in zip(gammas, ts):
        dm, dp = ev(t, rep)
        cs = controls(t)
        cm = [abs(ev(c, rep)[0]) for c in cs]
        cp = [abs(ev(c, rep)[1]) for c in cs]
        gm_m = float(np.exp(np.mean(np.log(cm)))) if cm else float("nan")
        gm_p = float(np.exp(np.mean(np.log(cp)))) if cp else float("nan")
        r_m, r_p = abs(dm) / gm_m, abs(dp) / gm_p
        if r_m < 1e-4:
            hits_m += 1
            rmin_m = r_m if rmin_m is None else min(rmin_m, r_m)
            rmax_m = r_m if rmax_m is None else max(rmax_m, r_m)
        if r_p < 1e-4:
            hits_p += 1
        print(f"| {float(g):+.9f} | {float(t):+.9f} | {abs(dm):.4e} | {gm_m:.3e} "
              f"| {r_m:.3e} | {abs(dp):.4e} | {gm_p:.3e} | {r_p:.3e} |", flush=True)
    summary[label] = (hits_m, hits_p, rmin_m, rmax_m)
    print(f"# {label}: det(1-PL) hits {hits_m}/{len(gammas)}, "
          f"det(1+PL) hits {hits_p}/{len(gammas)}", flush=True)

print(f"\n## SUMMARY  (hit = ratio < 1e-4)", flush=True)
print("| operator | det(1-PL) | det(1+PL) | ratio range on hits |", flush=True)
print("|---|---|---|---|", flush=True)
for label, (hm, hp, lo, hi) in summary.items():
    rng = f"{lo:.1e} .. {hi:.1e}" if lo is not None else "--"
    print(f"| Gamma_0(9) {label} | {hm}/{len(gammas)} | {hp}/{len(gammas)} | {rng} |",
          flush=True)
print(f"\n# wall time {time.time()-t0:.0f}s, {len(cache)} distinct evaluations", flush=True)
print("# float64 is a hit detector, not a depth measurement -- see the header.", flush=True)
