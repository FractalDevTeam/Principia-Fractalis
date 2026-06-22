#!/usr/bin/env python3
"""
spec_ratio_4p27_search.py

Goal
----
Search algebraic combinations of the Principia Fractalis substrate
basis constants for clean closed-form candidates that match the
empirical IBM-dataset ratio

      r_emp = mean(spec_peak1 / spec_peak5)  ~  4.272

across the 141 measurement rows.

This script
1. Loads the CSV at
   /home/xluxx/Principia-Fractalis/Papers/Data/
       principia_fractalis_143_problems_IBM_dataset.csv
   parses the `spectrum` column (5 floats per row), computes the
   per-row ratio peak1/peak5, and reports mean/std/median/IQR/min/max.
2. Builds the substrate atom set:
     {1, 2, 3, pi, phi, sqrt(2), e, pi/10, c2=0.95}
   plus the 9 alpha-skeleton values and the Galois-pair offdiagonal
   d = (4*phi - 5)/8 and the H3 Coxeter number h(H3) = 10.
3. Enumerates 1-, 2-, and 3-term arithmetic combinations
   (+, -, *, /) of these atoms (with depth-controlled growth)
   and ranks by absolute distance to r_emp = 4.272.
4. Reports top-5 by closeness AND a separate top-5 by
   complexity-penalized score (Occam's razor).
5. Also probes specific structured candidates: zeta(2)*x, e*x,
   sqrt(n)*x, and rational multiples of pi.

This is intentionally CONSERVATIVE in search depth so that the
candidate count stays small and any "match" near 0.001 is not
washed out by combinatorial noise.

Author: drafted for Pabs Cohen / Principia Fractalis vetting
"""

from __future__ import annotations

import itertools as it
import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np
import pandas as pd

mp.mp.dps = 50  # 50 decimal digits

# ------------------------------------------------------------
# 1. Empirical target from the CSV
# ------------------------------------------------------------
CSV = ("/home/xluxx/Principia-Fractalis/Papers/Data/"
       "principia_fractalis_143_problems_IBM_dataset.csv")


def load_ratios(path: str = CSV) -> np.ndarray:
    """Parse `spectrum` column and return per-row peak1/peak5 ratios."""
    df = pd.read_csv(path)
    ratios = []
    bad = 0
    for s in df["spectrum"]:
        try:
            vals = [float(x) for x in s.strip("[]").split(",")]
            if len(vals) >= 5 and vals[4] != 0:
                ratios.append(vals[0] / vals[4])
            else:
                bad += 1
        except Exception:
            bad += 1
    print(f"  parsed {len(ratios)} rows, skipped {bad}")
    return np.array(ratios)


def summarize(arr: np.ndarray) -> dict:
    q1, med, q3 = np.percentile(arr, [25, 50, 75])
    return {
        "n": int(arr.size),
        "mean": float(np.mean(arr)),
        "std": float(np.std(arr, ddof=1)),
        "median": float(med),
        "IQR": float(q3 - q1),
        "q1": float(q1),
        "q3": float(q3),
        "min": float(arr.min()),
        "max": float(arr.max()),
    }


# ------------------------------------------------------------
# 2. Substrate atoms
# ------------------------------------------------------------
PI = mp.pi
PHI = (1 + mp.sqrt(5)) / 2
SQRT2 = mp.sqrt(2)
E = mp.e
SQRT5 = mp.sqrt(5)

# Alpha-skeleton (9 values from the substrate)
ALPHA = {
    "alpha_Poincare": mp.mpf(1),
    "alpha_P":        SQRT2,
    "alpha_Hodge":    PHI,
    "alpha_RH":       mp.mpf("1.5"),
    "alpha_NP":       PHI + mp.mpf("0.25"),
    "alpha_YM":       mp.mpf(2),
    "alpha_BSD":      3 * PI / 4,
    "alpha_QG":       mp.sqrt(2 * PI),
    "alpha_NS":       3 * PI / 2,
}

# Substrate primitives + key derived constants
ATOMS = {
    "1":         mp.mpf(1),
    "2":         mp.mpf(2),
    "3":         mp.mpf(3),
    "4":         mp.mpf(4),
    "5":         mp.mpf(5),
    "pi":        PI,
    "phi":       PHI,
    "sqrt2":     SQRT2,
    "sqrt5":     SQRT5,
    "e":         E,
    "pi/10":     PI / 10,
    "c2":        mp.mpf("0.95"),
    "h_H3":      mp.mpf(10),
    "d_Galois":  (4 * PHI - 5) / 8,
}
ATOMS.update(ALPHA)

# ------------------------------------------------------------
# 3. Enumeration
# ------------------------------------------------------------
OPS = [
    ("+",  lambda a, b: a + b,        "{a} + {b}"),
    ("-",  lambda a, b: a - b,        "{a} - {b}"),
    ("*",  lambda a, b: a * b,        "{a} * {b}"),
    ("/",  lambda a, b: a / b if b != 0 else None, "{a} / {b}"),
]


@dataclass
class Candidate:
    expr: str
    value: float
    depth: int  # number of atoms used


def gen_depth1():
    for n, v in ATOMS.items():
        yield Candidate(n, float(v), 1)


def gen_depth2():
    names = list(ATOMS.items())
    for (na, va), (nb, vb) in it.product(names, names):
        for sym, fn, fmt in OPS:
            try:
                val = fn(va, vb)
                if val is None or not mp.isfinite(val):
                    continue
                yield Candidate(fmt.format(a=na, b=nb), float(val), 2)
            except (ZeroDivisionError, ValueError):
                continue


def gen_depth3(target: float, tol: float = 0.5):
    """Three-atom expressions (a op1 b) op2 c, pruned by closeness."""
    names = list(ATOMS.items())
    # Pre-build depth-2 partials within tol of target/atom-range
    for (na, va), (nb, vb) in it.product(names, names):
        for s1, f1, fm1 in OPS:
            try:
                v_ab = f1(va, vb)
                if v_ab is None or not mp.isfinite(v_ab):
                    continue
            except Exception:
                continue
            for (nc, vc) in names:
                for s2, f2, fm2 in OPS:
                    try:
                        v = f2(v_ab, vc)
                        if v is None or not mp.isfinite(v):
                            continue
                        fv = float(v)
                        if abs(fv - target) <= tol:
                            expr = "(" + fm1.format(a=na, b=nb) + ") " + s2 + " " + nc
                            yield Candidate(expr, fv, 3)
                    except Exception:
                        continue


# ------------------------------------------------------------
# 4. Ranking
# ------------------------------------------------------------
def rank(cands, target: float, sigma: float, top: int = 5,
         complexity_weight: float = 0.0):
    out = []
    for c in cands:
        err = abs(c.value - target)
        sig_err = err / sigma
        score = sig_err + complexity_weight * (c.depth - 1)
        out.append((score, sig_err, err, c))
    out.sort(key=lambda x: x[0])
    return out[:top]


def fmt_row(score, sig_err, err, cand):
    return (f"  err={err:.5f} ({sig_err:.2f}sigma)  depth={cand.depth}  "
            f"value={cand.value:.6f}  expr={cand.expr}")


# ------------------------------------------------------------
# 5. Structured probes
# ------------------------------------------------------------
def structured_probes(target: float):
    """Check obvious 'X * something simple' decompositions."""
    print("\n--- Structured probes ---")
    probes = {
        "zeta(2)":     float(mp.zeta(2)),
        "e":           float(E),
        "pi":          float(PI),
        "phi":         float(PHI),
        "sqrt(2)":     float(SQRT2),
        "sqrt(3)":     float(mp.sqrt(3)),
        "log(2)":      float(mp.log(2)),
        "Catalan":     float(mp.catalan),
        "gamma":       float(mp.euler),
    }
    for name, x in probes.items():
        q = target / x
        # nearby small rationals
        nearest = None
        best = 1e9
        for num in range(1, 30):
            for den in range(1, 30):
                d = abs(q - num / den)
                if d < best:
                    best = d
                    nearest = (num, den)
        print(f"  {target} / {name} = {q:.6f}, "
              f"nearest small ratio = {nearest[0]}/{nearest[1]} "
              f"= {nearest[0]/nearest[1]:.6f} (off by {best:.5f})")


# ------------------------------------------------------------
# Main
# ------------------------------------------------------------
def main():
    print("=" * 70)
    print("Step 1: empirical ratio statistics from CSV")
    print("=" * 70)
    ratios = load_ratios()
    stats = summarize(ratios)
    for k, v in stats.items():
        print(f"  {k:>8s} : {v}")
    target = stats["mean"]
    sigma = stats["std"]

    print("\n" + "=" * 70)
    print(f"Step 2: searching for target = {target:.4f} (sigma = {sigma:.4f})")
    print("=" * 70)

    # depth 1
    d1 = list(gen_depth1())
    print(f"\nDepth-1 candidates: {len(d1)}")
    for s, se, e_, c in rank(d1, target, sigma):
        print(fmt_row(s, se, e_, c))

    # depth 2
    d2 = list(gen_depth2())
    print(f"\nDepth-2 candidates: {len(d2)}  (top by closeness)")
    for s, se, e_, c in rank(d2, target, sigma):
        print(fmt_row(s, se, e_, c))

    # depth 3 (pruned)
    d3 = list(gen_depth3(target, tol=0.5))
    print(f"\nDepth-3 candidates within +/-0.5: {len(d3)}")
    print("  Top by raw closeness:")
    for s, se, e_, c in rank(d3, target, sigma, top=10):
        print(fmt_row(s, se, e_, c))

    # combined Occam-weighted ranking across all depths
    print("\nOccam-weighted top across all depths (penalty=0.5/depth):")
    all_c = d1 + d2 + d3
    for s, se, e_, c in rank(all_c, target, sigma, top=10,
                              complexity_weight=0.5):
        print(fmt_row(s, se, e_, c))

    # structured probes
    structured_probes(target)

    # specific named conjectures the paper may want to land on
    print("\n--- Named candidates of interest ---")
    named = {
        "pi + alpha_Poincare":       PI + 1,
        "pi + 9/(2*pi*phi)":         PI + 9 / (2 * PI * PHI),
        "alpha_NS - phi/3":          3 * PI / 2 - PHI / 3,
        "alpha_NS - pi/10 - 1/3":    3 * PI / 2 - PI / 10 - mp.mpf(1)/3,
        "4 + (phi - 1)/2 - small":   4 + (PHI - 1) / 2,
        "pi * sqrt(2) - 1/(...)":    PI * SQRT2,
        "4 + 2/(pi*phi)":            4 + 2 / (PI * PHI),
        "alpha_NS - alpha_Hodge/(3.6)":  3*PI/2 - PHI/mp.mpf("3.6"),
        "alpha_QG * alpha_P/(sqrt(2)) hack": mp.sqrt(2*PI) * 1.7,
        "pi*phi/(phi - small)":      PI * PHI / mp.mpf("1.189"),
        "phi^3 + phi":               PHI**3 + PHI,
        "phi^3 + 1/phi":             PHI**3 + 1/PHI,
        "phi + sqrt(2) + 1.24":      PHI + SQRT2 + mp.mpf("1.24"),
        "alpha_RH + pi - 1/(...)":   mp.mpf("1.5") + PI - mp.mpf("0.37"),
        "h_H3/sqrt(2*pi*phi)":       10 / mp.sqrt(2*PI*PHI),
    }
    for name, v in named.items():
        fv = float(v)
        err = abs(fv - target)
        print(f"  {name:42s} = {fv:.6f}  err={err:.5f} ({err/sigma:.2f}sigma)")


if __name__ == "__main__":
    main()
