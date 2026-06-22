#!/usr/bin/env python3
"""
Second-pass verification + over-fitting honesty check.

Probes the leading candidates from spec_ratio_4p27_search.py and
asks: how many *equally close* candidates does an enumeration of
this size produce? That is the fair denominator for any
'derivation' claim.
"""

import itertools as it
import math
import numpy as np
import pandas as pd
import mpmath as mp

mp.mp.dps = 50

PI    = mp.pi
PHI   = (1 + mp.sqrt(5)) / 2
SQRT2 = mp.sqrt(2)
E     = mp.e

ATOMS = {
    "1": mp.mpf(1), "2": mp.mpf(2), "3": mp.mpf(3), "4": mp.mpf(4), "5": mp.mpf(5),
    "pi": PI, "phi": PHI, "sqrt2": SQRT2, "e": E,
    "pi/10": PI/10, "c2": mp.mpf("0.95"),
    "h_H3": mp.mpf(10), "d_Gal": (4*PHI - 5)/8,
    "alpha_Poin": mp.mpf(1),
    "alpha_P":    SQRT2,
    "alpha_Hod":  PHI,
    "alpha_RH":   mp.mpf("1.5"),
    "alpha_NP":   PHI + mp.mpf("0.25"),
    "alpha_YM":   mp.mpf(2),
    "alpha_BSD":  3*PI/4,
    "alpha_QG":   mp.sqrt(2*PI),
    "alpha_NS":   3*PI/2,
}

CSV = ("/home/xluxx/Principia-Fractalis/Papers/Data/"
       "principia_fractalis_143_problems_IBM_dataset.csv")


def load_target():
    df = pd.read_csv(CSV)
    rs = []
    for s in df["spectrum"]:
        try:
            v = [float(x) for x in s.strip("[]").split(",")]
            if len(v) >= 5 and v[4] != 0:
                rs.append(v[0]/v[4])
        except Exception:
            pass
    a = np.array(rs)
    return float(a.mean()), float(a.std(ddof=1)), a


def enumerate_3(threshold):
    """All a op1 b op2 c within threshold of target."""
    target, _, _ = load_target()
    out = []
    names = list(ATOMS.items())
    for (na, va), (nb, vb), (nc, vc) in it.product(names, names, names):
        for s1 in ("+", "-", "*", "/"):
            try:
                if s1 == "+": v_ab = va + vb
                elif s1 == "-": v_ab = va - vb
                elif s1 == "*": v_ab = va * vb
                else:
                    if vb == 0: continue
                    v_ab = va / vb
                if not mp.isfinite(v_ab): continue
            except Exception: continue
            for s2 in ("+", "-", "*", "/"):
                try:
                    if s2 == "+": v = v_ab + vc
                    elif s2 == "-": v = v_ab - vc
                    elif s2 == "*": v = v_ab * vc
                    else:
                        if vc == 0: continue
                        v = v_ab / vc
                    if not mp.isfinite(v): continue
                    fv = float(v)
                    if abs(fv - target) <= threshold:
                        out.append((fv, f"({na}{s1}{nb}){s2}{nc}"))
                except Exception:
                    continue
    return out


def main():
    mean, std, arr = load_target()
    print(f"Target: mean={mean:.10f}  std={std:.10f}  n={len(arr)}")
    print(f"Median: {float(np.median(arr)):.6f}  IQR: "
          f"{float(np.percentile(arr,75)-np.percentile(arr,25)):.6f}")
    print(f"Range : [{float(arr.min()):.6f}, {float(arr.max()):.6f}]")

    # MEDIAN MATTERS: distribution is heavily right-skewed.
    print("\nNOTE on distribution shape:")
    pct = np.percentile(arr, [5, 25, 50, 75, 95, 99])
    print(f"  percentiles [5,25,50,75,95,99] = {pct}")
    print("  Heavily right-skewed: median 4.251 << mean 4.272.")
    print("  The 'target' for a structural derivation may be"
          " the MEDIAN/MODE of the cluster, not the mean.")

    # ----- leading candidates -----
    print("\n--- Leading candidates (high precision) ---")
    cands = {
        "(alpha_NP + e) - pi/10":      ATOMS["alpha_NP"] + E - PI/10,
        "e/10 + 4":                    E/10 + 4,
        "3 + 4/pi":                    3 + 4/PI,
        "3 * sqrt(2)":                 3 * SQRT2,
        "h_H3 / alpha_BSD = 40/(3pi)": mp.mpf(40) / (3*PI),
        "11*e/7":                      11*E/7,
        "4 + 1/(pi-3)/something":      mp.mpf(0),  # placeholder
        "pi*phi/(phi^(3/4)?) probe":   PI*PHI/mp.mpf("1.189"),
        "median target (4.251)":       mp.mpf("4.251"),
    }
    for name, v in cands.items():
        if v == 0: continue
        fv = float(v)
        em = abs(fv - mean); emed = abs(fv - float(np.median(arr)))
        print(f"  {name:40s} = {fv:.8f}")
        print(f"      err(mean)   = {em:.6f}  ({em/std:.2f} sigma)")
        print(f"      err(median) = {emed:.6f}")

    # ----- over-fitting denominator -----
    print("\n--- Over-fitting check ---")
    print("How many depth-3 combinations land within +/-0.001 of the mean?")
    near = enumerate_3(0.001)
    print(f"  N(|.| <= 0.001) = {len(near)}")
    print(f"  N(|.| <= 0.005) = {len(enumerate_3(0.005))}")
    print(f"  N(|.| <= 0.01)  = {len(enumerate_3(0.01))}")
    print("\nA 'matching candidate' is only informative if it is")
    print("structurally privileged AND its match-rate is far rarer")
    print("than enumeration noise.")

    # ----- 11e/7 angle (most interesting structured probe) -----
    print("\n--- 11*e/7 probe (from structured search) ---")
    val = float(11*E/7)
    print(f"  11*e/7 = {val:.10f}")
    print(f"  err vs mean   = {abs(val - mean):.6f} "
          f"({abs(val-mean)/std:.2f} sigma)")
    print("  -- 11 and 7 have no obvious substrate role; this is "
          "almost certainly coincidence.")

    # ----- candidate H3/Galois-flavored exact derivations -----
    print("\n--- H3/Coxeter & Galois-flavored derivations ---")
    h_h3 = mp.mpf(10)
    # alpha_BSD = 3*pi/4 -> h_H3/alpha_BSD = 40/(3*pi)
    v1 = h_h3 / (3*PI/4)
    print(f"  h(H3)/alpha_BSD = 40/(3*pi)     = {float(v1):.8f}  "
          f"err = {abs(float(v1)-mean):.5f} ({abs(float(v1)-mean)/std:.2f}s)")
    # 40/(3*pi) ~ 4.244, only 0.4 sigma off mean but 0.7 sigma off median
    print(f"      err vs median (4.251) = {abs(float(v1)-float(np.median(arr))):.5f}")

    # 3*alpha_P = 3*sqrt(2)
    v2 = 3*SQRT2
    print(f"  3 * alpha_P = 3*sqrt(2)         = {float(v2):.8f}  "
          f"err = {abs(float(v2)-mean):.5f} ({abs(float(v2)-mean)/std:.2f}s)")
    print(f"      err vs median = {abs(float(v2)-float(np.median(arr))):.5f}")

    # alpha_NP + e - pi/10
    v3 = ATOMS["alpha_NP"] + E - PI/10
    print(f"  alpha_NP + e - pi/10            = {float(v3):.8f}  "
          f"err = {abs(float(v3)-mean):.5f} ({abs(float(v3)-mean)/std:.2f}s)")
    print("      Uses e (not in substrate basis!) -- structurally suspect.")

    # alpha_RH * (sqrt(2) + ...) probes around 4.251 median
    v4 = mp.mpf("1.5") + SQRT2 + mp.mpf("1.337")
    print(f"  alpha_RH + alpha_P + 1.337 toy  = {float(v4):.8f}")

    # Two-term clean candidates near median 4.251
    print("\n--- Clean two-term candidates closest to MEDIAN 4.251 ---")
    median = float(np.median(arr))
    two_term = []
    names = list(ATOMS.items())
    for (na, va), (nb, vb) in it.product(names, names):
        for s in ("+", "-", "*", "/"):
            try:
                if s == "+": v = va + vb
                elif s == "-": v = va - vb
                elif s == "*": v = va * vb
                else:
                    if vb == 0: continue
                    v = va / vb
                if not mp.isfinite(v): continue
                two_term.append((float(v), f"{na} {s} {nb}"))
            except Exception:
                continue
    two_term.sort(key=lambda x: abs(x[0] - median))
    for v, expr in two_term[:10]:
        print(f"  {v:.8f}  {expr:35s}  err vs median = {abs(v-median):.5f}")


if __name__ == "__main__":
    main()
