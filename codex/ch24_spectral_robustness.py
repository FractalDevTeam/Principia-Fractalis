#!/usr/bin/env python3
"""
ch24 spectral-operator robustness sweep.

Tests the ONE claim from codex/CH24_SPECTRAL_TEST_2026-07-28.md that survived:
that the dominant |eigenvalue| of the discretized operator

    (T_E f)(x) = sum_{p good} (a_p / p) * exp(i*pi*alpha*D(p)*x) * f(x/p),
    alpha = 3*pi/4,  D(p) = base-3 digit sum of p

is monotone in rank E(Q) at about +2 per rank.  That test used
11a1 (r=0), 37a1 (r=1), 389a1 (r=2), 5077a1 (r=3) -- whose conductors are
11, 37, 389, 5077.  RANK AND CONDUCTOR INCREASE TOGETHER THERE, so a
"rank signal" and a "conductor signal" are indistinguishable in it.

Two sweeps:

  A. (grid, PMAX) robustness on the original four curves.  Is the slope
     stable under refinement, or does it drift?

  B. THE CONFOUND TEST.  Nine curves of classical rank 1 whose rank >= 1 is
     kernel-verified in this corpus (r131-r142), conductors 37..106, a ~3x
     spread at FIXED rank.  If lambda_max reads rank, these cluster.  If it
     reads conductor, they spread monotonically in N.

Curve coefficients (a1,a2,a3,a4,a6) are taken verbatim from the Lean
definitions in PF/E*RankOne_r1*.lean, not from memory.  Bad primes are
detected from the discriminant, so no conductor input is trusted.

Run: /home/xluxx/ai-env/bin/python codex/ch24_spectral_robustness.py
"""

import numpy as np
from sympy import primerange, factorint

ALPHA = 3.0 * np.pi / 4.0

# (a1,a2,a3,a4,a6) exactly as in the Lean corpus; 11a1 is the rank-0 control.
CURVES = {
    "11a1":   ((0, -1, 1, -10, -20), 0),
    "37a1":   ((0, 0, 1, -1, 0),     1),
    "43a1":   ((0, 1, 1, 0, 0),      1),
    "53a1":   ((1, -1, 1, 0, 0),     1),
    "61a1":   ((1, 0, 0, -2, 1),     1),
    "79a1":   ((1, 1, 1, -2, 0),     1),
    "83a1":   ((1, 1, 1, 1, 0),      1),
    "89a1":   ((1, 1, 1, -1, 0),     1),
    "101a1":  ((0, 1, 1, -1, -1),    1),
    "106a1":  ((1, 1, 0, -7, 5),     1),
    "389a1":  ((0, 1, 1, -2, 0),     2),
    "5077a1": ((0, 0, 1, -7, 6),     3),
}


def invariants(a1, a2, a3, a4, a6):
    b2 = a1 * a1 + 4 * a2
    b4 = 2 * a4 + a1 * a3
    b6 = a3 * a3 + 4 * a6
    b8 = a1**2 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3**2 - a4**2
    disc = -b2**2 * b8 - 8 * b4**3 - 27 * b6**2 + 9 * b2 * b4 * b6
    return b2, b4, b6, b8, disc


def a_p_table(coeffs, pmax):
    """a_p = -sum_x chi(4x^3 + b2 x^2 + 2 b4 x + b6) over F_p, for good odd p.

    Completing the square in y turns y^2 + a1 x y + a3 y = x^3 + ... into
    (2y + a1 x + a3)^2 = 4x^3 + b2 x^2 + 2 b4 x + b6, so the affine count is
    sum_x (1 + chi(g(x))) and a_p = p + 1 - #E = -sum_x chi(g(x)).
    """
    b2, b4, b6, _, disc = invariants(*coeffs)
    out = {}
    for p in primerange(3, pmax):
        if disc % p == 0:            # bad reduction, detected not assumed
            continue
        x = np.arange(p, dtype=np.int64)
        g = (4 * x**3 + b2 * x**2 + 2 * b4 * x + b6) % p
        # chi via a precomputed quadratic-residue indicator: 0 -> 0, QR -> +1, else -1
        chi = np.full(p, -1, dtype=np.int64)
        sq = (np.arange(1, (p + 1) // 2, dtype=np.int64) ** 2) % p
        chi[sq] = 1
        chi[0] = 0
        out[p] = int(-chi[g].sum())
    return out, disc


def digitsum3(n):
    s = 0
    while n:
        s += n % 3
        n //= 3
    return s


def lambda_max(coeffs, grid, pmax, aps=None):
    """Largest |eigenvalue| of the collocation discretization on grid points
    x_j = (j+0.5)/grid, with f(x_j/p) by linear interpolation."""
    if aps is None:
        aps, _ = a_p_table(coeffs, pmax)
    xs = (np.arange(grid) + 0.5) / grid
    M = np.zeros((grid, grid), dtype=np.complex128)
    for p, ap in aps.items():
        if ap == 0:
            continue
        phase = np.exp(1j * np.pi * ALPHA * digitsum3(p) * xs)
        w = (ap / p) * phase
        y = xs / p                          # target locations, all in [0, 1/p]
        t = y * grid - 0.5                  # fractional grid index
        k0 = np.floor(t).astype(int)
        fr = t - k0
        k1 = k0 + 1
        ok0 = (k0 >= 0) & (k0 < grid)
        ok1 = (k1 >= 0) & (k1 < grid)
        rows = np.arange(grid)
        np.add.at(M, (rows[ok0], k0[ok0]), (w * (1 - fr))[ok0])
        np.add.at(M, (rows[ok1], k1[ok1]), (w * fr)[ok1])
    return float(np.abs(np.linalg.eigvals(M)).max())


def fit_slope(ranks, vals):
    A = np.vstack([np.array(ranks, float), np.ones(len(ranks))]).T
    (m, c), *_ = np.linalg.lstsq(A, np.array(vals, float), rcond=None)
    pred = A @ np.array([m, c])
    ss_res = float(((np.array(vals) - pred) ** 2).sum())
    ss_tot = float(((np.array(vals) - np.mean(vals)) ** 2).sum())
    r2 = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")
    return m, c, r2


if __name__ == "__main__":
    print("=" * 74)
    print("SWEEP A -- (grid, PMAX) robustness on the original four curves")
    print("   NOTE: in this set rank and conductor rise together (11,37,389,5077),")
    print("   so a rank signal cannot be distinguished from a conductor signal.")
    print("=" * 74)
    quad = ["11a1", "37a1", "389a1", "5077a1"]
    cache = {}
    for pmax in (500, 1500, 5000, 15000):
        for nm in quad:
            cache[(nm, pmax)] = a_p_table(CURVES[nm][0], pmax)[0]
        print(f"\n  PMAX = {pmax}")
        print(f"    {'grid':>5} " + "".join(f"{n:>10}" for n in quad)
              + f"{'slope':>9}{'R^2':>8}")
        for grid in (120, 240, 480):
            vals = [lambda_max(CURVES[n][0], grid, pmax, cache[(n, pmax)])
                    for n in quad]
            m, c, r2 = fit_slope([CURVES[n][1] for n in quad], vals)
            print(f"    {grid:>5} " + "".join(f"{v:>10.4f}" for v in vals)
                  + f"{m:>9.3f}{r2:>8.4f}")

    print()
    print("=" * 74)
    print("SWEEP B -- THE CONFOUND TEST: nine curves, ALL classical rank 1,")
    print("   conductors 37..106 (a ~3x spread at FIXED rank).")
    print("   Cluster  => lambda_max reads RANK.")
    print("   Spread   => lambda_max reads CONDUCTOR, and Sweep A was an artifact.")
    print("=" * 74)
    r1 = ["37a1", "43a1", "53a1", "61a1", "79a1", "83a1", "89a1", "101a1", "106a1"]
    for pmax in (1500, 5000):
        for grid in (240, 480):
            vals = []
            for nm in r1:
                aps, _ = a_p_table(CURVES[nm][0], pmax)
                vals.append(lambda_max(CURVES[nm][0], grid, pmax, aps))
            arr = np.array(vals)
            print(f"\n  grid={grid}, PMAX={pmax}")
            for nm, v in zip(r1, vals):
                print(f"    {nm:>7}  lambda_max = {v:8.4f}")
            print(f"    -> mean {arr.mean():.4f}, sd {arr.std(ddof=1):.4f}, "
                  f"min {arr.min():.4f}, max {arr.max():.4f}, "
                  f"spread/mean {(arr.max()-arr.min())/arr.mean():.3f}")
            # correlation with conductor, at fixed rank
            Ns = [int(nm[:-2]) for nm in r1]
            cc = float(np.corrcoef(np.array(Ns, float), arr)[0, 1])
            print(f"    -> corr(lambda_max, conductor) at FIXED rank 1 = {cc:+.4f}")
