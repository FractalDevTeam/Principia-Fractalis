#!/usr/bin/env python3
"""
Convergence test: does the closest eigenvalue approach pi/(10*alpha)
as depth k -> infinity, or saturate elsewhere?

Focus on the two cases where k=4,5 gaps looked smallest:
  - alpha=2, a=2, ultrametric            (gap ~ 0.0055)
  - alpha=sqrt(2), a=sqrt(2), log dist   (gap ~ 0.01-0.02, but unstable)

Test k = 3, 4, 5, 6 (k=6 -> 729x729) and watch the trajectory.

Also test: is the apparent match actually pi/(10*alpha), or is it
just some other natural quantity (e.g. (1-1/a) * geometric-sum-tail)?
"""

import numpy as np
import math
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from padic_test import build_H_alpha, build_H_alpha_phase

def closest_to_target(H, target):
    w = np.linalg.eigvalsh(H)
    aw = np.abs(w)
    idx = np.argmin(np.abs(aw - target))
    return w[idx], aw[idx]

def convergence_trajectory(alpha, a, N_kernel, mode, ks, phase=False):
    target = math.pi / (10 * alpha)
    print(f"\n=== alpha={alpha:.6f}, a={a:.6f}, mode={mode}, phase={phase}, target={target:.8f} ===")
    print(f"  {'k':>3} {'n':>5} {'closest |lambda|':>20} {'gap':>15} {'gap ratio':>12}")
    prev_gap = None
    trajectory = []
    for k in ks:
        if phase:
            H = build_H_alpha_phase(k, alpha, a, N_kernel)
        else:
            H = build_H_alpha(k, alpha, a, N_kernel, distance_mode=mode)
        lam, alam = closest_to_target(H, target)
        gap = abs(alam - target)
        ratio = '-' if prev_gap is None else f"{gap/prev_gap:.4f}"
        print(f"  {k:>3} {3**k:>5} {alam:>20.10f} {gap:>15.8f} {ratio:>12}")
        trajectory.append((k, alam, gap))
        prev_gap = gap
    return trajectory

if __name__ == '__main__':
    N = 20

    print("Convergence study: tracking closest |lambda| to pi/(10*alpha) as k grows.")
    print("If the substrate genuinely realizes the conjecture, gap -> 0 as k -> infinity.")
    print("If it saturates at some nonzero value, the eigenvalue is some OTHER quantity")
    print("that just happens to lie near pi/(10*alpha) by coincidence.")

    # Case 1: alpha=2, a=2, ultrametric — smallest gap seen (~0.005)
    convergence_trajectory(2.0, 2.0, N, 'ultrametric', [3, 4, 5, 6])

    # Case 2: alpha=2, a=2, phase
    convergence_trajectory(2.0, 2.0, N, 'ultrametric', [3, 4, 5, 6], phase=True)

    # Case 3: alpha=sqrt(2), a=sqrt(2), log distance — had k=4 gap ~0.01
    convergence_trajectory(math.sqrt(2), math.sqrt(2), N, 'log', [3, 4, 5, 6])

    # Case 4: alpha=sqrt(2), a=sqrt(2), ultrametric (for comparison)
    convergence_trajectory(math.sqrt(2), math.sqrt(2), N, 'ultrametric', [3, 4, 5, 6])

    # Case 5: alpha=3/2, a=3/2, ultrametric and phase
    convergence_trajectory(1.5, 1.5, N, 'ultrametric', [3, 4, 5, 6])
    convergence_trajectory(1.5, 1.5, N, 'ultrametric', [3, 4, 5, 6], phase=True)
