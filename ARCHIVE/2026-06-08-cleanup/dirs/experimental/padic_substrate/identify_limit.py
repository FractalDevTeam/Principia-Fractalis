#!/usr/bin/env python3
"""
The convergence study shows the closest eigenvalues are saturating at
values DIFFERENT from pi/(10*alpha). Identify what those limits are.

Hypothesis: on an ultrametric space the kernel V_alpha(d) with d in
{3^{-k+1}, ..., 1} produces eigenvalues governed by the discrete distance
spectrum {0, 3^0, 3^{-1}, ..., 3^{-(k-1)}} and the structure of nested
ultrametric balls. These eigenvalues are p-adic structural constants,
not pi/(10*alpha).
"""

import numpy as np
import math
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from padic_test import build_H_alpha, V_alpha

def all_eigs(H):
    return np.sort(np.linalg.eigvalsh(H))

def identify_saturation(alpha, a, N_kernel, k_high=6):
    """At k_high, get the top few eigenvalues and try to fit them to
    natural constants: V_alpha(1), V_alpha(1/3), V_alpha at zero, etc."""
    target = math.pi / (10 * alpha)
    print(f"\n=== alpha={alpha:.6f}, a={a:.6f}, k={k_high} ===")
    print(f"  pi/(10*alpha) target            = {target:.10f}")

    # Natural reference quantities:
    V_at_0  = V_alpha(0.0, alpha, a, N_kernel)              # = sum a^-n
    V_at_1  = V_alpha(1.0, alpha, a, N_kernel)
    V_at_3i = V_alpha(1.0/3, alpha, a, N_kernel)
    V_at_9i = V_alpha(1.0/9, alpha, a, N_kernel)
    V_at_27i = V_alpha(1.0/27, alpha, a, N_kernel)
    geom    = 1.0 / (1.0 - 1.0/a) if a != 1.0 else None
    print(f"  V_alpha(0) (= geom sum)         = {V_at_0:.10f}")
    print(f"  geom 1/(1-1/a)                  = {geom:.10f}" if geom else "")
    print(f"  V_alpha(1)                      = {V_at_1:.10f}")
    print(f"  V_alpha(1/3)                    = {V_at_3i:.10f}")
    print(f"  V_alpha(1/9)                    = {V_at_9i:.10f}")
    print(f"  V_alpha(1/27)                   = {V_at_27i:.10f}")

    H = build_H_alpha(k_high, alpha, a, N_kernel, distance_mode='ultrametric')
    w = all_eigs(H)
    n = H.shape[0]

    # Show the largest eigenvalue + the multiplet near our target
    print(f"  matrix size n = 3^{k_high} = {n}")
    print(f"  largest lambda (PF eigenvector ~ uniform): {w[-1]:.10f}")
    print(f"     compare to mean(H) * n = V_alpha(0)/n * n = V_alpha(0) (no)")
    print(f"     actual mean diagonal:                     {np.mean(np.diag(H)):.10f}")
    print(f"     V_alpha(0)/n = {V_at_0/n:.10f}")
    # The diagonal H_{xx} = (1/n) V_alpha(0)
    # All-ones eigenvalue: lambda_top = sum_y H_{x,y} = (1/n) sum_y V_alpha(|x-y|_3)
    # which is the row sum.
    row_sum = np.sum(H[0, :])
    print(f"     row-sum (= top eigenvalue for PF kernel): {row_sum:.10f}")

    # Top few unique eigenvalues
    print(f"  top 6 unique |lambda|:")
    uniq = []
    for lam in sorted(np.abs(w), reverse=True):
        if not any(abs(lam - u) < 1e-7 for u in uniq):
            uniq.append(lam)
        if len(uniq) >= 6:
            break
    for u in uniq:
        ratio = u / target
        print(f"    {u:.10f}    ratio to pi/(10a) = {ratio:.6f}")

    # Closest to target and ratios
    aw = np.abs(w)
    idx = np.argmin(np.abs(aw - target))
    closest = aw[idx]
    print(f"  closest |lambda| to target = {closest:.10f}")
    print(f"  ratio closest / target     = {closest/target:.10f}")
    print(f"  ratio target  / closest    = {target/closest:.10f}")
    # Test simple algebraic relations
    print(f"  closest * 10 * alpha       = {closest * 10 * alpha:.10f}    (target * 10*alpha = pi = {math.pi:.10f})")
    # Test against V_alpha(d) at specific d
    print(f"  closest / V_alpha(1/3^{k_high-1})        = {closest / V_alpha(3.0**(-(k_high-1)), alpha, a, N_kernel):.10f}")

if __name__ == '__main__':
    N = 20
    for alpha, a in [(2.0, 2.0), (1.5, 1.5), (math.sqrt(2), math.sqrt(2))]:
        identify_saturation(alpha, a, N, k_high=6)
