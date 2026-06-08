#!/usr/bin/env python3
"""
p-adic substrate test for Principia Fractalis spectral conjecture.

Tests whether the natural base-3 substrate L^2(Z_3) — matching the framework's
D_3 digital sum, base-3 recursion, and fractal structure — produces
lambda_0(H_alpha) = pi/(10*alpha) as a literal eigenvalue.

The 3-adic absolute value |x - y|_3 gives an ultrametric on Z_3.
Truncating to depth k yields 3^k discrete points with Haar measure 1/3^k.

Operators tested:
  (A) H_alpha on L^2(Z_3, depth k) with kernel V_alpha(|x-y|_3)
  (B) H_alpha with logarithmic 3-adic distance
  (C) H_alpha with base-3 digital-sum phase twist (the natural p-adic
      generalization of the framework's base-3 phase structure)
"""

import numpy as np
from numpy.linalg import eigh
import math

# ----------------------------------------------------------------------
# 3-adic primitives
# ----------------------------------------------------------------------

def three_adic_valuation(n, max_digits):
    """v_3(n) = max k such that 3^k | n. Returns max_digits if n == 0."""
    if n == 0:
        return max_digits
    v = 0
    while n % 3 == 0:
        n //= 3
        v += 1
    return v

def three_adic_abs(x, y, k):
    """|x - y|_3 where x, y in {0, ..., 3^k - 1} are identified
    with strings of 3-adic digits of length k.

    Returns 3^{-v} where v = v_3(x - y), and 0 if x == y.
    """
    if x == y:
        return 0.0
    d = x - y  # may be negative; v_3(d) = v_3(|d|)
    v = three_adic_valuation(abs(d), k)
    return 3.0 ** (-v)

def base3_digital_sum(x, k):
    """Sum of base-3 digits of x (treated as length-k string)."""
    s = 0
    n = x
    for _ in range(k):
        s += n % 3
        n //= 3
    return s

# ----------------------------------------------------------------------
# Kernel V_alpha
# ----------------------------------------------------------------------

def V_alpha(d, alpha, a, N):
    """V_alpha(d) = sum_{n=0}^{N} a^{-n} cos(pi alpha^n d).

    a is the self-similarity rate; framework uses a = alpha (or related)."""
    if d == 0.0:
        # cos(0) = 1, geometric sum
        return sum(a**(-n) for n in range(N + 1))
    total = 0.0
    for n in range(N + 1):
        total += (a ** (-n)) * math.cos(math.pi * (alpha ** n) * d)
    return total

# ----------------------------------------------------------------------
# Build operator matrices
# ----------------------------------------------------------------------

def build_distance_matrix(k, mode='ultrametric'):
    """Return n x n matrix of d(x, y) with n = 3^k.

    mode:
      'ultrametric'   : |x - y|_3
      'log'           : -log_3 of 3-adic abs (gives valuation v)
                        (use v itself as 'distance' in some natural sense)
    """
    n = 3 ** k
    D = np.zeros((n, n))
    for x in range(n):
        for y in range(x + 1, n):
            if mode == 'ultrametric':
                d = three_adic_abs(x, y, k)
            elif mode == 'log':
                # log_3(|x-y|_3^{-1}) = v_3(x-y)
                d = float(three_adic_valuation(abs(x - y), k))
            else:
                raise ValueError(mode)
            D[x, y] = d
            D[y, x] = d
    return D

def build_H_alpha(k, alpha, a, N, distance_mode='ultrametric'):
    """Build the n x n real symmetric operator matrix H_alpha.

    (H_alpha)_{x,y} = (1/3^k) * V_alpha(d(x, y))

    The 1/3^k prefactor is the Haar measure on Z_3 truncated to depth k.
    """
    n = 3 ** k
    D = build_distance_matrix(k, mode=distance_mode)
    H = np.zeros((n, n))
    haar = 1.0 / n  # 1/3^k
    for x in range(n):
        for y in range(n):
            H[x, y] = haar * V_alpha(D[x, y], alpha, a, N)
    # Symmetrize to remove FP noise
    H = 0.5 * (H + H.T)
    return H

def build_H_alpha_phase(k, alpha, a, N):
    """Build the n x n complex Hermitian operator with base-3 digital-sum
    phase twist:

    (H_alpha^phi)_{x,y} = (1/3^k) * exp(i pi alpha (D3(x) - D3(y))) * V_alpha(|x-y|_3)

    This is Hermitian because the phase is anti-symmetric in (x, y) and
    V_alpha(|x-y|_3) is symmetric.
    """
    n = 3 ** k
    D = build_distance_matrix(k, mode='ultrametric')
    D3 = np.array([base3_digital_sum(x, k) for x in range(n)], dtype=float)
    H = np.zeros((n, n), dtype=complex)
    haar = 1.0 / n
    for x in range(n):
        for y in range(n):
            phase = np.exp(1j * math.pi * alpha * (D3[x] - D3[y]))
            H[x, y] = haar * phase * V_alpha(D[x, y], alpha, a, N)
    H = 0.5 * (H + H.conj().T)
    return H

# ----------------------------------------------------------------------
# Diagonalize + search for target eigenvalue
# ----------------------------------------------------------------------

def diagonalize_and_report(H, target, label, top=20, tol=1e-3):
    """Diagonalize Hermitian H, report top eigenvalues, look for target."""
    if np.iscomplexobj(H):
        w = np.linalg.eigvalsh(H)
    else:
        w = np.linalg.eigvalsh(H)
    w_sorted = np.sort(w)
    # Top by magnitude (largest in absolute value)
    w_by_mag = w[np.argsort(-np.abs(w))]
    # Also smallest positive
    pos = w_sorted[w_sorted > 0]
    print(f"\n--- {label} ---")
    print(f"  matrix size: {H.shape[0]}, target: {target:.6f}")
    print(f"  spectral range: [{w_sorted[0]:.6f}, {w_sorted[-1]:.6f}]")
    print(f"  top {top} |lambda|:")
    for i, lam in enumerate(w_by_mag[:top]):
        gap = abs(abs(lam) - target)
        marker = '  <-- MATCH' if gap < tol else ''
        print(f"    {i+1:2d}: lambda = {lam:+.8f}   |gap to target| = {gap:.6f}{marker}")
    # Closest eigenvalue (by absolute value) to target
    closest_idx = np.argmin(np.abs(np.abs(w) - target))
    closest = w[closest_idx]
    print(f"  closest |lambda| to target: {abs(closest):.8f}  (gap = {abs(abs(closest) - target):.6f})")
    return w, closest

# ----------------------------------------------------------------------
# Main test battery
# ----------------------------------------------------------------------

def run_battery():
    print("=" * 72)
    print("p-adic substrate test for Principia Fractalis")
    print("=" * 72)

    # Test cases: (alpha, a, target, label)
    # framework's claim: lambda_0(H_alpha) = pi/(10*alpha)
    # and natural ladder a = alpha (use a = alpha to match the Ch 3
    # self-similar kernel; also try a = 3 to match the substrate's base)
    cases = [
        (math.sqrt(2), math.sqrt(2), math.pi / (10 * math.sqrt(2)), 'alpha=sqrt(2), a=sqrt(2)'),
        (math.sqrt(2), 3.0,           math.pi / (10 * math.sqrt(2)), 'alpha=sqrt(2), a=3 (base-3 ladder)'),
        (1.5,           1.5,           math.pi / 15.0,                'alpha=3/2, a=3/2'),
        (1.5,           3.0,           math.pi / 15.0,                'alpha=3/2, a=3'),
        (2.0,           2.0,           math.pi / 20.0,                'alpha=2, a=2'),
        (2.0,           3.0,           math.pi / 20.0,                'alpha=2, a=3'),
    ]

    N_kernel = 20  # truncation of the V_alpha series

    for k in [4, 5]:
        print(f"\n{'#'*72}\n# Depth k = {k}  ({3**k} x {3**k} matrices)\n{'#'*72}")
        for alpha, a, target, label in cases:
            print(f"\n=== alpha={alpha:.6f}, a={a:.6f}, target=pi/(10*alpha)={target:.6f} ({label}) ===")
            # (A) ultrametric
            H_ultra = build_H_alpha(k, alpha, a, N_kernel, distance_mode='ultrametric')
            diagonalize_and_report(H_ultra, target,
                                   f"A. ultrametric  {label}, k={k}")
            # (B) log distance
            H_log = build_H_alpha(k, alpha, a, N_kernel, distance_mode='log')
            diagonalize_and_report(H_log, target,
                                   f"B. log distance {label}, k={k}")
            # (C) phase twist
            H_phase = build_H_alpha_phase(k, alpha, a, N_kernel)
            diagonalize_and_report(H_phase, target,
                                   f"C. D3-phase     {label}, k={k}")

if __name__ == '__main__':
    run_battery()
