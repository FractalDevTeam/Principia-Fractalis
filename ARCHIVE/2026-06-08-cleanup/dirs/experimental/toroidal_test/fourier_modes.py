"""
Fourier expansion of V_alpha on T^2 x T^2 (and single T^2).

For a convolution operator with kernel K(x,y) = V_alpha(d(x,y)) on a flat torus,
the eigenvalues are
    lambda_k = integral_{torus} K(0, y) e^{-i k . y} dHaar(y)
            = V_hat_alpha(k).

For k = 0, this is exactly the spatial mean (already computed in toroidal_lambda0.py).
For k != 0, these are the other eigenvalues.

Sanity check 1: the "geodesic" extension is NOT translation invariant in the
usual flat sense across the boundary... actually it IS translation invariant
because d(x, y) depends only on (x - y) mod 2pi. So K IS a convolution kernel
and IS diagonalized by Fourier modes.

Test compares the largest-magnitude lambda_k values to pi/(10*alpha).
"""

import numpy as np
import math
from scipy import integrate

PI = math.pi


def g(theta):
    t = theta % (2 * PI)
    return np.minimum(t, 2 * PI - t)


def V_alpha_vec(d, alpha, a=2.0, N=20):
    d_arr = np.asarray(d, dtype=float)
    total = np.zeros_like(d_arr)
    for n in range(N):
        total += (a ** (-n)) * np.cos(PI * (alpha ** n) * d_arr)
    return total


def fourier_coeff_T2(k1, k2, alpha, a=2.0, N=20, n_grid=512):
    """Fourier coefficient on single T^2:
       V_hat(k1, k2) = (1/(2pi)^2) int_{[0,2pi]^2} V_alpha(d(0, (t1,t2))) e^{-i(k1 t1 + k2 t2)} dt
    where d(0, (t1,t2)) = sqrt(g(t1)^2 + g(t2)^2).
    Use trapezoid/FFT-style summation on n_grid x n_grid mesh.
    """
    t = np.linspace(0, 2 * PI, n_grid, endpoint=False)
    T1, T2 = np.meshgrid(t, t, indexing="ij")
    G1 = g(T1)
    G2 = g(T2)
    D = np.sqrt(G1 ** 2 + G2 ** 2)
    V = V_alpha_vec(D, alpha, a, N)
    phase = np.exp(-1j * (k1 * T1 + k2 * T2))
    integrand = V * phase
    # average (trapezoid with uniform grid -> just mean)
    return integrand.mean()


def fourier_coeff_T2T2(k, alpha, a=2.0, N=20, n_grid=128):
    """Fourier coefficient on T^2 x T^2 with k = (k1, k2, k3, k4).
    V_hat(k) = (1/(2pi)^4) int_{[0,2pi]^4} V_alpha(sqrt(g(t1)^2+...+g(t4)^2))
                                          e^{-i k.t} dt.

    This is a 4D integral - we use a Cartesian grid (n_grid^4).
    For n_grid=128, that's 2.68e8 points; for n_grid=64, 1.68e7 (manageable).
    """
    k1, k2, k3, k4 = k
    t = np.linspace(0, 2 * PI, n_grid, endpoint=False)
    # vectorize via outer products and broadcast
    G = g(t)
    # compute |G|^2 sums
    G2 = G ** 2
    # broadcast to 4D
    G2_sum = (G2[:, None, None, None] + G2[None, :, None, None]
              + G2[None, None, :, None] + G2[None, None, None, :])
    D = np.sqrt(G2_sum)
    V = V_alpha_vec(D, alpha, a, N)
    phase1 = np.exp(-1j * k1 * t)
    phase2 = np.exp(-1j * k2 * t)
    phase3 = np.exp(-1j * k3 * t)
    phase4 = np.exp(-1j * k4 * t)
    Phase = (phase1[:, None, None, None] * phase2[None, :, None, None]
             * phase3[None, None, :, None] * phase4[None, None, None, :])
    integrand = V * Phase
    return integrand.mean()


def main():
    target_root2 = PI / (10 * math.sqrt(2))
    print("=" * 70)
    print("FOURIER MODES of K(x,y) = V_alpha(d(x,y)) on the torus(es)")
    print("=" * 70)
    print(f"Target pi/(10*sqrt(2)) = {target_root2:.10f}")
    print()
    print("SINGLE T^2 (n_grid=512):  V_hat(k1,k2) for low (k1,k2)")
    print("-" * 70)
    alpha = math.sqrt(2)
    print(f"{'(k1,k2)':>10}  {'Re':>14}  {'Im':>14}  {'|.|':>14}")
    for k1 in range(0, 6):
        for k2 in range(0, 6):
            val = fourier_coeff_T2(k1, k2, alpha)
            print(f"  ({k1},{k2})    {val.real:+.10f}  {val.imag:+.10f}  {abs(val):.10f}")

    print()
    print("DOUBLE T^2 x T^2 (n_grid=64):  V_hat(k) for low k = (k1,k2,k3,k4)")
    print("-" * 70)
    # Only sample a few low-multi-index modes to keep cost manageable
    ks_to_try = [
        (0, 0, 0, 0),
        (1, 0, 0, 0),
        (0, 1, 0, 0),
        (1, 1, 0, 0),
        (1, 0, 1, 0),
        (1, 1, 1, 1),
        (2, 0, 0, 0),
        (2, 1, 0, 0),
    ]
    print(f"{'k':>15}  {'Re':>14}  {'Im':>14}  {'|.|':>14}")
    for k in ks_to_try:
        val = fourier_coeff_T2T2(k, alpha, n_grid=64)
        print(f"  {str(k):>15}  {val.real:+.10f}  {val.imag:+.10f}  {abs(val):.10f}")


if __name__ == "__main__":
    main()
