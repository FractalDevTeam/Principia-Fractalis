"""
Scan more Fourier modes on single T^2 to find any near the conjectured value
pi/(10*sqrt(2)) ~ 0.22214.

Also try the alternative chord distance d_chord = 2*sin(g(theta)/2) to see if
the conjecture lives there instead.
"""

import numpy as np
import math

PI = math.pi

def g(theta):
    t = theta % (2 * PI)
    return np.minimum(t, 2 * PI - t)

def chord(theta):
    """Euclidean chord on R/2piZ embedded in R^2 (radius 1): 2|sin(theta/2)|."""
    return 2.0 * np.abs(np.sin(theta / 2.0))

def V_alpha_vec(d, alpha, a=2.0, N=20):
    d_arr = np.asarray(d, dtype=float)
    total = np.zeros_like(d_arr)
    for n in range(N):
        total += (a ** (-n)) * np.cos(PI * (alpha ** n) * d_arr)
    return total


def scan_T2(alpha, n_grid=512, dist_kind="geodesic", kmax=15):
    """Scan |V_hat(k1,k2)| for k1,k2 in [-kmax, kmax]."""
    t = np.linspace(0, 2 * PI, n_grid, endpoint=False)
    T1, T2 = np.meshgrid(t, t, indexing="ij")
    if dist_kind == "geodesic":
        D = np.sqrt(g(T1) ** 2 + g(T2) ** 2)
    elif dist_kind == "chord_per_axis":
        D = np.sqrt(chord(T1) ** 2 + chord(T2) ** 2)
    elif dist_kind == "chord_4d":
        # treat T^2 as S^1 x S^1 embedded in R^4
        D = np.sqrt(chord(T1) ** 2 + chord(T2) ** 2)
    V = V_alpha_vec(D, alpha)

    # 2D FFT to get all Fourier coefficients at once
    coeffs = np.fft.fft2(V) / (n_grid * n_grid)
    target = PI / (10 * alpha)

    print(f"\n--- T^2 scan, alpha={alpha:.6f}, dist={dist_kind}, "
          f"target={target:.10f} ---")
    # Collect (k1, k2, value)
    rows = []
    for k1 in range(-kmax, kmax + 1):
        for k2 in range(-kmax, kmax + 1):
            i1 = k1 % n_grid
            i2 = k2 % n_grid
            c = coeffs[i1, i2]
            rows.append((k1, k2, c.real, c.imag, abs(c)))
    # Sort by closeness to target
    rows_sorted = sorted(rows, key=lambda r: abs(r[2] - target))
    print("Top 10 modes by closeness of Re(V_hat) to target:")
    print(f"{'(k1,k2)':>10}  {'Re':>14}  {'Im':>14}  {'|.|':>14}  {'|Re-target|':>14}")
    for r in rows_sorted[:10]:
        k1, k2, re, im, mag = r
        print(f"  ({k1:+d},{k2:+d})  {re:+.10f}  {im:+.10f}  {mag:.10f}  {abs(re-target):.10f}")


def main():
    for alpha in [math.sqrt(2), 1.5, 2.0]:
        scan_T2(alpha, dist_kind="geodesic", kmax=10)
        scan_T2(alpha, dist_kind="chord_per_axis", kmax=10)


if __name__ == "__main__":
    main()
