"""
06 — Convergence of the spectral gap lam_1 - lam_2 (and other gaps) with N.
Also tabulate FULL converged spectrum to see structure.
"""
import sys, importlib.util
import numpy as np
from numpy.linalg import eigh

spec = importlib.util.spec_from_file_location("k1", "01_kernel_and_cantor.py")
k1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(k1)

ALPHA = k1.ALPHA
LAMBDA_PRED = k1.LAMBDA_PRED


def cantor_spectrum(N, alpha=ALPHA, a=2.0, n_max=80):
    pts = k1.cantor_points(N)
    w = k1.hausdorff_weights(N)
    H_sym, _ = k1.build_H_matrix(pts, w, alpha=alpha, a=a, n_max=n_max)
    eigvals, _ = eigh(H_sym)
    return np.sort(eigvals)[::-1]


def main():
    print("Convergence of top eigenvalues (Cantor measure)")
    print(f"Target lambda_pred = pi/(10 sqrt 2) = {LAMBDA_PRED:.12f}\n")
    Ns = [6, 7, 8, 9, 10, 11]
    header = "  N |"
    for k in range(8):
        header += f"   lam_{k}   |"
    print(header)
    print("-" * len(header))
    spectra = {}
    for N in Ns:
        s = cantor_spectrum(N)
        spectra[N] = s
        row = f" {N:2d} |"
        for k in range(min(8, len(s))):
            row += f" {s[k]:.7f} |"
        print(row)

    print("\nGap analysis (lam_1 - lam_2):")
    for N in Ns:
        s = spectra[N]
        gap = s[1] - s[2]
        print(f"  N={N}: gap = {gap:.10f}   diff to target = {gap - LAMBDA_PRED:+.4e}")

    print("\nGap analysis (lam_0 - lam_1):")
    for N in Ns:
        s = spectra[N]
        gap = s[0] - s[1]
        print(f"  N={N}: gap = {gap:.10f}   diff to target = {gap - LAMBDA_PRED:+.4e}")

    # Try the lambda_0 of an ABSOLUTE-VALUE operator (compact integral op spectrum
    # can be characterized via |H|'s ground state)
    print("\nAbs-value ranked (|lam_k|) at N=11:")
    s = spectra[11]
    by_abs = np.sort(np.abs(s))[::-1]
    print(f"  Top 10 |eig|: {by_abs[:10]}")


if __name__ == "__main__":
    main()
