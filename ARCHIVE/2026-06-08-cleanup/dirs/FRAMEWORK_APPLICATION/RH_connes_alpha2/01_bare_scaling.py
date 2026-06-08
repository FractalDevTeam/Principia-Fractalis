"""
Bare Connes-style scaling operator on L^2((1, beta), dx/x) — baseline.

Operator: D = -i x d/dx  (generator of dilations).

In log-coordinate u = log x ∈ (0, L) with L = log(beta), this becomes
D = -i d/du on L^2((0, L), du). With Dirichlet/periodic BCs, the spectrum
is essentially equispaced: eigenvalues k * pi/L (Dirichlet sin basis)
or 2*pi*k/L (Fourier).

This script establishes the baseline spectrum WITHOUT any framework
modulation. It is the null hypothesis: bare Connes scaling on a finite
log interval gives a uniform Weyl-density spectrum that does NOT match
the zeta zeros.

Author: Pablo Cohen + Claude (Principia Fractalis, Wave 11)
Date: 2026-05-23
"""

import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import eigsh
import mpmath as mp
import json
import os

mp.mp.dps = 30

OUT_DIR = os.path.dirname(os.path.abspath(__file__))


def build_scaling_matrix_log_coords(L, N, bc="dirichlet"):
    """
    Discretize D = -i d/du on (0, L) with N grid points using
    central differences. Returns a HERMITIAN matrix (after symmetrization).

    bc: "dirichlet" => u(0) = u(L) = 0 (fixes boundary terms)
        "periodic"  => u(0) = u(L)   (Fourier modes)
    """
    du = L / (N + 1) if bc == "dirichlet" else L / N
    # central difference: (psi[k+1] - psi[k-1]) / (2 du), prefactor -i
    # but -i * d/du is Hermitian, so the discretized matrix should be
    # M[j, j+1] = -i / (2 du), M[j+1, j] = +i / (2 du)
    main = np.zeros(N, dtype=complex)
    upper = np.full(N - 1, -1j / (2 * du), dtype=complex)
    lower = np.full(N - 1, 1j / (2 * du), dtype=complex)
    M = np.diag(main) + np.diag(upper, 1) + np.diag(lower, -1)
    if bc == "periodic":
        M[0, -1] = 1j / (2 * du)
        M[-1, 0] = -1j / (2 * du)
    # Hermitize numerically (already Hermitian by construction)
    M = 0.5 * (M + M.conj().T)
    return M


def first_zeta_zeros(k):
    """First k imaginary parts of Riemann zeta zeros (positive)."""
    return np.array([float(mp.im(mp.zetazero(n))) for n in range(1, k + 1)])


def topk_positive_eigs(M, k):
    """Return the k smallest positive eigenvalues."""
    w = np.linalg.eigvalsh(M)
    pos = w[w > 1e-10]
    return np.sort(pos)[:k]


def analyze(L, N, label):
    """Diagonalize bare scaling on (0, L) with N pts. Compare to first 20 zeros."""
    M = build_scaling_matrix_log_coords(L, N, bc="dirichlet")
    eigs = topk_positive_eigs(M, 20)
    zeros = first_zeta_zeros(20)

    # Expected analytical spectrum: k * pi / L for k = 1..N
    expected = np.array([k * np.pi / L for k in range(1, 21)])

    rms_vs_zeros = float(np.sqrt(np.mean((eigs - zeros) ** 2)))
    rms_vs_analytical = float(np.sqrt(np.mean((eigs - expected) ** 2)))

    print(f"\n=== {label}: L={L}, N={N} ===")
    print(f"First 5 eigs   : {eigs[:5]}")
    print(f"First 5 zeros  : {zeros[:5]}")
    print(f"Analytical k*pi/L: {expected[:5]}")
    print(f"RMS error vs zeta zeros        : {rms_vs_zeros:.4f}")
    print(f"RMS error vs analytical k*pi/L : {rms_vs_analytical:.6f}")

    return {
        "label": label,
        "L": L,
        "N": N,
        "eigenvalues": eigs.tolist(),
        "zeta_zeros": zeros.tolist(),
        "analytical_k_pi_over_L": expected.tolist(),
        "rms_vs_zeros": rms_vs_zeros,
        "rms_vs_analytical": rms_vs_analytical,
    }


if __name__ == "__main__":
    results = []
    for L, N in [(20.0, 400), (50.0, 1000), (100.0, 1500), (200.0, 2000)]:
        results.append(analyze(L, N, f"bare_L{int(L)}"))

    with open(os.path.join(OUT_DIR, "results_01_bare_scaling.json"), "w") as f:
        json.dump(results, f, indent=2)

    print("\nSummary: bare Connes scaling on log-coord truncation")
    print(f"{'Truncation':<15}{'RMS vs zeros':<18}{'RMS vs k*pi/L':<18}")
    for r in results:
        print(f"L={r['L']:<13}{r['rms_vs_zeros']:<18.4f}{r['rms_vs_analytical']:<18.6f}")
