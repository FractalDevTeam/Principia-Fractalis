"""
04_wigner_dyson.py

Compute level-spacing statistics of the H_alpha^prime spectrum and compare
to GUE (Gaussian Unitary Ensemble), which is the conjectured ensemble for
zeta zeros (Montgomery pair-correlation, Odlyzko numerical confirmation).

For GUE:
  - Wigner surmise P(s) = (32/pi^2) s^2 exp(-4 s^2 / pi)
  - <s> = 1 by construction (after unfolding)
  - Var(s) = (3 pi - 8)/pi  approx  0.1781

For Poisson (no level repulsion):
  - P(s) = exp(-s)
  - Var(s) = 1

We unfold the spectrum (subtract smooth average density via polynomial fit)
and compute nearest-neighbor spacings.
"""

import numpy as np
import os
import sys
import pickle

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from importlib import import_module
mod = import_module("01_construct_H_alpha_prime")
build_H_alpha_prime = mod.build_H_alpha_prime


def unfold(eigs, deg=7, n_drop_edges=20):
    """
    Unfold spectrum: replace E_n by N_smooth(E_n) where N_smooth is
    a polynomial fit to the staircase function N(E) = #{E_i <= E}.
    """
    eigs = np.sort(eigs)
    N = len(eigs)
    counts = np.arange(1, N + 1, dtype=float)
    # Fit polynomial of degree `deg`
    coef = np.polyfit(eigs, counts, deg)
    N_smooth = np.polyval(coef, eigs)
    # Drop edges (boundary effects)
    return N_smooth[n_drop_edges:-n_drop_edges]


def spacings(unfolded):
    s = np.diff(unfolded)
    # Normalize so <s> = 1
    s = s / np.mean(s)
    return s


def wigner_surmise(s):
    return (32.0 / np.pi**2) * s**2 * np.exp(-4.0 * s**2 / np.pi)


def poisson(s):
    return np.exp(-s)


def main():
    print("=" * 72)
    print("WIGNER-DYSON FINGERPRINT TEST")
    print("=" * 72)

    # We need ENOUGH eigenvalues for statistics.  N=1000 grid gives ~1000 eigs;
    # we'll keep positive ones, drop edges.
    H, _ = build_H_alpha_prime(N=1000, L=50.0, alpha=1.5, p_max=100,
                               epsilon=1.0, phase_scheme="Z3",
                               ch2=0.95, apply_mech3=True)
    H_dense = H.toarray()
    eigs = np.linalg.eigvalsh(H_dense)
    pos = np.sort(eigs[eigs > 0])
    print(f"Positive eigenvalues: {len(pos)}")
    print(f"Range: [{pos[0]:.4f}, {pos[-1]:.4f}]")

    # Unfold using degree-7 polynomial
    unf = unfold(pos, deg=7, n_drop_edges=20)
    s = spacings(unf)
    print(f"After unfolding + edge-drop: {len(s)} spacings")
    print(f"Mean spacing: {np.mean(s):.4f} (should be ~1)")
    print(f"Var(s):       {np.var(s):.4f}")
    print(f"Compare:")
    print(f"  GUE      Var(s) ~ 0.1781")
    print(f"  GOE      Var(s) ~ 0.2860")
    print(f"  Poisson  Var(s) ~ 1.0000")

    # KS test against Wigner and Poisson CDFs
    from scipy.stats import kstest

    def wigner_cdf(s):
        return 1.0 - np.exp(-4.0 * s**2 / np.pi) * (1.0 + 4.0 * s**2 / np.pi) \
               * 0  # placeholder
    # Manual KS via empirical sort
    s_sorted = np.sort(s)
    F_emp = np.arange(1, len(s) + 1) / len(s)

    # Wigner CDF (numerical from surmise PDF)
    sgrid = np.linspace(0, 5, 10000)
    pdf_w = wigner_surmise(sgrid)
    cdf_w_grid = np.cumsum(pdf_w) * (sgrid[1] - sgrid[0])
    cdf_w_grid /= cdf_w_grid[-1]
    F_w = np.interp(s_sorted, sgrid, cdf_w_grid)
    F_p = 1.0 - np.exp(-s_sorted)
    ks_w = np.max(np.abs(F_emp - F_w))
    ks_p = np.max(np.abs(F_emp - F_p))
    print(f"\nKolmogorov-Smirnov statistic:")
    print(f"  vs Wigner-Dyson GUE:  KS = {ks_w:.4f}")
    print(f"  vs Poisson:           KS = {ks_p:.4f}")
    winner = "GUE (RMT signature)" if ks_w < ks_p else "POISSON (integrable signature)"
    print(f"  -> closer to: {winner}")

    # Histogram and write a text-mode plot
    hist, bin_edges = np.histogram(s, bins=30, range=(0, 4), density=True)
    print(f"\nP(s) histogram (range [0, 4], 30 bins):")
    centers = 0.5 * (bin_edges[:-1] + bin_edges[1:])
    for i in range(len(centers)):
        c = centers[i]
        h = hist[i]
        w = wigner_surmise(c)
        p = poisson(c)
        bar = "#" * int(40 * h)
        print(f"  s={c:.2f}  P_emp={h:.3f}  P_W={w:.3f}  P_P={p:.3f}  {bar}")

    # Save
    with open(os.path.join(HERE, "wigner_dyson_results.pkl"), "wb") as f:
        pickle.dump({"spacings": s, "ks_wigner": ks_w, "ks_poisson": ks_p,
                     "var": float(np.var(s))}, f)


if __name__ == "__main__":
    main()
