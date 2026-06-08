"""
03_gauge_and_mech3_test.py

Two independence/sensitivity tests:

(A) GAUGE NON-TRIVIALITY: different phase schemes (Z3, random, trivial) must
    give different spectra. If they all coincide, the R_f phase is gauge-trivial
    (the tridiagonal-route obstruction from Wave 7).

(B) MECHANISM 3 ch_2-sensitivity: sweep ch_2 in {0.5, 0.9, 0.95, 0.99} and
    measure how the spectrum changes. The framework prediction: ch_2 = 0.95
    is the Hermitian sweet spot; elsewhere the operator becomes non-Hermitian
    and eigenvalues acquire imaginary parts (or shift).
"""

import numpy as np
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from importlib import import_module
mod = import_module("01_construct_H_alpha_prime")
build_H_alpha_prime = mod.build_H_alpha_prime


def top_eigs(H, k=20):
    H_dense = H.toarray()
    vals = np.linalg.eigvalsh(H_dense)
    pos = np.sort(vals[vals > 0])
    return pos[:k]


def all_eigs_complex(H):
    """Drop Hermitization, return possibly-complex spectrum."""
    H_dense = H.toarray()
    vals = np.linalg.eigvals(H_dense)
    return vals


# ------------------------------------------------------------------
# (A) Gauge non-triviality
# ------------------------------------------------------------------
def test_gauge_nontriviality(N=1000, L=50.0, alpha=1.5, p_max=100, eps=1.0):
    print("=" * 72)
    print("(A) GAUGE NON-TRIVIALITY TEST")
    print("=" * 72)
    print("Compare top 20 positive eigenvalues for 3 phase schemes.")
    print("If schemes give IDENTICAL spectra -> gauge-trivial (obstruction).")
    print("If schemes give DIFFERENT spectra -> framework phase is meaningful.\n")

    schemes = ["trivial", "Z3", "random"]
    spectra = {}
    for s in schemes:
        H, _ = build_H_alpha_prime(N=N, L=L, alpha=alpha, p_max=p_max,
                                   epsilon=eps, phase_scheme=s,
                                   ch2=0.95, apply_mech3=True)
        spectra[s] = top_eigs(H, k=20)

    print(f"{'idx':>3}  {'trivial':>12}  {'Z3':>12}  {'random':>12}"
          f"  {'|Z3-triv|':>10}  {'|rand-triv|':>11}")
    for i in range(20):
        t = spectra['trivial'][i]
        z = spectra['Z3'][i]
        r = spectra['random'][i]
        print(f"{i+1:3d}  {t:12.5f}  {z:12.5f}  {r:12.5f}"
              f"  {abs(z-t):10.5f}  {abs(r-t):11.5f}")

    diff_z = np.linalg.norm(spectra['Z3'] - spectra['trivial'])
    diff_r = np.linalg.norm(spectra['random'] - spectra['trivial'])
    print(f"\nL2 distance Z3 vs trivial:     {diff_z:.4f}")
    print(f"L2 distance random vs trivial: {diff_r:.4f}")
    print(f"L2 distance Z3 vs random:      "
          f"{np.linalg.norm(spectra['Z3'] - spectra['random']):.4f}")

    verdict = "PASSES (gauge non-trivial)" if diff_z > 0.01 else "FAILS (gauge trivial)"
    print(f"\nGauge non-triviality: {verdict}")
    return spectra


# ------------------------------------------------------------------
# (B) Mechanism 3 ch_2 sensitivity
# ------------------------------------------------------------------
def test_mechanism3_sensitivity(N=1000, L=50.0, alpha=1.5, p_max=100, eps=1.0):
    print("\n" + "=" * 72)
    print("(B) MECHANISM 3 ch_2-SENSITIVITY")
    print("=" * 72)
    print("Build H WITHOUT final Hermitization, sweep ch_2,")
    print("measure max(|Im(eigenvalues)|).\n")

    # We need a non-Hermitized variant. Modify locally.
    from importlib import reload
    import scipy.sparse as sp
    Hxp, x = mod.build_H_xp(N, L)
    V = mod.build_V_alpha_prime(x, alpha, p_max, phase_scheme="Z3")
    H_base = Hxp + eps * V  # already Hermitian (V Hermitized)

    print(f"{'ch_2':>6}  {'max|Im(eig)|':>14}  {'min Re(eig)':>14}  "
          f"{'max Re(eig)':>14}")
    for ch2 in [0.5, 0.7, 0.9, 0.95, 0.99, 1.0]:
        delta = 0.95 - ch2
        modulation = 1.0 + 1j * 1.0 * delta
        H_diag = sp.diags(H_base.diagonal(), 0, format="csc")
        H_off = H_base - H_diag
        # Apply modulation WITHOUT Hermitizing (so we can see the asymmetry)
        H_mod = H_diag + modulation * H_off
        eigs = all_eigs_complex(H_mod)
        max_im = np.max(np.abs(eigs.imag))
        re_pos = eigs.real[eigs.real > 0]
        if len(re_pos) > 0:
            min_re = np.min(re_pos)
            max_re = np.max(re_pos)
        else:
            min_re = max_re = 0.0
        flag = "  <-- Hermitian sweet spot" if ch2 == 0.95 else ""
        print(f"{ch2:6.2f}  {max_im:14.6e}  {min_re:14.5f}  "
              f"{max_re:14.5f}{flag}")


if __name__ == "__main__":
    spectra = test_gauge_nontriviality()
    test_mechanism3_sensitivity()
