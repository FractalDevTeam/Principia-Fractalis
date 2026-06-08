"""
02_diagonalize_and_compare.py

Diagonalize H_alpha^prime at various epsilon and compare top eigenvalues
to the first 20 Riemann zeta zeros (imaginary parts of nontrivial zeros).
"""

import numpy as np
import scipy.sparse.linalg as spla
import pickle
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from importlib import import_module
mod = import_module("01_construct_H_alpha_prime")
build_H_alpha_prime = mod.build_H_alpha_prime

# First 20 nontrivial zeta zero imaginary parts (Odlyzko, well known)
ZETA_ZEROS = np.array([
    14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
    37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478,
    52.970321478, 56.446247697, 59.347044003, 60.831778525, 65.112544048,
    67.079810529, 69.546401711, 72.067157674, 75.704690699, 77.144840069,
])


def top_positive_eigs(H, k=40):
    """Top k eigenvalues by absolute value, then keep positive ones sorted ascending."""
    H_dense = H.toarray()
    # full diagonalization (N=1000 fine)
    vals = np.linalg.eigvalsh(H_dense)
    pos = np.sort(vals[vals > 0])
    return pos[:k]


def compare(eigs_pos, zeros, top=20):
    n = min(top, len(eigs_pos), len(zeros))
    e = eigs_pos[:n]
    z = zeros[:n]
    # Two comparison modes: direct, and rescaled (best-fit linear)
    rms_direct = np.sqrt(np.mean((e - z) ** 2))
    # Best linear scale s minimizing ||s*e - z||
    s_opt = np.dot(e, z) / np.dot(e, e)
    rms_scaled = np.sqrt(np.mean((s_opt * e - z) ** 2))
    rel_scaled = rms_scaled / np.mean(z)
    return {
        "n": n,
        "rms_direct": rms_direct,
        "s_opt": s_opt,
        "rms_scaled": rms_scaled,
        "rel_scaled": rel_scaled,
        "eigs": e,
        "zeros": z,
    }


if __name__ == "__main__":
    N = 1000
    L = 50.0
    alpha = 1.5
    p_max = 100

    print("=" * 72)
    print("DIAGONALIZATION SWEEP: H_alpha^prime, alpha = 3/2 (RH framework)")
    print("=" * 72)

    results = {}
    for eps in [0.1, 0.5, 1.0, 2.0]:
        H, x = build_H_alpha_prime(N=N, L=L, alpha=alpha, p_max=p_max,
                                   epsilon=eps, phase_scheme="Z3",
                                   ch2=0.95, apply_mech3=True)
        eigs = top_positive_eigs(H, k=40)
        cmp = compare(eigs, ZETA_ZEROS, top=20)
        results[eps] = (eigs, cmp)

        print(f"\n--- epsilon = {eps} ---")
        print(f"  top 20 positive eigenvalues:")
        for i, (e, z) in enumerate(zip(cmp["eigs"], cmp["zeros"]), 1):
            print(f"    [{i:2d}]  eig = {e:9.4f}    zeta_zero = {z:9.4f}"
                  f"    diff = {e - z:+8.4f}    ratio = {e/z:.4f}")
        print(f"  RMS (direct):           {cmp['rms_direct']:.4f}")
        print(f"  optimal linear scale:   {cmp['s_opt']:.4f}")
        print(f"  RMS (rescaled):         {cmp['rms_scaled']:.4f}")
        print(f"  relative RMS (rescaled): {cmp['rel_scaled']*100:.2f}%")

    # Save
    with open(os.path.join(HERE, "diagonalization_results.pkl"), "wb") as f:
        pickle.dump(results, f)

    # Honest assessment
    print("\n" + "=" * 72)
    print("HONEST ASSESSMENT")
    print("=" * 72)
    best_eps, (_, best) = min(results.items(), key=lambda kv: kv[1][1]["rel_scaled"])
    print(f"Best epsilon: {best_eps}")
    print(f"  optimal scale s={best['s_opt']:.4f}, rel RMS={best['rel_scaled']*100:.2f}%")
    print(f"  individual match rate (|rel err| < 5%):")
    rel_err = np.abs(best['s_opt'] * best['eigs'] - best['zeros']) / best['zeros']
    n_good = int(np.sum(rel_err < 0.05))
    print(f"    {n_good}/{best['n']}  good matches")
