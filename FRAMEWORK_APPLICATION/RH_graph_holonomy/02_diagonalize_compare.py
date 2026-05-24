"""
02_diagonalize_compare.py

Diagonalize H_graph (framework, random, trivial phase variants) at
alpha=3/2, ch_2=0.95, and compare top eigenvalues to first ~20
non-trivial zeros of zeta.

Key questions:
  1) Does the spectrum DIFFER between framework / random / trivial?
     (gauge-non-invariance test — must succeed for plaquette holonomy
      to be a real physical effect)
  2) Do framework eigenvalues approximate the first ~20 zeta zeros?
  3) RMS error vs zeta zeros.
"""

import numpy as np
import scipy.sparse as sp
import scipy.linalg as la
import pickle
import os
import json

OUT = os.path.dirname(os.path.abspath(__file__))


# First 20 Im(zeta_zero) values from Odlyzko
ZETA_ZEROS = np.array([
    14.134725141734693, 21.022039638771555, 25.010857580145688,
    30.424876125859513, 32.935061587739190, 37.586178158825671,
    40.918719012147495, 43.327073280914999, 48.005150881167160,
    49.773832477672302, 52.970321477714460, 56.446247697063394,
    59.347044002602353, 60.831778524609810, 65.112544048081607,
    67.079810529494173, 69.546401711173980, 72.067157674481907,
    75.704690699083933, 77.144840068874806,
])


def load_built():
    with open(os.path.join(OUT, "H_graph_built.pkl"), "rb") as f:
        return pickle.load(f)


def diagonalize(H_sparse):
    H = H_sparse.toarray().astype(np.complex128)
    # Symmetrize numerically
    H = 0.5 * (H + H.conj().T)
    w = la.eigvalsh(H)
    return np.sort(w)


def spectrum_lower_band(w, k):
    return w[:k]


def main():
    blob = load_built()
    H_fw = blob["H_framework"]
    H_rnd = blob["H_random"]
    H_tr = blob["H_trivial"]
    N = blob["N"]
    alpha = blob["alpha"]
    ch_2 = blob["ch_2"]
    print(f"Loaded: N={N}, dim={N*N}, alpha={alpha}, ch_2={ch_2}")

    print("\nDiagonalizing (dense, Hermitian)...")
    w_fw = diagonalize(H_fw)
    w_rnd = diagonalize(H_rnd)
    w_tr = diagonalize(H_tr)
    print(f"  framework spectrum range: [{w_fw[0]:.4f}, {w_fw[-1]:.4f}]")
    print(f"  random    spectrum range: [{w_rnd[0]:.4f}, {w_rnd[-1]:.4f}]")
    print(f"  trivial   spectrum range: [{w_tr[0]:.4f}, {w_tr[-1]:.4f}]")

    K = 20

    # Gauge-non-invariance test: compare bottom-K spectra
    print(f"\n--- Gauge-non-invariance test (first {K} eigenvalues) ---")
    fw_low = spectrum_lower_band(w_fw, K)
    rnd_low = spectrum_lower_band(w_rnd, K)
    tr_low = spectrum_lower_band(w_tr, K)

    diff_fw_rnd = np.abs(fw_low - rnd_low)
    diff_fw_tr = np.abs(fw_low - tr_low)
    diff_rnd_tr = np.abs(rnd_low - tr_low)
    print(f"  RMS |framework - random | = {np.sqrt(np.mean(diff_fw_rnd**2)):.4f}")
    print(f"  RMS |framework - trivial| = {np.sqrt(np.mean(diff_fw_tr**2)):.4f}")
    print(f"  RMS |random    - trivial| = {np.sqrt(np.mean(diff_rnd_tr**2)):.4f}")

    print(f"\n  k |   framework |     random   |    trivial   |  fw-tr  |  fw-rnd")
    for k in range(K):
        print(f"  {k:2d} | {fw_low[k]:+10.4f} | {rnd_low[k]:+10.4f} | {tr_low[k]:+10.4f} | {fw_low[k]-tr_low[k]:+7.4f} | {fw_low[k]-rnd_low[k]:+7.4f}")

    # zeta zeros comparison
    # Strategy: framework eigenvalues are absolute values around Berry-Keating scaling.
    # Shift by minimum eigenvalue and compare lowest positive part to zeta_zeros (sorted).
    print(f"\n--- Comparing framework lower-band eigenvalues to first {K} zeta zeros ---")
    # Try absolute eigenvalues (since H is Hermitian and may have negatives)
    fw_pos = w_fw[w_fw > 0][:K]
    print(f"  framework positive eigenvalues (lowest {K}):")
    print(f"  {fw_pos}")
    print(f"  zeta zeros: {ZETA_ZEROS[:K]}")

    if len(fw_pos) >= K:
        diff = fw_pos - ZETA_ZEROS
        rel = diff / ZETA_ZEROS
        rms_abs = np.sqrt(np.mean(diff**2))
        rms_rel = np.sqrt(np.mean(rel**2))
        print(f"\n  k | framework_pos |   zeta_zero  |  diff       |  rel%")
        for k in range(K):
            print(f"  {k:2d} | {fw_pos[k]:+13.4f} | {ZETA_ZEROS[k]:+12.4f} | {diff[k]:+10.4f} | {100*rel[k]:+7.2f}")
        print(f"\n  RMS abs error: {rms_abs:.4f}")
        print(f"  RMS rel error: {100*rms_rel:.2f}%")

    # Save
    out = {
        "eigvals_framework_full": w_fw,
        "eigvals_random_full": w_rnd,
        "eigvals_trivial_full": w_tr,
        "K": K,
        "N": N,
        "alpha": alpha,
        "ch_2": ch_2,
        "ZETA_ZEROS": ZETA_ZEROS,
    }
    path = os.path.join(OUT, "diagonalization_results.pkl")
    with open(path, "wb") as f:
        pickle.dump(out, f)
    print(f"\nSaved: {path}")

    # Also save JSON summary
    summary = {
        "N": int(N),
        "alpha": float(alpha),
        "ch_2": float(ch_2),
        "rms_framework_minus_random": float(np.sqrt(np.mean(diff_fw_rnd**2))),
        "rms_framework_minus_trivial": float(np.sqrt(np.mean(diff_fw_tr**2))),
        "rms_random_minus_trivial": float(np.sqrt(np.mean(diff_rnd_tr**2))),
        "framework_first_20_low": fw_low.tolist(),
        "trivial_first_20_low": tr_low.tolist(),
        "random_first_20_low": rnd_low.tolist(),
        "framework_first_20_positive": fw_pos[:K].tolist() if len(fw_pos) >= K else fw_pos.tolist(),
        "zeta_zeros_first_20": ZETA_ZEROS.tolist(),
    }
    if len(fw_pos) >= K:
        summary["rms_framework_vs_zeta_abs"] = float(rms_abs)
        summary["rms_framework_vs_zeta_rel_pct"] = float(100 * rms_rel)

    with open(os.path.join(OUT, "diagonalization_summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print(f"Saved JSON summary.")


if __name__ == "__main__":
    main()
