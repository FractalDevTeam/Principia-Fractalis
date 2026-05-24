"""
04_mech3_and_scaling.py

(a) Mechanism 3 cross-domain consistency test:
    Sweep ch_2 in {0.7, 0.8, 0.9, 0.95, 1.0, 1.05} and check whether
    framework spectrum statistics show a sweet spot at ch_2 = 0.95.

(b) Scaling test with larger N:
    Build N=25 and N=30 framework graphs, verify
    gauge non-invariance persists (rms framework - trivial grows with N).
"""

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np
import scipy.linalg as la
import json
from collections import defaultdict

from importlib import import_module
spec = __import__("importlib.util").util.spec_from_file_location(
    "construct", os.path.join(os.path.dirname(os.path.abspath(__file__)), "01_construct_H_graph.py"))
construct = __import__("importlib.util").util.module_from_spec(spec)
spec.loader.exec_module(construct)

build_H_graph = construct.build_H_graph

OUT = os.path.dirname(os.path.abspath(__file__))


def diag(H):
    Hd = H.toarray().astype(np.complex128)
    Hd = 0.5 * (Hd + Hd.conj().T)
    return np.sort(la.eigvalsh(Hd))


def gue_test_stat(spacings):
    """variance ratio: var(s)/0.180 for GUE; smaller (closer to 1) = more GUE-like."""
    return np.var(spacings) / 0.180


def spectrum_stats(w, deg=8, trim_frac=0.1):
    w = np.sort(w)
    n = len(w)
    lo = int(trim_frac * n)
    hi = int((1 - trim_frac) * n)
    bulk = w[lo:hi]
    cumN = np.arange(1, len(bulk) + 1, dtype=float)
    coeffs = np.polyfit(bulk, cumN, deg)
    p = np.poly1d(coeffs)
    unf = p(bulk)
    s = np.diff(unf)
    s = s / np.mean(s)
    return {
        "var": float(np.var(s)),
        "mean": float(np.mean(s)),
        "n_spacings": int(len(s)),
        "first_eigval": float(w[0]),
        "last_eigval": float(w[-1]),
    }


def mech3_sweep():
    print("=" * 60)
    print("Mechanism 3 sweep: ch_2 -> spectrum statistics")
    print("=" * 60)
    N = 20
    alpha = 1.5
    results = {}
    rng = np.random.default_rng(0xFA)
    for ch_2 in [0.50, 0.70, 0.85, 0.90, 0.95, 1.00, 1.05, 1.10, 1.20]:
        H_fw, _, _ = build_H_graph(N, alpha, ch_2=ch_2, phase_mode="framework")
        H_tr, _, _ = build_H_graph(N, alpha, ch_2=ch_2, phase_mode="trivial")
        w_fw = diag(H_fw)
        w_tr = diag(H_tr)
        K = 20
        diff_K = np.sqrt(np.mean((w_fw[:K] - w_tr[:K])**2))
        # full spectrum L2
        diff_full = np.sqrt(np.mean((w_fw - w_tr)**2))
        # GUE-like-ness of framework spectrum
        st_fw = spectrum_stats(w_fw)
        st_tr = spectrum_stats(w_tr)
        results[ch_2] = {
            "diff_low20_rms": float(diff_K),
            "diff_full_rms": float(diff_full),
            "framework_var": st_fw["var"],
            "trivial_var": st_tr["var"],
        }
        print(f"  ch_2={ch_2:.3f}  rms(fw-tr) low20={diff_K:.4f}  full={diff_full:.4f}  var(fw)={st_fw['var']:.3f}  var(tr)={st_tr['var']:.3f}")
    return results


def scaling_test():
    print("\n" + "=" * 60)
    print("Scaling test: does gauge non-invariance persist with N?")
    print("=" * 60)
    alpha = 1.5
    ch_2 = 0.95
    rng = np.random.default_rng(0xC0)
    results = {}
    for N in [10, 15, 20, 25]:
        H_fw, _, _ = build_H_graph(N, alpha, ch_2=ch_2, phase_mode="framework")
        H_tr, _, _ = build_H_graph(N, alpha, ch_2=ch_2, phase_mode="trivial")
        H_rnd, _, _ = build_H_graph(N, alpha, ch_2=ch_2, phase_mode="random", rng=rng)
        w_fw = diag(H_fw)
        w_tr = diag(H_tr)
        w_rnd = diag(H_rnd)
        K = min(20, len(w_fw))
        rms_fw_tr = float(np.sqrt(np.mean((w_fw[:K] - w_tr[:K])**2)))
        rms_fw_rnd = float(np.sqrt(np.mean((w_fw[:K] - w_rnd[:K])**2)))
        st_fw = spectrum_stats(w_fw)
        results[N] = {
            "dim": int(N * N),
            "rms_fw_tr": rms_fw_tr,
            "rms_fw_rnd": rms_fw_rnd,
            "var_unfolded_fw": st_fw["var"],
            "first_eigval": st_fw["first_eigval"],
            "last_eigval": st_fw["last_eigval"],
        }
        print(f"  N={N:2d} (dim={N*N:4d})  rms(fw-tr)={rms_fw_tr:.4f}  rms(fw-rnd)={rms_fw_rnd:.4f}  var(unfolded)={st_fw['var']:.3f}")
    return results


def diagonal_dominance_diagnostic():
    """Quick diagnostic: is the diagonal so large the off-diagonals barely move things?"""
    print("\n" + "=" * 60)
    print("Diagonal-vs-off-diagonal magnitude diagnostic")
    print("=" * 60)
    N = 20
    alpha = 1.5
    for ch_2 in [0.95, 5.0, 50.0]:
        H, _, _ = build_H_graph(N, alpha, ch_2=ch_2, phase_mode="framework")
        Hd = H.toarray()
        diag_avg = np.mean(np.abs(np.diag(Hd)))
        offdiag_avg = np.mean(np.abs(Hd - np.diag(np.diag(Hd))))
        # diagonal sets scale; off-diag is a perturbation
        print(f"  ch_2={ch_2}:  |diag|_avg={diag_avg:.3f}  |offdiag|_avg={offdiag_avg:.3f}  ratio={offdiag_avg/diag_avg:.4f}")


def main():
    r1 = mech3_sweep()
    r2 = scaling_test()
    diagonal_dominance_diagnostic()
    summary = {
        "mech3_sweep": {str(k): v for k, v in r1.items()},
        "scaling_test": {str(k): v for k, v in r2.items()},
    }
    with open(os.path.join(OUT, "mech3_scaling_summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print("\nSaved JSON summary.")


if __name__ == "__main__":
    main()
