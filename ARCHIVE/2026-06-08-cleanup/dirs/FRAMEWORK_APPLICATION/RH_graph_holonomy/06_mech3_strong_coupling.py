"""
06_mech3_strong_coupling.py

Test Mechanism 3 ch_2 = 0.95 special-value hypothesis in the
STRONG-COUPLING regime (no dominant diagonal), using Config A
(pure hopping) where framework Z_3 holonomy actually drives dynamics.

Sweep ch_2 in {0.5, 0.7, 0.85, 0.9, 0.92, 0.95, 0.97, 1.0, 1.05, 1.1}
and look for a sweet spot in spectral statistics.

Also run larger N to see scaling.
"""

import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.sparse as sp
import scipy.linalg as la
from importlib import util

spec = util.spec_from_file_location("strong", os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "05_strong_coupling_limit.py"))
strong = util.module_from_spec(spec)
spec.loader.exec_module(strong)
build_graph_general = strong.build_graph_general
diag_eigs = strong.diag_eigs
spacing_stats = strong.spacing_stats
ZETA_ZEROS = strong.ZETA_ZEROS

OUT = os.path.dirname(os.path.abspath(__file__))


def sweep_ch2_strong(N=20, alpha=1.5):
    diag0 = lambda m, n: 0.0
    print(f"=== Mech3 ch_2 sweep (strong-coupling Config A) N={N} ===")
    print(f"  ch_2  | var(fw) | var(tr) | rms(fw-tr) | rms_zeta_rescaled")
    out = {}
    for ch_2 in [0.50, 0.70, 0.85, 0.90, 0.92, 0.94, 0.95, 0.96, 0.98, 1.00, 1.05, 1.10, 1.20]:
        H_fw = build_graph_general(N, alpha, ch_2, diag0, "framework")
        H_tr = build_graph_general(N, alpha, ch_2, diag0, "trivial")
        w_fw = diag_eigs(H_fw)
        w_tr = diag_eigs(H_tr)
        K = 20
        rms_fw_tr = float(np.sqrt(np.mean((w_fw[:K] - w_tr[:K]) ** 2)))
        st_fw = spacing_stats(w_fw)
        st_tr = spacing_stats(w_tr)
        w_pos = w_fw[w_fw > 0]
        rms_z = None
        if len(w_pos) >= K:
            x = w_pos[:K]
            A = np.vstack([x, np.ones_like(x)]).T
            coef, _, _, _ = np.linalg.lstsq(A, ZETA_ZEROS, rcond=None)
            rms_z = float(np.sqrt(np.mean((coef[0]*x + coef[1] - ZETA_ZEROS)**2)))
        print(f"  {ch_2:.3f} | {st_fw['var']:.3f}  | {st_tr['var']:.3f}  | {rms_fw_tr:.4f}    | {rms_z if rms_z else 'NA'}")
        out[str(ch_2)] = {
            "var_fw": st_fw['var'], "var_tr": st_tr['var'],
            "rms_fw_tr": rms_fw_tr, "rms_zeta_rescaled": rms_z,
        }
    return out


def scaling_strong(alpha=1.5, ch_2=0.95):
    print(f"\n=== Scaling test (strong-coupling Config A) alpha={alpha}, ch_2={ch_2} ===")
    print(f"  N  | dim  | var(fw) | rms(fw-tr) | rms(fw-rnd) | rms_zeta_rescaled")
    diag0 = lambda m, n: 0.0
    out = {}
    rng = np.random.default_rng(0xC0FFEE)
    for N in [10, 15, 20, 25, 30]:
        H_fw = build_graph_general(N, alpha, ch_2, diag0, "framework")
        H_tr = build_graph_general(N, alpha, ch_2, diag0, "trivial")
        H_rnd = build_graph_general(N, alpha, ch_2, diag0, "random", rng=rng)
        w_fw = diag_eigs(H_fw)
        w_tr = diag_eigs(H_tr)
        w_rnd = diag_eigs(H_rnd)
        K = min(20, len(w_fw))
        rms_fw_tr = float(np.sqrt(np.mean((w_fw[:K] - w_tr[:K]) ** 2)))
        rms_fw_rnd = float(np.sqrt(np.mean((w_fw[:K] - w_rnd[:K]) ** 2)))
        st_fw = spacing_stats(w_fw)
        w_pos = w_fw[w_fw > 0]
        rms_z = None
        if len(w_pos) >= K:
            x = w_pos[:K]
            A = np.vstack([x, np.ones_like(x)]).T
            coef, _, _, _ = np.linalg.lstsq(A, ZETA_ZEROS, rcond=None)
            rms_z = float(np.sqrt(np.mean((coef[0]*x + coef[1] - ZETA_ZEROS)**2)))
        print(f"  {N:2d} | {N*N:4d} | {st_fw['var']:.3f}  | {rms_fw_tr:.4f}    | {rms_fw_rnd:.4f}     | {rms_z}")
        out[str(N)] = {
            "dim": N*N, "var_fw": st_fw['var'],
            "rms_fw_tr": rms_fw_tr, "rms_fw_rnd": rms_fw_rnd,
            "rms_zeta_rescaled": rms_z,
        }
    return out


def main():
    r1 = sweep_ch2_strong(N=20)
    r2 = scaling_strong(ch_2=0.95)
    summary = {"mech3_sweep_strong": r1, "scaling_strong": r2}
    with open(os.path.join(OUT, "mech3_strong_summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    print("\nSaved JSON.")


if __name__ == "__main__":
    main()
