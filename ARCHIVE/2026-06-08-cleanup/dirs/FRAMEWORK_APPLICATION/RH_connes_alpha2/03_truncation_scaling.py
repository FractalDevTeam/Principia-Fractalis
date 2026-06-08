"""
Truncation scaling test: do framework R_f-modulated eigenvalues
APPROACH zeta zeros as L -> infinity?

This is THE critical test. For each potential, sweep L in {20, 50, 100, 200}
at constant grid density (du ~ 0.05), holding ch_2 = 0.95 (Mechanism 3
transition point). Track RMS vs zeros.

If RMS DECREASES monotonically with L, the framework's R_f anchor INJECTS
the number-theoretic content of zeta zeros.

If RMS plateaus or grows, the framework's coupling at alpha=2 does NOT
operationally close Connes's scaling-spectrum identification.

Author: Pablo Cohen + Claude (Wave 11)
Date: 2026-05-23
"""

import numpy as np
import mpmath as mp
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from importlib import import_module

mod = import_module("02_Rf_modulated_alpha2")

OUT_DIR = os.path.dirname(os.path.abspath(__file__))


def main():
    mp.mp.dps = 25
    DU_TARGET = 0.05  # grid step
    EPS = 1.0
    CH2 = 0.95

    results = []
    for L in [20.0, 50.0, 100.0, 200.0]:
        N = int(L / DU_TARGET) - 1
        # Cap N for memory
        if N > 4000:
            N = 4000
        print(f"\n=== L={L}, N={N}, du={L/(N+1):.4f} ===")
        for pot in ["bare", "Rf_at_2", "prime_mod", "one_over_zeta_sq"]:
            r = mod.run_experiment(L, N, pot, EPS, CH2)
            results.append(r)
            print(
                f"  pot={pot:<18} RMS_zeros={r['rms_vs_zeros']:8.3f}  "
                f"KS_GUE={r['wd_stats']['ks_to_GUE']:.3f}  "
                f"top_eig={r['eigs'][0]:.3f} (zero1=14.135)"
            )

    with open(os.path.join(OUT_DIR, "results_03_truncation.json"), "w") as f:
        json.dump(results, f, indent=2)

    # Summary table
    print("\n\n========== TRUNCATION SCALING SUMMARY ==========")
    print(f"{'pot':<20}{'L=20':<12}{'L=50':<12}{'L=100':<12}{'L=200':<12}")
    by_pot = {}
    for r in results:
        by_pot.setdefault(r["pot"], {})[r["L"]] = r["rms_vs_zeros"]
    for pot, vals in by_pot.items():
        row = f"{pot:<20}"
        for L in [20.0, 50.0, 100.0, 200.0]:
            row += f"{vals.get(L, np.nan):<12.3f}"
        print(row)


if __name__ == "__main__":
    main()
