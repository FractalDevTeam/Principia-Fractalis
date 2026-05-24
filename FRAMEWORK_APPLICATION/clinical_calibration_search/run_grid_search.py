"""
run_grid_search.py — full (NORM, alpha, base) grid search on 100-patient cohort.

Reuses yesterday's synthetic generators. For each combo:
  - compute ch_2 across cohort
  - find optimal threshold (binary: conscious+LIS vs coma+veg)
  - report best accuracy + sensitivity/specificity + Cohen's d
"""

import sys
import os
import time
import json
import numpy as np

HERE = os.path.dirname(__file__)
sys.path.insert(0, HERE)
from calib_core import (NORMS, ALPHAS, BASES, make_cohort,
                         evaluate_calibration)


def main():
    print("=" * 78)
    print("CLINICAL ch_2 CALIBRATION GRID SEARCH")
    print("=" * 78)
    print("Cohort: 20 patients x 5 classes = 100 synthetic EEGs")
    print(f"NORMs ({len(NORMS)}): {list(NORMS.keys())}")
    print(f"alphas ({len(ALPHAS)}): {list(ALPHAS.keys())}")
    print(f"bases ({len(BASES)}): {BASES}")
    print(f"TOTAL combinations: {len(NORMS) * len(ALPHAS) * len(BASES)}")
    print()

    t0 = time.time()
    print("Building cohort (no noise, M=32, T=5s, fs=256)...")
    cohort = make_cohort(n_per_class=20, M=32, T_sec=5.0, fs=256.0,
                          snr_db=None, seed_base=20000)
    print(f"  done in {time.time()-t0:.1f}s")
    print()

    results = []
    total = len(NORMS) * len(ALPHAS) * len(BASES)
    idx = 0
    for norm_name in NORMS:
        for alpha_name, alpha_val in ALPHAS.items():
            for base in BASES:
                idx += 1
                t1 = time.time()
                res = evaluate_calibration(
                    cohort, fs=256.0, alpha=alpha_val, base=base,
                    norm_name=norm_name,
                )
                row = {
                    "norm": norm_name,
                    "alpha_name": alpha_name,
                    "alpha_val": float(alpha_val),
                    "base": base,
                    "best_thr": res["best_thr"],
                    "best_acc": res["best_acc"],
                    "sens": res["best_sens"],
                    "spec": res["best_spec"],
                    "cohen_d": res["cohen_d"],
                    "pos_mean": res["pos_mean"],
                    "neg_mean": res["neg_mean"],
                }
                results.append(row)
                print(f"[{idx:3d}/{total}] norm={norm_name:11s} "
                      f"alpha={alpha_name:13s} base={base} | "
                      f"acc={row['best_acc']*100:5.1f}%  "
                      f"d={row['cohen_d']:5.2f}  "
                      f"thr={row['best_thr']:8.4g}  "
                      f"({time.time()-t1:.1f}s)")

    print()
    print("=" * 78)
    print("TOP 15 BY BINARY ACCURACY")
    print("=" * 78)
    results.sort(key=lambda r: (-r["best_acc"], -r["cohen_d"]))
    print(f"{'rank':>4s}  {'norm':<11s} {'alpha':<13s} {'base':>4s}  "
          f"{'acc':>6s}  {'d':>5s}  {'thr':>10s}  "
          f"{'pos_mu':>10s}  {'neg_mu':>10s}")
    print("-" * 90)
    for i, r in enumerate(results[:15]):
        print(f"{i+1:>4d}  {r['norm']:<11s} {r['alpha_name']:<13s} "
              f"{r['base']:>4d}  {r['best_acc']*100:>5.1f}%  "
              f"{r['cohen_d']:>5.2f}  {r['best_thr']:>10.4g}  "
              f"{r['pos_mean']:>10.4g}  {r['neg_mean']:>10.4g}")

    # Save full results
    out_path = os.path.join(HERE, "grid_search_results.json")
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print()
    print(f"Saved full results -> {out_path}")
    print(f"Total time: {time.time()-t0:.1f}s")
    return results


if __name__ == "__main__":
    main()
