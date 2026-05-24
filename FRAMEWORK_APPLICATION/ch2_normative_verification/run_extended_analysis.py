"""
run_extended_analysis.py — Extended Ch 32 verification.

(a) Try multiple normalizations + bases to see if any produce values closer
    to the Ch 32 normative TABLE (not just ordering).
(b) Test monotone nonlinear remap (sigmoid family) — explains whether the
    framework's "ch_2" needs an additional state-mapping step that Ch 32
    glosses over.
(c) Re-run the rank check with bootstrapped CIs.
"""

from __future__ import annotations

import os
import sys
import json
import numpy as np
from scipy.stats import spearmanr, pearsonr
from scipy.optimize import minimize

ROOT = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(ROOT, '..', 'clinical_calibration_search'))
sys.path.insert(0, ROOT)

from calib_core import ch2_generalized, NORMS  # noqa: E402
from sleep_eeg_simulator import (  # noqa: E402
    SleepSpec, GENERATORS, NORMATIVE_TARGETS,
)


PHI = (1.0 + np.sqrt(5.0)) / 2.0
M = 32
T = 8.0
FS = 256.0
N = 25
W = 0.5


def cohort_chvals(alpha: float, base: int, norm_name: str,
                  n_per_class: int = N) -> dict:
    norm_fn = NORMS[norm_name]
    out = {}
    seed = 70_000
    for label, gen in GENERATORS.items():
        vals = []
        for k in range(n_per_class):
            spec = SleepSpec(label=label, M=M, T_sec=T, fs=FS, seed=seed)
            eeg = gen(spec)
            v = ch2_generalized(eeg, fs=FS, alpha=alpha, base=base,
                                 norm_fn=norm_fn, window_sec=W, clip=False)
            vals.append(v)
            seed += 1
        out[label] = np.array(vals)
    return out


def score_against_norms(results: dict) -> dict:
    """Return Spearman/Pearson + best affine R^2."""
    states = list(NORMATIVE_TARGETS.keys())
    x = np.array([float(results[s].mean()) for s in states])
    y = np.array([NORMATIVE_TARGETS[s][0] for s in states])
    sp, _ = spearmanr(x, y)
    pe, _ = pearsonr(x, y)
    # Best affine
    A = np.vstack([x, np.ones_like(x)]).T
    (a, b), *_ = np.linalg.lstsq(A, y, rcond=None)
    resids = a * x + b - y
    r2_affine = float(1.0 - np.sum(resids**2) / np.sum((y - y.mean())**2))
    # Best sigmoid: y = L / (1 + exp(-k*(x - x0)))
    def loss(p):
        L, k, x0 = p
        y_hat = L / (1.0 + np.exp(-k * (x - x0)))
        return float(np.sum((y_hat - y) ** 2))
    res = minimize(loss, x0=[1.0, 10.0, float(x.mean())],
                    method='Nelder-Mead')
    p = res.x
    y_sig = p[0] / (1.0 + np.exp(-p[1] * (x - p[2])))
    r2_sig = float(1.0 - np.sum((y_sig - y) ** 2) / np.sum((y - y.mean())**2))
    return {
        'spearman': float(sp), 'pearson': float(pe),
        'r2_affine': r2_affine,
        'r2_sigmoid': r2_sig,
        'sigmoid_L_k_x0': p.tolist(),
        'x_means': x.tolist(),
        'states': states,
    }


def main():
    configs = [
        ('phi+1/4', PHI + 0.25, 2, 'rms_MB'),    # Wave 9 best
        ('phi+1/4', PHI + 0.25, 3, 'rms_MB'),
        ('phi+1/4', PHI + 0.25, 2, 'literal_MB'),
        ('sqrt2',   np.sqrt(2),  3, 'rms_MB'),
        ('phi',     PHI,         3, 'rms_MB'),
        ('1.5',     1.5,         2, 'rms_MB'),
        ('phi+1/4', PHI + 0.25, 2, 'rms_M'),
        ('phi+1/4', PHI + 0.25, 2, 'M_only'),
    ]
    out = []
    print("=" * 88)
    print("Ch 32 NORMATIVE VERIFICATION — SWEEP OVER (alpha, base, norm)")
    print("=" * 88)
    print(f"{'alpha':<10s} {'base':>4s} {'norm':<12s} "
          f"{'mean min':>9s} {'mean max':>9s} "
          f"{'Spearman':>9s} {'Pearson':>8s} "
          f"{'R^2 aff':>8s} {'R^2 sig':>8s}")
    print("-" * 88)
    for name, alpha, base, norm in configs:
        try:
            res = cohort_chvals(alpha, base, norm)
            sc = score_against_norms(res)
            xmin = float(np.min(sc['x_means']))
            xmax = float(np.max(sc['x_means']))
            print(f"{name:<10s} {base:>4d} {norm:<12s} "
                  f"{xmin:>9.4f} {xmax:>9.4f} "
                  f"{sc['spearman']:>+9.4f} {sc['pearson']:>+8.4f} "
                  f"{sc['r2_affine']:>8.4f} {sc['r2_sigmoid']:>8.4f}")
            out.append({
                'alpha_name': name, 'alpha': float(alpha),
                'base': base, 'norm': norm,
                'x_min': xmin, 'x_max': xmax,
                **sc,
                'per_class_mean': {k: float(v.mean())
                                    for k, v in res.items()},
                'per_class_std': {k: float(v.std())
                                    for k, v in res.items()},
            })
        except Exception as e:
            print(f"{name:<10s} {base:>4d} {norm:<12s}  ERROR: {e}")
    print()

    # Save the sweep
    with open(os.path.join(ROOT, 'sweep_results.json'), 'w') as f:
        json.dump(out, f, indent=2)
    print(f"Saved sweep: {os.path.join(ROOT, 'sweep_results.json')}")

    # For Wave 9 config: print the sigmoid remap
    print()
    print("WAVE 9 CONFIG — SIGMOID REMAP DETAILS")
    print("-" * 88)
    w9 = out[0]
    L, k, x0 = w9['sigmoid_L_k_x0']
    print(f"  Best sigmoid: y = {L:.4f} / (1 + exp(-{k:.4f}*(x - {x0:.4f})))")
    print(f"  R^2 = {w9['r2_sigmoid']:.4f}")
    print(f"  This is the monotone state-mapping the framework would need to")
    print(f"  apply on top of raw ch_2 to reproduce Ch 32 normative values.")


if __name__ == '__main__':
    main()
