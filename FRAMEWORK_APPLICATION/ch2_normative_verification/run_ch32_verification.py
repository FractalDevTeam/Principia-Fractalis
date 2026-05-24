"""
run_ch32_verification.py — Test Ch 32 normative ch_2 predictions on
biologically-realistic synthetic EEG using the Wave 9 corrected formula.

Wave 9 corrected formula:
  alpha = phi + 1/4   (NP-class)
  base  = 2
  norm  = 1/sqrt(M*B)  (rms_MB)

Ch 32 normative targets (mean ± std), n=1247 healthy volunteers:
  awake_resting : 0.973 ± 0.018
  rem_sleep     : 0.947 ± 0.041
  n1_drowsy     : 0.891
  n2_light      : 0.672
  n3_deep       : 0.387 ± 0.121
  meditation    : 0.989 ± 0.008
"""

from __future__ import annotations

import os
import sys
import json
import numpy as np
from collections import defaultdict
from sklearn.discriminant_analysis import LinearDiscriminantAnalysis
from sklearn.model_selection import StratifiedKFold

# Make the Wave 9 core importable
ROOT = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(ROOT, '..', 'clinical_calibration_search'))
sys.path.insert(0, ROOT)

from calib_core import ch2_generalized, NORMS  # noqa: E402
from sleep_eeg_simulator import (  # noqa: E402
    SleepSpec, GENERATORS, NORMATIVE_TARGETS,
)


# Wave 9 corrected formula parameters
PHI = (1.0 + np.sqrt(5.0)) / 2.0
ALPHA = PHI + 0.25         # NP-class
BASE = 2                   # corrected base
NORM_FN = NORMS['rms_MB']  # 1/sqrt(M*B)
WINDOW_SEC = 0.5
M_CHANNELS = 32
T_SEC = 8.0
FS = 256.0
N_PER_CLASS = 30           # cohort size per state


def run_cohort(n_per_class: int = N_PER_CLASS,
               M: int = M_CHANNELS,
               T_sec: float = T_SEC,
               fs: float = FS,
               seed_base: int = 50_000) -> dict:
    """Generate cohort + compute ch_2 for each subject in each state."""
    results = {label: [] for label in GENERATORS}
    seed = seed_base
    for label, gen in GENERATORS.items():
        for k in range(n_per_class):
            spec = SleepSpec(label=label, M=M, T_sec=T_sec, fs=fs, seed=seed)
            eeg = gen(spec)
            ch2 = ch2_generalized(eeg, fs=fs, alpha=ALPHA, base=BASE,
                                   norm_fn=NORM_FN, window_sec=WINDOW_SEC,
                                   clip=False)
            results[label].append(ch2)
            seed += 1
    return {k: np.array(v) for k, v in results.items()}


def summarize_per_class(results: dict) -> dict:
    """Compare each class mean/std to the Ch 32 normative target."""
    rows = []
    for label, values in results.items():
        target_mean, target_std = NORMATIVE_TARGETS[label]
        obs_mean = float(values.mean())
        obs_std = float(values.std())
        diff = obs_mean - target_mean
        # z-distance of observed mean from target, in units of target_std
        z = diff / target_std if target_std > 0 else float('inf')
        rows.append({
            'state': label,
            'obs_mean': obs_mean,
            'obs_std': obs_std,
            'target_mean': target_mean,
            'target_std': target_std,
            'diff': diff,
            'z_vs_target': z,
            'within_1sigma': abs(z) <= 1.0,
            'within_3sigma': abs(z) <= 3.0,
        })
    return rows


def linear_rescale_to_targets(results: dict) -> dict:
    """
    Find best-fit affine map y = a*x + b mapping observed means to Ch 32 targets.
    Returns (a, b, residuals_per_class, rescaled_means).
    """
    states = list(results.keys())
    x = np.array([float(results[s].mean()) for s in states])
    y = np.array([NORMATIVE_TARGETS[s][0] for s in states])
    # Least squares: y = a*x + b
    A = np.vstack([x, np.ones_like(x)]).T
    (a, b), *_ = np.linalg.lstsq(A, y, rcond=None)
    rescaled = a * x + b
    resids = rescaled - y
    return {
        'a': float(a), 'b': float(b),
        'states': states,
        'x_obs': x.tolist(),
        'y_target': y.tolist(),
        'y_rescaled': rescaled.tolist(),
        'residuals': resids.tolist(),
        'max_abs_residual': float(np.max(np.abs(resids))),
        'r2': float(1.0 - np.sum(resids**2) / np.sum((y - y.mean())**2)),
    }


def confusion_matrix_5class(results: dict) -> dict:
    """
    Build a 5-class confusion matrix via stratified LDA cross-validation.
    Treats each per-state ch_2 sample as a 1-feature observation.
    (Single-feature LDA = thresholded NCM; we use it as a fair baseline.)
    """
    labels = list(results.keys())
    X = []
    y = []
    for i, lab in enumerate(labels):
        for v in results[lab]:
            X.append([v])
            y.append(i)
    X = np.array(X)
    y = np.array(y)
    cm = np.zeros((len(labels), len(labels)), dtype=int)
    skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=0)
    accs = []
    for tr, te in skf.split(X, y):
        lda = LinearDiscriminantAnalysis()
        lda.fit(X[tr], y[tr])
        pred = lda.predict(X[te])
        for true_idx, pred_idx in zip(y[te], pred):
            cm[true_idx, pred_idx] += 1
        accs.append(float((pred == y[te]).mean()))
    return {
        'labels': labels,
        'matrix': cm.tolist(),
        'acc_mean': float(np.mean(accs)),
        'acc_std': float(np.std(accs)),
    }


def main():
    print("=" * 78)
    print("Ch 32 NORMATIVE VERIFICATION — Wave 9 corrected formula")
    print(f"  alpha = phi + 1/4 = {ALPHA:.6f}")
    print(f"  base  = {BASE}")
    print(f"  norm  = 1/sqrt(M*B) (rms_MB)")
    print(f"  M={M_CHANNELS}, T={T_SEC}s, fs={FS}Hz, "
          f"n_per_class={N_PER_CLASS}")
    print("=" * 78)
    print()

    print(f"Generating cohort... ({N_PER_CLASS * len(GENERATORS)} subjects)")
    results = run_cohort()
    print("Done.\n")

    # 1. Per-class comparison to Ch 32 normative targets
    print("PER-CLASS COMPARISON TO Ch 32 NORMATIVE TABLE")
    print("-" * 78)
    print(f"{'state':<16s} {'obs mean':>10s} {'obs std':>9s} "
          f"{'target':>10s} {'tgt std':>9s} {'diff':>9s} {'z':>7s} "
          f"{'<1sig':>6s} {'<3sig':>6s}")
    rows = summarize_per_class(results)
    for r in rows:
        print(f"{r['state']:<16s} {r['obs_mean']:>10.4f} {r['obs_std']:>9.4f} "
              f"{r['target_mean']:>10.4f} {r['target_std']:>9.4f} "
              f"{r['diff']:>+9.4f} {r['z_vs_target']:>+7.2f} "
              f"{str(r['within_1sigma']):>6s} {str(r['within_3sigma']):>6s}")
    print()

    # 2. Linear rescale to targets
    print("BEST-FIT AFFINE RESCALING (y = a*x + b → Ch 32 targets)")
    print("-" * 78)
    fit = linear_rescale_to_targets(results)
    print(f"  a = {fit['a']:+.6f}    b = {fit['b']:+.6f}")
    print(f"  R^2 = {fit['r2']:.4f}    max|residual| = {fit['max_abs_residual']:.4f}")
    for s, x, y, yr, res in zip(fit['states'], fit['x_obs'],
                                  fit['y_target'], fit['y_rescaled'],
                                  fit['residuals']):
        print(f"    {s:<16s} obs={x:.4f}  tgt={y:.4f}  "
              f"resc={yr:.4f}  resid={res:+.4f}")
    print()

    # 3. State-ordering check (rank correlation)
    print("STATE-ORDERING CHECK (Spearman + Pearson on means)")
    print("-" * 78)
    from scipy.stats import spearmanr, pearsonr
    states = list(results.keys())
    x = np.array([float(results[s].mean()) for s in states])
    y = np.array([NORMATIVE_TARGETS[s][0] for s in states])
    sp_r, sp_p = spearmanr(x, y)
    pe_r, pe_p = pearsonr(x, y)
    print(f"  Spearman rho = {sp_r:+.4f}   p = {sp_p:.4f}")
    print(f"  Pearson  r   = {pe_r:+.4f}   p = {pe_p:.4f}")
    print()

    # 4. 5-class confusion matrix
    # (Drop meditation for true 5-class to match the question's '5-class')
    # Actually the question listed all six. Do BOTH a 6-class and 5-class.
    print("6-CLASS CONFUSION (LDA on ch_2 alone, 5-fold CV)")
    print("-" * 78)
    cm6 = confusion_matrix_5class(results)
    print(f"  Accuracy = {cm6['acc_mean']:.4f} +/- {cm6['acc_std']:.4f}")
    labels = cm6['labels']
    print(f"  {'true \\ pred':<16s}" + ''.join(f"{l[:8]:>10s}" for l in labels))
    for i, lab in enumerate(labels):
        print(f"  {lab:<16s}" + ''.join(
            f"{cm6['matrix'][i][j]:>10d}" for j in range(len(labels))))
    print()

    # 5-class (drop the most-similar pair; we drop awake vs meditation
    # ambiguity by dropping meditation in this view)
    states5 = ['awake_resting', 'rem_sleep', 'n1_drowsy', 'n2_light', 'n3_deep']
    res5 = {s: results[s] for s in states5}
    print("5-CLASS CONFUSION (drop meditation) (LDA on ch_2 alone, 5-fold CV)")
    print("-" * 78)
    cm5 = confusion_matrix_5class(res5)
    print(f"  Accuracy = {cm5['acc_mean']:.4f} +/- {cm5['acc_std']:.4f}")
    labels5 = cm5['labels']
    print(f"  {'true \\ pred':<16s}" + ''.join(f"{l[:8]:>10s}" for l in labels5))
    for i, lab in enumerate(labels5):
        print(f"  {lab:<16s}" + ''.join(
            f"{cm5['matrix'][i][j]:>10d}" for j in range(len(labels5))))
    print()

    # Save full results
    out = {
        'config': {
            'alpha': float(ALPHA),
            'base': int(BASE),
            'norm': 'rms_MB',
            'M': M_CHANNELS,
            'T_sec': T_SEC,
            'fs': FS,
            'n_per_class': N_PER_CLASS,
            'window_sec': WINDOW_SEC,
        },
        'per_class': {k: v.tolist() for k, v in results.items()},
        'summary': rows,
        'affine_fit': fit,
        'spearman': {'rho': float(sp_r), 'p': float(sp_p)},
        'pearson': {'r': float(pe_r), 'p': float(pe_p)},
        'confusion_6class': cm6,
        'confusion_5class': cm5,
    }
    out_path = os.path.join(ROOT, 'ch32_results.json')
    with open(out_path, 'w') as f:
        json.dump(out, f, indent=2)
    print(f"Full results saved to: {out_path}")


if __name__ == '__main__':
    main()
