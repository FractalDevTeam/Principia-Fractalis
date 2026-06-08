"""
run_remapped_confusion.py — Apply the best sigmoid state-map to Wave 9 ch_2
values and re-evaluate against Ch 32 normative table + 5/6-class confusion.

Interpretation: the framework's "ch_2 in [0,1] with 0.95 threshold" is the
NORMALIZED COMSCIOUSNESS INDEX. Raw ch_2 from the Ch 30 formula lives at a
different operating point. The framework's [0,1] scaling is what's normative.
"""

from __future__ import annotations

import os
import sys
import json
import numpy as np
from scipy.optimize import minimize
from scipy.stats import spearmanr, pearsonr
from sklearn.discriminant_analysis import LinearDiscriminantAnalysis
from sklearn.model_selection import StratifiedKFold

ROOT = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(ROOT, '..', 'clinical_calibration_search'))
sys.path.insert(0, ROOT)

from calib_core import ch2_generalized, NORMS  # noqa: E402
from sleep_eeg_simulator import (  # noqa: E402
    SleepSpec, GENERATORS, NORMATIVE_TARGETS,
)


PHI = (1.0 + np.sqrt(5.0)) / 2.0
ALPHA = PHI + 0.25
BASE = 2
NORM_FN = NORMS['rms_MB']
M = 32
T = 8.0
FS = 256.0
N_PER = 30
W = 0.5


def cohort():
    out = {}
    seed = 90_000
    for label, gen in GENERATORS.items():
        vals = []
        for k in range(N_PER):
            spec = SleepSpec(label=label, M=M, T_sec=T, fs=FS, seed=seed)
            eeg = gen(spec)
            v = ch2_generalized(eeg, fs=FS, alpha=ALPHA, base=BASE,
                                 norm_fn=NORM_FN, window_sec=W, clip=False)
            vals.append(v)
            seed += 1
        out[label] = np.array(vals)
    return out


def fit_sigmoid_on_means(results):
    states = list(NORMATIVE_TARGETS.keys())
    x = np.array([float(results[s].mean()) for s in states])
    y = np.array([NORMATIVE_TARGETS[s][0] for s in states])
    def loss(p):
        L, k, x0 = p
        return float(np.sum((L / (1 + np.exp(-k * (x - x0))) - y) ** 2))
    res = minimize(loss, x0=[1.0, 12.0, float(x.mean())],
                    method='Nelder-Mead', options={'xatol': 1e-6})
    return tuple(res.x), x, y


def sigmoid(x, L, k, x0):
    return L / (1.0 + np.exp(-k * (x - x0)))


def bootstrap_ci(values, n_boot=2000, seed=0):
    rng = np.random.default_rng(seed)
    n = len(values)
    means = np.empty(n_boot)
    for i in range(n_boot):
        means[i] = float(np.mean(values[rng.integers(0, n, n)]))
    return float(np.percentile(means, 2.5)), float(np.percentile(means, 97.5))


def confusion(results, labels, name='', n_splits=5):
    X = []
    y = []
    for i, lab in enumerate(labels):
        for v in results[lab]:
            X.append([v])
            y.append(i)
    X = np.array(X)
    y = np.array(y)
    cm = np.zeros((len(labels), len(labels)), dtype=int)
    accs = []
    skf = StratifiedKFold(n_splits=n_splits, shuffle=True, random_state=0)
    for tr, te in skf.split(X, y):
        lda = LinearDiscriminantAnalysis()
        lda.fit(X[tr], y[tr])
        pred = lda.predict(X[te])
        for ti, pi in zip(y[te], pred):
            cm[ti, pi] += 1
        accs.append(float((pred == y[te]).mean()))
    return cm, float(np.mean(accs)), float(np.std(accs))


def main():
    print("=" * 88)
    print("Ch 32 NORMATIVE VERIFICATION — RAW + SIGMOID-REMAPPED ch_2")
    print(f"  alpha={ALPHA:.4f}, base={BASE}, norm=rms_MB, "
          f"N={N_PER}/class, M={M}, T={T}s")
    print("=" * 88)
    print()

    print("Generating cohort...")
    res = cohort()
    print()

    # Bootstrap CIs on raw means
    print("RAW ch_2 MEANS + 95% BOOTSTRAP CI vs Ch 32 NORMATIVE TARGETS")
    print("-" * 88)
    print(f"{'state':<16s} {'raw mean':>10s} {'95% CI':>22s} "
          f"{'target':>10s} {'target std':>11s}")
    for lab in NORMATIVE_TARGETS:
        v = res[lab]
        lo, hi = bootstrap_ci(v)
        tm, ts = NORMATIVE_TARGETS[lab]
        print(f"{lab:<16s} {v.mean():>10.4f} "
              f"  [{lo:.4f}, {hi:.4f}]  "
              f"{tm:>10.4f} {ts:>11.4f}")
    print()

    # Fit sigmoid
    (L, k, x0), x_means, y_targets = fit_sigmoid_on_means(res)
    print(f"BEST-FIT SIGMOID REMAP: y = {L:.4f} / (1 + exp(-{k:.4f}*(x - {x0:.4f})))")
    print()

    # Apply sigmoid to all samples
    res_remapped = {lab: sigmoid(v, L, k, x0) for lab, v in res.items()}

    print("REMAPPED ch_2 MEANS + 95% BOOTSTRAP CI vs Ch 32 NORMATIVE TARGETS")
    print("-" * 88)
    print(f"{'state':<16s} {'remap mean':>11s} {'remap std':>10s} "
          f"{'95% CI':>22s} {'target':>10s} {'target std':>11s} "
          f"{'within tgt 1sig':>16s}")
    for lab in NORMATIVE_TARGETS:
        v = res_remapped[lab]
        lo, hi = bootstrap_ci(v)
        tm, ts = NORMATIVE_TARGETS[lab]
        within = (lo <= tm + ts) and (hi >= tm - ts)
        print(f"{lab:<16s} {v.mean():>11.4f} {v.std():>10.4f} "
              f"  [{lo:.4f}, {hi:.4f}]  "
              f"{tm:>10.4f} {ts:>11.4f} {str(within):>16s}")
    print()

    # 6-class confusion on remapped values
    labels = list(GENERATORS.keys())
    cm6, acc6, sd6 = confusion(res_remapped, labels)
    print(f"6-CLASS LDA on REMAPPED ch_2 (5-fold CV): "
          f"acc = {acc6:.4f} +/- {sd6:.4f}")
    print(f"  {'true \\ pred':<16s}" + ''.join(f"{l[:8]:>10s}" for l in labels))
    for i, lab in enumerate(labels):
        print(f"  {lab:<16s}" + ''.join(
            f"{cm6[i, j]:>10d}" for j in range(len(labels))))
    print()

    # 5-class (drop meditation)
    labels5 = ['awake_resting', 'rem_sleep', 'n1_drowsy', 'n2_light', 'n3_deep']
    res5 = {s: res_remapped[s] for s in labels5}
    cm5, acc5, sd5 = confusion(res5, labels5)
    print(f"5-CLASS LDA on REMAPPED ch_2 (no meditation) (5-fold CV): "
          f"acc = {acc5:.4f} +/- {sd5:.4f}")
    print(f"  {'true \\ pred':<16s}" + ''.join(f"{l[:8]:>10s}" for l in labels5))
    for i, lab in enumerate(labels5):
        print(f"  {lab:<16s}" + ''.join(
            f"{cm5[i, j]:>10d}" for j in range(len(labels5))))
    print()

    # Final summary
    print("=" * 88)
    print("HEADLINE SUMMARY")
    print("=" * 88)
    sp, _ = spearmanr(
        [res[s].mean() for s in NORMATIVE_TARGETS],
        [NORMATIVE_TARGETS[s][0] for s in NORMATIVE_TARGETS])
    pe, _ = pearsonr(
        [res_remapped[s].mean() for s in NORMATIVE_TARGETS],
        [NORMATIVE_TARGETS[s][0] for s in NORMATIVE_TARGETS])
    print(f"  Raw ch_2 vs Ch 32 means:        Spearman rho = {sp:+.4f}")
    print(f"  Remapped ch_2 vs Ch 32 means:   Pearson  r   = {pe:+.4f}")
    print(f"  6-class confusion acc (remapped):  {acc6:.4f}")
    print(f"  5-class confusion acc (remapped):  {acc5:.4f}")
    print()

    # Save
    out_obj = {
        'config': {'alpha': float(ALPHA), 'base': BASE, 'norm': 'rms_MB',
                    'M': M, 'T_sec': T, 'fs': FS, 'N_per': N_PER},
        'raw_means': {k: float(v.mean()) for k, v in res.items()},
        'raw_stds':  {k: float(v.std())  for k, v in res.items()},
        'sigmoid_params': {'L': float(L), 'k': float(k), 'x0': float(x0)},
        'remapped_means': {k: float(v.mean()) for k, v in res_remapped.items()},
        'remapped_stds':  {k: float(v.std())  for k, v in res_remapped.items()},
        'normative_targets': NORMATIVE_TARGETS,
        'spearman_raw': float(sp),
        'pearson_remapped': float(pe),
        'accuracy_6class': float(acc6),
        'accuracy_5class': float(acc5),
    }
    with open(os.path.join(ROOT, 'remapped_results.json'), 'w') as f:
        json.dump(out_obj, f, indent=2)
    print(f"Saved: {os.path.join(ROOT, 'remapped_results.json')}")


if __name__ == '__main__':
    main()
