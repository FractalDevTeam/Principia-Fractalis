"""
alpha_base_sweep.py
====================

Sensitivity analysis:
  - vary alpha in {1, sqrt(2), 3/2, phi+1/4, 2, sqrt(2*pi)}
  - vary base in {2, 3, 10}

Question:
  - Does alpha = sqrt(2) (P-class) maximize discrimination as the framework
    predicts?
  - Is base-3 essential or arbitrary?
"""

import numpy as np
from ch2_clinical_v2 import (
    cohort_experiment, accuracy_at_threshold, find_best_threshold
)
from ch2_clinical import (
    ALPHA_P, ALPHA_NP, ALPHA_RH, ALPHA_QG, ALPHA_YM, ALPHA_HODGE, ALPHA_POINCARE
)


ALPHAS = {
    'alpha_Poincare = 1':     ALPHA_POINCARE,
    'alpha_RH = 3/2':         ALPHA_RH,
    'alpha_P = sqrt(2)':      ALPHA_P,
    'alpha_NP = phi+1/4':     ALPHA_NP,
    'alpha_YM = 2':           ALPHA_YM,
    'alpha_QG = sqrt(2pi)':   ALPHA_QG,
    'alpha_Hodge = phi':      ALPHA_HODGE,
}


def discrimination(results, key='rms'):
    """Mean conscious score - mean unconscious score (effect size)."""
    pos = []
    neg = []
    for l in ['conscious', 'locked-in']:
        pos.extend(results[l][key])
    for l in ['coma', 'vegetative']:
        neg.extend(results[l][key])
    pos = np.array(pos); neg = np.array(neg)
    if pos.std() + neg.std() < 1e-9:
        return 0.0
    cohens_d = (pos.mean() - neg.mean()) / np.sqrt(0.5*(pos.std()**2 + neg.std()**2))
    return float(cohens_d)


def alpha_sweep(base: int = 3, n_per_class: int = 15):
    print(f"\nALPHA SWEEP (base = {base})")
    print("=" * 76)
    print(f"{'alpha label':<24s} {'mean(consc)':>11s} {'mean(unconsc)':>13s} "
          f"{'Cohen d':>9s} {'best_thr':>9s} {'best_acc':>9s}")
    print("-" * 76)
    rows = []
    for label, alpha in ALPHAS.items():
        res = cohort_experiment(n_per_class=n_per_class, M=24, T_sec=3.0,
                                 fs=256.0, alpha=alpha, base=base)
        pos = np.concatenate([res['conscious']['rms'], res['locked-in']['rms']])
        neg = np.concatenate([res['coma']['rms'], res['vegetative']['rms']])
        d = discrimination(res, key='rms')
        best_thr, best_acc = find_best_threshold(res, key='rms')
        rows.append((label, alpha, pos.mean(), neg.mean(), d, best_thr, best_acc))
        print(f"{label:<24s} {pos.mean():>11.4f} {neg.mean():>13.4f} "
              f"{d:>9.3f} {best_thr:>9.4f} {best_acc:>9.3f}")
    return rows


def base_sweep(alpha: float = ALPHA_P, n_per_class: int = 15):
    print(f"\nBASE SWEEP (alpha = {alpha:.5f})")
    print("=" * 76)
    print(f"{'base':<6s} {'mean(consc)':>11s} {'mean(unconsc)':>13s} "
          f"{'Cohen d':>9s} {'best_thr':>9s} {'best_acc':>9s}")
    print("-" * 76)
    rows = []
    for base in [2, 3, 5, 7, 10]:
        res = cohort_experiment(n_per_class=n_per_class, M=24, T_sec=3.0,
                                 fs=256.0, alpha=alpha, base=base)
        pos = np.concatenate([res['conscious']['rms'], res['locked-in']['rms']])
        neg = np.concatenate([res['coma']['rms'], res['vegetative']['rms']])
        d = discrimination(res, key='rms')
        best_thr, best_acc = find_best_threshold(res, key='rms')
        rows.append((base, pos.mean(), neg.mean(), d, best_thr, best_acc))
        print(f"{base:<6d} {pos.mean():>11.4f} {neg.mean():>13.4f} "
              f"{d:>9.3f} {best_thr:>9.4f} {best_acc:>9.3f}")
    return rows


if __name__ == "__main__":
    alpha_rows = alpha_sweep(base=3, n_per_class=15)
    base_rows = base_sweep(alpha=ALPHA_P, n_per_class=15)

    print("\n" + "=" * 76)
    print("SUMMARY")
    print("=" * 76)
    best_alpha = max(alpha_rows, key=lambda r: r[6])
    print(f"Best alpha by accuracy: {best_alpha[0]} "
          f"(acc={best_alpha[6]:.3f}, Cohen d={best_alpha[4]:.3f})")
    best_base = max(base_rows, key=lambda r: r[5])
    print(f"Best base by accuracy: base={best_base[0]} "
          f"(acc={best_base[5]:.3f}, Cohen d={best_base[3]:.3f})")
