"""
full_cohort_experiment.py
==========================

Run a 100-patient (20 per class) synthetic cohort with the full ch_2
clinical formula. Report:
  - per-class statistics
  - confusion matrix at framework's 0.95 threshold
  - confusion matrix at empirically-optimal threshold
  - 5-class accuracy

This is the closest we can get to simulating the 847-patient Ch 30 cohort
without real data. Establishes COMPUTABILITY of the formula and its
operating point.
"""

import numpy as np
from ch2_clinical import (SYNTH, PatientSpec, ALPHA_P)
from ch2_clinical_v2 import ch2_clinical_both


def run_full(n_per_class=20, M=32, T_sec=5.0, fs=256.0):
    seed = 10000
    data = {label: [] for label in SYNTH}
    for label, gen in SYNTH.items():
        for k in range(n_per_class):
            spec = PatientSpec(label=label, M=M, T_sec=T_sec, fs=fs, seed=seed)
            eeg = gen(spec)
            _, c_rms = ch2_clinical_both(eeg, fs, alpha=ALPHA_P, base=3)
            data[label].append(c_rms)
            seed += 1
    return data


def report(data, thr_95=0.95):
    print("=" * 70)
    print("FULL COHORT (100 synthetic patients, alpha=sqrt(2), base=3)")
    print("=" * 70)
    print(f"{'class':<12s} {'n':>4s} {'mean':>8s} {'std':>8s} {'min':>8s} {'max':>8s}")
    print("-" * 50)
    for label, vals in data.items():
        v = np.array(vals)
        print(f"{label:<12s} {len(v):>4d} {v.mean():>8.4f} {v.std():>8.4f} "
              f"{v.min():>8.4f} {v.max():>8.4f}")

    # Framework's threshold 0.95
    print(f"\n--- Framework threshold 0.95 ---")
    for label, vals in data.items():
        v = np.array(vals)
        pct = 100 * (v >= thr_95).mean()
        print(f"  {label:<12s}: {pct:.0f}% classified conscious")

    # Empirical optimal threshold
    pos = np.concatenate([data['conscious'], data['locked-in']])
    neg = np.concatenate([data['coma'], data['vegetative']])
    all_v = np.concatenate([pos, neg])
    grid = np.linspace(all_v.min(), all_v.max(), 400)
    best = (0.5, 0.0, 0.0, 0.0)
    for t in grid:
        tp = (pos >= t).sum()
        fn = (pos <  t).sum()
        tn = (neg <  t).sum()
        fp = (neg >= t).sum()
        acc = (tp + tn) / (tp + fn + tn + fp)
        sens = tp / (tp + fn) if (tp + fn) else 0
        spec = tn / (tn + fp) if (tn + fp) else 0
        if acc > best[1]:
            best = (float(t), float(acc), float(sens), float(spec))
    print(f"\n--- Empirical optimal threshold (binary: conscious+LIS vs coma+veg) ---")
    print(f"  threshold = {best[0]:.4f}")
    print(f"  accuracy  = {100*best[1]:.1f}%")
    print(f"  sens      = {100*best[2]:.1f}%   spec = {100*best[3]:.1f}%")

    # 5-class accuracy via nearest-class-mean
    means = {l: np.mean(v) for l, v in data.items()}
    correct = 0
    total = 0
    confusion = {l: {l2: 0 for l2 in data} for l in data}
    for true_label, vals in data.items():
        for v in vals:
            pred = min(means, key=lambda l: abs(v - means[l]))
            confusion[true_label][pred] += 1
            if pred == true_label:
                correct += 1
            total += 1
    print(f"\n--- 5-class nearest-class-mean accuracy ---")
    print(f"  {100*correct/total:.1f}%   (vs chance 20%)")
    print(f"\nConfusion matrix (rows=true, cols=pred):")
    cols = list(data.keys())
    print(f"  {'':<12s}" + "".join(f"{c[:8]:>10s}" for c in cols))
    for tr in cols:
        row = "  " + f"{tr:<12s}" + "".join(f"{confusion[tr][p]:>10d}" for p in cols)
        print(row)


if __name__ == "__main__":
    data = run_full(n_per_class=20, M=32, T_sec=5.0, fs=256.0)
    report(data)
