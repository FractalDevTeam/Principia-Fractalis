"""
five_class_and_robust.py
========================

Once we found best (norm, alpha, base) via grid_search:
  1. Build 5-class confusion matrix (nearest-class-mean) at best calibration
  2. Compare against inter-electrode coherence baseline (yesterday d=34.3)
  3. Robustness sweep: SNR = inf, 20, 10, 5 dB
  4. Sklearn LinearDiscriminant 5-class accuracy (proper classifier)

Also computes the literal "0.95 threshold" sanity check at chosen calibration.
"""

import sys
import os
import json
import time
import numpy as np

HERE = os.path.dirname(__file__)
sys.path.insert(0, HERE)
from calib_core import (NORMS, ALPHAS, BASES, make_cohort,
                         evaluate_calibration, ch2_generalized,
                         POS_LABELS, NEG_LABELS)
# Also yesterday's coherence baseline
sys.path.insert(0, os.path.join(HERE, "..", "clinical_ch2_verification"))
from feature_importance import avg_pairwise_coherence

from sklearn.discriminant_analysis import LinearDiscriminantAnalysis
from sklearn.model_selection import StratifiedKFold
from sklearn.metrics import accuracy_score, confusion_matrix


# Best calibrations from grid sweep
BEST_CALIBS = [
    # (norm, alpha_name, alpha_val, base, label)
    ("rms_MB", "phi_plus_qtr", ALPHAS["phi_plus_qtr"], 2, "BEST: phi+1/4, base=2"),
    ("rms_MB", "phi",          ALPHAS["phi"],          3, "alt:  phi, base=3"),
    ("rms_MB", "1p5",          ALPHAS["1p5"],          2, "alt:  3/2 (RH), base=2"),
    ("rms_MB", "sqrt2",        ALPHAS["sqrt2"],        2, "alt:  sqrt2 (P), base=2"),
]


def compute_ch2_vector(cohort, alpha, base, norm_name, fs=256.0):
    """Compute ch_2 for every patient. Returns dict label -> np.ndarray."""
    out = {}
    norm_fn = NORMS[norm_name]
    for label, eegs in cohort.items():
        vals = []
        for eeg in eegs:
            v = ch2_generalized(eeg, fs, alpha, base, norm_fn, clip=False)
            vals.append(v)
        out[label] = np.array(vals)
    return out


def five_class_ncm(per_class):
    """Nearest-class-mean 5-class accuracy. Returns (acc, confusion dict)."""
    means = {l: float(np.mean(v)) for l, v in per_class.items()}
    correct = 0; total = 0
    cols = list(per_class.keys())
    conf = {l: {l2: 0 for l2 in cols} for l in cols}
    for true_label, vals in per_class.items():
        for v in vals:
            pred = min(means, key=lambda l: abs(v - means[l]))
            conf[true_label][pred] += 1
            if pred == true_label:
                correct += 1
            total += 1
    return correct / total, conf, means


def five_class_lda(per_class):
    """Sklearn LDA 5-fold CV on single ch_2 feature. Returns mean accuracy."""
    X, y = [], []
    for label, vals in per_class.items():
        for v in vals:
            X.append([v]); y.append(label)
    X = np.array(X); y = np.array(y)
    skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
    accs = []
    for tr, te in skf.split(X, y):
        lda = LinearDiscriminantAnalysis()
        lda.fit(X[tr], y[tr])
        accs.append(accuracy_score(y[te], lda.predict(X[te])))
    return float(np.mean(accs)), float(np.std(accs))


def compute_coherence_baseline(cohort, fs=256.0):
    """Yesterday's discriminator. Returns per-class arrays."""
    out = {}
    for label, eegs in cohort.items():
        vals = []
        for eeg in eegs:
            vals.append(avg_pairwise_coherence(eeg, fs))
        out[label] = np.array(vals)
    return out


def binary_metrics(per_class):
    pos = np.concatenate([per_class[l] for l in POS_LABELS])
    neg = np.concatenate([per_class[l] for l in NEG_LABELS])
    if pos.std() + neg.std() < 1e-12:
        d = 0.0
    else:
        d = abs(pos.mean() - neg.mean()) / np.sqrt(0.5*(pos.std()**2 + neg.std()**2))
    # Best threshold sweep
    all_v = np.concatenate([pos, neg]); grid = np.linspace(all_v.min(), all_v.max(), 400)
    best_acc = 0.0; best_t = float(np.median(all_v))
    for polarity in (+1, -1):
        for t in grid:
            if polarity > 0:
                tp = (pos >= t).sum(); fn = (pos < t).sum()
                tn = (neg <  t).sum(); fp = (neg >= t).sum()
            else:
                tp = (pos <  t).sum(); fn = (pos >= t).sum()
                tn = (neg >= t).sum(); fp = (neg <  t).sum()
            acc = (tp+tn) / (tp+fn+tn+fp)
            if acc > best_acc:
                best_acc = float(acc); best_t = float(t)
    return float(d), float(best_acc), float(best_t)


def report_calib(per_class, name):
    print(f"\n>>> {name}")
    for label, v in per_class.items():
        print(f"    {label:<11s} mean={v.mean():12.4g}  std={v.std():12.4g}  "
              f"min={v.min():12.4g}  max={v.max():12.4g}")
    d, bin_acc, thr = binary_metrics(per_class)
    acc5, conf, means = five_class_ncm(per_class)
    lda_acc, lda_std = five_class_lda(per_class)
    print(f"    Binary (conscious+LIS vs coma+veg): "
          f"acc={bin_acc*100:5.1f}%  Cohen d={d:.2f}  thr={thr:.4g}")
    print(f"    5-class nearest-class-mean: {acc5*100:5.1f}%")
    print(f"    5-class LDA 5-fold CV:      {lda_acc*100:5.1f}% +/- {lda_std*100:.1f}%")
    cols = list(per_class.keys())
    print(f"    5-class confusion matrix (rows=true, cols=pred):")
    print(f"      {'':<12s}" + "".join(f"{c[:8]:>10s}" for c in cols))
    for tr in cols:
        row = "      " + f"{tr:<12s}" + "".join(f"{conf[tr][p]:>10d}" for p in cols)
        print(row)
    return {"binary_acc": bin_acc, "cohen_d": d, "best_thr": thr,
            "ncm_5class": acc5, "lda_5class": lda_acc, "lda_std": lda_std,
            "confusion": conf, "means": means}


def main():
    print("="*78)
    print("DELIVERABLE 3-5: 5-class + coherence comparison + noise robustness")
    print("="*78)
    full_report = {"snr_sweep": {}, "baseline_coherence": {}, "best_calibs": {}}

    # ---- clean cohort ----
    print("\nBuilding clean cohort (M=32, T=5s, fs=256, 20 per class)...")
    t0 = time.time()
    cohort_clean = make_cohort(n_per_class=20, M=32, T_sec=5.0, fs=256.0,
                                snr_db=None, seed_base=20000)
    print(f"  done in {time.time()-t0:.1f}s")

    # ---- baseline: coherence ----
    print("\n--- BASELINE: Inter-electrode coherence (yesterday's d=34.3) ---")
    t0 = time.time()
    coh = compute_coherence_baseline(cohort_clean)
    print(f"  computed in {time.time()-t0:.1f}s")
    full_report["baseline_coherence"]["clean"] = report_calib(coh, "Coherence")

    # ---- best calibration ----
    for norm_name, an, av, base, label in BEST_CALIBS:
        per = compute_ch2_vector(cohort_clean, av, base, norm_name)
        rep = report_calib(per, f"{label}  [norm={norm_name}]")
        full_report["best_calibs"][label] = rep

    # ---- noise robustness on best calibration only ----
    print("\n" + "="*78)
    print("DELIVERABLE 5: NOISE ROBUSTNESS SWEEP (best calibration)")
    print("="*78)
    best = BEST_CALIBS[0]
    norm_name, an, av, base, label = best
    print(f"Calibration under test: {label}  norm={norm_name}")

    for snr in [20.0, 10.0, 5.0]:
        print(f"\n--- SNR = {snr} dB ---")
        cohort_noisy = make_cohort(n_per_class=20, M=32, T_sec=5.0, fs=256.0,
                                    snr_db=snr, seed_base=20000)
        # ch_2 with best calib
        per = compute_ch2_vector(cohort_noisy, av, base, norm_name)
        rep_ch2 = report_calib(per, f"ch_2 ({label}) at SNR={snr}dB")
        # coherence baseline at same SNR
        coh_n = compute_coherence_baseline(cohort_noisy)
        rep_coh = report_calib(coh_n, f"Coherence at SNR={snr}dB")
        full_report["snr_sweep"][f"snr_{snr}"] = {
            "ch2": rep_ch2, "coherence": rep_coh,
        }

    # ---- literal 0.95 threshold sanity check at best calibration ----
    print("\n" + "="*78)
    print("LITERAL 0.95 THRESHOLD SANITY CHECK on best calibration")
    print("="*78)
    norm_name, an, av, base, label = best
    per_clean = compute_ch2_vector(cohort_clean, av, base, norm_name)
    pos = np.concatenate([per_clean[l] for l in POS_LABELS])
    neg = np.concatenate([per_clean[l] for l in NEG_LABELS])
    print(f"At norm={norm_name} alpha={an} base={base}:")
    print(f"  positive class range: [{pos.min():.4g}, {pos.max():.4g}], "
          f"mean={pos.mean():.4g}")
    print(f"  negative class range: [{neg.min():.4g}, {neg.max():.4g}], "
          f"mean={neg.mean():.4g}")
    print(f"  framework's literal 0.95 threshold would classify:")
    print(f"    positive >= 0.95: {(pos >= 0.95).sum()}/{len(pos)}")
    print(f"    negative >= 0.95: {(neg >= 0.95).sum()}/{len(neg)}")
    print(f"  but RAW values live near {pos.mean():.4g} (pos) / {neg.mean():.4g} (neg)")
    print(f"  so literal 0.95 is wrong UNIT — need rescaling or threshold update.")
    print(f"  Calibrated threshold: {full_report['best_calibs'][label]['best_thr']:.4g}")

    # Save
    out_path = os.path.join(HERE, "five_class_robustness_results.json")
    # JSON-safe conversion
    def to_safe(o):
        if isinstance(o, dict): return {k: to_safe(v) for k,v in o.items()}
        if isinstance(o, list): return [to_safe(v) for v in o]
        if isinstance(o, np.ndarray): return o.tolist()
        if isinstance(o, (np.floating, np.integer)): return float(o)
        return o
    with open(out_path, "w") as f:
        json.dump(to_safe(full_report), f, indent=2)
    print(f"\nSaved full report -> {out_path}")


if __name__ == "__main__":
    main()
