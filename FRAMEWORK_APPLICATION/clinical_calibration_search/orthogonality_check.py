"""
orthogonality_check.py
=======================

Question: does the best-calibrated ch_2 carry information orthogonal to
inter-electrode coherence, or is it redundant?

Method:
  - Compute both features on the clean cohort
  - Pearson correlation between ch_2 and coherence
  - Combined 5-class LDA accuracy vs each alone

If combined > each-alone, there's orthogonal information. If combined ~= max,
ch_2 is redundant with coherence (both capturing the same low-frequency
phase-locking signal).
"""

import sys
import os
import numpy as np

HERE = os.path.dirname(__file__)
sys.path.insert(0, HERE)
from calib_core import (NORMS, ALPHAS, make_cohort, ch2_generalized)
sys.path.insert(0, os.path.join(HERE, "..", "clinical_ch2_verification"))
from feature_importance import avg_pairwise_coherence

from sklearn.discriminant_analysis import LinearDiscriminantAnalysis
from sklearn.model_selection import StratifiedKFold
from sklearn.metrics import accuracy_score


def run():
    print("Building clean cohort (20 x 5, M=32, T=5s, fs=256)...")
    cohort = make_cohort(n_per_class=20, M=32, T_sec=5.0, fs=256.0,
                          seed_base=20000)

    # Best calib
    norm_name, alpha_name, alpha_val, base = (
        "rms_MB", "phi_plus_qtr", ALPHAS["phi_plus_qtr"], 2)
    norm_fn = NORMS[norm_name]

    rows = []
    for label, eegs in cohort.items():
        for eeg in eegs:
            c2 = ch2_generalized(eeg, 256.0, alpha_val, base, norm_fn,
                                  clip=False)
            coh = avg_pairwise_coherence(eeg, 256.0)
            rows.append({"label": label, "ch2": c2, "coh": coh})

    labels = np.array([r["label"] for r in rows])
    ch2 = np.array([r["ch2"] for r in rows])
    coh = np.array([r["coh"] for r in rows])

    print()
    print("FEATURE STATS (clean cohort)")
    print(f"  ch_2 (best calib):  mean={ch2.mean():.4g}  std={ch2.std():.4g}  "
          f"range=[{ch2.min():.4g}, {ch2.max():.4g}]")
    print(f"  coherence:          mean={coh.mean():.4g}  std={coh.std():.4g}  "
          f"range=[{coh.min():.4g}, {coh.max():.4g}]")

    # Pearson
    r = np.corrcoef(ch2, coh)[0, 1]
    print()
    print(f"Pearson correlation  ch_2 <-> coherence:  r = {r:+.3f}")

    # Per-class correlation
    print()
    print("Per-class correlation:")
    for label in ["conscious", "mcs", "vegetative", "coma", "locked-in"]:
        mask = labels == label
        if mask.sum() > 1:
            r_l = np.corrcoef(ch2[mask], coh[mask])[0, 1]
            print(f"  {label:<12s}  r={r_l:+.3f}")

    # 5-class LDA
    print()
    print("5-class LDA 5-fold CV accuracy:")
    skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
    for X, name in [(ch2.reshape(-1,1), "ch_2 alone"),
                     (coh.reshape(-1,1), "coherence alone"),
                     (np.column_stack([ch2, coh]), "ch_2 + coherence")]:
        accs = []
        for tr, te in skf.split(X, labels):
            lda = LinearDiscriminantAnalysis()
            lda.fit(X[tr], labels[tr])
            accs.append(accuracy_score(labels[te], lda.predict(X[te])))
        print(f"  {name:<25s} acc = {np.mean(accs)*100:5.1f}%  +/- "
              f"{np.std(accs)*100:.1f}%")

    # Specifically: does coherence struggle to separate vegetative vs coma?
    # (Yesterday's confusion matrix says yes.) Does ch_2 do better?
    print()
    print("CRITICAL TEST: vegetative-vs-coma discrimination")
    veg = ch2[labels == "vegetative"]
    com = ch2[labels == "coma"]
    veg_coh = coh[labels == "vegetative"]
    com_coh = coh[labels == "coma"]
    d_ch2 = abs(veg.mean() - com.mean()) / np.sqrt(0.5*(veg.std()**2 + com.std()**2))
    d_coh = abs(veg_coh.mean() - com_coh.mean()) / np.sqrt(
        0.5*(veg_coh.std()**2 + com_coh.std()**2) + 1e-12)
    print(f"  ch_2:       Cohen d (veg vs coma) = {d_ch2:.2f}")
    print(f"              veg={veg.mean():.4g}±{veg.std():.4g}  "
          f"coma={com.mean():.4g}±{com.std():.4g}")
    print(f"  coherence:  Cohen d (veg vs coma) = {d_coh:.2f}")
    print(f"              veg={veg_coh.mean():.4g}±{veg_coh.std():.4g}  "
          f"coma={com_coh.mean():.4g}±{com_coh.std():.4g}")

    # Conscious vs locked-in
    print()
    print("CRITICAL TEST: conscious-vs-locked-in discrimination")
    con = ch2[labels == "conscious"]
    lck = ch2[labels == "locked-in"]
    con_coh = coh[labels == "conscious"]
    lck_coh = coh[labels == "locked-in"]
    d_ch2 = abs(con.mean() - lck.mean()) / np.sqrt(0.5*(con.std()**2 + lck.std()**2))
    d_coh = abs(con_coh.mean() - lck_coh.mean()) / np.sqrt(
        0.5*(con_coh.std()**2 + lck_coh.std()**2) + 1e-12)
    print(f"  ch_2:       Cohen d (con vs LIS) = {d_ch2:.2f}")
    print(f"  coherence:  Cohen d (con vs LIS) = {d_coh:.2f}")


if __name__ == "__main__":
    run()
