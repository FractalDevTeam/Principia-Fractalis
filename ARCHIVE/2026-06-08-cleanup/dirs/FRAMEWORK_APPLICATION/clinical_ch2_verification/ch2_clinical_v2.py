"""
ch2_clinical_v2.py — Two normalization conventions for the Ch 30 formula.

LITERAL_NORM:  1/(M*5)              (Ch 30 line 197 as written)
RMS_NORM:      1/sqrt(M*5)          (coherence-fraction interpretation)

We compute both, and use them in the cohort experiment to expose which
interpretation makes the 0.95 threshold meaningful.
"""

import numpy as np
from scipy import signal
from dataclasses import dataclass

from ch2_clinical import (
    BANDS, ALPHA_P, ALPHA_NP, ALPHA_RH, ALPHA_QG,
    ALPHA_HODGE, ALPHA_YM, ALPHA_POINCARE,
    THRESHOLD_CONSCIOUS, THRESHOLD_PROTO,
    digital_sum_vec, bandpass, quantize_power,
    PatientSpec, SYNTH,
)


def ch2_clinical_both(eeg: np.ndarray, fs: float,
                       alpha: float = ALPHA_P,
                       base: int = 3,
                       window_sec: float = 0.5) -> tuple[float, float]:
    """
    Returns (ch2_literal, ch2_rms) — same formula, two normalizations.
    """
    M, N = eeg.shape
    window_samples = int(window_sec * fs)
    if window_samples < 8:
        window_samples = 8
    n_windows = N // window_samples
    if n_windows < 1:
        raise ValueError("Recording too short.")

    band_phi_raw = {b: bandpass(eeg, fs, lo, hi) for b, (lo, hi) in BANDS.items()}
    band_phi = {}
    for b in BANDS:
        x = band_phi_raw[b]
        peak = np.max(np.abs(x), axis=-1, keepdims=True) + 1e-12
        band_phi[b] = x / peak
    band_n = {b: quantize_power(band_phi_raw[b], fs, window_samples) for b in BANDS}
    band_phase = {b: np.exp(1j * np.pi * alpha * digital_sum_vec(band_n[b], base=base))
                  for b in BANDS}

    norm_literal = 1.0 / (M * len(BANDS))
    norm_rms     = 1.0 / np.sqrt(M * len(BANDS))

    means_literal = np.zeros(n_windows)
    means_rms     = np.zeros(n_windows)
    for w in range(n_windows):
        s0, s1 = w * window_samples, (w + 1) * window_samples
        accum = np.zeros(s1 - s0, dtype=np.complex128)
        for b in BANDS:
            phase = band_phase[b][:, w]
            phi_samples = band_phi[b][:, s0:s1]
            accum += (phase[:, None] * phi_samples).sum(axis=0)
        means_literal[w] = (np.abs(norm_literal * accum) ** 2).mean()
        means_rms[w]     = (np.abs(norm_rms     * accum) ** 2).mean()

    return (float(np.clip(means_literal.mean(), 0, 1)),
            float(np.clip(means_rms.mean(), 0, 1)))


def cohort_experiment(n_per_class: int = 20,
                       M: int = 32,
                       T_sec: float = 4.0,
                       fs: float = 256.0,
                       alpha: float = ALPHA_P,
                       base: int = 3) -> dict:
    """Run cohort of n_per_class synthetic patients across all 5 classes."""
    results = {label: {'literal': [], 'rms': []} for label in SYNTH}
    seed_base = 1000
    for label, gen in SYNTH.items():
        for k in range(n_per_class):
            spec = PatientSpec(label=label, M=M, T_sec=T_sec, fs=fs,
                                seed=seed_base + 31 * k)
            eeg = gen(spec)
            c_lit, c_rms = ch2_clinical_both(eeg, fs=fs, alpha=alpha, base=base)
            results[label]['literal'].append(c_lit)
            results[label]['rms'].append(c_rms)
            seed_base += 1
    return results


def summarize(results: dict, label_thresh: tuple[str, str, str] =
              ('conscious', 'mcs', 'unconscious')):
    """Print per-class mean/std for both normalizations."""
    print(f"{'class':<11s} {'lit mean':>10s} {'lit std':>9s}  "
          f"{'rms mean':>10s} {'rms std':>9s}")
    print("-" * 60)
    for label, d in results.items():
        lit = np.array(d['literal'])
        rms = np.array(d['rms'])
        print(f"{label:<11s} {lit.mean():>10.4f} {lit.std():>9.4f}  "
              f"{rms.mean():>10.4f} {rms.std():>9.4f}")


def accuracy_at_threshold(results: dict, thr: float, key: str = 'rms') -> dict:
    """
    Binary accuracy at threshold: conscious + locked-in are POSITIVE,
    coma + vegetative are NEGATIVE, MCS is ambiguous (excluded).
    """
    positive = ['conscious', 'locked-in']
    negative = ['coma', 'vegetative']
    tp = sum(1 for l in positive for v in results[l][key] if v >= thr)
    fn = sum(1 for l in positive for v in results[l][key] if v <  thr)
    tn = sum(1 for l in negative for v in results[l][key] if v <  thr)
    fp = sum(1 for l in negative for v in results[l][key] if v >= thr)
    total = tp + fn + tn + fp
    return {
        'tp': tp, 'fn': fn, 'tn': tn, 'fp': fp,
        'accuracy': (tp + tn) / total if total else 0.0,
        'sensitivity': tp / (tp + fn) if (tp + fn) else 0.0,
        'specificity': tn / (tn + fp) if (tn + fp) else 0.0,
    }


def find_best_threshold(results: dict, key: str = 'rms') -> tuple[float, float]:
    """Sweep thresholds, return (best_thr, best_accuracy)."""
    all_vals = []
    for l in ['conscious', 'locked-in', 'coma', 'vegetative']:
        all_vals.extend(results[l][key])
    grid = np.linspace(min(all_vals), max(all_vals), 200)
    best = (0.5, 0.0)
    for t in grid:
        a = accuracy_at_threshold(results, t, key=key)['accuracy']
        if a > best[1]:
            best = (float(t), a)
    return best


if __name__ == "__main__":
    print("=" * 70)
    print("CLINICAL CH_2 COHORT — alpha = sqrt(2), base = 3")
    print("=" * 70)
    res = cohort_experiment(n_per_class=20, M=32, T_sec=4.0, fs=256.0,
                             alpha=ALPHA_P, base=3)
    print()
    summarize(res)
    print()

    print("Framework's prescribed threshold 0.95 (rms norm):")
    m = accuracy_at_threshold(res, 0.95, key='rms')
    print(f"  acc={m['accuracy']:.3f}  sens={m['sensitivity']:.3f}  "
          f"spec={m['specificity']:.3f}  (TP={m['tp']} FN={m['fn']} "
          f"TN={m['tn']} FP={m['fp']})")

    best_thr, best_acc = find_best_threshold(res, key='rms')
    print(f"Optimal threshold (rms norm): thr={best_thr:.3f}, acc={best_acc:.3f}")

    print()
    print("Framework's literal 0.95 threshold (literal norm — Ch 30 as written):")
    m = accuracy_at_threshold(res, 0.95, key='literal')
    print(f"  acc={m['accuracy']:.3f}  sens={m['sensitivity']:.3f}  "
          f"spec={m['specificity']:.3f}")
    best_thr_l, best_acc_l = find_best_threshold(res, key='literal')
    print(f"Optimal threshold (literal norm): thr={best_thr_l:.5f}, acc={best_acc_l:.3f}")
