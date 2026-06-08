"""
predict_ch2.py
===============

Framework's Ch 30 clinical prediction interface.

Usage:
  from predict_ch2 import predict
  result = predict(eeg, fs=256.0)
  print(result)  # {'ch2': 0.78, 'verdict': 'proto-conscious', ...}

Returns the rms-normalized ch_2 (which gives the formula a meaningful
output range across realistic M); the literal Ch 30 (1/(M*5)) norm is
also returned for transparency.
"""

import numpy as np
from ch2_clinical_v2 import ch2_clinical_both
from ch2_clinical import ALPHA_P


def predict(eeg: np.ndarray, fs: float = 256.0,
            alpha: float = ALPHA_P, base: int = 3) -> dict:
    """
    Apply the framework's clinical ch_2 to a single EEG recording.

    Parameters
    ----------
    eeg : (M, N) array — M electrodes, N time samples
    fs  : sample rate (Hz)
    alpha : 1.41421... (sqrt(2), P-class) by default
    base  : 3 by default (framework canonical)

    Returns
    -------
    dict with keys:
      ch2_literal     — Ch 30 line 197 as written (1/(M*5) normalization)
      ch2_rms         — rms-coherence interpretation (1/sqrt(M*5) norm)
      verdict_literal — string label per literal threshold 0.95
      verdict_rms     — string label per rms threshold 0.95
      verdict_optimal — string label per empirically-fit threshold ~0.148
    """
    c_lit, c_rms = ch2_clinical_both(eeg, fs=fs, alpha=alpha, base=base)

    def verdict(v, t_conscious=0.95, t_proto=0.5):
        if v >= t_conscious:
            return 'conscious'
        if v >= t_proto:
            return 'proto-conscious (MCS)'
        return 'unconscious'

    # Empirically-derived threshold from simulation cohort (alpha=sqrt(2),
    # base=3): rms norm threshold ~ 0.148 separates conscious+LIS from
    # coma+veg at ~80% accuracy. This is the only threshold the formula
    # actually supports as written.
    EMPIRICAL_RMS = 0.148
    return {
        'ch2_literal': c_lit,
        'ch2_rms': c_rms,
        'verdict_literal_0.95': verdict(c_lit),
        'verdict_rms_0.95':     verdict(c_rms),
        'verdict_empirical':    'conscious-like' if c_rms >= EMPIRICAL_RMS
                                else 'unconscious-like',
    }


if __name__ == "__main__":
    # Demo: run prediction on one synthetic patient of each class
    from ch2_clinical import SYNTH, PatientSpec
    print("=" * 70)
    print("PREDICT_CH2 DEMO — framework clinical prediction interface")
    print("=" * 70)
    for label, gen in SYNTH.items():
        spec = PatientSpec(label=label, M=32, T_sec=4.0, fs=256.0, seed=777)
        eeg = gen(spec)
        r = predict(eeg, fs=256.0)
        print(f"\n{label}:")
        for k, v in r.items():
            if isinstance(v, float):
                print(f"  {k:<28s} {v:.4f}")
            else:
                print(f"  {k:<28s} {v}")
