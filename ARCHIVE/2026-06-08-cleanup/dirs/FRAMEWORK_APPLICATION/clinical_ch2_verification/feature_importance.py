"""
feature_importance.py
======================

Which underlying signal feature drives the discrimination?
Compare:
  - ch_2_clinical (full Ch 30 formula)
  - amplitude_coherence: drop the phase, keep |sum phi|^2 (= alpha->2 limit)
  - gamma_power: just band-limited gamma power
  - inter_electrode_coherence: average pairwise coherence
  - D_3 entropy: Shannon entropy of D_3(n) distribution per band

This tells us how much of the framework's classifier is from the FRACTAL
PHASE structure vs from conventional EEG features.
"""

import numpy as np
from scipy import signal as ssig
from ch2_clinical import (
    BANDS, ALPHA_P, SYNTH, PatientSpec, bandpass, quantize_power,
    digital_sum_vec
)
from ch2_clinical_v2 import ch2_clinical_both


def amplitude_coherence(eeg, fs, window_sec=0.5):
    """|sum phi|^2 averaged — same as alpha=2 limit of ch_2 formula."""
    M, N = eeg.shape
    ws = int(window_sec * fs)
    band_phi_raw = {b: bandpass(eeg, fs, lo, hi) for b, (lo, hi) in BANDS.items()}
    band_phi = {}
    for b in BANDS:
        x = band_phi_raw[b]
        peak = np.max(np.abs(x), axis=-1, keepdims=True) + 1e-12
        band_phi[b] = x / peak
    nw = N // ws
    norm = 1.0 / np.sqrt(M * len(BANDS))
    out = np.zeros(nw)
    for w in range(nw):
        s0, s1 = w*ws, (w+1)*ws
        accum = np.zeros(s1 - s0)
        for b in BANDS:
            accum += band_phi[b][:, s0:s1].sum(axis=0)
        out[w] = ((norm * accum) ** 2).mean()
    return float(np.clip(out.mean(), 0, 1))


def gamma_power(eeg, fs):
    """Mean band-passed gamma power (30-80 Hz)."""
    g = bandpass(eeg, fs, 30.0, 80.0)
    return float(np.mean(g ** 2))


def avg_pairwise_coherence(eeg, fs):
    """Average pairwise spectral coherence across channels (gamma band)."""
    M = eeg.shape[0]
    coh_vals = []
    pairs = [(i, j) for i in range(M) for j in range(i+1, M)]
    # Use subset for speed
    rng = np.random.default_rng(0)
    if len(pairs) > 50:
        idx = rng.choice(len(pairs), 50, replace=False)
        pairs = [pairs[i] for i in idx]
    for i, j in pairs:
        f, Cxy = ssig.coherence(eeg[i], eeg[j], fs=fs, nperseg=128)
        gamma_mask = (f >= 30) & (f <= 80)
        if gamma_mask.any():
            coh_vals.append(np.mean(Cxy[gamma_mask]))
    return float(np.mean(coh_vals)) if coh_vals else 0.0


def D3_entropy(eeg, fs, window_sec=0.5, base=3):
    """Shannon entropy of D_3(n) distribution across all bands+channels+windows."""
    ws = int(window_sec * fs)
    all_D = []
    for b, (lo, hi) in BANDS.items():
        phi = bandpass(eeg, fs, lo, hi)
        n = quantize_power(phi, fs, ws)
        D = digital_sum_vec(n, base=base)
        all_D.append(D.ravel())
    all_D = np.concatenate(all_D)
    counts = np.bincount(all_D)
    p = counts / counts.sum()
    p = p[p > 0]
    H = -np.sum(p * np.log2(p))
    return float(H)


def collect_features(n_per_class=15, M=24, T_sec=3.0, fs=256.0):
    rows = []
    seed = 5000
    for label, gen in SYNTH.items():
        for k in range(n_per_class):
            spec = PatientSpec(label=label, M=M, T_sec=T_sec, fs=fs, seed=seed)
            eeg = gen(spec)
            c_lit, c_rms = ch2_clinical_both(eeg, fs, alpha=ALPHA_P, base=3)
            ac = amplitude_coherence(eeg, fs)
            gp = gamma_power(eeg, fs)
            ipc = avg_pairwise_coherence(eeg, fs)
            ent = D3_entropy(eeg, fs)
            rows.append({
                'label': label,
                'ch2_rms': c_rms,
                'ch2_lit': c_lit,
                'amp_coh': ac,
                'gamma_pow': gp,
                'inter_coh': ipc,
                'D3_entropy': ent,
            })
            seed += 1
    return rows


def discrimination_score(rows, feature):
    pos = [r[feature] for r in rows if r['label'] in ('conscious', 'locked-in')]
    neg = [r[feature] for r in rows if r['label'] in ('coma', 'vegetative')]
    pos = np.array(pos); neg = np.array(neg)
    s = np.sqrt(0.5*(pos.std()**2 + neg.std()**2))
    if s < 1e-12:
        return 0.0
    return float((pos.mean() - neg.mean()) / s)


if __name__ == "__main__":
    print("Collecting features across cohort (this takes ~1 min)...")
    rows = collect_features(n_per_class=15, M=24, T_sec=3.0, fs=256.0)
    print()
    print("=" * 60)
    print("FEATURE DISCRIMINATION (Cohen's d, conscious+LIS vs coma+veg)")
    print("=" * 60)
    print(f"{'feature':<20s} {'Cohen d':>10s}")
    print("-" * 32)
    for feat in ['ch2_rms', 'ch2_lit', 'amp_coh', 'gamma_pow',
                  'inter_coh', 'D3_entropy']:
        d = discrimination_score(rows, feat)
        print(f"{feat:<20s} {d:>10.3f}")

    # Correlation of ch2_rms with each feature
    print()
    print("CORRELATION of ch_2 (rms norm) with other features:")
    ch2 = np.array([r['ch2_rms'] for r in rows])
    for feat in ['amp_coh', 'gamma_pow', 'inter_coh', 'D3_entropy']:
        v = np.array([r[feat] for r in rows])
        if v.std() > 0:
            corr = np.corrcoef(ch2, v)[0, 1]
            print(f"  ch2_rms vs {feat:<14s}: r = {corr:+.3f}")
