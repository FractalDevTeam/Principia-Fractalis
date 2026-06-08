"""
calib_core.py — Calibration-search core for Ch 30 clinical ch_2 formula.

Generalized ch_2 evaluator: (NORM, alpha, base) sweep on synthetic cohort.

  ch_2^{clinical}(NORM, alpha, base) = (1/T) integral_0^T
       | (1/NORM) * sum_{b,j} e^{i pi alpha D_base(n_{b,j}(t))} phi_{b,j}(t) |^2 dt

NORM choices (M = channels, B = 5 bands, N_t = window samples):
  literal_MB     -> M*B               (Ch 30 line 197 literal)
  rms_MB         -> sqrt(M*B)         (coherence-fraction interpretation)
  rms_MBNt       -> sqrt(M*B*N_t)     (square-norm of phi over the window)
  none           -> 1                 (no normalization)
  squared_MB     -> (M*B)^2           (highly suppressive)
"""

from __future__ import annotations

import sys
import os
sys.path.insert(
    0,
    os.path.join(os.path.dirname(__file__), "..", "clinical_ch2_verification"),
)

import numpy as np
from typing import Callable
from ch2_clinical import (
    BANDS, ALPHA_P, ALPHA_NP, ALPHA_RH, ALPHA_QG,
    ALPHA_HODGE, ALPHA_YM, ALPHA_POINCARE,
    digital_sum_vec, bandpass, quantize_power,
    PatientSpec, SYNTH,
)


# -----------------------------------------------------------------------------
# Normalization registry
# -----------------------------------------------------------------------------

ALPHA_PHI = (1 + np.sqrt(5)) / 2  # phi (Hodge)

NORMS = {
    "literal_MB":   lambda M, B, Nt: float(M * B),
    "rms_MB":       lambda M, B, Nt: float(np.sqrt(M * B)),
    "rms_MBNt":     lambda M, B, Nt: float(np.sqrt(M * B * Nt)),
    "none":         lambda M, B, Nt: 1.0,
    "squared_MB":   lambda M, B, Nt: float((M * B) ** 2),
    "rms_M":        lambda M, B, Nt: float(np.sqrt(M)),
    "M_only":       lambda M, B, Nt: float(M),
    "B_only":       lambda M, B, Nt: float(B),
}

ALPHAS = {
    "sqrt2":         np.sqrt(2.0),
    "1p5":           1.5,
    "phi_plus_qtr":  ALPHA_PHI + 0.25,
    "phi":           ALPHA_PHI,
}

BASES = [2, 3, 5]


# -----------------------------------------------------------------------------
# Generalized ch_2 evaluator
# -----------------------------------------------------------------------------

def ch2_generalized(
    eeg: np.ndarray,
    fs: float,
    alpha: float,
    base: int,
    norm_fn: Callable[[int, int, int], float],
    window_sec: float = 0.5,
    clip: bool = False,
) -> float:
    """
    Generalized Ch 30 clinical ch_2 with configurable normalization.

    Parameters
    ----------
    eeg, fs, alpha, base, window_sec: standard.
    norm_fn(M, B, N_t) -> float: normalization denominator (we use 1/norm).
    clip: if True, clip to [0,1]. The whole point of calibration is to find
          the right operating range, so DEFAULT FALSE.

    Returns
    -------
    Raw ch_2 value (may exceed 1 if norm_fn under-normalizes).
    """
    M, N = eeg.shape
    B = len(BANDS)
    window_samples = int(window_sec * fs)
    if window_samples < 8:
        window_samples = 8
    n_windows = N // window_samples
    if n_windows < 1:
        raise ValueError("Recording too short for any window.")

    band_phi_raw = {b: bandpass(eeg, fs, lo, hi)
                    for b, (lo, hi) in BANDS.items()}
    band_phi = {}
    for b in BANDS:
        x = band_phi_raw[b]
        peak = np.max(np.abs(x), axis=-1, keepdims=True) + 1e-12
        band_phi[b] = x / peak
    band_n = {b: quantize_power(band_phi_raw[b], fs, window_samples)
              for b in BANDS}
    band_phase = {
        b: np.exp(1j * np.pi * alpha * digital_sum_vec(band_n[b], base=base))
        for b in BANDS
    }

    norm = 1.0 / norm_fn(M, B, window_samples)
    means = np.zeros(n_windows)
    for w in range(n_windows):
        s0, s1 = w * window_samples, (w + 1) * window_samples
        accum = np.zeros(s1 - s0, dtype=np.complex128)
        for b in BANDS:
            phase = band_phase[b][:, w]
            phi_samples = band_phi[b][:, s0:s1]
            accum += (phase[:, None] * phi_samples).sum(axis=0)
        means[w] = (np.abs(norm * accum) ** 2).mean()

    val = float(means.mean())
    if clip:
        val = float(np.clip(val, 0.0, 1.0))
    return val


# -----------------------------------------------------------------------------
# Synthetic cohort generator with noise injection
# -----------------------------------------------------------------------------

def add_white_noise(eeg: np.ndarray, snr_db: float,
                     rng: np.random.Generator) -> np.ndarray:
    """Add white noise at specified SNR (dB)."""
    if snr_db is None or not np.isfinite(snr_db):
        return eeg
    sig_pow = float(np.mean(eeg ** 2))
    snr_lin = 10 ** (snr_db / 10.0)
    noise_pow = sig_pow / snr_lin
    noise = rng.standard_normal(eeg.shape) * np.sqrt(noise_pow)
    return eeg + noise


def make_cohort(n_per_class: int = 20,
                 M: int = 32,
                 T_sec: float = 5.0,
                 fs: float = 256.0,
                 snr_db: float | None = None,
                 seed_base: int = 20000) -> dict[str, list[np.ndarray]]:
    """Generate synthetic cohort with optional noise injection."""
    cohort = {label: [] for label in SYNTH}
    seed = seed_base
    rng = np.random.default_rng(seed_base + 999)
    for label, gen in SYNTH.items():
        for k in range(n_per_class):
            spec = PatientSpec(label=label, M=M, T_sec=T_sec, fs=fs,
                               seed=seed)
            eeg = gen(spec)
            if snr_db is not None:
                eeg = add_white_noise(eeg, snr_db, rng)
            cohort[label].append(eeg)
            seed += 1
    return cohort


# -----------------------------------------------------------------------------
# Calibration evaluation
# -----------------------------------------------------------------------------

POS_LABELS = ('conscious', 'locked-in')
NEG_LABELS = ('coma', 'vegetative')


def evaluate_calibration(cohort: dict, fs: float, alpha: float, base: int,
                          norm_name: str, window_sec: float = 0.5) -> dict:
    """Compute ch_2 for every patient and return per-class arrays + stats."""
    norm_fn = NORMS[norm_name]
    out = {label: [] for label in cohort}
    for label, eegs in cohort.items():
        for eeg in eegs:
            v = ch2_generalized(eeg, fs, alpha, base, norm_fn,
                                 window_sec=window_sec, clip=False)
            out[label].append(v)
    out = {k: np.array(v) for k, v in out.items()}

    # Binary discriminator: conscious+LIS vs coma+veg
    pos = np.concatenate([out[l] for l in POS_LABELS])
    neg = np.concatenate([out[l] for l in NEG_LABELS])

    # Find optimal threshold via grid sweep on values
    if len(pos) == 0 or len(neg) == 0:
        return {"per_class": out, "best_thr": None, "best_acc": 0.0,
                "cohen_d": 0.0}
    all_v = np.concatenate([pos, neg])
    grid = np.linspace(all_v.min(), all_v.max(), 400)
    best_acc = 0.0
    best_thr = float(np.median(all_v))
    best_sens = 0.0
    best_spec = 0.0
    # Try both polarities (pos > thr or pos < thr) — formula direction
    # could be inverted depending on norm.
    for polarity in (+1, -1):
        for t in grid:
            if polarity > 0:
                tp = int((pos >= t).sum())
                fn = int((pos <  t).sum())
                tn = int((neg <  t).sum())
                fp = int((neg >= t).sum())
            else:
                tp = int((pos <  t).sum())
                fn = int((pos >= t).sum())
                tn = int((neg >= t).sum())
                fp = int((neg <  t).sum())
            acc = (tp + tn) / (tp + fn + tn + fp)
            if acc > best_acc:
                best_acc = acc
                best_thr = float(t)
                best_sens = tp / (tp + fn) if (tp + fn) else 0.0
                best_spec = tn / (tn + fp) if (tn + fp) else 0.0
                best_polarity = polarity

    # Cohen's d
    pooled_std = np.sqrt(0.5 * (pos.std() ** 2 + neg.std() ** 2)) + 1e-12
    cohen_d = float(abs(pos.mean() - neg.mean()) / pooled_std)

    return {
        "per_class": out,
        "pos_mean": float(pos.mean()), "pos_std": float(pos.std()),
        "neg_mean": float(neg.mean()), "neg_std": float(neg.std()),
        "best_thr": best_thr, "best_acc": float(best_acc),
        "best_sens": float(best_sens), "best_spec": float(best_spec),
        "cohen_d": cohen_d,
    }
