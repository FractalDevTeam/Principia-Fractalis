"""
Principia Fractalis — Clinical ch_2 Formula Implementation
===========================================================

Ch 30 line 197 clinical consciousness measurement:

  ch_2^{clinical} = (1/T) integral_0^T |(1/(M*5)) Sum_{b in bands} Sum_{j=1}^M
                       e^{i*pi*alpha*D(n_{b,j}(t))} * phi_{b,j}(t)|^2 dt

where:
  T        = recording duration window (seconds)
  M        = number of EEG electrodes
  bands    = {delta, theta, alpha, beta, gamma} (5 bands)
  D(n)     = base-3 digital sum (framework's core invariant)
  phi      = band-filtered signal at electrode j
  n_{b,j}  = quantized power = floor(1000 * integral |F_b(phi_j)|^2 dt)
  alpha    = framework parameter (alpha_P = sqrt(2) for clinical context)

Threshold: ch_2 >= 0.95 <=> conscious (framework Ch 6 Chern-Weil derivation)

APPLICATION MODE: We are implementing the framework as given. The goal is to
establish COMPUTABILITY and INTERNAL CONSISTENCY of the clinical formula, not
to adversarially test against external standards.
"""

import numpy as np
from scipy import signal
from dataclasses import dataclass


# =============================================================================
# Framework constants
# =============================================================================

ALPHA_P = np.sqrt(2.0)         # P-class, clinical default
ALPHA_NP = (1 + np.sqrt(5)) / 2 + 0.25   # phi + 1/4
ALPHA_RH = 1.5
ALPHA_QG = np.sqrt(2 * np.pi)
ALPHA_HODGE = (1 + np.sqrt(5)) / 2       # phi
ALPHA_YM = 2.0
ALPHA_POINCARE = 1.0

# Clinical bands (Hz)
BANDS = {
    'delta': (0.5, 4.0),
    'theta': (4.0, 8.0),
    'alpha': (8.0, 13.0),
    'beta':  (13.0, 30.0),
    'gamma': (30.0, 80.0),
}

THRESHOLD_CONSCIOUS = 0.95
THRESHOLD_PROTO     = 0.50


# =============================================================================
# Digital sums (the framework's core invariant)
# =============================================================================

def digital_sum(n: int, base: int = 3) -> int:
    """Sum of digits of n in given base. D_3 is the framework's canonical choice."""
    if n < 0:
        n = -n
    if n == 0:
        return 0
    s = 0
    while n > 0:
        s += n % base
        n //= base
    return s


def digital_sum_vec(arr: np.ndarray, base: int = 3) -> np.ndarray:
    """Vectorized digital sum on an integer array."""
    out = np.empty_like(arr, dtype=np.int64)
    flat = arr.ravel()
    res = np.empty(flat.shape, dtype=np.int64)
    for i, v in enumerate(flat):
        res[i] = digital_sum(int(v), base)
    return res.reshape(arr.shape)


# =============================================================================
# Band-pass filtering
# =============================================================================

def bandpass(x: np.ndarray, fs: float, lo: float, hi: float, order: int = 4) -> np.ndarray:
    """Zero-phase Butterworth band-pass; x is (M, N_samples)."""
    nyq = 0.5 * fs
    lo_n = max(lo / nyq, 1e-4)
    hi_n = min(hi / nyq, 0.999)
    b, a = signal.butter(order, [lo_n, hi_n], btype='band')
    return signal.filtfilt(b, a, x, axis=-1)


# =============================================================================
# Clinical ch_2 (the framework's Ch 30 line 197 formula)
# =============================================================================

def quantize_power(phi_b: np.ndarray, fs: float, window_samples: int) -> np.ndarray:
    """
    n_{b,j}(t) = floor(1000 * integral_window |phi_b(s)|^2 ds)

    Returns an integer array of shape (M, n_windows).
    """
    M, N = phi_b.shape
    dt = 1.0 / fs
    n_windows = N // window_samples
    power = np.zeros((M, n_windows), dtype=np.int64)
    for w in range(n_windows):
        seg = phi_b[:, w * window_samples:(w + 1) * window_samples]
        integ = np.sum(seg ** 2, axis=-1) * dt
        power[:, w] = np.floor(1000.0 * integ).astype(np.int64)
    return power


def ch2_clinical(eeg: np.ndarray, fs: float, alpha: float = ALPHA_P,
                 base: int = 3, window_sec: float = 0.5) -> float:
    """
    Compute ch_2^clinical per Ch 30 line 197.

    Parameters
    ----------
    eeg : (M, N_samples) array — EEG voltage in arbitrary units
    fs  : sample rate (Hz)
    alpha : framework parameter (default sqrt(2) = alpha_P)
    base  : digital-sum radix (framework canonical = 3)
    window_sec : time-window for quantization (default 0.5 s)

    Returns
    -------
    ch2 in [0, 1]
    """
    M, N = eeg.shape
    window_samples = int(window_sec * fs)
    if window_samples < 8:
        window_samples = 8
    n_windows = N // window_samples
    if n_windows < 1:
        raise ValueError("Recording too short for any window.")

    # Per-band filtered signals (raw)
    band_phi_raw = {b: bandpass(eeg, fs, lo, hi) for b, (lo, hi) in BANDS.items()}

    # Per-band per-channel L^infinity normalization so |phi_{b,j}(t)| <= 1
    # for all t. This matches the Ch 30 convention that phi_{b,j} is a
    # dimensionless mode amplitude, and guarantees ch_2 in [0,1].
    band_phi = {}
    for b in BANDS:
        x = band_phi_raw[b]
        peak = np.max(np.abs(x), axis=-1, keepdims=True) + 1e-12
        band_phi[b] = x / peak

    # Per-band quantized power -> integer index n_{b,j}(t)
    # IMPORTANT: power is computed on the RAW band-passed signal (not the
    # normalized phi) so n carries band-energy information across patients.
    band_n = {b: quantize_power(band_phi_raw[b], fs, window_samples) for b in BANDS}

    # Pre-compute digital sums and phases per band/electrode/window
    band_phase = {}
    for b in BANDS:
        D = digital_sum_vec(band_n[b], base=base)
        band_phase[b] = np.exp(1j * np.pi * alpha * D)  # shape (M, n_windows)

    # Build the per-window integrand:
    #   I(t_w) = |(1/(M*5)) sum_{b,j} e^{i*pi*alpha*D} * phi_{b,j}(t)|^2
    # averaged over samples within the window, then averaged over windows.
    #
    # INTERPRETATION NOTE (APPLICATION MODE):
    # The literal Ch 30 normalization 1/(M*5) corresponds to a coherence
    # measure: it equals 1 when all M*5 phases align (perfect global
    # consciousness coupling) and 1/(M*5) when each contribution is
    # incoherent unit-magnitude. Synthetic incoherent baseline ~ O(1/(M*5)).
    # For a clinical CLASSIFIER that maps to [0,1] cleanly across realistic
    # M, the framework's effective measure must be normalized as an
    # rms-coherence: divide by sqrt(M*5) to get the per-mode amplitude, then
    # square to get a fraction-of-coherence. Both conventions are tested in
    # alternative_norms.py to make this explicit.
    norm = 1.0 / (M * len(BANDS))
    window_means = np.zeros(n_windows)
    for w in range(n_windows):
        s0, s1 = w * window_samples, (w + 1) * window_samples
        # accumulate complex sum at each sample inside window
        accum = np.zeros(s1 - s0, dtype=np.complex128)
        for b in BANDS:
            phase = band_phase[b][:, w]          # (M,)
            phi_samples = band_phi[b][:, s0:s1]  # (M, window_samples)
            # sum over electrodes of phase[j] * phi[j, t]
            accum += (phase[:, None] * phi_samples).sum(axis=0)
        integrand = np.abs(norm * accum) ** 2
        window_means[w] = integrand.mean()

    ch2 = float(window_means.mean())
    # The formula as written naturally lives in [0, 1] because the average
    # of |phi_{b,j}|^2 ~ 1 and the (1/(M*5)) prefactor with M*5 terms summed
    # coherently gives at most magnitude ~ 1. We clip for numerical safety.
    return float(np.clip(ch2, 0.0, 1.0))


# =============================================================================
# Synthetic patient generators
# =============================================================================

@dataclass
class PatientSpec:
    label: str         # 'conscious', 'mcs', 'vegetative', 'coma', 'locked-in'
    M: int = 64
    T_sec: float = 10.0
    fs: float = 256.0
    seed: int = 0


def synth_conscious(spec: PatientSpec) -> np.ndarray:
    """High inter-channel coherence + gamma-band activity."""
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    t = np.arange(N) / spec.fs
    # Shared gamma oscillation (40 Hz) drives most channels coherently
    shared_gamma = np.sin(2 * np.pi * 40.0 * t)
    shared_beta = 0.6 * np.sin(2 * np.pi * 20.0 * t + 0.3)
    shared_alpha = 0.4 * np.sin(2 * np.pi * 10.0 * t + 0.7)
    eeg = np.zeros((spec.M, N))
    for j in range(spec.M):
        local_noise = 0.4 * rng.standard_normal(N)
        eeg[j] = shared_gamma + shared_beta + shared_alpha + local_noise
    return eeg


def synth_unconscious(spec: PatientSpec) -> np.ndarray:
    """Low coherence, delta-dominant (coma / deep anesthesia)."""
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    t = np.arange(N) / spec.fs
    eeg = np.zeros((spec.M, N))
    for j in range(spec.M):
        # Each channel: independent delta oscillation + lots of noise
        phase = rng.uniform(0, 2 * np.pi)
        freq = rng.uniform(1.0, 3.5)
        delta = 2.0 * np.sin(2 * np.pi * freq * t + phase)
        noise = 1.0 * rng.standard_normal(N)
        eeg[j] = delta + noise
    return eeg


def synth_mcs(spec: PatientSpec) -> np.ndarray:
    """Minimally conscious: intermediate coherence, mixed bands."""
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    t = np.arange(N) / spec.fs
    # Partially shared alpha rhythm, weak gamma, plus per-channel noise
    shared_alpha = 0.6 * np.sin(2 * np.pi * 10.0 * t)
    shared_theta = 0.5 * np.sin(2 * np.pi * 6.0 * t + 0.2)
    eeg = np.zeros((spec.M, N))
    for j in range(spec.M):
        weak_gamma = 0.15 * np.sin(2 * np.pi * 40.0 * t + rng.uniform(0, 2 * np.pi))
        local = 0.8 * rng.standard_normal(N)
        eeg[j] = shared_alpha + shared_theta + weak_gamma + local
    return eeg


def synth_vegetative(spec: PatientSpec) -> np.ndarray:
    """Vegetative: low-amplitude, mostly delta + theta, low coherence."""
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    t = np.arange(N) / spec.fs
    eeg = np.zeros((spec.M, N))
    weak_shared_delta = 0.3 * np.sin(2 * np.pi * 2.0 * t)
    for j in range(spec.M):
        local_theta = 0.4 * np.sin(2 * np.pi * rng.uniform(4, 7) * t +
                                    rng.uniform(0, 2 * np.pi))
        noise = 0.9 * rng.standard_normal(N)
        eeg[j] = weak_shared_delta + local_theta + noise
    return eeg


def synth_locked_in(spec: PatientSpec) -> np.ndarray:
    """Locked-in: like conscious (gamma + beta coherent), motor cortex altered."""
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    t = np.arange(N) / spec.fs
    shared_gamma = 0.9 * np.sin(2 * np.pi * 42.0 * t)
    shared_beta = 0.7 * np.sin(2 * np.pi * 22.0 * t + 0.5)
    shared_alpha = 0.5 * np.sin(2 * np.pi * 11.0 * t)
    eeg = np.zeros((spec.M, N))
    for j in range(spec.M):
        local = 0.45 * rng.standard_normal(N)
        eeg[j] = shared_gamma + shared_beta + shared_alpha + local
    return eeg


SYNTH = {
    'conscious':  synth_conscious,
    'mcs':        synth_mcs,
    'vegetative': synth_vegetative,
    'coma':       synth_unconscious,
    'locked-in':  synth_locked_in,
}


def classify(ch2_value: float) -> str:
    if ch2_value >= THRESHOLD_CONSCIOUS:
        return 'conscious'
    if ch2_value >= THRESHOLD_PROTO:
        return 'proto-conscious'
    return 'unconscious'


if __name__ == "__main__":
    # Minimal demo: one patient of each class
    print("=" * 70)
    print("ch_2 clinical demo — single patient per class, alpha = sqrt(2)")
    print("=" * 70)
    for label, gen in SYNTH.items():
        spec = PatientSpec(label=label, M=32, T_sec=4.0, fs=256.0, seed=42)
        eeg = gen(spec)
        ch2 = ch2_clinical(eeg, fs=spec.fs, alpha=ALPHA_P, base=3)
        verdict = classify(ch2)
        print(f"  {label:11s} -> ch_2 = {ch2:.4f}   verdict: {verdict}")
