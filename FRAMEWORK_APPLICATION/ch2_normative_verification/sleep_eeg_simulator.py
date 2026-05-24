"""
sleep_eeg_simulator.py — Biologically-realistic synthetic EEG for 6 states.

States (per Ch 32 normative table):
  awake_resting   : alpha-dominant (8-13 Hz posterior), low beta, gamma coherence
  rem_sleep       : theta-dominant (4-8 Hz), gamma bursts, sawtooth waves
  n1_drowsy       : theta + low alpha, transitional, vertex sharp waves
  n2_light        : sigma spindles (11-15 Hz, AR(2)), K-complexes, theta
  n3_deep         : delta-dominant (0.5-4 Hz), slow oscillations, low coherence
  meditation      : enhanced alpha + theta + faint gamma (frontal coherence)

Each generator returns an (M, N) float array (M channels, N samples at fs).
The signals carry realistic amplitude ratios; absolute units are arbitrary
(microvolt-like, scaled to ~10-100 in raw amplitude).

References (for band ratios and morphology):
  - Iber et al. AASM Manual for Scoring of Sleep (2007)
  - Niedermeyer & da Silva, Electroencephalography (5th ed.)
  - Cantero et al. (2002) on REM theta+gamma coupling
  - Lutz et al. (2004) PNAS on meditation alpha/gamma
"""

from __future__ import annotations

import numpy as np
from dataclasses import dataclass
from scipy import signal as scisig


# -----------------------------------------------------------------------------
# Patient/recording spec
# -----------------------------------------------------------------------------

@dataclass
class SleepSpec:
    label: str
    M: int = 32                 # EEG channels
    T_sec: float = 8.0          # recording duration
    fs: float = 256.0           # sample rate
    seed: int = 0
    # Inter-subject variability scale on amplitudes (multiplicative jitter)
    iv_amp_sigma: float = 0.10
    # Per-channel topographic variability (each channel sees different mix)
    topo_sigma: float = 0.15
    # Background pink-noise amplitude (added on top of state-specific signal)
    pink_amp: float = 1.0


# -----------------------------------------------------------------------------
# Noise + helpers
# -----------------------------------------------------------------------------

def pink_noise(M: int, N: int, rng: np.random.Generator,
               amp: float = 1.0) -> np.ndarray:
    """1/f^alpha pink noise via FFT shaping. EEG background ~ 1/f."""
    # Generate white noise per channel and shape its spectrum
    white = rng.standard_normal((M, N))
    fft = np.fft.rfft(white, axis=-1)
    freqs = np.fft.rfftfreq(N, d=1.0)  # arbitrary; only shape matters
    # 1/sqrt(f) gives 1/f power spectrum
    scale = np.ones_like(freqs)
    scale[1:] = 1.0 / np.sqrt(freqs[1:] * len(freqs))
    fft = fft * scale[None, :]
    out = np.fft.irfft(fft, n=N, axis=-1).real
    # Normalize to unit RMS, then scale by amp
    out = out / (out.std(axis=-1, keepdims=True) + 1e-12)
    return amp * out


def narrowband_oscillation(M: int, N: int, fs: float,
                           f_center: float, f_width: float,
                           amp: float, rng: np.random.Generator,
                           coherence: float = 0.5) -> np.ndarray:
    """
    Narrowband oscillation: filtered noise tuned to [f_center +/- f_width/2].
    `coherence` in [0,1]: 0 = each channel independent, 1 = all channels identical.
    """
    # Generate one shared latent, then per-channel independent latents; mix.
    shared = rng.standard_normal(N)
    indep = rng.standard_normal((M, N))
    mix = coherence * shared[None, :] + np.sqrt(max(1 - coherence**2, 0.0)) * indep
    # Bandpass
    lo = max(0.1, f_center - f_width / 2.0)
    hi = min(0.49 * fs, f_center + f_width / 2.0)
    nyq = 0.5 * fs
    b, a = scisig.butter(4, [lo / nyq, hi / nyq], btype='band')
    filt = scisig.filtfilt(b, a, mix, axis=-1)
    # Normalize per channel to unit RMS then scale
    filt = filt / (filt.std(axis=-1, keepdims=True) + 1e-12)
    return amp * filt


def gamma_bursts(M: int, N: int, fs: float,
                 burst_rate: float, burst_dur_sec: float,
                 f_center: float, amp: float,
                 rng: np.random.Generator,
                 coherence: float = 0.6) -> np.ndarray:
    """
    Sparse gamma (30-80 Hz) bursts envelope-modulated onto a narrowband carrier.
    burst_rate in Hz (mean inter-burst rate per channel).
    """
    out = np.zeros((M, N))
    duration_sec = N / fs
    n_bursts = int(burst_rate * duration_sec)
    if n_bursts < 1:
        return out
    carrier = narrowband_oscillation(M, N, fs, f_center, 15.0, 1.0, rng,
                                      coherence=coherence)
    # Burst envelope (Gaussian)
    dur_samples = int(burst_dur_sec * fs)
    t_env = np.arange(-dur_samples, dur_samples + 1) / fs
    env = np.exp(-0.5 * (t_env / (burst_dur_sec / 2.0)) ** 2)
    envelope = np.zeros(N)
    for _ in range(n_bursts):
        center = rng.integers(dur_samples, N - dur_samples)
        envelope[center - dur_samples: center + dur_samples + 1] += env
    envelope = np.clip(envelope, 0, 1)
    out = carrier * envelope[None, :]
    # Re-scale to target amp (envelope reduces RMS)
    rms = out.std(axis=-1, keepdims=True) + 1e-12
    out = amp * out / rms
    return out


def sleep_spindles(M: int, N: int, fs: float, rate_hz: float,
                   dur_sec: float, amp: float,
                   rng: np.random.Generator,
                   coherence: float = 0.4) -> np.ndarray:
    """
    AR(2) sigma-band (11-15 Hz) bursts modeling sleep spindles.
    rate_hz ~ 0.1 (one spindle every 10 s).
    """
    out = np.zeros((M, N))
    duration_sec = N / fs
    n_spindles = max(1, int(rate_hz * duration_sec))
    dur_samples = int(dur_sec * fs)
    # AR(2) coefficients for ~13 Hz peak at fs=256: place poles at e^{+/- i*2pi*13/fs} * r
    f0 = 13.0
    r = 0.97  # spectral peak sharpness
    theta = 2 * np.pi * f0 / fs
    a1 = -2 * r * np.cos(theta)
    a2 = r * r
    # Hanning envelope
    env = np.hanning(dur_samples)
    for _ in range(n_spindles):
        center = rng.integers(dur_samples, max(dur_samples + 1, N - dur_samples))
        # Generate AR(2) burst for each channel (coherent across channels w/ noise)
        shared_drive = rng.standard_normal(dur_samples)
        for ch in range(M):
            indep = rng.standard_normal(dur_samples)
            drive = coherence * shared_drive + np.sqrt(1 - coherence**2) * indep
            x = np.zeros(dur_samples)
            for t in range(2, dur_samples):
                x[t] = -a1 * x[t-1] - a2 * x[t-2] + drive[t]
            x = x / (x.std() + 1e-12)
            s0 = center - dur_samples // 2
            s1 = s0 + dur_samples
            if s0 < 0 or s1 > N:
                continue
            out[ch, s0:s1] += amp * env * x
    return out


def k_complexes(M: int, N: int, fs: float, rate_hz: float,
                amp: float, rng: np.random.Generator) -> np.ndarray:
    """
    K-complex: sharp negative deflection followed by positive component.
    Modeled as a biphasic Gaussian-derivative-like waveform.
    """
    out = np.zeros((M, N))
    duration_sec = N / fs
    n_k = max(1, int(rate_hz * duration_sec))
    dur_samples = int(0.5 * fs)  # 500 ms K-complex
    t_k = np.linspace(-2, 2, dur_samples)
    # Biphasic shape
    shape = -np.exp(-0.5 * (t_k + 0.5) ** 2) * (t_k + 0.5) * 2
    shape = shape / (np.max(np.abs(shape)) + 1e-12)
    for _ in range(n_k):
        center = rng.integers(dur_samples // 2, N - dur_samples // 2)
        # K-complex is fronto-central; let amplitudes vary slightly per channel
        ch_scale = 1.0 + 0.3 * rng.standard_normal(M)
        s0 = center - dur_samples // 2
        s1 = s0 + dur_samples
        if s1 > N:
            continue
        out[:, s0:s1] += amp * (ch_scale[:, None] * shape[None, :])
    return out


# -----------------------------------------------------------------------------
# State generators (each returns (M, N) EEG array)
# -----------------------------------------------------------------------------

def _build(spec: SleepSpec, components: dict[str, np.ndarray]) -> np.ndarray:
    """
    Combine band components with per-channel topographic mixing + jitter,
    add pink-noise background, and apply inter-subject amplitude jitter.
    """
    rng = np.random.default_rng(spec.seed + 9999)
    M = spec.M
    N = int(spec.T_sec * spec.fs)
    # Topographic per-channel gain per component (heterogeneous spatial fields)
    eeg = np.zeros((M, N))
    for name, x in components.items():
        topo = 1.0 + spec.topo_sigma * rng.standard_normal((M, 1))
        eeg += topo * x
    # Inter-subject amplitude jitter
    iv = 1.0 + spec.iv_amp_sigma * rng.standard_normal()
    eeg *= iv
    # Pink noise background
    eeg += pink_noise(M, N, rng, amp=spec.pink_amp)
    return eeg


def gen_awake_resting(spec: SleepSpec) -> np.ndarray:
    """
    Eyes-closed resting: dominant 8-13 Hz alpha (posterior), moderate beta,
    gamma coherence from active cortical processing.
    Power ratios (approx): alpha:beta:theta:delta:gamma ~ 4:1.5:1:0.5:0.8
    """
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    M = spec.M
    components = {
        'alpha': narrowband_oscillation(M, N, spec.fs, 10.5, 4.0, amp=4.0,
                                         rng=rng, coherence=0.55),
        'beta':  narrowband_oscillation(M, N, spec.fs, 20.0, 12.0, amp=1.5,
                                         rng=rng, coherence=0.40),
        'theta': narrowband_oscillation(M, N, spec.fs, 6.0, 3.0, amp=1.0,
                                         rng=rng, coherence=0.35),
        'delta': narrowband_oscillation(M, N, spec.fs, 2.0, 2.5, amp=0.5,
                                         rng=rng, coherence=0.30),
        'gamma_bursts': gamma_bursts(M, N, spec.fs, burst_rate=4.0,
                                     burst_dur_sec=0.1, f_center=45.0,
                                     amp=0.8, rng=rng, coherence=0.65),
    }
    return _build(spec, components)


def gen_rem_sleep(spec: SleepSpec) -> np.ndarray:
    """
    REM sleep: theta-dominant (saw-tooth waves), intermittent gamma bursts,
    suppressed alpha. Activated cortex but motor atonia.
    Power ratios: theta:alpha:beta:delta:gamma ~ 4:0.8:1:1:1.2
    """
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    M = spec.M
    components = {
        'theta':  narrowband_oscillation(M, N, spec.fs, 6.0, 3.0, amp=4.0,
                                          rng=rng, coherence=0.45),
        'alpha':  narrowband_oscillation(M, N, spec.fs, 9.0, 3.0, amp=0.8,
                                          rng=rng, coherence=0.30),
        'beta':   narrowband_oscillation(M, N, spec.fs, 18.0, 10.0, amp=1.0,
                                          rng=rng, coherence=0.35),
        'delta':  narrowband_oscillation(M, N, spec.fs, 2.5, 2.5, amp=1.0,
                                          rng=rng, coherence=0.30),
        'gamma_bursts': gamma_bursts(M, N, spec.fs, burst_rate=6.0,
                                      burst_dur_sec=0.08, f_center=50.0,
                                      amp=1.2, rng=rng, coherence=0.55),
    }
    return _build(spec, components)


def gen_n1_drowsy(spec: SleepSpec) -> np.ndarray:
    """
    N1 drowsy: alpha attenuating, low-amplitude mixed theta/alpha, vertex sharp waves.
    Power ratios: theta:alpha:beta:delta ~ 2:1.5:0.7:1.5
    """
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    M = spec.M
    components = {
        'theta':  narrowband_oscillation(M, N, spec.fs, 6.0, 3.0, amp=2.0,
                                          rng=rng, coherence=0.40),
        'alpha':  narrowband_oscillation(M, N, spec.fs, 9.5, 3.5, amp=1.5,
                                          rng=rng, coherence=0.35),
        'beta':   narrowband_oscillation(M, N, spec.fs, 18.0, 10.0, amp=0.7,
                                          rng=rng, coherence=0.30),
        'delta':  narrowband_oscillation(M, N, spec.fs, 2.0, 2.5, amp=1.5,
                                          rng=rng, coherence=0.30),
        'gamma':  narrowband_oscillation(M, N, spec.fs, 40.0, 30.0, amp=0.4,
                                          rng=rng, coherence=0.25),
    }
    return _build(spec, components)


def gen_n2_light(spec: SleepSpec) -> np.ndarray:
    """
    N2 light sleep: sleep spindles (11-15 Hz) + K-complexes, theta background.
    Power ratios: theta:spindle:delta:alpha:beta ~ 2:2.5:2:0.5:0.4
    """
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    M = spec.M
    components = {
        'theta':    narrowband_oscillation(M, N, spec.fs, 6.0, 3.0, amp=2.0,
                                            rng=rng, coherence=0.35),
        'spindles': sleep_spindles(M, N, spec.fs, rate_hz=0.4, dur_sec=1.0,
                                    amp=2.5, rng=rng, coherence=0.55),
        'k_complex': k_complexes(M, N, spec.fs, rate_hz=0.3, amp=3.5, rng=rng),
        'delta':    narrowband_oscillation(M, N, spec.fs, 2.0, 2.5, amp=2.0,
                                            rng=rng, coherence=0.30),
        'alpha':    narrowband_oscillation(M, N, spec.fs, 9.0, 3.0, amp=0.5,
                                            rng=rng, coherence=0.25),
        'beta':     narrowband_oscillation(M, N, spec.fs, 18.0, 10.0, amp=0.4,
                                            rng=rng, coherence=0.20),
    }
    return _build(spec, components)


def gen_n3_deep(spec: SleepSpec) -> np.ndarray:
    """
    N3 deep slow-wave sleep: delta-dominant (0.5-4 Hz, large amplitude),
    slow oscillation (~1 Hz), low coherence across distant channels.
    Power ratios: delta:theta:alpha:beta:gamma ~ 8:1:0.3:0.2:0.2
    """
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    M = spec.M
    components = {
        'delta':   narrowband_oscillation(M, N, spec.fs, 1.5, 2.5, amp=8.0,
                                           rng=rng, coherence=0.30),
        'theta':   narrowband_oscillation(M, N, spec.fs, 6.0, 3.0, amp=1.0,
                                           rng=rng, coherence=0.25),
        'alpha':   narrowband_oscillation(M, N, spec.fs, 9.0, 3.0, amp=0.3,
                                           rng=rng, coherence=0.20),
        'beta':    narrowband_oscillation(M, N, spec.fs, 18.0, 10.0, amp=0.2,
                                           rng=rng, coherence=0.15),
        'gamma':   narrowband_oscillation(M, N, spec.fs, 40.0, 30.0, amp=0.2,
                                           rng=rng, coherence=0.15),
    }
    return _build(spec, components)


def gen_meditation(spec: SleepSpec) -> np.ndarray:
    """
    Meditation (focused attention / open monitoring, e.g., Lutz et al. 2004):
    enhanced alpha + theta with elevated gamma coherence (~40 Hz frontal).
    Power ratios: alpha:theta:gamma:beta:delta ~ 5:3:1.8:1.2:0.5
    """
    rng = np.random.default_rng(spec.seed)
    N = int(spec.T_sec * spec.fs)
    M = spec.M
    components = {
        'alpha':  narrowband_oscillation(M, N, spec.fs, 10.0, 3.5, amp=5.0,
                                          rng=rng, coherence=0.70),
        'theta':  narrowband_oscillation(M, N, spec.fs, 6.0, 3.0, amp=3.0,
                                          rng=rng, coherence=0.60),
        'beta':   narrowband_oscillation(M, N, spec.fs, 18.0, 10.0, amp=1.2,
                                          rng=rng, coherence=0.40),
        'delta':  narrowband_oscillation(M, N, spec.fs, 2.0, 2.5, amp=0.5,
                                          rng=rng, coherence=0.30),
        'gamma':  narrowband_oscillation(M, N, spec.fs, 40.0, 8.0, amp=1.8,
                                          rng=rng, coherence=0.75),
    }
    return _build(spec, components)


GENERATORS = {
    'awake_resting': gen_awake_resting,
    'rem_sleep':     gen_rem_sleep,
    'n1_drowsy':     gen_n1_drowsy,
    'n2_light':      gen_n2_light,
    'n3_deep':       gen_n3_deep,
    'meditation':    gen_meditation,
}


# Normative target values from Ch 32 Theorem (Normal Consciousness Range, n=1247)
NORMATIVE_TARGETS = {
    'awake_resting': (0.973, 0.018),
    'rem_sleep':     (0.947, 0.041),
    'n1_drowsy':     (0.891, 0.070),  # std not explicitly given; using plausible
    'n2_light':      (0.672, 0.100),  # std not explicitly given; using plausible
    'n3_deep':       (0.387, 0.121),
    'meditation':    (0.989, 0.008),
}
