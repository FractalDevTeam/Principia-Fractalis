"""
diagnostic_check.py
====================

Investigate the saturation observed for alpha=2 and alpha=NP=phi+1/4.

Framework anchor: at alpha=2, e^(i*pi*2*D) = e^(2*pi*i*D) = 1 for all integer
D, so the phase contribution vanishes and the formula reduces to:

  ch_2 = (1/T) integral |(1/(M*5)) sum phi_{b,j}(t)|^2 dt

i.e., it measures the global phi-amplitude coherence, independent of D_3
information. This explains the saturation in conscious cases where all
phi's are aligned.

For alpha=NP=phi+1/4, the same e^(i*pi*alpha*D) phase is NOT a root of
unity but happens to align in particular ways for specific D distributions.

This script characterizes:
  1. What fraction of integer D values produce phase ~= 1 at each alpha
  2. The distribution of n_{b,j} across the cohort
  3. The actual phi-coherence vs the phase-modulated coherence
"""

import numpy as np
from ch2_clinical import (
    ALPHA_P, ALPHA_NP, ALPHA_RH, ALPHA_QG, ALPHA_YM, ALPHA_HODGE,
    ALPHA_POINCARE, digital_sum, SYNTH, PatientSpec, bandpass,
    quantize_power, BANDS
)


def phase_distribution(alpha: float, base: int = 3, n_max: int = 1000):
    """How does e^(i*pi*alpha*D) distribute as n ranges 0..n_max-1?"""
    D = np.array([digital_sum(n, base=base) for n in range(n_max)])
    phases = np.exp(1j * np.pi * alpha * D)
    mean_phase = phases.mean()
    return D, phases, mean_phase


def main():
    print("=" * 70)
    print("PHASE DISTRIBUTION DIAGNOSTIC (base 3, n in 0..999)")
    print("=" * 70)
    print(f"{'alpha':<22s} {'|<e^(i pi a D)>|':>18s} {'arg':>10s}")
    print("-" * 60)
    for label, a in [
        ('Poincare = 1', ALPHA_POINCARE),
        ('RH = 3/2', ALPHA_RH),
        ('P = sqrt(2)', ALPHA_P),
        ('NP = phi+1/4', ALPHA_NP),
        ('YM = 2', ALPHA_YM),
        ('QG = sqrt(2pi)', ALPHA_QG),
        ('Hodge = phi', ALPHA_HODGE),
    ]:
        D, phases, mp = phase_distribution(a, base=3, n_max=1000)
        print(f"{label:<22s} {abs(mp):>18.4f} {np.angle(mp):>10.4f}")
    print()
    print("INTERPRETATION:")
    print(" |<phase>| ~ 1 means phases collapse to a single value")
    print("   => formula becomes amplitude-coherence (independent of D info)")
    print(" |<phase>| << 1 means phases are spread on the unit circle")
    print("   => formula extracts D_3-conditioned information")
    print()
    print("alpha=2: e^(2 pi i D) = 1 always -> |<phase>| = 1.0 EXACTLY")
    print("        (framework's anchor R_f(2,s) = zeta(s) follows from this)")

    # Now look at the actual n_{b,j}(t) distribution in a real synthetic patient
    print()
    print("=" * 70)
    print("ACTUAL n_{b,j}(t) DISTRIBUTION FROM SYNTHETIC PATIENTS")
    print("=" * 70)
    for label in ['conscious', 'coma']:
        spec = PatientSpec(label=label, M=16, T_sec=4.0, fs=256.0, seed=99)
        eeg = SYNTH[label](spec)
        band_phi_raw = {b: bandpass(eeg, spec.fs, lo, hi)
                         for b, (lo, hi) in BANDS.items()}
        all_n = []
        for b in BANDS:
            n = quantize_power(band_phi_raw[b], spec.fs,
                               window_samples=int(0.5 * spec.fs))
            all_n.append(n.ravel())
        all_n = np.concatenate(all_n)
        print(f"\n  {label}: n in [{all_n.min()}, {all_n.max()}], "
              f"median = {int(np.median(all_n))}, mean = {all_n.mean():.1f}")
        # Distribution of digital sums for these n
        D_actual = np.array([digital_sum(int(v), base=3) for v in all_n])
        print(f"           D_3(n): in [{D_actual.min()}, {D_actual.max()}], "
              f"median = {int(np.median(D_actual))}, mean = {D_actual.mean():.2f}")
        # phase mean over actual distribution
        for a_label, a in [('alpha=sqrt(2)', ALPHA_P),
                            ('alpha=phi+1/4', ALPHA_NP),
                            ('alpha=2', ALPHA_YM)]:
            ph = np.exp(1j * np.pi * a * D_actual)
            print(f"           {a_label}: <phase> = {abs(ph.mean()):.4f}")


if __name__ == "__main__":
    main()
