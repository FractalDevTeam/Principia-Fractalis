"""
NULL TEST: compute min |Re(eig) - t| for many random targets t in [-2, 2]
and see how often t = pi/(10*alpha) is exceptional.

If pi/(10*alpha) is a true prediction, it should be a SHARP minimum (gap << typical
gap for random t). If not, it's just spectral density noise.
"""
import numpy as np
from hp_language_n3 import trivial_spectrum, all_strings_upto

def gap_to_target(eigs_re, t):
    return np.min(np.abs(eigs_re - t))

if __name__ == '__main__':
    for N in [2, 3]:
        for alpha_name, alpha in [('sqrt(2)', np.sqrt(2)),
                                  ('3/2', 1.5),
                                  ('2', 2.0)]:
            eigs = trivial_spectrum(alpha, N)
            eigs_re = np.real(eigs)
            target = np.pi / (10 * alpha)
            gap_target = gap_to_target(eigs_re, target)

            # Random null distribution: 10000 random t in [eigs_re.min(), eigs_re.max()]
            rng = np.random.default_rng(0)
            lo, hi = eigs_re.min(), eigs_re.max()
            ts = rng.uniform(lo, hi, 10000)
            gaps_random = np.array([gap_to_target(eigs_re, t) for t in ts])

            quantile = np.mean(gaps_random < gap_target)
            print(f"N={N} alpha={alpha_name:7s}: target={target:.6f}  "
                  f"gap_target={gap_target:.6e}  median_random={np.median(gaps_random):.6e}  "
                  f"quantile(target<random) = {quantile:.4f}  "
                  f"(target is {'CHANCE' if 0.01 < quantile < 0.99 else 'EXTREME'})")

    # Also test alpha=2, where weights are real: only Hermitian eigenvalues
    print("\nReality check: trivial spectrum at alpha=2 is REAL (phases =1)")
    eigs = trivial_spectrum(2.0, 3)
    print(f"  max |Im(eig)| at alpha=2, N=3: {np.max(np.abs(np.imag(eigs))):.2e}")
    target = np.pi / 20
    print(f"  target pi/20 = {target:.6f}, min |eig-target| = {np.min(np.abs(np.real(eigs)-target)):.6e}")
    # Spectrum has analytic form sum_x (1/2^|x|) eps_x; min gap is just nearest dyadic sum
    print(f"  nearest eigenvalue: {eigs[np.argmin(np.abs(np.real(eigs)-target))]}")
