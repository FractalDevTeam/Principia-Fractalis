"""
DENSITY BASELINE — Are the "near matches" actually significant?

With ~195,000 eigenvalues of the difference operator on T^2 x T^2 (counter-
rotating), it would be surprising NOT to find a match within 5% of any
chosen target.  Quantify this by computing the empirical density of the
spectrum near a sliding window of random targets, and compare to the
density near pi/(10·alpha).
"""

from __future__ import annotations

import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from counter_rotating_spectrum import (  # type: ignore
    fourier_table_T2, difference_spectrum, smallest_positive_real,
)

PI = math.pi


def density_in_window(values, target, half_width):
    """Fraction of values in [target - hw, target + hw]."""
    av = np.abs(values)
    return float(np.sum((av >= target - half_width) & (av <= target + half_width))) / av.size


def main():
    M = 10
    n_grid = 512
    print("DENSITY BASELINE — counter-rotating difference operator on T^2 x T^2")
    print("=" * 78)
    for alpha, label in [(math.sqrt(2), "√2"), (1.5, "3/2"), (2.0, "2")]:
        target = PI / (10 * alpha)
        Vhat = fourier_table_T2(alpha, M=M, n_grid=n_grid, distance="geodesic")
        diff, _ = difference_spectrum(Vhat)
        av = np.abs(diff)
        hw = 0.05 * target  # 5% absolute window
        n_hit_target = int(np.sum((av >= target - hw) & (av <= target + hw)))

        # Sample 200 random targets uniformly in [0, max-spectrum] and
        # measure how many of those windows are hit.
        rng = np.random.default_rng(seed=42)
        max_sp = float(np.max(av))
        random_targets = rng.uniform(0, max_sp, size=200)
        random_hits = np.array([
            int(np.sum((av >= rt - hw) & (av <= rt + hw)))
            for rt in random_targets
        ])

        print(f"\nα = {alpha:.6f}  ({label})")
        print(f"  target          = π/(10α) = {target:.10f}")
        print(f"  window halfwidth = 5% of target = {hw:.6e}")
        print(f"  spectrum size    = {av.size:,}")
        print(f"  HITS at target  = {n_hit_target}")
        print(f"  random-target HITS (200 trials):  mean = {random_hits.mean():.1f}   "
              f"median = {np.median(random_hits):.0f}   "
              f"max = {random_hits.max()}")
        print(f"  → fraction of random targets that ALSO get ≥{n_hit_target} hits: "
              f"{float(np.mean(random_hits >= n_hit_target)):.3f}")


if __name__ == "__main__":
    main()
