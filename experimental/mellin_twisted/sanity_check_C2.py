"""
At the 'hit' configs (C_sandwich, eps=0.1), check what RANK eigenvalue is matching.
If it's not the lowest positive — the hit is meaningless.
"""
import numpy as np
from mellin_twisted import construction_c_sandwich, diagonalize

CASES = [
    ("sqrt2", np.sqrt(2.0), np.pi/(10*np.sqrt(2.0)), 3, 0.1),
    ("3/2",   1.5,           np.pi/15,                4, 0.1),
    ("2",     2.0,           np.pi/20,                3, 0.1),
    ("sqrt2", np.sqrt(2.0), np.pi/(10*np.sqrt(2.0)), 3, np.pi/10),
]

for aname, alpha, target, k, eps in CASES:
    L = k * np.log(alpha)
    M, _ = construction_c_sandwich(alpha, eps, L, 800)
    w = diagonalize(M, k=None)
    pos = w[w > 1e-10]
    pos_sorted = np.sort(pos)
    # Index closest to target
    idx = int(np.argmin(np.abs(pos_sorted - target)))
    closest = pos_sorted[idx]
    print(f"\nalpha={aname} k={k} eps={eps:.4f} target={target:.5f}")
    print(f"  closest in positive spectrum = {closest:.6f}  (rank {idx} of {len(pos_sorted)} positives)")
    print(f"  lowest 8 positives: {pos_sorted[:8]}")
    print(f"  positives near target: {pos_sorted[max(0,idx-3):idx+4]}")
