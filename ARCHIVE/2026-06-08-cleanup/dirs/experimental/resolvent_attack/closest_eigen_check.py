"""Quick post-hoc check: closest eigenvalue to target across all (alpha,k) runs."""
import os, math, numpy as np
OUT = os.path.dirname(os.path.abspath(__file__))
for fn in sorted(os.listdir(OUT)):
    if fn.startswith('poles_') and fn.endswith('.npz'):
        d = np.load(os.path.join(OUT, fn))
        w = d['eigvals']
        tgt = float(d['target'])
        diffs = np.abs(w - tgt)
        i = int(np.argmin(diffs))
        # also smallest |lambda|
        j = int(np.argmin(np.abs(w)))
        print(f"{fn}: target={tgt:.6f}, closest eigenvalue={w[i]:+.6f} (|delta|={diffs[i]:.4e}), smallest|lam|={w[j]:+.6f}, N={len(w)}")
        # rank of closest
        rank_in_pos = int(np.sum((w > 0) & (w < w[i])))
        print(f"   closest is at rank {rank_in_pos} among positive eigenvalues; total positive eigvals: {int(np.sum(w>0))}")
