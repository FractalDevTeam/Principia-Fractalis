"""
BBM v2: sweep ch_2 to test whether ch_2 = 0.95 is a special/stationary point of
the spectrum of H_BBM^framework, and assess whether framework modulation
improves the ζ-zero match relative to bare BBM.

We also use SCALED spacing variance and a "ζ-match score" = mean relative error
on the first 10 levels after global rescaling.
"""
from __future__ import annotations
import json
import numpy as np

from bbm_framework import (
    Grid, H_BBM, H_BBM_framework, eigen_sorted,
    pt_symmetry_residual, unfolded_spacings, variance_of_spacings,
    ZETA_ZEROS,
)


def metrics_for(H, grid):
    ev = eigen_sorted(H, n_keep=20)
    im = ev.imag
    if im.size == 0 or im[0] <= 0:
        return dict(zeta_score=float("nan"), var_s=float("nan"),
                    pt_res=pt_symmetry_residual(H, grid),
                    first_im=float("nan"))
    scale = ZETA_ZEROS[0] / im[0]
    scaled = im * scale
    K = min(10, len(scaled), len(ZETA_ZEROS))
    rel = np.abs(scaled[:K] - ZETA_ZEROS[:K]) / ZETA_ZEROS[:K]
    s = unfolded_spacings(im)
    return dict(
        zeta_score=float(np.mean(rel)),
        var_s=variance_of_spacings(s),
        pt_res=pt_symmetry_residual(H, grid),
        first_im=float(im[0]),
        scale=float(scale),
    )


def sweep_ch2():
    grid = Grid(N=400, L=50.0)  # slightly smaller for speed
    ch2_values = np.linspace(0.50, 1.00, 26)  # 0.50, 0.52, ..., 1.00
    results = []
    H_bare = H_BBM(grid, hbar=1.0)
    bare_m = metrics_for(H_bare, grid)
    print(f"Bare BBM: {bare_m}")
    for c in ch2_values:
        H = H_BBM_framework(grid, hbar=1.0, ch_2=float(c),
                            alpha=1.5, epsilon=1.0)
        m = metrics_for(H, grid)
        m["ch_2"] = float(c)
        results.append(m)
        print(f"  ch_2={c:.3f}  zeta_score={m['zeta_score']:.4f}  "
              f"var_s={m['var_s']:.4f}  pt_res={m['pt_res']:.4f}")

    bare_m["ch_2"] = "bare"
    return dict(bare=bare_m, sweep=results)


if __name__ == "__main__":
    out = sweep_ch2()
    with open(
        "/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/"
        "RH_BBM_nonlocal/bbm_ch2_sweep.json",
        "w",
    ) as f:
        json.dump(out, f, indent=2)
    print("Saved bbm_ch2_sweep.json")
