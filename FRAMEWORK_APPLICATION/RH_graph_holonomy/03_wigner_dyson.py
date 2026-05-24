"""
03_wigner_dyson.py

Test Wigner-Dyson statistics for H_graph eigenvalues.

Steps:
  1) Unfold spectrum by fitting cumulative density N(E) with polynomial
     or spline. Unfolded spacings should have mean 1.
  2) Compute nearest-neighbor spacing distribution P(s).
  3) Compare to:
        Poisson:  P(s) = exp(-s)
        GUE:      P(s) ~ (32/pi^2) s^2 exp(-4 s^2 / pi)
        GOE:      P(s) ~ (pi/2) s exp(-pi s^2 / 4)
  4) KS test against each.
  5) Number variance Sigma^2(L) and rigidity Delta_3.

Compare framework / random / trivial.

ZETA-zero hypothesis: framework should look GUE if the framework
encodes RH-relevant content.
"""

import numpy as np
import pickle
import os
import json
from scipy.stats import ks_2samp

OUT = os.path.dirname(os.path.abspath(__file__))


def load_diag():
    with open(os.path.join(OUT, "diagonalization_results.pkl"), "rb") as f:
        return pickle.load(f)


def unfold_spectrum(eigvals, deg=10):
    """Polynomial unfolding: fit cumulative N(E) and replace E_i -> N_fit(E_i)."""
    eigvals = np.sort(eigvals)
    N = len(eigvals)
    cumN = np.arange(1, N + 1, dtype=float)
    coeffs = np.polyfit(eigvals, cumN, deg)
    p = np.poly1d(coeffs)
    return p(eigvals)


def nn_spacings(unfolded):
    return np.diff(np.sort(unfolded))


def gue_pdf(s):
    return (32.0 / np.pi**2) * s**2 * np.exp(-4 * s**2 / np.pi)


def goe_pdf(s):
    return (np.pi / 2.0) * s * np.exp(-np.pi * s**2 / 4.0)


def poisson_pdf(s):
    return np.exp(-s)


def sample_pdf(pdf, n, smax=6.0):
    """Inverse-CDF sampling of pdf on [0, smax]."""
    xs = np.linspace(1e-6, smax, 4000)
    ys = pdf(xs)
    cdf = np.cumsum(ys)
    cdf /= cdf[-1]
    u = np.random.rand(n)
    return np.interp(u, cdf, xs)


def variance_stat(spacings):
    return np.var(spacings)


def main():
    blob = load_diag()
    fw = blob["eigvals_framework_full"]
    rnd = blob["eigvals_random_full"]
    tr = blob["eigvals_trivial_full"]
    N = blob["N"]
    alpha = blob["alpha"]
    print(f"Loaded: N={N}, dim={N*N}, alpha={alpha}")

    # Trim band edges (top/bottom 10% to avoid surface effects)
    def trim(w):
        n = len(w)
        lo = int(0.1 * n)
        hi = int(0.9 * n)
        return np.sort(w)[lo:hi]

    fw_bulk = trim(fw)
    rnd_bulk = trim(rnd)
    tr_bulk = trim(tr)
    print(f"  bulk size (each): {len(fw_bulk)}")

    # Unfold each
    fw_unf = unfold_spectrum(fw_bulk, deg=8)
    rnd_unf = unfold_spectrum(rnd_bulk, deg=8)
    tr_unf = unfold_spectrum(tr_bulk, deg=8)

    fw_s = nn_spacings(fw_unf)
    rnd_s = nn_spacings(rnd_unf)
    tr_s = nn_spacings(tr_unf)

    # Re-normalize: mean spacing -> 1
    fw_s = fw_s / np.mean(fw_s)
    rnd_s = rnd_s / np.mean(rnd_s)
    tr_s = tr_s / np.mean(tr_s)

    print(f"\nSpacing statistics (mean=1 normalized):")
    print(f"               mean    var    skew")
    for tag, s in [("framework", fw_s), ("random", rnd_s), ("trivial", tr_s)]:
        from scipy.stats import skew
        print(f"  {tag:9s}  {np.mean(s):.3f}  {np.var(s):.3f}  {skew(s):.3f}")
    print(f"  GUE target    1.000   0.180   0.610")
    print(f"  GOE target    1.000   0.286   0.998")
    print(f"  Poisson       1.000   1.000   2.000")

    # KS tests vs reference samples
    nref = 10000
    gue_samples = sample_pdf(gue_pdf, nref)
    goe_samples = sample_pdf(goe_pdf, nref)
    poi_samples = sample_pdf(poisson_pdf, nref)

    print(f"\nKS test (smaller = better match):")
    print(f"               vs GUE        vs GOE        vs Poisson")
    results = {}
    for tag, s in [("framework", fw_s), ("random", rnd_s), ("trivial", tr_s)]:
        ks_gue = ks_2samp(s, gue_samples)
        ks_goe = ks_2samp(s, goe_samples)
        ks_poi = ks_2samp(s, poi_samples)
        print(f"  {tag:9s}  D={ks_gue.statistic:.3f} p={ks_gue.pvalue:.2e}  D={ks_goe.statistic:.3f} p={ks_goe.pvalue:.2e}  D={ks_poi.statistic:.3f} p={ks_poi.pvalue:.2e}")
        results[tag] = {
            "ks_gue_D": float(ks_gue.statistic),
            "ks_gue_p": float(ks_gue.pvalue),
            "ks_goe_D": float(ks_goe.statistic),
            "ks_goe_p": float(ks_goe.pvalue),
            "ks_poi_D": float(ks_poi.statistic),
            "ks_poi_p": float(ks_poi.pvalue),
            "var": float(np.var(s)),
            "mean": float(np.mean(s)),
            "n_spacings": int(len(s)),
        }

    # Histogram-based comparison
    print(f"\nP(s) histogram (s-binned, mean=1):")
    bins = np.linspace(0, 4, 21)
    centers = 0.5 * (bins[:-1] + bins[1:])
    H_fw, _ = np.histogram(fw_s, bins=bins, density=True)
    H_rnd, _ = np.histogram(rnd_s, bins=bins, density=True)
    H_tr, _ = np.histogram(tr_s, bins=bins, density=True)
    H_gue = gue_pdf(centers)
    H_goe = goe_pdf(centers)
    H_poi = poisson_pdf(centers)
    print(f"   s    | framework | random  | trivial |  GUE   |  GOE   | Poisson")
    for k, c in enumerate(centers):
        print(f"  {c:.2f}  |   {H_fw[k]:.3f}   |  {H_rnd[k]:.3f}  |  {H_tr[k]:.3f}  | {H_gue[k]:.3f}  | {H_goe[k]:.3f}  |  {H_poi[k]:.3f}")

    out = {
        "framework_spacings": fw_s,
        "random_spacings": rnd_s,
        "trivial_spacings": tr_s,
        "ks_results": results,
    }
    with open(os.path.join(OUT, "wigner_dyson_results.pkl"), "wb") as f:
        pickle.dump(out, f)
    with open(os.path.join(OUT, "wigner_dyson_summary.json"), "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nSaved.")


if __name__ == "__main__":
    main()
