"""
COUNTER-ROTATING DOUBLE TORUS — Construction Attack #1

Construct and test the operator
    H_alpha := H_alpha^+ ⊗ I − I ⊗ H_alpha^-
on ℋ = L²(T²)_+ ⊗ L²(T²)_-
where H_alpha^± is the convolution operator with kernel V_alpha(d) on T² with
the two U(1) orientations.

In the Fourier basis e^(i m_+ · θ_+) ⊗ e^(i m_- · θ_-), it is diagonal:
    λ(m_+, m_-) = V̂_alpha(m_+) − V̂_alpha(m_-).

Strategy:
  1. Precompute V̂_alpha(m) on T² for all m = (m1, m2) with |mi| ≤ 10.
  2. Form ALL pairwise differences and look for the smallest positive eigenvalue.
  3. Compare against π/(10·α) at α=√2, 3/2, 2.
  4. Also test alternative constructions: sum, tensor-product, abs.
  5. Search any eigenvalue within 5% of π/(10·α).
  6. Try both geodesic and chord distance.

Targets:
    α=√2  →  π/(10√2)   ≈ 0.22214
    α=3/2 →  π/15       ≈ 0.20944
    α=2   →  π/20       ≈ 0.15708
"""

from __future__ import annotations

import math
import os
import sys
from itertools import product

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "toroidal_test"))
from fourier_modes import g, V_alpha_vec  # type: ignore

PI = math.pi
HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------
# Distance functions on T^2
# ---------------------------------------------------------------------------

def geodesic_distance(T1, T2):
    """d(0,(t1,t2)) = sqrt( g(t1)^2 + g(t2)^2 ), g = wrap-to-[-π,π]."""
    return np.sqrt(g(T1) ** 2 + g(T2) ** 2)


def chord_distance(T1, T2):
    """Chord distance on the embedded (S^1)^2 ⊂ ℝ^4.

    For each circle the chord length between angles 0 and t is
    |e^{it} - 1| = 2|sin(t/2)|.  Sum-of-squares gives a chord-style metric
    on T^2.
    """
    c1 = 2.0 * np.abs(np.sin(T1 / 2.0))
    c2 = 2.0 * np.abs(np.sin(T2 / 2.0))
    return np.sqrt(c1 ** 2 + c2 ** 2)


# ---------------------------------------------------------------------------
# Fourier coefficient table on T^2 (single torus)
# ---------------------------------------------------------------------------

def fourier_table_T2(alpha, M=10, a=2.0, N_terms=20, n_grid=512,
                     distance="geodesic"):
    """Return a (2M+1, 2M+1) complex array V̂[m1+M, m2+M] = V̂_alpha(m1, m2).

    Uses a single uniform [0, 2π)^2 mesh of shape (n_grid, n_grid) and
    FFTs all (2M+1)^2 Fourier coefficients in one pass.
    """
    if distance == "geodesic":
        dist_fn = geodesic_distance
    elif distance == "chord":
        dist_fn = chord_distance
    else:
        raise ValueError(distance)

    t = np.linspace(0, 2 * PI, n_grid, endpoint=False)
    T1, T2 = np.meshgrid(t, t, indexing="ij")
    D = dist_fn(T1, T2)
    V = V_alpha_vec(D, alpha, a=a, N=N_terms)

    # 2-D DFT.  np.fft.fft2 computes
    #   F[k1,k2] = sum_{n1,n2} V[n1,n2] exp(-2π i (k1 n1 + k2 n2)/n_grid).
    # The Fourier coefficient we want is
    #   V̂(m1,m2) = (1/(2π)^2) ∫ V(t1,t2) exp(-i(m1 t1 + m2 t2)) dt
    #            ≈ (Δt)^2/(2π)^2 * sum V[n1,n2] exp(-i(m1 + m2)·2π n/n_grid)
    #            = (1/n_grid^2) * F[m1, m2].
    F = np.fft.fft2(V) / (n_grid ** 2)

    table = np.zeros((2 * M + 1, 2 * M + 1), dtype=complex)
    for m1 in range(-M, M + 1):
        for m2 in range(-M, M + 1):
            table[m1 + M, m2 + M] = F[m1 % n_grid, m2 % n_grid]
    return table


# ---------------------------------------------------------------------------
# Spectrum constructions
# ---------------------------------------------------------------------------

def difference_spectrum(Vhat):
    """λ(m_+, m_-) = V̂(m_+) − V̂(m_-) for all index pairs.  Flatten to 1D."""
    flat = Vhat.flatten()
    n = flat.size
    diff = flat[:, None] - flat[None, :]
    return diff.flatten(), n


def sum_spectrum_diagonal(Vhat):
    """λ(m) = 2 · Re V̂(m)  on the diagonal m_+ = m_- = m  (after taking real
    part, since V̂(m) need not be real; though for a real symmetric kernel
    centred at origin it is)."""
    return Vhat.flatten() + Vhat.flatten()  # 2 V̂(m)


def tensor_product_spectrum(Vhat):
    flat = Vhat.flatten()
    return (flat[:, None] * flat[None, :]).flatten()


# ---------------------------------------------------------------------------
# Reporting helpers
# ---------------------------------------------------------------------------

def smallest_positive_real(values, eps=1e-12):
    """Among the REAL parts (within tol of real), return the smallest positive."""
    re = np.real(values)
    im = np.imag(values)
    real_mask = np.abs(im) < 1e-8 * (np.abs(re) + 1.0)
    pos_mask = re > eps
    candidates = re[real_mask & pos_mask]
    if candidates.size == 0:
        return None
    return float(np.min(candidates))


def smallest_positive_abs(values, eps=1e-12):
    av = np.abs(values)
    pos = av[av > eps]
    if pos.size == 0:
        return None
    return float(np.min(pos))


def near_matches(values, target, tol_frac=0.05, max_report=15):
    """Return indices/values within tol_frac of target (relative)."""
    av = np.abs(values)
    rel = np.abs(av - target) / target
    idx = np.where(rel < tol_frac)[0]
    if idx.size == 0:
        return []
    order = idx[np.argsort(rel[idx])]
    return [(int(i), complex(values[i]), float(rel[i])) for i in order[:max_report]]


def unflatten_index(idx, M):
    """Decode flat index for V̂ table (2M+1)^2."""
    side = 2 * M + 1
    a = idx // side
    b = idx % side
    return (a - M, b - M)


def unflatten_pair(idx, M):
    """Decode flat index of (m_+, m_-) pair from difference flattening."""
    table_size = (2 * M + 1) ** 2
    plus = idx // table_size
    minus = idx % table_size
    return unflatten_index(plus, M), unflatten_index(minus, M)


# ---------------------------------------------------------------------------
# Main driver
# ---------------------------------------------------------------------------

def analyse_alpha(alpha, label, M=10, n_grid=512, distance="geodesic"):
    target = PI / (10 * alpha)
    Vhat = fourier_table_T2(alpha, M=M, a=2.0, N_terms=20,
                            n_grid=n_grid, distance=distance)

    # Take real part for diagnostics (symmetric kernel ⇒ V̂ is real to FFT prec)
    re_max_im = float(np.max(np.abs(Vhat.imag)))

    flat = Vhat.flatten()

    # (1) Difference operator
    diff, _ = difference_spectrum(Vhat)
    pos_diff = smallest_positive_real(diff)

    # (2a) Sum on diagonal
    sum_diag = sum_spectrum_diagonal(Vhat)
    pos_sum = smallest_positive_real(sum_diag)

    # (2b) Tensor product
    tens = tensor_product_spectrum(Vhat)
    pos_tens = smallest_positive_real(tens)

    # (2c) |difference|
    abs_diff = np.abs(diff)
    pos_abs = smallest_positive_abs(abs_diff)

    out = []
    out.append("")
    out.append("=" * 78)
    out.append(f"α = {alpha:.10f}   ({label})    distance = {distance}    "
               f"|m_i| ≤ {M}    grid = {n_grid}")
    out.append(f"TARGET π/(10·α) = {target:.10f}")
    out.append(f"max |Im V̂|     = {re_max_im:.3e}  (kernel is real-symmetric ⇒ expect ~0)")
    out.append("-" * 78)

    def fmt(x):
        if x is None:
            return "  (none > 0)"
        rel = (x - target) / target
        return f"  value = {x:.10f}    rel-err vs target = {rel:+.6f}"

    out.append(f"(A) DIFFERENCE  H_α^+ ⊗ I − I ⊗ H_α^-   smallest positive eigenvalue:")
    out.append(fmt(pos_diff))
    out.append(f"(B) SUM diagonal m_+ = m_-                smallest positive 2 V̂(m):")
    out.append(fmt(pos_sum))
    out.append(f"(C) TENSOR  H_α^+ ⊗ H_α^-                 smallest positive V̂(m_+)·V̂(m_-):")
    out.append(fmt(pos_tens))
    out.append(f"(D) |DIFFERENCE|                          smallest positive |V̂(m_+)−V̂(m_-)|:")
    out.append(fmt(pos_abs))

    # Generous near-match search on the four spectra
    out.append("-" * 78)
    out.append("NEAR-MATCH SEARCH (within 5% of target):")

    def report_matches(name, vals, decode=None):
        matches = near_matches(vals, target, tol_frac=0.05, max_report=10)
        if not matches:
            out.append(f"  [{name}]  no matches within 5%.")
            return
        out.append(f"  [{name}]  {len(matches)} match(es) within 5%:")
        for idx, val, rel in matches:
            extra = ""
            if decode is not None:
                extra = f"   indices = {decode(idx)}"
            out.append(f"      idx={idx:>8d}  val={val.real:+.10f}{val.imag:+.2e}i"
                       f"   rel={rel:.4f}{extra}")

    report_matches("difference",     diff, decode=lambda i: unflatten_pair(i, M))
    report_matches("sum-diagonal",   sum_diag, decode=lambda i: unflatten_index(i, M))
    report_matches("tensor-product", tens,
                   decode=lambda i: (unflatten_index(i // ((2*M+1)**2), M),
                                     unflatten_index(i %  ((2*M+1)**2), M)))
    report_matches("|difference|",   abs_diff, decode=lambda i: unflatten_pair(i, M))

    out.append("=" * 78)
    return "\n".join(out)


def main():
    M = 10           # m_i ∈ [-10, 10]   →   441 modes per torus, 441^2 ≈ 195k pairs
    n_grid = 512     # FFT mesh on T^2

    alphas = [
        (math.sqrt(2), "α=√2"),
        (1.5,          "α=3/2"),
        (2.0,          "α=2"),
    ]

    full_log = []
    for distance in ("geodesic", "chord"):
        header = f"\n#### DISTANCE = {distance.upper()} ####\n"
        print(header)
        full_log.append(header)
        for alpha, label in alphas:
            report = analyse_alpha(alpha, label, M=M, n_grid=n_grid,
                                   distance=distance)
            print(report)
            full_log.append(report)

    # Write a verdict summary
    summary_path = os.path.join(HERE, "results.txt")
    with open(summary_path, "w") as f:
        f.write("\n".join(full_log))
    print(f"\nFull log written to {summary_path}")


if __name__ == "__main__":
    main()
