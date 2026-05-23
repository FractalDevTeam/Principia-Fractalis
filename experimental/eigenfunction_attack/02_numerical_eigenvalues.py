"""
Task 6 + Tasks 1, 2: Numerical eigenvalue extraction of H_alpha on Cantor K.

Discretize K to level N (M = 2^N points), build the symmetric matrix
    H_sym[i,j] = sqrt(w_i w_j) * V_alpha(x_i, x_j)
and compute its eigenvalues. Compare lowest |lambda| and lowest positive
to the predicted lambda_0 = pi/(10 sqrt2) ~ 0.22214.

Also test the indicator (constant) ansatz psi == 1: this is the Hausdorff-
measure ansatz of Task 1 because the constant function against the canonical
mu_self_similar is the simplest natural choice.
"""
import sys
sys.path.insert(0, ".")
import numpy as np
from numpy.linalg import eigh
from scipy.linalg import eigh as scipy_eigh

import importlib.util
spec = importlib.util.spec_from_file_location("k1", "01_kernel_and_cantor.py")
k1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(k1)

ALPHA = k1.ALPHA
LAMBDA_PRED = k1.LAMBDA_PRED


def spectrum_at_level(N, alpha=ALPHA, a=2.0, n_max=80):
    pts = k1.cantor_points(N)
    w = k1.hausdorff_weights(N)
    H_sym, V = k1.build_H_matrix(pts, w, alpha=alpha, a=a, n_max=n_max)
    eigvals, eigvecs = eigh(H_sym)  # ascending
    return pts, w, H_sym, V, eigvals, eigvecs


def rayleigh_constant(pts, w, V):
    """Task 1: psi = 1 (constant against Hausdorff measure)."""
    # In sqrt-weight basis, the constant psi=1 corresponds to vector v_i = sqrt(w_i).
    # <psi, H psi> = sum_i sum_j w_i V(x_i,x_j) w_j  (in original basis)
    # ||psi||^2 = sum_i w_i = 1
    numer = (w[:, None] * V * w[None, :]).sum()
    denom = w.sum()  # = 1
    return numer / denom


def indicator_rayleigh(N, alpha=ALPHA, a=2.0, n_max=80):
    """Task 2: indicator on a subset (full Cantor K_N) -- same as constant since
    we're already inside K. Try indicator on the LEFT cantor third K_N^L."""
    pts = k1.cantor_points(N)
    w = k1.hausdorff_weights(N)
    V = k1.V_kernel(pts[:, None], pts[None, :], alpha=alpha, a=a, n_max=n_max)
    # full indicator
    R_full = (w[:, None] * V * w[None, :]).sum() / w.sum()
    # left half (first 2^(N-1) midpoints lie in the left third)
    M = 2**(N - 1)
    sub = slice(0, M)
    wL = w[sub]
    VL = V[sub, sub]
    R_left = (wL[:, None] * VL * wL[None, :]).sum() / wL.sum()
    return R_full, R_left


def main():
    print("=" * 78)
    print("NUMERICAL EIGENVALUE EXTRACTION of H_alpha at alpha = sqrt(2), a = 2")
    print("=" * 78)
    print(f"Predicted lambda_0 = pi/(10 sqrt 2) = {LAMBDA_PRED:.12f}\n")

    results = []
    for N in [5, 6, 7, 8, 9, 10, 11]:
        M = 2**N
        pts, w, H_sym, V, eigvals, eigvecs = spectrum_at_level(N)
        # Sort by magnitude as well
        idx_by_abs = np.argsort(np.abs(eigvals))[::-1]
        top5 = eigvals[idx_by_abs][:5]
        # lowest positive eigenvalue
        pos = eigvals[eigvals > 0]
        neg = eigvals[eigvals < 0]
        lowest_pos = pos.min() if len(pos) else np.nan
        largest_pos = pos.max() if len(pos) else np.nan
        largest_neg = neg.max() if len(neg) else np.nan
        most_neg = neg.min() if len(neg) else np.nan

        R_const = rayleigh_constant(pts, w, V)
        R_full, R_left = indicator_rayleigh(N)

        results.append((N, M, eigvals, R_const))

        print(f"--- N = {N}  (M = {M} points) ---")
        print(f"  5 largest |eig|       : {top5}")
        print(f"  smallest positive eig : {lowest_pos:.10f}")
        print(f"  largest positive eig  : {largest_pos:.10f}")
        print(f"  largest negative eig  : {largest_neg:.10f}")
        print(f"  most negative eig     : {most_neg:.10f}")
        print(f"  Rayleigh(psi=1)       : {R_const:.10f}   "
              f"(target {LAMBDA_PRED:.10f}, diff {R_const-LAMBDA_PRED:+.4e})")
        print(f"  Rayleigh(left third)  : {R_left:.10f}")
        print()

    # Convergence summary on the "interesting" eigenvalues
    print("=" * 78)
    print("CONVERGENCE TABLE: top positive eigenvalues vs N")
    print("=" * 78)
    print(f"{'N':>3} {'M':>6} {'lam_max':>14} {'lam_1':>14} {'lam_2':>14} "
          f"{'lam_3':>14} {'R(psi=1)':>14}")
    for N, M, eigvals, R in results:
        sorted_desc = np.sort(eigvals)[::-1]
        row = (N, M, sorted_desc[0],
               sorted_desc[1] if M > 1 else np.nan,
               sorted_desc[2] if M > 2 else np.nan,
               sorted_desc[3] if M > 3 else np.nan, R)
        print(f"{row[0]:>3} {row[1]:>6} {row[2]:14.8f} {row[3]:14.8f} "
              f"{row[4]:14.8f} {row[5]:14.8f} {row[6]:14.8f}")

    print(f"\n  target lambda_0   = {LAMBDA_PRED:.10f}")

if __name__ == "__main__":
    main()
