"""
03 — Probe normalization conventions and Walsh-style ansatz.

The numerical spectrum at N=11 is:
    {1.15336, 0.42342, 0.20724, 0.15072, 0.02185, ...}
The predicted lambda_0 = pi/(10 sqrt 2) = 0.22214 does NOT match any of these.

We check:
  (A) is pi/(10 alpha) really the framework's number, OR is the prediction
      a SPECTRAL GAP (difference of eigenvalues)?  e.g. 0.42342 - 0.20724 = 0.21618.
      0.20724 - 0 = 0.20724. None match exactly.
  (B) is the operator normalization different?  Try (a-1)/a * V (so V(x,x)=1).
      Then divide all eigenvalues by 2.  -> {0.5767, 0.2117, 0.1036, 0.0754,...}
      Try multiplying by 2: {2.307, 0.847, 0.414, 0.301, ...}
      Try 1/sqrt(N) normalization, etc.
  (C) Walsh-Rademacher functions:  psi_k(x) = (-1)^{bit k of cantor address}.
      These are orthogonal in L^2(K,mu) and are the natural eigenfunctions
      of operators acting block-diagonally on the IFS self-similar structure.
      Compute Rayleigh for first few Walsh modes.
  (D) Try alpha = sqrt(2) but operator on [0,1] with Lebesgue measure (NOT
      Cantor with Hausdorff)  -- maybe the framework's domain is [0,1] not K?
"""
import sys, importlib.util
import numpy as np
from numpy.linalg import eigh

spec = importlib.util.spec_from_file_location("k1", "01_kernel_and_cantor.py")
k1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(k1)

ALPHA = k1.ALPHA
LAMBDA_PRED = k1.LAMBDA_PRED


def walsh_mode(N, k):
    """
    k-th Walsh-Rademacher mode on 2^N Cantor midpoints.
    The k-th address bit b_k is read from the index.
    psi_k(x_i) = (-1)^{b_k(i)} where i has binary expansion b_0 b_1 ... b_{N-1}.
    """
    indices = np.arange(2**N)
    bits = (indices >> k) & 1
    return 1.0 - 2.0 * bits  # +/- 1


def walsh_product(N, ks):
    """Walsh-Paley product mode (product over a set of bits)."""
    M = 2**N
    out = np.ones(M)
    for k in ks:
        out *= walsh_mode(N, k)
    return out


def rayleigh(psi, w, V):
    num = ((w * psi)[:, None] * V * (w * psi)[None, :]).sum()
    den = (w * psi * psi).sum()
    return num / den


def main():
    N = 10
    pts = k1.cantor_points(N)
    w = k1.hausdorff_weights(N)
    V = k1.V_kernel(pts[:, None], pts[None, :], alpha=ALPHA, a=2.0, n_max=80)
    H_sym, _ = k1.build_H_matrix(pts, w, alpha=ALPHA, a=2.0, n_max=80)

    eigvals, eigvecs = eigh(H_sym)
    sorted_desc = np.sort(eigvals)[::-1]

    print(f"Predicted lambda_0    = {LAMBDA_PRED:.10f}")
    print(f"Predicted *2          = {2*LAMBDA_PRED:.10f}")
    print(f"Predicted /2          = {LAMBDA_PRED/2:.10f}")
    print(f"Predicted * (a-1)/a   = {LAMBDA_PRED/2:.10f}")
    print(f"sqrt of predicted     = {np.sqrt(LAMBDA_PRED):.10f}")
    print()

    print("Top 12 eigenvalues (positive, descending):")
    pos = sorted_desc[sorted_desc > 1e-12][:12]
    for i, e in enumerate(pos):
        # Look for relationships to LAMBDA_PRED
        ratio = e / LAMBDA_PRED
        print(f"  lam_{i:2d} = {e:.10f}    ratio to pi/(10a) = {ratio:.6f}")

    # Spectral gaps
    print("\nGaps between consecutive top eigenvalues:")
    for i in range(len(pos)-1):
        g = pos[i] - pos[i+1]
        print(f"  gap_{i} = {g:.10f}   ratio to lambda_pred = {g/LAMBDA_PRED:.6f}")

    # Walsh modes
    print("\n--- Walsh-Rademacher Rayleigh quotients ---")
    for k in range(min(N, 8)):
        psi = walsh_mode(N, k)
        R = rayleigh(psi, w, V)
        print(f"  psi = Walsh_{k} :  R(psi) = {R:.10f}   "
              f"diff to lambda_pred = {R-LAMBDA_PRED:+.4e}")

    # Walsh products of two bits
    print("\n--- Walsh-Paley products of two bits ---")
    for k1_ in range(4):
        for k2 in range(k1_+1, 5):
            psi = walsh_product(N, [k1_, k2])
            R = rayleigh(psi, w, V)
            print(f"  psi = W_{k1_}*W_{k2}: R = {R:.10f}   "
                  f"diff = {R-LAMBDA_PRED:+.4e}")

    # Test eigenvectors: are they walsh-like?
    print("\n--- Top 4 eigenvectors: are they Walsh-like? ---")
    # Convert back from sqrt-weight to original basis
    inv_sw = 1.0 / np.sqrt(w)
    for k in range(4):
        v_sym = eigvecs[:, np.argsort(eigvals)[-1-k]]  # k-th from top
        psi = v_sym * inv_sw
        psi = psi / np.linalg.norm(psi)
        # Project onto Walsh modes
        proj = []
        for j in range(min(N, 6)):
            wj = walsh_mode(N, j)
            wj_norm = wj / np.sqrt((w * wj * wj).sum())
            inner = (w * wj_norm * (psi / np.sqrt((w * psi * psi).sum()))).sum()
            proj.append(inner)
        print(f"  eig #{k}, lambda = {sorted_desc[k]:.8f},  proj onto Walsh_0..5: "
              f"{[f'{p:+.3f}' for p in proj]}")


if __name__ == "__main__":
    main()
