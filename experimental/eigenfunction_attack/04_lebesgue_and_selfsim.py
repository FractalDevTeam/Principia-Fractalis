"""
04 — Test H_alpha on [0,1] with Lebesgue measure (NOT Cantor).

Hypothesis: the framework's H_P operator may live on L^2([0,1], dx), not
L^2(K, mu_Hausdorff).  The Cantor set may be the "support of fractal modes"
but the operator may be defined on the larger Lebesgue space.

Also: investigate the self-similarity identity
    K_alpha(t/alpha) = (1/a) K_alpha(t) + cos(pi t / alpha)
    where K_alpha(t) = sum_{n>=0} a^(-n) cos(pi alpha^n t).
This is the framework's STRUCTURAL identity (Task 4).
Verify it numerically, then derive the eigenfunction constraint.
"""
import sys, importlib.util
import numpy as np
from numpy.linalg import eigh

spec = importlib.util.spec_from_file_location("k1", "01_kernel_and_cantor.py")
k1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(k1)

ALPHA = k1.ALPHA
LAMBDA_PRED = k1.LAMBDA_PRED


def K_alpha(t, alpha=ALPHA, a=2.0, n_max=80):
    """K_alpha(t) = sum_{n>=0} a^(-n) cos(pi alpha^n t)."""
    t = np.asarray(t, dtype=float)
    n = np.arange(n_max + 1)
    decay = a ** (-n)
    arg = np.pi * np.multiply.outer(t, alpha ** n)
    return np.sum(decay * np.cos(arg), axis=-1)


def verify_selfsimilar(alpha=ALPHA, a=2.0):
    """Check K_alpha(t/alpha) - (1/a) K_alpha(t) - cos(pi t / alpha) = ?"""
    print("Self-similarity identity check:")
    print("  K(t/alpha) - (1/a) K(t) = ?  (manuscript says = cos(pi t /alpha)?)")
    for t in [0.1, 0.3, 0.7, 1.5, 2.0]:
        lhs = K_alpha(t / alpha)
        rhs1 = (1.0 / a) * K_alpha(t) + np.cos(np.pi * t / alpha)
        # Actually the correct shift identity:
        # K(t) = cos(pi t) + (1/a) K(alpha t)   <-- because the n=0 term peels off
        # so K(alpha t) = a * (K(t) - cos(pi t))
        rhs2 = a * (K_alpha(t) - np.cos(np.pi * t))
        lhs2 = K_alpha(alpha * t)
        print(f"  t={t}: K(t/a)={lhs:.6f}  K(alpha*t)={lhs2:.6f}  "
              f"a(K(t)-cos(pi t))={rhs2:.6f}  diff={lhs2-rhs2:+.3e}")


def lebesgue_spectrum(M, alpha=ALPHA, a=2.0, n_max=80):
    """Discretize [0,1] with M uniform points (Lebesgue) and compute spectrum."""
    pts = (np.arange(M) + 0.5) / M
    w = np.full(M, 1.0 / M)
    V = k1.V_kernel(pts[:, None], pts[None, :], alpha=alpha, a=a, n_max=n_max)
    sw = np.sqrt(w)
    H_sym = sw[:, None] * V * sw[None, :]
    eigvals, eigvecs = eigh(H_sym)
    return pts, w, eigvals, eigvecs


def main():
    print("=" * 78)
    print("LEBESGUE SPECTRUM of H_alpha on [0,1]  (alpha = sqrt(2), a = 2)")
    print("=" * 78)
    for M in [128, 256, 512, 1024, 1500]:
        pts, w, eigvals, eigvecs = lebesgue_spectrum(M)
        sorted_desc = np.sort(eigvals)[::-1]
        pos = sorted_desc[sorted_desc > 1e-12]
        print(f"\n--- M = {M} ---")
        for i in range(min(12, len(pos))):
            ratio = pos[i] / LAMBDA_PRED
            print(f"  lam_{i:2d} = {pos[i]:.10f}   "
                  f"ratio pi/(10a) = {ratio:.6f}")

    print(f"\n  target = pi/(10 sqrt 2) = {LAMBDA_PRED:.10f}")

    print("\n" + "=" * 78)
    print("SELF-SIMILARITY IDENTITY (Task 4)")
    print("=" * 78)
    verify_selfsimilar()


if __name__ == "__main__":
    main()
