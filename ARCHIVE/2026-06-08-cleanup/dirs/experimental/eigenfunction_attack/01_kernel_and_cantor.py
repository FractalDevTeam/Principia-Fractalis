"""
Eigenfunction Construction for H_alpha on the Ternary Cantor Set
==================================================================

Operator:
    (H_alpha psi)(x) = integral_K V_alpha(x,y) psi(y) d mu(y)

Kernel:
    V_alpha(x,y) = sum_{n=0}^infty a^(-n) cos(pi * alpha^n * |x-y|)

Test point: alpha = sqrt(2), a = 2.
Predicted lowest eigenvalue: lambda_0 = pi / (10 * sqrt(2)) ~ 0.2221441469.

This module provides:
  - cantor_points(N): N-th level approximation of ternary Cantor set
  - kernel V_alpha truncated at order n_max
  - canonical self-similar (Hausdorff) measure weights
"""
import numpy as np

# ---- Constants ----
ALPHA = np.sqrt(2.0)
A_DECAY = 2.0
LAMBDA_PRED = np.pi / (10.0 * ALPHA)  # ~ 0.2221441469


def cantor_points(N):
    """
    Returns the 2^N midpoints of the level-N ternary Cantor approximation.
    Each level-N interval has length 3^(-N) and lives in [0,1].
    The 2^N intervals are indexed by binary strings (b_0 ... b_{N-1}) in {0,2},
    with left endpoint sum_{k=0}^{N-1} b_k * 3^{-(k+1)}.
    """
    if N == 0:
        return np.array([0.5])  # entire [0,1], midpoint
    indices = np.arange(2**N)
    # Convert each index to a base-2 string of length N, then map 0->0, 1->2
    bits = ((indices[:, None] >> np.arange(N)[None, :]) & 1).astype(np.float64)
    digits = 2.0 * bits  # 0 or 2
    powers = 3.0 ** (-np.arange(1, N + 1, dtype=np.float64))
    left = digits @ powers
    width = 3.0 ** (-N)
    midpoints = left + 0.5 * width
    return midpoints


def hausdorff_weights(N):
    """
    Canonical self-similar measure on level-N Cantor: each of the 2^N
    intervals carries weight 2^(-N), summing to 1.
    """
    return np.full(2**N, 2.0**(-N))


def V_kernel(x, y, alpha=ALPHA, a=A_DECAY, n_max=60):
    """
    V_alpha(x,y) truncated at n_max.
    x, y can be scalars or numpy arrays (broadcastable).
    Series geometrically decays; n_max=60 gives error < 2^(-60) ~ 1e-18.
    """
    d = np.abs(np.asarray(x) - np.asarray(y))
    n = np.arange(n_max + 1)
    # shape: (..., n_max+1)
    decay = a ** (-n)
    phase = np.pi * (alpha ** n)  # length n_max+1
    # Broadcast: d shape (...,) and phase shape (n_max+1,)
    arg = np.multiply.outer(d, phase)
    return np.sum(decay * np.cos(arg), axis=-1)


def build_H_matrix(pts, weights, alpha=ALPHA, a=A_DECAY, n_max=60):
    """
    Build the (M x M) matrix approximating the integral operator H_alpha
    discretized on `pts` with quadrature weights `weights`:
        H[i,j] = V_alpha(pts[i], pts[j]) * weights[j]
    The eigenvalues of this matrix approximate eigenvalues of H_alpha.
    For a SELF-ADJOINT discretization, we symmetrize via sqrt-weights:
        H_sym[i,j] = sqrt(w_i) * V(x_i,x_j) * sqrt(w_j).
    Both have the same nonzero spectrum.
    """
    X = pts[:, None]
    Y = pts[None, :]
    V = V_kernel(X, Y, alpha=alpha, a=a, n_max=n_max)
    sw = np.sqrt(weights)
    H_sym = (sw[:, None] * V) * sw[None, :]
    return H_sym, V


if __name__ == "__main__":
    print(f"alpha = sqrt(2)   = {ALPHA:.15f}")
    print(f"lambda predicted  = pi/(10 sqrt2) = {LAMBDA_PRED:.15f}")
    for N in [4, 6, 8]:
        pts = cantor_points(N)
        w = hausdorff_weights(N)
        print(f"\nN={N}: {len(pts)} midpoints in [{pts.min():.6f}, {pts.max():.6f}]")
        print(f"   weight sum = {w.sum():.6f}")
    # Quick kernel sanity: V(x,x) = sum a^(-n) = a/(a-1) = 2
    print(f"\nV(0.5,0.5) should be a/(a-1)=2: {V_kernel(0.5,0.5):.10f}")
    print(f"V(0,1)  = {V_kernel(0.0,1.0):.10f}")
