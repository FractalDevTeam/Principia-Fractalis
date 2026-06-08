"""
Mercer rank-2-per-level decomposition — v2: proper generalized eigenvalue
formulation, with high-precision arithmetic and explicit handling of
the null space (modes that become linearly dependent at high N).

Theory
------
The truncated operator
   H_N = sum_{n=0}^N a^{-n} ( |c_n><c_n| + |s_n><s_n| )
acts on L^2([0,1]). Its image is contained in S_N = span{c_n, s_n}_{n=0..N}.

The NONZERO spectrum equals the spectrum of M v = lambda v where
   M_{ij} = sqrt(w_i w_j) <u_i, u_j>      (the spectral matrix)
PROVIDED the {u_i} are linearly independent.

When they become numerically dependent (at large N some alpha^n is close
to alpha^m mod 2, generating near-collinearity), M acquires near-zero
eigenvalues that are SPURIOUS (corresponding to coefficient vectors c
with sum_i c_i u_i ~ 0; they are not real spectrum, they are kernel of
the synthesis map).

Cure: compute M's nonzero spectrum and DROP the near-zero modes (treat
them as numerical zero in the synthesis map). Equivalently, regularize:
look at the spectrum of M projected to the range of the basis Gram G.

Solve: form G (gram matrix), M (spectral matrix). The actual operator
spectrum on the truncated space comes from M v = lambda G v (generalized
eigenvalue) - but rewritten in orthonormal basis. Equivalently:

  Step 1: G = U Lambda U^T (high precision)
  Step 2: keep eigenvalues > tol (effective rank r)
  Step 3: half-power inverse Q = U Lambda^{-1/2}  (restricted to range)
  Step 4: form K = Q^T M' Q where M' is the operator matrix in the same basis
          (without the sqrt weighting; with bare weighting M' = D <u,u> D
          where D = diag(w_n))  -- actually for the rank-2 operator
          H f = sum_k w_k u_k <u_k, f>, in u-basis matrix elements are
          <u_i, H u_j> = sum_k w_k <u_i, u_k><u_k, u_j> = (G W G)_{ij}
          where W = diag(w_n) duplicated.
  Step 5: K = (G^{-1/2}) (G W G) (G^{-1/2}) = G^{1/2} W G^{1/2}
  Step 6: eigenvalues of K are the true operator eigenvalues on S_N.

This is mathematically clean and avoids the spurious zeros.
"""

import numpy as np
import mpmath as mp

mp.mp.dps = 60


def inner_cc(p, q):
    p = mp.mpf(p); q = mp.mpf(q)
    eps = mp.mpf("1e-50")
    s = mp.sin(mp.pi * (p - q)) / (mp.pi * (p - q)) if abs(p - q) > eps else mp.mpf(1)
    t = mp.sin(mp.pi * (p + q)) / (mp.pi * (p + q)) if abs(p + q) > eps else mp.mpf(1)
    return (s + t) / 2

def inner_ss(p, q):
    p = mp.mpf(p); q = mp.mpf(q)
    eps = mp.mpf("1e-50")
    s = mp.sin(mp.pi * (p - q)) / (mp.pi * (p - q)) if abs(p - q) > eps else mp.mpf(1)
    t = mp.sin(mp.pi * (p + q)) / (mp.pi * (p + q)) if abs(p + q) > eps else mp.mpf(1)
    return (s - t) / 2

def inner_cs(p, q):
    p = mp.mpf(p); q = mp.mpf(q)
    eps = mp.mpf("1e-50")
    A = mp.pi * p; B = mp.pi * q
    def Iint(omega):
        if abs(omega) < eps:
            return mp.mpf(0)
        return (1 - mp.cos(omega)) / omega
    return (Iint(A + B) - Iint(A - B)) / 2


def build_gram(N, alpha):
    """Gram matrix G_ij = <u_i, u_j> in the cos/sin basis (un-weighted)."""
    alpha = mp.mpf(alpha)
    dim = 2 * (N + 1)
    G = mp.matrix(dim, dim)
    freqs = [alpha ** n for n in range(N + 1)]
    for n in range(N + 1):
        for m in range(N + 1):
            p = freqs[n]; q = freqs[m]
            G[2 * n, 2 * m] = inner_cc(p, q)
            G[2 * n + 1, 2 * m + 1] = inner_ss(p, q)
            G[2 * n, 2 * m + 1] = inner_cs(p, q)
            G[2 * n + 1, 2 * m] = inner_cs(q, p)
    return G


def build_weight(N, a):
    """W = diag of weights w_n = a^{-n}, duplicated for cos/sin."""
    a = mp.mpf(a)
    dim = 2 * (N + 1)
    W = mp.matrix(dim, dim)
    for n in range(N + 1):
        w = a ** (-n)
        W[2 * n, 2 * n] = w
        W[2 * n + 1, 2 * n + 1] = w
    return W


def mp_to_np(M):
    rows, cols = M.rows, M.cols
    A = np.zeros((rows, cols), dtype=np.float64)
    for i in range(rows):
        for j in range(cols):
            A[i, j] = float(M[i, j])
    return A


def operator_eigenvalues(N, alpha, a, tol=1e-13):
    """
    Compute true operator eigenvalues on S_N using G^{1/2} W G^{1/2}.
    Returns sorted eigenvalues and the effective rank.
    """
    G = build_gram(N, alpha)
    W = build_weight(N, a)
    Gnp = mp_to_np(G); Wnp = mp_to_np(W)
    # symmetrize
    Gnp = 0.5 * (Gnp + Gnp.T)

    # eigendecomp of G
    g_vals, g_vecs = np.linalg.eigh(Gnp)
    # rank by tolerance relative to max eigenvalue
    cutoff = tol * g_vals.max()
    keep = g_vals > cutoff
    rank = int(keep.sum())
    sqrt_g = np.zeros_like(g_vals)
    sqrt_g[keep] = np.sqrt(g_vals[keep])
    G_half = g_vecs @ np.diag(sqrt_g) @ g_vecs.T

    # K = G^{1/2} W G^{1/2}
    K = G_half @ Wnp @ G_half
    K = 0.5 * (K + K.T)
    w = np.sort(np.linalg.eigvalsh(K))
    # remove machine-zero null modes from the dropped Gram null-space
    # nonzero entries should be the operator spectrum on the effective basis
    return w, rank, g_vals.min(), g_vals.max()


def main():
    alpha = mp.sqrt(2)
    a = mp.mpf(2)
    target = float(mp.pi / (10 * mp.sqrt(2)))
    print(f"alpha = sqrt(2),  a = 2")
    print(f"target lambda_0 = pi/(10*sqrt(2)) = {target:.12f}")
    print("=" * 100)
    print(f"{'N':>3} | {'dim':>4} | {'rank':>4} | {'lam_min':>14} | {'lam_5th':>14} | "
          f"{'lam_max':>14} | {'g_min':>10} | {'g_max':>10}")
    print("-" * 100)

    Ns = [3, 5, 8, 10, 12, 15, 18, 20]
    all_specs = {}
    for N in Ns:
        w, r, gmin, gmax = operator_eigenvalues(N, alpha, a)
        # only the top r eigenvalues are "real" — the trailing ones are
        # numerically below the kernel-null cutoff
        # sort descending
        w_desc = w[::-1]
        # take rank top values
        true_spec = w_desc[:r]
        lam_min = true_spec[-1]   # smallest TRUE positive eigenvalue
        lam_5th = true_spec[4] if len(true_spec) > 4 else float("nan")
        lam_max = true_spec[0]
        all_specs[N] = true_spec
        print(f"{N:>3} | {2*(N+1):>4} | {r:>4} | {lam_min:>14.10f} | {lam_5th:>14.10f} | "
              f"{lam_max:>14.10f} | {gmin:>10.2e} | {gmax:>10.2e}")

    # detailed listing for N=15
    print("\nFull spectrum at N=15 (true positive eigenvalues, descending):")
    spec15 = all_specs[15]
    for i, v in enumerate(spec15):
        diff_target = abs(v - target)
        marker = "  <-- close to pi/(10 sqrt 2)" if diff_target < 0.03 else ""
        print(f"  k={i:2d}  lambda = {v:.10f}   |diff to target|={diff_target:.6e}{marker}")

    print("\nFull spectrum at N=20:")
    spec20 = all_specs[20]
    for i, v in enumerate(spec20):
        diff_target = abs(v - target)
        marker = "  <-- close to pi/(10 sqrt 2)" if diff_target < 0.03 else ""
        print(f"  k={i:2d}  lambda = {v:.10f}   |diff to target|={diff_target:.6e}{marker}")

    # convergence of each rank-ordered eigenvalue across N
    print("\nConvergence of top-K eigenvalues across N (descending order):")
    K = 8
    Ns_show = [5, 8, 10, 12, 15, 18, 20]
    header = "  k |" + " | ".join([f"  N={n:2d}    " for n in Ns_show])
    print(header)
    for k in range(K):
        row = f" {k:2d} |"
        for n in Ns_show:
            s = all_specs[n]
            if k < len(s):
                row += f" {s[k]:.8f} |"
            else:
                row += f"     ---    |"
        print(row)

    # Check whether the smallest positive eigenvalue or any rank converges
    # toward target = 0.22214
    print("\nSearch for any eigenvalue near the target across N:")
    for N in Ns:
        s = all_specs[N]
        near = [(i, v) for i, v in enumerate(s) if abs(v - target) < 0.05]
        if near:
            print(f"  N={N:2d}: candidates: {[(i, f'{v:.8f}') for i, v in near]}")
        else:
            # find closest
            i_best = int(np.argmin(np.abs(s - target)))
            print(f"  N={N:2d}: no eigenvalue within 0.05 of target;"
                  f" closest is index {i_best} = {s[i_best]:.8f} "
                  f"(diff={s[i_best]-target:+.6f})")


if __name__ == "__main__":
    main()
