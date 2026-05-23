"""
Mercer rank-2-per-level decomposition of the Principia Fractalis kernel.

V_alpha(x,y) = sum_{n=0}^inf a^{-n} cos(pi * alpha^n * |x-y|)
             = sum_{n=0}^inf a^{-n} [ cos(pi alpha^n x) cos(pi alpha^n y)
                                      + sin(pi alpha^n x) sin(pi alpha^n y) ]

On L^2([0,1]), truncated to N+1 levels, this is a rank <= 2(N+1) operator.

Strategy
--------
Span S_N = span{ c_n(x)=cos(pi alpha^n x), s_n(x)=sin(pi alpha^n x) : n=0..N }.
Let phi_k be the basis vector. The operator H_N acts on f in S_N as

    H_N f = sum_n a^{-n} [ <c_n, f> c_n + <s_n, f> s_n ]

In the (non-orthonormal) basis [c_0,s_0,c_1,s_1,...,c_N,s_N] this is
H_N = B^T D B where B is the (2N+2)x(2N+2) Gram-like matrix and D = diag(a^-n)
duplicated. The generalized eigenvalue problem H v = lambda G v with
G = Gram matrix of the basis gives the spectrum on S_N.

Equivalent symmetric form: Let A = G^{-1/2} (D' G) G^{-1/2} where D' is the
diagonal weight; then the eigenvalues of the operator restricted to S_N are
the eigenvalues of the symmetric form K = G^{1/2} (...) - easier approach:

Use the fact that for any operator T = sum_k w_k u_k u_k^T on a finite-dim
space, restricted to the span U = [u_1,...,u_M] in L^2, the nonzero spectrum
equals the spectrum of the M x M matrix M_ij = sqrt(w_i w_j) <u_i, u_j>.

Proof: T u_j = sum_k w_k u_k <u_k, u_j>. Eigenfunction f = sum_j c_j u_j.
T f = sum_k w_k u_k sum_j c_j <u_k, u_j>. For eigenvalue lambda:
lambda sum_j c_j u_j = sum_k (w_k sum_j c_j <u_k,u_j>) u_k.
If the u_k are linearly independent, equate coefficients in the u-basis:
lambda c_k = w_k sum_j c_j <u_k, u_j>.
Let d_k = sqrt(w_k) c_k. Then lambda d_k = sqrt(w_k) sum_j (1/sqrt(w_j)) d_j w_k <u_k,u_j>
                                         = sum_j sqrt(w_k w_j) <u_k, u_j> d_j.
So d is an eigenvector of M_ij = sqrt(w_k w_j) <u_k, u_j> with the same eigenvalue.

This is the standard "spectral matrix" reduction. We use it here.
"""

import numpy as np
from numpy.linalg import eigh, eigvalsh
import mpmath as mp

mp.mp.dps = 50  # 50 decimal digit precision for inner products


# ---------- exact inner products on [0,1] ----------

def inner_cc(p, q):
    """<cos(pi p x), cos(pi q x)>_{L^2[0,1]} exact via mpmath."""
    p = mp.mpf(p); q = mp.mpf(q)
    if abs(p - q) < mp.mpf("1e-40") and abs(p + q) < mp.mpf("1e-40"):
        return mp.mpf(1)  # both zero
    s = mp.sin(mp.pi * (p - q)) / (mp.pi * (p - q)) if abs(p - q) > 1e-40 else mp.mpf(1)
    t = mp.sin(mp.pi * (p + q)) / (mp.pi * (p + q)) if abs(p + q) > 1e-40 else mp.mpf(1)
    return (s + t) / 2

def inner_ss(p, q):
    """<sin(pi p x), sin(pi q x)>_{L^2[0,1]}."""
    p = mp.mpf(p); q = mp.mpf(q)
    s = mp.sin(mp.pi * (p - q)) / (mp.pi * (p - q)) if abs(p - q) > 1e-40 else mp.mpf(1)
    t = mp.sin(mp.pi * (p + q)) / (mp.pi * (p + q)) if abs(p + q) > 1e-40 else mp.mpf(1)
    return (s - t) / 2

def inner_cs(p, q):
    """<cos(pi p x), sin(pi q x)>_{L^2[0,1]}."""
    p = mp.mpf(p); q = mp.mpf(q)
    # int cos(pi p x) sin(pi q x) dx, x in [0,1]
    # = (1/2) int [sin(pi(p+q)x) - sin(pi(p-q)x)] dx (using sin(a)cos(b)=...
    # Actually: cos A sin B = (1/2)[sin(A+B) - sin(A-B)]
    A = mp.pi * p; B = mp.pi * q
    # integral from 0 to 1 of (1/2)[sin((A+B)x) - sin((A-B)x)] dx
    def Iint(omega):
        if abs(omega) < 1e-40:
            return mp.mpf(0)
        return (1 - mp.cos(omega)) / omega
    return (Iint(A + B) - Iint(A - B)) / 2


# ---------- build spectral matrix ----------

def build_spectral_matrix(N, alpha, a):
    """
    Basis u_k = cos or sin functions, weights w_k = a^{-n}.
    Order: (c_0, s_0, c_1, s_1, ..., c_N, s_N) -> size 2(N+1).
    """
    alpha = mp.mpf(alpha)
    a = mp.mpf(a)
    dim = 2 * (N + 1)
    M = mp.matrix(dim, dim)

    # frequencies
    freqs = [alpha ** n for n in range(N + 1)]
    # weights for each level n
    wts = [mp.sqrt(a ** (-n)) for n in range(N + 1)]  # sqrt(w_n)

    # index map: idx = 2n (cos), 2n+1 (sin)
    for n in range(N + 1):
        for m in range(N + 1):
            p = freqs[n]; q = freqs[m]
            sw = wts[n] * wts[m]
            # c_n, c_m
            M[2 * n, 2 * m] = sw * inner_cc(p, q)
            # s_n, s_m
            M[2 * n + 1, 2 * m + 1] = sw * inner_ss(p, q)
            # c_n, s_m
            M[2 * n, 2 * m + 1] = sw * inner_cs(p, q)
            # s_n, c_m
            M[2 * n + 1, 2 * m] = sw * inner_cs(q, p)  # <s_n, c_m> = <c_m, s_n>
    return M


def matrix_to_numpy(M):
    rows = M.rows; cols = M.cols
    A = np.zeros((rows, cols), dtype=np.float64)
    for i in range(rows):
        for j in range(cols):
            A[i, j] = float(M[i, j])
    # symmetrize numerical
    A = 0.5 * (A + A.T)
    return A


def gram_matrix(N, alpha):
    """Gram matrix of the un-weighted basis (for checking linear independence)."""
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


# ---------- main computation ----------

def main():
    alpha = mp.sqrt(2)
    a = mp.mpf(2)
    target = mp.pi / (10 * mp.sqrt(2))
    print(f"alpha = sqrt(2) = {float(alpha):.10f}")
    print(f"a     = {float(a):.10f}")
    print(f"target lambda_0 = pi/(10*sqrt(2)) = {float(target):.10f}")
    print("=" * 78)

    results = {}
    for N in [3, 5, 8, 10, 12, 15, 18, 20]:
        print(f"\n--- N = {N} (dim = {2*(N+1)}) ---")
        M = build_spectral_matrix(N, alpha, a)
        A = matrix_to_numpy(M)
        # Also Gram matrix to assess conditioning
        G = gram_matrix(N, alpha)
        Gnp = matrix_to_numpy(G)
        eigs_A = np.sort(eigvalsh(A))
        eigs_G = np.sort(eigvalsh(Gnp))
        # report
        smallest_pos = eigs_A[eigs_A > 1e-14]
        largest = eigs_A[-1]
        print(f"  Gram min eigenvalue (basis conditioning): {eigs_G[0]:.3e}")
        print(f"  Gram max eigenvalue                     : {eigs_G[-1]:.3e}")
        print(f"  Gram condition number                   : {eigs_G[-1]/max(eigs_G[0],1e-30):.3e}")
        print(f"  Spectral matrix: largest eigenvalue     : {largest:.10f}")
        print(f"  Spectral matrix: 5 smallest (full)      : {eigs_A[:5]}")
        if len(smallest_pos) > 0:
            print(f"  Spectral matrix: 5 smallest positive    : {smallest_pos[:5]}")
            print(f"  Smallest positive eigenvalue            : {smallest_pos[0]:.10f}")
        results[N] = {
            "eigs": eigs_A,
            "gram_eigs": eigs_G,
            "smallest_pos": smallest_pos[0] if len(smallest_pos) > 0 else None,
            "largest": largest,
        }

    # Convergence table
    print("\n" + "=" * 78)
    print(f"{'N':>4} | {'dim':>4} | {'smallest pos':>14} | {'|diff to target|':>18} | "
          f"{'largest':>12} | {'gram cond':>12}")
    print("-" * 78)
    for N, r in results.items():
        sp = r["smallest_pos"]
        diff = abs(sp - float(target)) if sp is not None else float("nan")
        print(f"{N:>4} | {2*(N+1):>4} | {sp:>14.10f} | {diff:>18.6e} | "
              f"{r['largest']:>12.6f} | {r['gram_eigs'][-1]/max(r['gram_eigs'][0],1e-30):>12.3e}")

    # Identify eigenvector for largest N
    Nbig = 15
    print(f"\n--- Eigenvector structure at N={Nbig} ---")
    M = build_spectral_matrix(Nbig, alpha, a)
    A = matrix_to_numpy(M)
    w, V = eigh(A)
    order = np.argsort(w)
    # smallest positive
    pos_mask = w > 1e-14
    pos_idx = np.where(pos_mask)[0]
    if len(pos_idx) > 0:
        k_small = pos_idx[np.argmin(w[pos_idx])]
        vec = V[:, k_small]
        print(f"  Smallest positive eigenvalue: {w[k_small]:.10f}")
        print(f"  Eigenvector components (cos/sin per level):")
        for n in range(Nbig + 1):
            c_coef = vec[2 * n]
            s_coef = vec[2 * n + 1]
            mag = np.hypot(c_coef, s_coef)
            print(f"    n={n:2d}  freq=alpha^{n}={float(alpha**n):.4f}  "
                  f"|c|={abs(c_coef):.4e}  |s|={abs(s_coef):.4e}  total={mag:.4e}")

    # Also report level-1 specific eigenvalues (just the rank-2 from n=0)
    print("\n--- Single-level rank-2 contributions a^-n * (<c_n,c_n>, <s_n,s_n>) ---")
    print("  (these are the level-by-level upper bounds for the operator norm slices)")
    for n in range(6):
        p = alpha ** n
        w_n = a ** (-n)
        cc = inner_cc(p, p)
        ss = inner_ss(p, p)
        print(f"  n={n:2d}  freq={float(p):.6f}  w={float(w_n):.6f}  "
              f"w*<c,c>={float(w_n*cc):.6f}  w*<s,s>={float(w_n*ss):.6f}")


if __name__ == "__main__":
    main()
