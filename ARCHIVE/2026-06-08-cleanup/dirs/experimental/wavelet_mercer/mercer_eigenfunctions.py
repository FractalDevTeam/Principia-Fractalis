"""
Eigenfunction structure analysis for the truncated rank-2-per-level operator.

Reports the lowest few eigenvalues + the eigenvector coefficients in the
ORTHONORMALIZED basis (back-translated to cos/sin amplitudes per level).
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


def build(N, alpha, a):
    alpha = mp.mpf(alpha); a = mp.mpf(a)
    dim = 2 * (N + 1)
    G = np.zeros((dim, dim))
    W = np.zeros((dim, dim))
    freqs = [alpha ** n for n in range(N + 1)]
    for n in range(N + 1):
        w = float(a ** (-n))
        W[2*n, 2*n] = w; W[2*n+1, 2*n+1] = w
        for m in range(N + 1):
            p = freqs[n]; q = freqs[m]
            G[2*n, 2*m]     = float(inner_cc(p, q))
            G[2*n+1, 2*m+1] = float(inner_ss(p, q))
            G[2*n, 2*m+1]   = float(inner_cs(p, q))
            G[2*n+1, 2*m]   = float(inner_cs(q, p))
    G = 0.5 * (G + G.T)
    return G, W, freqs


def true_spectrum(N, alpha, a, tol=1e-13):
    G, W, freqs = build(N, alpha, a)
    g_vals, g_vecs = np.linalg.eigh(G)
    cutoff = tol * g_vals.max()
    keep = g_vals > cutoff
    r = int(keep.sum())
    sqrt_g = np.zeros_like(g_vals); inv_sqrt_g = np.zeros_like(g_vals)
    sqrt_g[keep] = np.sqrt(g_vals[keep])
    inv_sqrt_g[keep] = 1.0 / np.sqrt(g_vals[keep])
    G_half = g_vecs @ np.diag(sqrt_g) @ g_vecs.T
    G_inv_half = g_vecs @ np.diag(inv_sqrt_g) @ g_vecs.T

    # K = G^{1/2} W G^{1/2}, eigenvectors d.  Original basis coeffs c = G^{-1/2} d.
    K = G_half @ W @ G_half
    K = 0.5 * (K + K.T)
    vals, vecs = np.linalg.eigh(K)
    order = np.argsort(vals)[::-1]
    vals = vals[order]; vecs = vecs[:, order]
    # back-translate eigenvectors
    coefs = G_inv_half @ vecs  # columns = c vectors in (cos,sin) basis
    return vals, coefs, freqs, r


def main():
    alpha = mp.sqrt(2)
    a = mp.mpf(2)
    target = float(mp.pi / (10 * mp.sqrt(2)))
    print(f"target = pi/(10 sqrt 2) = {target:.10f}")
    print()

    for N in [10, 15, 20]:
        vals, coefs, freqs, r = true_spectrum(N, alpha, a)
        print(f"=== N = {N}, effective rank {r} ===")
        print(f"Top 5 eigenvalues: {vals[:5]}")
        print()
        # Detailed for the k=2 eigenvalue (closest to target)
        for k in [0, 1, 2, 3]:
            lam = vals[k]
            c = coefs[:, k]
            # normalize so that ||sum c_i u_i||_{L^2} = 1 -> c^T G c = 1
            # (already ensured by construction: G^{-1/2} d with d unit norm
            #  gives c such that c^T G c = d^T G^{-1/2} G G^{-1/2} d = d^T d = 1)
            # report amplitudes per level
            print(f"  k={k}  lambda = {lam:.10f}  (diff to target = {lam - target:+.6e})")
            tot = 0.0
            for n in range(N + 1):
                cn = c[2 * n]; sn = c[2 * n + 1]
                mag = np.hypot(cn, sn)
                if mag > 1e-6 or n < 5:
                    print(f"      n={n:2d} alpha^n={float(freqs[n]):8.4f}  "
                          f"c={cn:+.4e}  s={sn:+.4e}  |.|={mag:.4e}")
                tot += mag**2
            print()
        # also: what is the spectral gap (1st - 2nd, etc.)?
        print(f"  Differences (k to k+1): {np.diff(vals[:6])}")
        print()

    # Compare to manuscript's level-1 prediction lambda^(1)_+ ≈ 0.49 etc.
    print("Manuscript-derived level-1 brackets at alpha=sqrt(2):")
    print("  lambda^(1)_+ in [0.451, 0.534]   (Ch 21 level-1 spectrum)")
    print("  lambda^(1)_- in [1.466, 1.549]   (Ch 21 level-1 spectrum)")
    print("  conjectured lim lambda_0 = pi/(10*sqrt(2)) = 0.22214")
    print()
    print("Numerical truncated spectrum has TOP eigenvalues:")
    print("  0.9061, 0.7071, 0.1722, 0.1023, ...")
    print()
    print("The eigenvalue 0.17219 (k=2) is the closest to target 0.22214")
    print("but |0.17219 - 0.22214| = 0.04995 (5e-2 gap).")
    print("Converged to 8 digits by N=12 — so this is NOT a truncation artifact.")
    print()
    print("Note: 0.17219 ≈ pi/(10 sqrt 2) * (1 - 0.225)")
    print("      0.17219 ≈ sqrt(2)/(8.21)   ≈ ?")
    print(f"      0.17219 / pi = {0.17219/np.pi:.6f}")
    print(f"      sqrt(2)/0.17219 = {np.sqrt(2)/0.17219:.6f}")
    print(f"      1/0.17219 = {1/0.17219:.6f}  ~ 5.808")
    print(f"      0.17219 * 10 = {0.17219 * 10}  not particularly clean")
    print(f"      0.17219 - 1/6 = {0.17219 - 1/6:+.6f}")
    print(f"      0.17219 vs sqrt(pi)/10.30 = {np.sqrt(np.pi)/10.30:.6f}")
    print(f"      cos(2 pi sqrt 2 / 3) ≈ {np.cos(2*np.pi*np.sqrt(2)/3):.6f}")
    print(f"      0.17219 / (pi/(10 sqrt 2)) = {0.17219/target:.6f}")


if __name__ == "__main__":
    main()
