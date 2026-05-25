"""
Phase 1b: corrected Mayer operator.

The Mayer transfer operator acts on the disc D = {|z-1| < 3/2}. The natural
basis is (z-1)^k. We project T_s onto this basis: write z = 1 + u with |u|<3/2,
expand both the kernel and f((1/(n+z))) in powers of u.

  (T_s f)(z) = sum_{n>=1} (n+z)^(-2s) f(1/(n+z))
             = sum_{n>=1} ((n+1) + u)^(-2s) f(1/((n+1) + u))

Let m = n+1 so m>=2. Then T_s acts on the new variable u via
  (T_s f)(u) = sum_{m>=2} (m+u)^(-2s) g_f(u, m)
where g_f(u,m) = f(1/(m+u) - 1)  -- since f is evaluated as a function of (z-1)
in our shifted variable.

Write 1/(m+u) - 1 = (1 - m - u)/(m+u) = -(m-1+u)/(m+u).
We want this as a series in u. Set v = u (small). Then
  1/(m+u) - 1 = -(m-1)/m + ... (a power series in u with leading constant
  -(m-1)/m).
For m=2: leading constant -1/2 (within |.|<3/2, ok). For m=3: -2/3. Etc.

If f(w) = w^k, then T_s(w^k)(u) = sum_{m>=2} (m+u)^(-2s) * [-(m-1+u)/(m+u)]^k
       = sum_{m>=2} (-1)^k (m-1+u)^k (m+u)^(-(2s+k)).

Expand around u=0:
  (m-1+u)^k = sum_{j=0..k} C(k,j) (m-1)^(k-j) u^j
  (m+u)^(-(2s+k)) = sum_{i>=0} C(-(2s+k), i) m^(-(2s+k)-i) u^i

So the coefficient of u^p in T_s(w^k)(u) is
  (-1)^k * sum_{m>=2} sum_{j+i=p, 0<=j<=k} C(k,j) (m-1)^(k-j) * C(-(2s+k), i) * m^(-(2s+k)-i)

We sum m from 2 to a large M (truncate the tail).

For s=3 (the Riemann zeta case), 2s=6, so m^(-(6+k)-i) decays fast and finite
sums converge geometrically.
"""
from __future__ import annotations
import mpmath as mp

mp.mp.dps = 50

def gen_binom(a, j):
    """generalized binomial C(a, j) for j non-negative integer, a complex."""
    if j == 0:
        return mp.mpc(1)
    prod = mp.mpc(1)
    for i in range(j):
        prod *= (a - i)
    return prod / mp.factorial(j)

def mayer_matrix_correct(s, N=30, Mmax=400):
    s = mp.mpc(s)
    M = mp.matrix(N, N)
    # Precompute (-1)^k factor handled per column
    for k in range(N):
        sign_k = mp.mpc(1) if k % 2 == 0 else mp.mpc(-1)
        for p in range(N):
            total = mp.mpc(0)
            # m from 2 to Mmax
            for mval in range(2, Mmax + 1):
                m_mp = mp.mpf(mval)
                # inner: sum_{j+i=p, 0<=j<=k} C(k,j)(m-1)^(k-j) C(-(2s+k),i) m^(-(2s+k)-i)
                inner = mp.mpc(0)
                jmax = min(k, p)
                for j in range(0, jmax + 1):
                    i = p - j
                    # C(k,j) integer binomial
                    Ck = mp.binomial(k, j)
                    # (m-1)^(k-j)
                    pow_mm1 = (m_mp - 1) ** (k - j)
                    # C(-(2s+k), i)
                    Cs = gen_binom(-(2 * s + k), i)
                    pow_m = m_mp ** (-(2 * s + k) - i)
                    inner += Ck * pow_mm1 * Cs * pow_m
                total += inner
            M[p, k] = sign_k * total
    return M

def mayer_eigenvalues_correct(s, N=30, Mmax=400, top=12):
    M = mayer_matrix_correct(s, N=N, Mmax=Mmax)
    E, _ = mp.eig(M)
    Es = sorted([complex(e) for e in E], key=lambda z: -abs(z))
    return Es[:top]

def main():
    print(f"Mayer T_s on basis (z-1)^k, s=3, mp.dps={mp.mp.dps}")
    # First, sanity check at s=1, where T_1 has eigenvalue 1 (eigenfunction
    # related to Gauss measure for the continued-fraction transfer operator).
    print("\n[s=1 sanity: leading eigenvalue should be 1 (Gauss / continued frac)]")
    for Nv in (15, 20, 25):
        eigs = mayer_eigenvalues_correct(1, N=Nv, Mmax=300, top=4)
        print(f"  N={Nv:2d}: " + ", ".join(f"{abs(e):.10f} (arg/pi={float(mp.arg(mp.mpc(e))/mp.pi):.3f})" for e in eigs))

    print("\n[s=3 leading eigenvalues]")
    for Nv in (15, 20, 25, 30):
        eigs = mayer_eigenvalues_correct(3, N=Nv, Mmax=400, top=8)
        print(f"  N={Nv:2d}:")
        for i, e in enumerate(eigs):
            print(f"    lambda_{i:02d} = {e}   |.|={abs(e):.12f}")

    # final dense:
    print("\n[s=3, N=30, larger Mmax=600 -- final]")
    eigs = mayer_eigenvalues_correct(3, N=30, Mmax=600, top=12)
    for i, e in enumerate(eigs):
        z = mp.mpc(e)
        print(f"  lambda_{i:02d} = {e}   |.|={abs(e):.20f}  arg/pi={mp.arg(z)/mp.pi}")

    # Now do the H3 + Galois pair tests on these:
    targets = {
        "-1 (Maass)": mp.mpc(-1),
        "+1": mp.mpc(1),
        "exp(+2pi i/10)": mp.exp(2j*mp.pi/10),
        "exp(-2pi i/10)": mp.exp(-2j*mp.pi/10),
        "1.5 (alpha_RH)": mp.mpc("1.5"),
        "1.868034 (Galois r1)": mp.mpc("1.868033988749895"),
        "1/phi": (mp.sqrt(5)-1)/2,
        "1/phi^2": ((mp.sqrt(5)-1)/2)**2,
    }
    print("\n[Targeted matches on s=3 spectrum]")
    for name, t in targets.items():
        dists = [abs(complex(t)-e) for e in eigs]
        best = min(dists)
        idx = dists.index(best)
        print(f"  {name:30s} closest |delta|={best:.6e} at lambda_{idx:02d}={eigs[idx]}")

if __name__ == "__main__":
    main()
