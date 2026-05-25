"""
Phase 1 numerical exploration: H3 Coxeter spectrum vs Mayer T_3 transfer operator.

Hypothesis: the H3 Coxeter element's -1 eigenvalue might be the "structural injection
point" of T_3 into H_alpha, giving a shorter path to the RH surjectivity conjecture
than the direct Lewis-Zagier route.

Steps:
  1. Build the H3 Coxeter element explicitly; verify its spectrum is
     {exp(+2*pi*i/10), exp(-2*pi*i/10), -1}.
  2. Compute the Mayer T_3 transfer operator on a polynomial basis on D = {|z|<1},
     get its leading eigenvalues numerically at mp.dps = 50.
  3. Compare: does the Mayer spectrum contain -1, +1, exp(+/- 2*pi*i/10)?
  4. Compare to first few Maass cusp form eigenvalues r_1..r_4.
  5. Test the IBM Galois pair quadratic 4 a^2 - (9 + 2 sqrt5) a + (9 + 6 sqrt5)/2 = 0
     for a 2x2 Mayer subblock.

NOT a proof. NOT a manuscript claim. Pure numerical reconnaissance.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 50

# ---------------------------------------------------------------------------
# 1. H3 Coxeter element
# ---------------------------------------------------------------------------
# H3 is the icosahedral Coxeter group. Coxeter number h = 10, exponents {1,5,9},
# rank 3. Standard Cartan-matrix-based realisation. We construct the Coxeter
# element as the product of the three simple reflections, using the Gram matrix
#
#     B = [[1, -cos(pi/3), 0],
#          [-cos(pi/3), 1, -cos(pi/5)],
#          [0,         -cos(pi/5), 1]]
#
# with simple reflections s_i(v) = v - 2 B[i,:] v_i.

def coxeter_element_H3():
    c3 = mp.cos(mp.pi / 3)        # 1/2
    c5 = mp.cos(mp.pi / 5)        # (1+sqrt5)/4
    B = mp.matrix(3, 3)
    B[0, 0] = mp.mpf(1); B[1, 1] = mp.mpf(1); B[2, 2] = mp.mpf(1)
    B[0, 1] = -c3; B[1, 0] = -c3
    B[1, 2] = -c5; B[2, 1] = -c5
    # B[0,2]=B[2,0]=0
    I = mp.eye(3)
    # Reflection s_i = I - 2 e_i e_i^T B (acts as v -> v - 2(B v)_i e_i)
    def reflection(i):
        S = mp.matrix(I.tolist())
        for j in range(3):
            S[i, j] -= 2 * B[i, j]
        return S
    s1 = reflection(0); s2 = reflection(1); s3 = reflection(2)
    return s1 * s2 * s3

def H3_spectrum():
    C = coxeter_element_H3()
    E, _ = mp.eig(C)
    return sorted([complex(e) for e in E], key=lambda z: (z.real, z.imag))


# ---------------------------------------------------------------------------
# 2. Mayer T_3 transfer operator
# ---------------------------------------------------------------------------
# Mayer 1991: T_s f(z) = sum_{n>=1} (1/(n+z))^{2s} f(1/(n+z)) on the disc
# |z - 1| < 3/2 (analytic functions). Determinant det(1 - T_s) = Selberg zeta of
# the modular surface (modulo factor) -> RH iff T_3 has +/-1 eigenvalues coming
# from Maass forms.
#
# Numerically: project T_s to the polynomial basis {1, z, z^2, ..., z^(N-1)} on
# a disc centered at z_0=0 (Mayer's original construction works there too,
# convergence is fine). Matrix entries:
#   M_{jk} = sum_{n>=1} integral or coefficient extraction.
# We use the simpler Taylor-coefficient approach:
#   (T_s f)(z) = sum_n (n+z)^(-2s) f(1/(n+z))
# Expand in z. Use power series in z to order N-1.

def mayer_matrix(s, N=30, nmax=200):
    """Truncated Mayer transfer operator T_s on polynomial basis {z^0,...,z^(N-1)}
    using Taylor expansion at z=0."""
    s = mp.mpc(s)
    M = mp.matrix(N, N)
    # For each basis function z^k, compute T_s(z^k) as a power series in z, then
    # extract coefficients 0..N-1.
    # T_s(z^k)(z) = sum_{n>=1} (n+z)^(-2s) * (1/(n+z))^k = sum_n (n+z)^(-(2s+k)).
    # Taylor at z=0: (n+z)^(-(2s+k)) = n^(-(2s+k)) * (1+z/n)^(-(2s+k))
    #   = n^(-(2s+k)) * sum_{j>=0} C(-(2s+k), j) (z/n)^j
    #   = sum_{j>=0} n^(-(2s+k+j)) * C(-(2s+k), j) z^j
    # So coefficient of z^j in T_s(z^k) is
    #   sum_{n=1}^inf n^(-(2s+k+j)) * binom(-(2s+k), j)
    #   = binom(-(2s+k), j) * zeta(2s+k+j)
    # using Riemann zeta -- but only when Re(2s+k+j) > 1, which is fine for s=3
    # since 2s=6.
    for k in range(N):
        for j in range(N):
            exponent = 2 * s + k + j
            # generalized binomial C(-(2s+k), j) = prod_{i=0..j-1} (-(2s+k)-i)/j!
            a = -(2 * s + k)
            if j == 0:
                binom = mp.mpc(1)
            else:
                num = mp.mpc(1)
                for i in range(j):
                    num *= (a - i)
                binom = num / mp.factorial(j)
            zeta_val = mp.zeta(exponent)
            M[j, k] = binom * zeta_val
    return M

def mayer_eigenvalues(s, N=30, top=20):
    M = mayer_matrix(s, N=N)
    E, _ = mp.eig(M)
    # Sort by |modulus|, descending.
    Esorted = sorted([complex(e) for e in E], key=lambda z: -abs(z))
    return Esorted[:top]


# ---------------------------------------------------------------------------
# 3. Maass cusp form eigenvalues
# ---------------------------------------------------------------------------
# Standard tabulated first few r_n for PSL(2,Z) (e.g. Then 1999, Booker 2006).
MAASS_R_TABULATED = [
    mp.mpf("13.77975135189"),
    mp.mpf("17.73856338106"),
    mp.mpf("19.42348147083"),
    mp.mpf("21.31579594020"),
    mp.mpf("22.19467397990"),
    mp.mpf("24.11235272132"),
]


# ---------------------------------------------------------------------------
# 4. Comparisons / structural tests
# ---------------------------------------------------------------------------

def report():
    print("="*70)
    print("PHASE 1: H3 vs Mayer T_3 numerical reconnaissance (mp.dps=50)")
    print("="*70)

    # ---- H3 Coxeter ----
    print("\n[H3 Coxeter element spectrum]")
    sp = H3_spectrum()
    for e in sp:
        z = mp.mpc(e)
        print(f"  {e}    |z|={mp.fabs(z)}   arg/pi = {mp.arg(z)/mp.pi}")

    # Expected: {1, exp(+2 pi i/10), exp(-2 pi i/10), -1} -- but rank-3 Coxeter has
    # exactly 3 eigenvalues. Per the standard formula they are exp(2 pi i m_j/h)
    # for exponents m_j in {1,5,9} and h=10:
    #   exp(2 pi i * 1/10), exp(2 pi i * 5/10) = -1, exp(2 pi i * 9/10) = exp(-2pi i/10).
    print("\n  Expected (m_j in {1,5,9}, h=10):")
    for m in (1, 5, 9):
        z = mp.exp(2j * mp.pi * m / 10)
        print(f"    m={m}: {complex(z)}   arg/pi={mp.arg(z)/mp.pi}")

    # ---- Mayer T_3 spectrum ----
    print("\n[Mayer T_3 leading eigenvalues -- truncation N=30]")
    eigs = mayer_eigenvalues(3, N=30, top=12)
    for i, e in enumerate(eigs):
        print(f"  lambda_{i:02d} = {e}    |.|={abs(e):.20f}")

    # ---- Targeted matches ----
    print("\n[Targeted match tests: does Mayer T_3 spectrum contain ...?]")
    targets = {
        "-1 (Maass)": mp.mpc(-1),
        "+1 (Eisenstein/even Maass)": mp.mpc(1),
        "exp(+2 pi i/10)": mp.exp(2j * mp.pi / 10),
        "exp(-2 pi i/10)": mp.exp(-2j * mp.pi / 10),
        "1/golden phi": (mp.sqrt(5) - 1) / 2,
        "1/golden^2": 1 / ((1 + mp.sqrt(5)) / 2)**2,
    }
    for name, t in targets.items():
        dists = [abs(complex(t) - e) for e in eigs]
        best = min(dists)
        idx = dists.index(best)
        print(f"  target {name:30s} -> closest |delta| = {best:.6e} at lambda_{idx:02d}")

    # ---- IBM Galois pair test ----
    # Galois pair quadratic 4a^2 - (9 + 2 sqrt5)a + (9 + 6 sqrt5)/2 = 0
    # roots = ((9 + 2 sqrt5) +/- sqrt(disc))/8
    print("\n[IBM Galois pair quadratic -- numerical roots]")
    sqrt5 = mp.sqrt(5)
    bcoef = -(9 + 2 * sqrt5)
    ccoef = (9 + 6 * sqrt5) / 2
    disc = bcoef * bcoef - 16 * ccoef
    print(f"  discriminant = {disc}")
    r1 = ((9 + 2 * sqrt5) + mp.sqrt(disc)) / 8
    r2 = ((9 + 2 * sqrt5) - mp.sqrt(disc)) / 8
    print(f"  Galois roots: {complex(r1)},  {complex(r2)}")
    print("  closest Mayer eigenvalues to these roots:")
    for r, lbl in ((r1, "root1"), (r2, "root2")):
        dists = [abs(complex(r) - e) for e in eigs]
        best = min(dists)
        idx = dists.index(best)
        print(f"    {lbl} -> closest |delta| = {best:.6e} at lambda_{idx:02d} = {eigs[idx]}")

    # ---- Maass eigenvalues vs H3 data ----
    print("\n[Maass cusp form r_n vs H3 exponents {1,5,9} and phi powers]")
    phi = (1 + mp.sqrt(5)) / 2
    print(f"  phi      = {phi}")
    print(f"  phi^2    = {phi**2}")
    print(f"  phi^5    = {phi**5}")
    print(f"  phi^7    = {phi**7}")
    print(f"  10*phi   = {10 * phi}")
    print(f"  pi*phi^2 = {mp.pi * phi**2}")
    print(f"  pi*5/phi = {mp.pi * 5 / phi}")
    for n, r in enumerate(MAASS_R_TABULATED, start=1):
        print(f"  r_{n} = {r}")
        # Look for any simple combination
        guesses = {
            "r_n / pi": r / mp.pi,
            "r_n / phi": r / phi,
            "r_n - 10": r - 10,
            "r_n - 5 phi": r - 5 * phi,
            "(r_n - r_1) / pi": (r - MAASS_R_TABULATED[0]) / mp.pi if n > 1 else None,
        }
        for k, v in guesses.items():
            if v is None:
                continue
            print(f"      {k:20s} = {v}")

    # ---- Convergence sanity ----
    print("\n[Mayer T_3 spectrum stability vs truncation]")
    for Nv in (15, 20, 25, 30, 40):
        eigs_v = mayer_eigenvalues(3, N=Nv, top=6)
        print(f"  N={Nv}: top-6 |lambda|: " + ", ".join(f"{abs(e):.10f}" for e in eigs_v))


if __name__ == "__main__":
    report()
