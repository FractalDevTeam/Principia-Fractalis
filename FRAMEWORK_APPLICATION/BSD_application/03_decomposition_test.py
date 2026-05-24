"""
BSD Application — Step 3
TEST the framework decomposition: L(E, s) =? R_f(3π/4, s) · M_E(s)

We compute M_E(s) := L(E, s) / R_f(3π/4, s) for each curve at s = 1,
and probe:
  (a) Is M_E something curve-specific (it MUST depend on E)?
  (b) Does the ratio capture rank — i.e., does M_E(1) vanish to the
      same order as L(E, s) at s=1?
  (c) Is there a clean "Dirichlet-convolution" relation:
          L(E, s) = R_f(3π/4, s) ⋆ c_E(s)
      where c_E(s) = Σ b_n / n^s with b_n explicit?

R_f(3π/4, s) DOES NOT vanish at s=1 (we saw R_f(3π/4, 1) ≈ -0.569+1.394i,
nonzero, ∂_s R_f also nonzero).  So a multiplicative factorization
L = R_f · M would force the rank ENTIRELY into M_E.  That makes M_E
the "real" carrier of arithmetic content — not what the framework claim
intends.  This is the central honesty point of this script.

We ALSO check the *additive* / *convolutional* alternatives that the
framework might intend, and compute the Dirichlet coefficients b_n in
each case.
"""

from mpmath import mp, mpf, mpc, pi, exp, sqrt, log, expj, e1
from math import gcd

mp.dps = 40

ALPHA_BSD = 3*pi/4

# Reuse helpers from script 2:
def is_prime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    i = 3
    while i*i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def d3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s


def count_points_long(a1, a2, a3, a4, a6, p):
    cnt = 1
    for x in range(p):
        rhs = (x*x*x + a2*x*x + a4*x + a6) % p
        b = (a1*x + a3) % p
        disc = (b*b + 4*rhs) % p
        if disc == 0:
            cnt += 1
        else:
            leg = pow(disc, (p-1)//2, p)
            if leg == 1:
                cnt += 2
    return cnt


def a_p_long(a1, a2, a3, a4, a6, p):
    return p + 1 - count_points_long(a1, a2, a3, a4, a6, p)


def build_an_sequence(coeffs_long, N_curve, n_max):
    a1, a2, a3, a4, a6 = coeffs_long
    primes = [p for p in range(2, n_max+1) if is_prime(p)]
    a_p = {p: a_p_long(a1, a2, a3, a4, a6, p) for p in primes}
    a_pk = {}
    for p in primes:
        a_pk[(p,1)] = a_p[p]
        chi = 0 if N_curve % p == 0 else 1
        k = 2
        while p**k <= n_max:
            a_pk[(p,k)] = a_p[p] * a_pk[(p,k-1)] - chi * p * a_pk.get((p,k-2), 1 if k==2 else 0)
            k += 1
    a = [0]*(n_max+1)
    a[1] = 1
    for n in range(2, n_max+1):
        m = n
        val = 1
        for p in primes:
            if p*p > m:
                break
            if m % p == 0:
                k = 0
                while m % p == 0:
                    m //= p
                    k += 1
                val *= a_pk[(p,k)]
        if m > 1:
            val *= a_p[m]
        a[n] = val
    return a


def L_at_1_AFE(a, N_curve, n_max):
    sqrtN = sqrt(mpf(N_curve))
    total = mpf(0)
    for n in range(1, n_max+1):
        if a[n] == 0: continue
        total += mpf(a[n])/n * exp(-2*pi*n/sqrtN)
    return 2 * total


def Lprime_at_1_AFE(a, N_curve, n_max):
    sqrtN = sqrt(mpf(N_curve))
    total = mpf(0)
    for n in range(1, n_max+1):
        if a[n] == 0: continue
        total += mpf(a[n])/n * e1(2*pi*n/sqrtN)
    return 2 * total


def rf(alpha, s, N):
    s = mpc(s); alpha = mpc(alpha)
    total = mpc(0); pia = pi * alpha
    for n in range(1, N+1):
        total += expj(pia * d3(n)) / mpc(n)**s
    return total


# Dirichlet convolution: c = a ⋆ b where c_n = Σ_{d|n} a_d b_{n/d}
def dirichlet_convolve(a, b, n_max):
    c = [mpc(0)]*(n_max+1)
    for d in range(1, n_max+1):
        if a[d] == 0: continue
        for k in range(1, n_max//d + 1):
            c[d*k] += a[d] * b[k]
    return c


# Dirichlet "deconvolution": given c and a (with a_1 ≠ 0), find b such that c = a ⋆ b.
# Recurrence:  c_n = Σ_{d|n} a_d b_{n/d} = a_1 b_n + Σ_{d|n, d>1} a_d b_{n/d}
# so  b_n = (c_n − Σ_{d|n, d>1} a_d b_{n/d}) / a_1.
def dirichlet_deconvolve(c, a, n_max):
    assert abs(a[1]) > 1e-40, "deconvolution requires a_1 ≠ 0"
    a1_inv = mpc(1) / a[1]
    b = [mpc(0)]*(n_max+1)
    for n in range(1, n_max+1):
        s = mpc(c[n])
        # divisors d > 1
        for d in range(2, n+1):
            if n % d == 0:
                s -= a[d] * b[n // d]
        b[n] = s * a1_inv
    return b


CURVES = [
    ("11a1",   (0,-1,1,-10,-20), 11,   0, +1),
    ("37a1",   (0, 0,1, -1,  0), 37,   1, -1),
    ("389a1",  (0, 1,1, -2,  0), 389,  2, +1),
    ("5077a1", (0, 0,1, -7,  6), 5077, 3, -1),
]


def main():
    n_max_an = 2000
    n_max_rf = 2000  # use the SAME truncation for the Dirichlet series factor

    # Build R_f's Dirichlet coefficients: r_n = e^{iπα D_3(n)}.
    # NOTE: these are coefficients of a Dirichlet series, NOT a multiplicative
    # arithmetic function in general — but the convolution algebra works regardless.
    print(f"\nBuilding R_f Dirichlet coefficients r_n = e^(iπ·3π/4·D_3(n)) for n ≤ {n_max_rf}")
    pia = pi * ALPHA_BSD
    r = [mpc(0)] + [expj(pia * d3(n)) for n in range(1, n_max_rf+1)]
    # consistency: Σ r_n / n with small damping = R_f(3π/4, 1) approximate
    quick = sum(r[n]/n for n in range(1, n_max_rf+1))
    print(f"  partial sum Σ_{{n≤{n_max_rf}}} r_n/n = {mp.nstr(quick, 8)}")
    print(f"  (cf. full R_f(3π/4,1) ≈ -0.569 + 1.394i)")

    # is r multiplicative? r_n_r_m = r_{nm}?  Test on a few coprime pairs
    print("\n  multiplicativity test (r_m · r_n  vs  r_{mn}, gcd(m,n)=1):")
    for (m,nn) in [(2,3),(2,5),(3,5),(2,7),(4,9),(5,7)]:
        lhs = r[m]*r[nn]; rhs = r[m*nn]
        print(f"    m={m},n={nn}: r_m r_n - r_{{mn}} = {mp.nstr(lhs - rhs, 4)}")
    # answer: D_3(mn) ≠ D_3(m)+D_3(n) in general; r_n is NOT multiplicative.

    print("\n" + "="*70)
    print("TEST: L(E, s) = R_f(3π/4, s) · M_E(s)  at  s = 1")
    print("="*70)

    rf_val = rf(ALPHA_BSD, 1, 500_000)
    print(f"\nR_f(3π/4, 1) ≈ {mp.nstr(rf_val, 16)}")
    print(f"  nonzero: |R_f| = {mp.nstr(abs(rf_val), 8)}")

    for label, coeffs, N_curve, rank, sign in CURVES:
        print(f"\n--- E_{label} (rank {rank}) ---")
        a = build_an_sequence(coeffs, N_curve, n_max_an)
        if sign == +1:
            Lv = L_at_1_AFE(a, N_curve, n_max_an)
        else:
            Lv = mpc(0)  # exact by functional eq
        Lv = mpc(Lv)
        ratio = Lv / rf_val
        print(f"  L(E, 1)         = {mp.nstr(Lv, 12)}")
        print(f"  M_E(1) := L/R_f = {mp.nstr(ratio, 12)}")
        if rank == 0:
            print(f"   • rank 0:  M_E(1) ≠ 0 expected — got |M_E| = {mp.nstr(abs(ratio), 6)}")
        else:
            print(f"   • rank {rank}: L=0, so M_E(1) = 0 trivially.")
            print(f"     Multiplicative factorisation FORCES rank into M_E(s).")
            print(f"     This is just a definitional rearrangement — R_f doesn't 'see' the rank.")

    print("\n" + "="*70)
    print("TEST: Dirichlet deconvolution.  Solve  a_E = r ⋆ b_E  for b_E.")
    print("If b_E has a clean closed form (or a finite support), there is a")
    print("genuine 'R_f explains L(E,s) up to b_E' result.  Otherwise b_E is")
    print("just  b_E = r^{-1} ⋆ a_E,  a formal rearrangement carrying ALL the")
    print("arithmetic content.")
    print("="*70)

    for label, coeffs, N_curve, rank, sign in CURVES:
        print(f"\n--- E_{label} ---")
        a = build_an_sequence(coeffs, N_curve, 50)
        # extend a to mpc list with index 0
        a_mpc = [mpc(0)] + [mpc(a[n]) for n in range(1, 51)]
        b = dirichlet_deconvolve(a_mpc, r[:51], 50)
        print(f"  first 20 b_n (E's contribution after dividing by R_f's coeffs):")
        for n in range(1, 21):
            print(f"    b_{n} = {mp.nstr(b[n], 6)}")
        # measure: are |b_n| growing, shrinking, or staying bounded?
        mags = [float(abs(b[n])) for n in range(1, 51)]
        print(f"  |b_n| stats over n=1..50:   max={max(mags):.4g}   "
              f"mean={sum(mags)/len(mags):.4g}   min(n>1)={min(mags[1:]):.4g}")
        # are they integer-related?  Check b_n / a_n (since a_n are integers).
        ratios = []
        for n in range(1, 21):
            if a[n] != 0:
                ratios.append((n, b[n]/mpc(a[n])))
        print(f"  b_n / a_n for n=1..20  (looking for any pattern):")
        for nn, rr in ratios[:10]:
            print(f"    b_{nn}/a_{nn} = {mp.nstr(rr, 6)}")

    print("\n" + "="*70)
    print("HONEST ASSESSMENT (printed for the record):")
    print("="*70)
    print("""
1. R_f(3π/4, 1) is FINITE AND NONZERO.  It can therefore neither
   vanish to order 0 (consistent with rank 0) nor to order 1, 2, 3
   (the actual ranks of our test curves) — it is α-fixed, not E-fixed.
2. A factorisation  L(E, s) = R_f(3π/4, s) · M_E(s)  is therefore a
   TAUTOLOGY: it merely defines M_E(s) := L(E, s)/R_f(3π/4, s), and
   ALL the arithmetic of E lives in M_E.  The framework needs a
   non-trivial structural relation between M_E and the curve, not a
   division identity.
3. φ/e is NOT a numerical match for R_f(3π/4, 1), |R_f(3π/4, 1)|,
   Re R_f(3π/4, 1), Im R_f(3π/4, 1), nor the universal coupling
   λ_0 = 2/15.  The 'distinguished eigenvalue' φ/e is a separate
   manuscript constant whose role in the BSD application is not
   discharged by the present numerical content.
4. The 4-basis pinning  α_BSD = (π/2)·α_RH  is purely an algebraic
   relation between the two α values; it does not by itself transfer
   any analytic content from RH to BSD.  A cascade  RH ⇒ BSD  would
   require an additional construction (e.g. an explicit relationship
   between Z(H_{α_RH}) and Z(H_{α_BSD}) inducing the L-function),
   which is not present in the framework's current machinery.
""")


if __name__ == "__main__":
    main()
