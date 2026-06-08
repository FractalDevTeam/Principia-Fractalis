"""
BSD Bridge — Step 2: Mertens-style explicit formula with R_f twist

KEY INSIGHT from step 1:
The CLASSICAL Mertens-type statistic
    M(E, X) := -Σ_{p ≤ X} a_p(E) / p
already tracks rank monotonically:
    rank 0:  0.91
    rank 1:  3.28
    rank 2:  5.13
    rank 3:  7.21

This is essentially Goldfeld's conjecture / the explicit formula at s=1:
   Σ_{p ≤ X} a_p · log(p) / p  ~  -rank · log(X)   as X → ∞.

THE BRIDGE TEST: does multiplying by r_p = e^{iπα D_3(p)} PRESERVE
the rank-detection signal, or DESTROY it?

If it preserves:
  - The framework's R_f at α=3π/4 acts as a UNITARY TWIST on the
    Hecke-eigenvalue rank fingerprint (|r_p|=1 so it's a phase rotation).
  - Then a refined operator R_f-weighted-Hecke could implement BSD
    rank detection inside the framework.

If it destroys:
  - R_f-phases interfere with each other and wash out the rank signal.
  - The bridge requires a SPECIFIC choice of α that interacts
    constructively with the explicit-formula sum.

We test BOTH at α=3π/4 AND at a sweep of nearby α to see if α=3π/4 is
special, AND with logarithmic weighting to match Goldfeld asymptotics.
"""

from mpmath import mp, mpf, mpc, pi, exp, sqrt, log, expj, e1
import math

mp.dps = 30

ALPHA_BSD = 3*pi/4

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0: return False
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def d3(n):
    s = 0
    while n > 0:
        s += n % 3; n //= 3
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
            if leg == 1: cnt += 2
    return cnt

def a_p_long(coeffs, p):
    a1,a2,a3,a4,a6 = coeffs
    return p + 1 - count_points_long(a1,a2,a3,a4,a6, p)


CURVES = [
    ("11a1",   (0,-1,1,-10,-20), 11,   0),
    ("37a1",   (0, 0,1, -1,  0), 37,   1),
    ("389a1",  (0, 1,1, -2,  0), 389,  2),
    ("5077a1", (0, 0,1, -7,  6), 5077, 3),
]


def main():
    P_MAX = 2000  # larger range for asymptotic clarity
    primes = [p for p in range(2, P_MAX+1) if is_prime(p)]
    print(f"Using {len(primes)} primes up to {P_MAX}")

    # Precompute a_p for all curves
    print("Precomputing a_p for all curves...")
    AP = {}
    for label, coeffs, N_curve, rank in CURVES:
        AP[label] = {}
        for p in primes:
            if N_curve % p == 0:
                AP[label][p] = None  # bad prime
            else:
                AP[label][p] = a_p_long(coeffs, p)
    print("  done.")

    print("\n" + "="*78)
    print("(A) GOLDFELD/EXPLICIT-FORMULA STATISTIC")
    print("    M_log(E, X) := -Σ_{p≤X} a_p log(p) / (p · log X)")
    print("    Expected: M_log → rank as X → ∞ (under BSD + GRH).")
    print("="*78)

    print(f"\n{'curve':10}{'rank':>5} | "
          f"{'M_log @ X=200':>14} | {'X=500':>10} | {'X=1000':>10} | {'X=2000':>10}")
    print("-"*72)
    for label, coeffs, N_curve, rank in CURVES:
        row = [label, rank]
        for X in [200, 500, 1000, 2000]:
            good = [p for p in primes if p <= X and AP[label][p] is not None]
            S = sum(mpf(AP[label][p]) * mp.log(p) / p for p in good)
            M_log = -S / mp.log(X)
            row.append(M_log)
        print(f"{row[0]:10}{row[1]:>5} | "
              f"{mp.nstr(row[2], 6):>14} | {mp.nstr(row[3], 6):>10} | "
              f"{mp.nstr(row[4], 6):>10} | {mp.nstr(row[5], 6):>10}")

    print("\n" + "="*78)
    print("(B) R_f-TWISTED STATISTIC at α=3π/4")
    print("    M_log^R_f(E, X) := -Σ_{p≤X} a_p · r_p · log(p) / (p · log X)")
    print("    Question: does the twist preserve the rank signal?")
    print("="*78)

    pia = pi * ALPHA_BSD
    r = {p: expj(pia * d3(p)) for p in primes}

    print(f"\n{'curve':10}{'rank':>5} | "
          f"{'|M_log^Rf| @ X=200':>20} | {'X=500':>12} | {'X=1000':>12} | {'X=2000':>12}")
    print("-"*82)
    for label, coeffs, N_curve, rank in CURVES:
        row = [label, rank]
        for X in [200, 500, 1000, 2000]:
            good = [p for p in primes if p <= X and AP[label][p] is not None]
            S = sum(mpf(AP[label][p]) * r[p] * mp.log(p) / p for p in good)
            M_log_rf = -S / mp.log(X)
            row.append(abs(M_log_rf))
        print(f"{row[0]:10}{row[1]:>5} | "
              f"{mp.nstr(row[2], 6):>20} | {mp.nstr(row[3], 6):>12} | "
              f"{mp.nstr(row[4], 6):>12} | {mp.nstr(row[5], 6):>12}")

    print("\n" + "="*78)
    print("(C) Re-PROJECTION: M_log^R_f^Re(E,X) := -Σ a_p · Re(r_p) · log(p)/(p log X)")
    print("    This is the (cos-weighted) PROJECTION onto a real subspace.")
    print("    The R_f-phase D_3(p) is taken mod (2π/3π/4 · 2) ≈ mod 8/3.")
    print("="*78)

    print(f"\n{'curve':10}{'rank':>5} | "
          f"{'M_log^Re @ X=200':>18} | {'X=500':>10} | {'X=1000':>10} | {'X=2000':>10}")
    print("-"*72)
    for label, coeffs, N_curve, rank in CURVES:
        row = [label, rank]
        for X in [200, 500, 1000, 2000]:
            good = [p for p in primes if p <= X and AP[label][p] is not None]
            S = sum(mpf(AP[label][p]) * mp.re(r[p]) * mp.log(p) / p for p in good)
            M_log_re = -S / mp.log(X)
            row.append(M_log_re)
        print(f"{row[0]:10}{row[1]:>5} | "
              f"{mp.nstr(row[2], 6):>18} | {mp.nstr(row[3], 6):>10} | "
              f"{mp.nstr(row[4], 6):>10} | {mp.nstr(row[5], 6):>10}")

    print("\n" + "="*78)
    print("(D) α-SWEEP: does α=3π/4 have a SPECIAL value here?")
    print("    Compute |M_log^R_f(E, X=2000)| over a grid of α values for rank-1 curve.")
    print("="*78)

    label_test = "37a1"; coeffs_test = (0,0,1,-1,0); N_test = 37
    X = 2000
    good_test = [p for p in primes if p <= X and N_test % p != 0]

    alpha_grid = [mpf(a)/10 for a in range(1, 41)]  # 0.1, 0.2, ..., 4.0
    results_alpha = []
    for alpha in alpha_grid:
        pia_a = pi * alpha
        S = sum(mpf(AP[label_test][p]) * expj(pia_a * d3(p)) * mp.log(p) / p
                for p in good_test)
        M = -S / mp.log(X)
        results_alpha.append((float(alpha), float(abs(M)), float(mp.re(M))))

    print(f"\n{'α':>6}    {'|M_log^Rf(37a1, 2000)|':>26}    {'Re':>12}")
    print("-"*60)
    for a, m_abs, m_re in results_alpha:
        marker = "  <-- α=3π/4 ≈ 2.356" if abs(a - float(3*pi/4)) < 0.06 else ""
        print(f"  {a:5.2f}     {m_abs:>22.6f}        {m_re:>10.4f}{marker}")

    print("\nHonest reading:")
    print("  (A) baseline M_log → rank classically — works.")
    print("  (B) magnitude of R_f-twisted: if monotone-in-rank → bridge candidate.")
    print("  (C) Re-projection: if it INHERITS the rank signal → real bridge candidate.")
    print("  (D) α-sweep: if α=3π/4 is at a peak/zero → α-canonical structure justified.")


if __name__ == "__main__":
    main()
