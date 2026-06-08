"""
BSD Bridge — Step 1: Hecke-eigenvalue correlation with R_f at α=3π/4

Wave 4 found:
  - R_f(3π/4, 1) ≈ -0.569 + 1.394i, nonzero
  - L(E, s) = R_f · M_E is a tautology (M_E absorbs everything)
  - Pinning α_BSD = (π/2)·α_RH doesn't transfer analytic content

New strategy: rather than a multiplicative L-function relation,
test a HECKE-EIGENVALUE correlation. The framework's R_f at α=3π/4
has Dirichlet coefficients r_n = e^{iπ·3π/4·D_3(n)}. If the framework
"sees" elliptic curves through Hecke eigenvalues, then for primes p
the correlation:
   ⟨a_p(E), r_p⟩  =  sum over primes (a_p · conj(r_p)) / p^s
should pick out curve-specific structure.

We compute three correlation statistics for each curve:
  (1) Σ_{p ≤ X} a_p(E) · cos(π·3π/4·D_3(p)) / p          (real part proj)
  (2) Σ_{p ≤ X} a_p(E) · e^{iπ·3π/4·D_3(p)} / p          (complex proj)
  (3) variance / norm  vs the rank

If (3) shows curves with higher rank have systematically larger
correlation magnitude → bridge exists.
"""

from mpmath import mp, mpf, mpc, pi, exp, sqrt, log, expj, cos as mcos, fabs

mp.dps = 40

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
            if leg == 1:
                cnt += 2
    return cnt

def a_p_long(a1, a2, a3, a4, a6, p):
    return p + 1 - count_points_long(a1, a2, a3, a4, a6, p)


CURVES = [
    ("11a1",   (0,-1,1,-10,-20), 11,   0),
    ("37a1",   (0, 0,1, -1,  0), 37,   1),
    ("389a1",  (0, 1,1, -2,  0), 389,  2),
    ("5077a1", (0, 0,1, -7,  6), 5077, 3),
]


def main():
    P_MAX = 500  # primes up to 500 — enough to see trends, fast
    primes = [p for p in range(2, P_MAX+1) if is_prime(p)]
    print(f"Using {len(primes)} primes up to {P_MAX}")

    pia = pi * ALPHA_BSD

    # r_p = e^{iπα D_3(p)} as a function of p
    r = {p: expj(pia * d3(p)) for p in primes}

    print("\nFirst 10 r_p values:")
    for p in primes[:10]:
        rp = r[p]
        print(f"  p={p:3d}  D_3(p)={d3(p)}  r_p = {mp.nstr(rp, 6)}  |r_p|=1")

    # The key test: for each curve, compute several correlation statistics
    print("\n" + "="*78)
    print("Hecke-eigenvalue correlations with R_f coefficients at α=3π/4")
    print("="*78)

    results = []
    for label, coeffs, N_curve, rank in CURVES:
        a1, a2, a3, a4, a6 = coeffs
        # exclude bad primes (those dividing the conductor)
        good_primes = [p for p in primes if N_curve % p != 0]
        a_p = {p: a_p_long(a1, a2, a3, a4, a6, p) for p in good_primes}

        # Stat 1: Sum a_p · cos(πα D_3(p)) / p
        S_cos = sum(mpf(a_p[p]) * mp.re(r[p]) / p for p in good_primes)
        # Stat 2: Sum a_p · r_p / p (complex)
        S_cplx = sum(mpf(a_p[p]) * r[p] / p for p in good_primes)
        # Stat 3: Sum a_p / p (Lang-Trotter / sato-Tate baseline)
        S_baseline = sum(mpf(a_p[p]) / p for p in good_primes)
        # Stat 4: weighted log: Σ a_p · r_p · log(p) / p
        S_logweighted = sum(mpf(a_p[p]) * r[p] * mp.log(p) / p for p in good_primes)
        # Stat 5: norm = Σ a_p² / p²  (variance scale)
        S_norm = sum(mpf(a_p[p])**2 / mpf(p)**2 for p in good_primes)

        results.append((label, rank, S_cos, S_cplx, S_baseline, S_logweighted, S_norm))

    print(f"\n{'curve':10}{'rank':>5} | {'Σa_p·Re(r_p)/p':>20} | {'|Σa_p·r_p/p|':>15} | "
          f"{'arg(Σ)':>10} | {'Σa_p/p':>15} | {'Σa²/p²':>12}")
    print("-"*112)
    for label, rank, sc, scx, sb, slw, sn in results:
        print(f"{label:10}{rank:>5} | {mp.nstr(sc, 8):>20} | {mp.nstr(abs(scx), 8):>15} | "
              f"{mp.nstr(mp.arg(scx), 6):>10} | {mp.nstr(sb, 8):>15} | {mp.nstr(sn, 6):>12}")

    print("\nHonest reading:")
    print("  - If the |Σ a_p · r_p / p| column tracks rank monotonically: bridge candidate.")
    print("  - If Σ a_p · Re(r_p) / p has a sign/magnitude tracking rank: real-projection bridge.")
    print("  - If Σ a_p/p baseline already tracks rank, R_f weighting is just noise on top.")
    print("  - The classical statistic Σ a_p log(p)/p ~ -rank * log(N) for nice curves;")
    print("    we compare its R_f-twisted version.")


if __name__ == "__main__":
    main()
