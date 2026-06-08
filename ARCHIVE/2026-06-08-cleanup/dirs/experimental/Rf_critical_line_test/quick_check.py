"""
QUICK CHECK of the manuscript Ch 9 line 369 claim:
   π/10 ?= (1/2) ∫_0^1 R_f(√2, 1/2 + ix) dx

R_f(α, s) = Σ_{n=1}^∞ e^(iπα·D_3(n)) / n^s

Use only N=500 first to get a rough answer fast, then refine if it looks right.
"""
from mpmath import mp, mpc, mpf, exp, log, pi, sqrt, quad, nstr
import sys

mp.dps = 30

def d3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

# Precompute D_3 values
def get_D3_table(N):
    return [d3(n) for n in range(N + 1)]

def Rf_partial(alpha, s, N, d3_table):
    """R_f(α, s) up to N terms — Dirichlet partial sum."""
    total = mpc(0)
    for n in range(1, N + 1):
        phase = exp(mpc(0, pi * alpha * d3_table[n]))
        total += phase / mpc(n) ** s
    return total

def main():
    sqrt2 = sqrt(2)
    pi_over_10 = pi / 10
    half = mpf("0.5")

    N_test = 500  # quick first pass
    print(f"Precision: {mp.dps} digits, N = {N_test}")
    print(f"Target π/10 = {nstr(pi_over_10, 15)}")
    sys.stdout.flush()

    d3_table = get_D3_table(N_test)

    # Integrand: R_f(√2, 1/2 + ix) at fixed x values to see shape
    print("\nValues of R_f(√2, 1/2 + ix) along the critical line:")
    for x in [mpf(0), mpf("0.1"), mpf("0.25"), mpf("0.5"), mpf("0.75"), mpf("0.9"), mpf(1)]:
        s = mpc(half, x)
        val = Rf_partial(sqrt2, s, N_test, d3_table)
        print(f"  x={float(x):.2f}: R_f = {nstr(val, 10)}")
        sys.stdout.flush()

    # Compute the integral via Gauss-Legendre quadrature
    print("\nComputing (1/2) ∫_0^1 R_f(√2, 1/2 + ix) dx ...")
    sys.stdout.flush()

    def integrand(x):
        return Rf_partial(sqrt2, mpc(half, x), N_test, d3_table)

    integral = quad(integrand, [0, 1])
    half_integral = integral / 2
    print(f"\nResult: {nstr(half_integral, 20)}")
    print(f"Target: {nstr(mpc(pi_over_10, 0), 20)}")
    print(f"|Re(result) - π/10| = {nstr(abs(half_integral.real - pi_over_10), 6)}")
    print(f"|Im(result)|         = {nstr(abs(half_integral.imag), 6)}")
    sys.stdout.flush()

    # Try larger N if the first looks promising or different
    for N in [2000, 5000]:
        print(f"\n--- Refining at N = {N} ---")
        sys.stdout.flush()
        d3t = get_D3_table(N)
        def integ(x):
            return Rf_partial(sqrt2, mpc(half, x), N, d3t)
        ival = quad(integ, [0, 1]) / 2
        print(f"  result = {nstr(ival, 18)}")
        print(f"  |Re - π/10| = {nstr(abs(ival.real - pi_over_10), 6)}")
        print(f"  |Im|        = {nstr(abs(ival.imag), 6)}")
        sys.stdout.flush()

if __name__ == "__main__":
    main()
