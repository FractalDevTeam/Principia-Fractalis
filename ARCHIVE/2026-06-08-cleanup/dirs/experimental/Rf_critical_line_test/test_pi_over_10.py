"""
TEST: Manuscript Ch 9 line 369 claim:
   π/10 = (1/2) ∫_0^1 R_f(√2, 1/2 + ix) dx

where R_f(α, s) = Σ_{n=1}^∞ e^(iπα·D_3(n)) / n^s
and D_3(n) is the base-3 digital sum of n.

If this is TRUE numerically, then π/10 has a direct integral definition
in terms of R_f along the critical line. This is the framework's universal
scaling constant on a CONCRETE, COMPUTABLE basis.

If TRUE, then λ_0(α) = π/(10·α) would correspond to:
   λ_0(α) = (1/(2α)) ∫_0^1 R_f(α, 1/2 + ix) dx
which is testable for every α.
"""
from mpmath import mp, mpc, mpf, exp, log, pi, sqrt, quad
import time

mp.dps = 50  # 50 decimal digits

def d3(n):
    """Base-3 digital sum."""
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

def Rf(alpha, s, N=20000):
    """R_f(α, s) = Σ_{n=1}^N e^(iπα·D_3(n)) / n^s, truncated at N."""
    total = mpc(0)
    for n in range(1, N + 1):
        phase = exp(mpc(0, pi * alpha * d3(n)))
        total += phase / mpc(n) ** s
    return total

def integrate_Rf_along_critical(alpha, N=20000, quad_points=30):
    """Compute (1/2) ∫_0^1 R_f(α, 1/2 + ix) dx using Gauss-Legendre quadrature."""
    half = mpf("0.5")
    def integrand(x):
        return Rf(alpha, mpc(half, x), N=N)
    integral = quad(integrand, [0, 1])
    return integral / 2

def main():
    sqrt2 = sqrt(2)
    pi_over_10 = pi / 10
    print(f"Working precision: {mp.dps} decimal digits")
    print(f"Target: π/10 = {pi_over_10}")
    print()

    # Test the manuscript claim at α = √2
    print("=" * 60)
    print(f"TEST: π/10 ≟ (1/2) ∫_0^1 R_f(√2, 1/2 + ix) dx")
    print("=" * 60)
    t0 = time.time()
    for N in [1000, 5000, 20000]:
        result = integrate_Rf_along_critical(sqrt2, N=N)
        diff = abs(result - pi_over_10)
        print(f"N={N:5d}: result = {result}")
        print(f"         |result - π/10| = {diff}")
        print(f"         time = {time.time() - t0:.1f}s")
        t0 = time.time()
    print()

    # Try the predicted scaling λ_0(α) = π/(10·α) via the same integral
    print("=" * 60)
    print(f"TEST: λ_0(α) = (1/(2α)) ∫_0^1 R_f(α, 1/2 + ix) dx ≟ π/(10·α)")
    print("=" * 60)
    for alpha_name, alpha_val, target_name, target_val in [
        ("√2",     sqrt2,        "π/(10√2)", pi/(10*sqrt2)),
        ("3/2",    mpf("1.5"),   "π/15",     pi/15),
        ("2",      mpf("2"),     "π/20",     pi/20),
        ("1",      mpf("1"),     "π/10",     pi/10),
    ]:
        try:
            integral = integrate_Rf_along_critical(alpha_val, N=5000)
            lambda_0 = integral / alpha_val
            diff = abs(lambda_0 - target_val)
            ratio = lambda_0 / target_val if abs(target_val) > 0 else mpc(0)
            print(f"α={alpha_name:5s}: λ_0 = {lambda_0}")
            print(f"         target {target_name} = {target_val}")
            print(f"         |diff| = {diff},  ratio = {ratio}")
        except Exception as e:
            print(f"α={alpha_name}: ERROR {e}")
    print()

if __name__ == "__main__":
    main()
