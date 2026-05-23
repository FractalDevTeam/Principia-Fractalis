"""
Test 6: Eisenstein series special values.

E_2(tau) = 1 - 24 sum sigma_1(n) q^n        (quasi-modular, weight 2)
E_4(tau) = 1 + 240 sum sigma_3(n) q^n       (weight 4)
E_6(tau) = 1 - 504 sum sigma_5(n) q^n       (weight 6)

Constants 24, 240, 504 are: 24 = 2*12, 240 = 2*120 = 2 * 5!, 504 = 2^3 * 63 = 2^3 * 7 * 9
None obviously involve 10.

Special values at lattice points:
  E_2(i) = 3 / pi  (after holomorphic projection)
  E_4(i) = 3 Gamma(1/4)^8 / (2 pi)^6
  E_6(i) = 0 (vanishing at lemniscate)

Look for pi/10 in any normalized special value.
"""

import numpy as np
from mpmath import mp, mpf, pi, sqrt, exp, log, gamma, mpc, eisenstein

mp.dps = 50

def E_k(k, tau, n_terms=200):
    """Eisenstein series E_k(tau) via q-expansion. tau = x + i*y."""
    q = exp(2 * pi * mpc(0, 1) * tau)
    if k == 2:
        coeff = -24
        sigma_fn = lambda n: sum(d for d in range(1, n+1) if n % d == 0)
    elif k == 4:
        coeff = 240
        sigma_fn = lambda n: sum(d**3 for d in range(1, n+1) if n % d == 0)
    elif k == 6:
        coeff = -504
        sigma_fn = lambda n: sum(d**5 for d in range(1, n+1) if n % d == 0)
    elif k == 8:
        coeff = 480
        sigma_fn = lambda n: sum(d**7 for d in range(1, n+1) if n % d == 0)
    elif k == 10:
        coeff = -264
        sigma_fn = lambda n: sum(d**9 for d in range(1, n+1) if n % d == 0)
    else:
        raise ValueError("k not supported")

    s = mpf(1)
    qn = mpc(1)
    for n in range(1, n_terms):
        qn = qn * q
        s = s + coeff * sigma_fn(n) * qn
    return s

def main():
    print("=" * 70)
    print("TEST 6: Eisenstein series — does any normalized version give pi/10?")
    print("=" * 70)
    print()
    pi10 = pi / 10
    print(f"Target: pi/10 = {pi10}")
    print()

    # Special values at tau = i
    tau = mpc(0, 1)
    for k in [2, 4, 6, 8, 10]:
        try:
            val = E_k(k, tau, n_terms=300)
            print(f"E_{k}(i) ~ {val}")
            print(f"  E_{k}(i) / pi = {val / pi}")
            print(f"  pi / E_{k}(i) = {pi / val if abs(val) > 1e-20 else 'inf'}")
            print(f"  E_{k}(i) / (pi/10) = {val / pi10}")
            print()
        except Exception as e:
            print(f"E_{k}(i): error {e}")

    # E_10 has coefficient -264; note 264 = 8 * 33 = 24 * 11. Not 10.

    # Theta-relations: theta_2(0,q)^4 + theta_4(0,q)^4 = theta_3(0,q)^4
    # Constants 240, 504, 480, 264 are 2*B_k/k * (some normalization).
    # B_2 = 1/6, B_4 = -1/30, B_6 = 1/42, B_8 = -1/30, B_10 = 5/66
    # B_10 = 5/66 -- contains a 5! and 66 = 6*11.
    print("Bernoulli numerators of B_{2k}:")
    print("  B_2 = 1/6, B_4 = -1/30, B_6 = 1/42, B_8 = -1/30, B_10 = 5/66")
    print("  Denominator 30 appears for B_4 and B_8. 30 = 3 * 10.")
    print()
    print("Note 1: B_4 = -1/30. denominator 30 = 3 * 10.")
    print("zeta(4) = pi^4 / 90 = pi^4 / (3 * 30). Not pi/10.")
    print()

    # The Eisenstein E_4 coefficient -240 = -2 * 120 = -2 * 5!
    # E_8 coefficient 480 = 2 * 240
    # Ratio 240/24 = 10!
    print("CRITICAL OBSERVATION:")
    print("  E_2 coefficient 24, E_4 coefficient 240. RATIO = 10.")
    print("  This is exactly the factor 10 we want.")
    print()
    print("  Reason: 240/24 = 10 comes from -2k/B_{2k} normalization.")
    print("  For E_2: 2*2/B_2 = 4/(1/6) = 24")
    print("  For E_4: 2*4/B_4 = 8/(-1/30) = -240")
    print("  Ratio = (8 * 6) / (4 * 30) * sign = -10")
    print()
    print("  However, this is a RATIO of coefficients, not pi/10.")
    print("  E_k(i) values are transcendental and do not give pi/10 cleanly.")
    print()
    print("VERDICT (TEST 6):")
    print("  The factor 10 DOES appear in modular form theory as the ratio E_4/E_2 coefficients,")
    print("  arising from Bernoulli numbers B_2 / B_4 = (1/6)/(1/30) = 5, doubled for index.")
    print("  But pi/10 does NOT emerge as a special value of Eisenstein series at canonical points.")
    print()
    print("  Suggestive but inconclusive: B_4 = -1/30 means the relation -1/(30) involves both 3 and 10.")
    print("  In the language of zeta(4) = pi^4/90, the '10' appears as 90 = 9 * 10.")

if __name__ == "__main__":
    main()
