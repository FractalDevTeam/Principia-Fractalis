"""
TEST 5: Direct Mellin integrals giving pi/10

We look for natural functions g(x) such that:
  integral_0^inf g(x) dx/x = pi/10

Candidates:
  (a) g(x) = sin(pi*x/5) / x  --> Dirichlet-type
  (b) g(x) = 1/(1 + x^10)
  (c) g(x) = x^(s-1)/(1+x)^n  -- beta integrals
  (d) g(x) = x^a (1-x)^b  -- on [0,1]
  (e) g(x) = arctan or related
"""

from mpmath import mp, mpf, pi, quad, sin, cos, atan, exp, log, sqrt, sec, csc, tan, gamma, beta

mp.dps = 50

def main():
    print("=" * 70)
    print("TEST 5: Direct integrals giving pi/10")
    print("=" * 70)
    target = pi/10
    print(f"Target: pi/10 = {float(target):.20f}\n")

    # (a) integral_0^inf 1/(x^n + 1) dx = pi/(n sin(pi/n))
    # At n = 10: pi/(10 sin(pi/10)) — NOT pi/10. But it has factor pi/10!
    print("Candidate (a): integral 1/(x^n + 1) dx from 0 to inf = pi/(n sin(pi/n))")
    for n in [2, 5, 10, 20]:
        val = pi / (n * sin(pi/n))
        print(f"  n={n:2d}: {float(val):.15f}  (pi/n = {float(pi/n):.15f})")

    # The integral does NOT give pi/10 directly. To get pi/10 = pi/(n sin(pi/n)),
    # we'd need n sin(pi/n) = 10. Solve:
    print("\nSolve n sin(pi/n) = 10 for n:")
    # For large n, n sin(pi/n) ~ pi, so we need n sin(pi/n) = 10 > pi.
    # Not achievable for any real n > pi. No solution.

    # (b) Mellin transform of f(x) = 1/(1+x)^a at s gives B(s, a-s).
    # Beta integral: integral_0^1 x^(s-1) (1-x)^(t-1) dx = B(s,t) = Gamma(s)Gamma(t)/Gamma(s+t)
    # Look for B values = pi/10.
    print("\nCandidate (b): Beta integral B(s,t) = pi/10")
    print("  B(1/2, 5/2) =", float(beta(mpf(1)/2, mpf(5)/2)))  # = 3 pi/8
    print("  B(3/2, 9/2) =", float(beta(mpf(3)/2, mpf(9)/2)))  #
    print("  B(1/2, 9/2) =", float(beta(mpf(1)/2, mpf(9)/2)))  #
    # B(1/2, k+1/2) = pi (2k)!/(4^k (k!)^2 (2k+1))
    # Look for one that = pi/10:
    for k in range(0, 8):
        val = beta(mpf(1)/2, k + mpf(1)/2)
        print(f"  B(1/2, {k}+1/2) = {float(val):.15f}, ratio to pi/10 = {float(val/(pi/10)):.6f}")

    # (c) Arctan
    print("\nCandidate (c): arctan integrals")
    # integral_0^inf arctan(ax)/(x^2+1) dx -related
    # tan(pi/10) = sqrt(1 - 2/sqrt(5))
    val = atan(mpf(1)/3)  # = something close
    print(f"  arctan(1/3) = {float(val):.15f}")
    print(f"  pi/10 = {float(pi/10):.15f}")
    print(f"  arctan(tan(pi/10)) = pi/10 trivially. tan(pi/10) = {float(tan(pi/10)):.15f}")

    # (d) integral involving sin(pi/10) - this is a Q(zeta_20) algebraic number
    # sin(pi/10) = (sqrt(5)-1)/4 = (phi - 1)/2 where phi = golden ratio!
    # cos(pi/10) = sqrt(10 + 2 sqrt(5))/4
    print("\nKEY OBSERVATION: pi/10 connects to GOLDEN RATIO via")
    print(f"  sin(pi/10) = (sqrt(5)-1)/4 = (phi-1)/2 = 1/(2 phi) = {float((sqrt(5)-1)/4):.15f}")
    print(f"  Numerical sin(pi/10) = {float(sin(pi/10)):.15f}")
    print(f"  cos(pi/5) = phi/2 = {float((1+sqrt(5))/4):.15f}")
    print(f"  These are CYCLOTOMIC values from Q(zeta_20).")

    # (e) integral via residues: Pochhammer/digamma combinations
    # digamma values at fractional arguments give pi*cot(pi/n)
    # psi(1/10) - psi(9/10) = -pi cot(pi/10)
    from mpmath import digamma
    val = pi * (1/tan(pi/10))
    print(f"\n  pi * cot(pi/10) = {float(val):.10f}")
    print(f"  cot(pi/10) = sqrt(5 + 2 sqrt(5)) = {float(sqrt(5 + 2*sqrt(5))):.10f}")

    print()
    print("=" * 70)
    print("DEEP CONNECTION: pi/10 = pi/(2*5) ties to cyclotomic field Q(zeta_20)")
    print("=" * 70)
    print("If alpha_NP = phi + 1/4, and sin(pi/10) = 1/(2 phi), then")
    print("  pi/(10 * (phi + 1/4)) involves BOTH the cyclotomic 1/10 AND golden phi.")
    print("This is consistent with Principia's prediction that algebraic numbers from")
    print("the 4-basis appear in spectral targets. But the 10 itself remains unexplained")
    print("as a natural Lie/geometric structure.")
    print()
    print("The most likely structural source of '10' is:")
    print("  - Cyclotomic decagon (20-th roots of unity) ↔ icosahedral/pentagonal symmetry")
    print("  - This connects DIRECTLY to phi (golden ratio) via the dihedral D_10 group")

if __name__ == "__main__":
    main()
