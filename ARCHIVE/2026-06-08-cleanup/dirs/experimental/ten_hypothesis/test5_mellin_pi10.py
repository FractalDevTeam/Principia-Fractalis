"""
Test 5: Direct test — what functions g on (0, inf) satisfy
    integral_0^inf g(x) dx/x = pi/10
(Haar integral on R_+ under multiplication.)

This is the Mellin transform M[g](0) = pi/10.

We list/check natural candidate functions g such that this integral evaluates to pi/10.
We want functions that are NATURAL — single-resonance, single-period, lattice-related.
"""

import numpy as np
from mpmath import mp, mpf, pi, sqrt, sin, cos, exp, log, quad, mpc, atan, gamma

mp.dps = 40

def main():
    print("=" * 70)
    print("TEST 5: functions g on R_+ with int_0^inf g(x) dx/x = pi/10")
    print("=" * 70)
    print()
    pi10 = pi / 10
    print(f"Target: pi/10 = {pi10}")
    print()

    candidates = []

    # ----- (A) 1/(x^a + 1) family -----
    # int_0^inf x^{s-1} / (x^a + 1) dx = (pi/a) / sin(pi s/a)
    # At s = 1 (i.e. dx, not dx/x): (pi/a) / sin(pi/a)
    # For dx/x measure (s=0), this is divergent. So shift:
    # int_0^inf x^{a-1}/(x^a + 1) * dx/x = int_0^inf 1/(x^a + 1) * x^{a-2} dx
    # Better: use g(x) = x/(x^a + 1) * dx/x family = int x/(x^a+1) dx/x = int 1/(x^a+1) dx
    # This has value pi/a / sin(pi/a). For this to equal pi/10:
    # 1/(a sin(pi/a)) = 1/10  ->  a sin(pi/a) = 10
    # Solve numerically:
    from scipy.optimize import brentq
    def f(a): return a * np.sin(np.pi / a) - 10
    # f(a) is monotonic in a for a large; a*sin(pi/a) -> pi as a-> inf
    # So this never reaches 10. CONFIRMED: no a gives int 1/(x^a+1) dx = pi/10.
    print("(A) int_0^inf x/(x^a + 1) dx/x = pi/(a sin(pi/a))")
    for a in [2, 3, 5, 10, 20]:
        val = pi / (a * sin(pi / a))
        print(f"    a={a:>3d}: value = {val:.6f}    target pi/10 = {float(pi10):.6f}")
    print("    -> No 'a' gives pi/10; a*sin(pi/a) -> pi < 10.")
    print()

    # ----- (B) Lorentzian: g(x) = 1/(1 + log(x)^2 * c) -----
    # int_0^inf dx/x / (1 + c log^2 x) = (1/sqrt(c)) * pi
    # = pi/10 requires c = 100, so c=100, i.e. g(x) = 1/(1 + 100 log^2 x).
    print("(B) Cauchy/Lorentzian: g(x) = 1/(1 + c log(x)^2)")
    print("    int_0^inf g(x) dx/x = pi / sqrt(c)")
    print(f"    -> pi/10 requires c = 100. g(x) = 1/(1 + 100 log(x)^2).")
    print("    This is NATURAL: it's a Cauchy distribution in log-coords with FWHM = 1/5.")
    val = quad(lambda x: 1 / (x * (1 + 100 * log(x) ** 2)), [0, 1, 10, mp.inf])
    print(f"    Numerical: {val}    target {pi10}")
    print()

    # ----- (C) Gaussian-on-log: g(x) = exp(-c log(x)^2) -----
    # int_0^inf exp(-c log^2 x) dx/x = sqrt(pi/c)
    # = pi/10 requires sqrt(pi/c) = pi/10 -> c = 100/pi
    print("(C) Gaussian in log-coords: g(x) = exp(-c log(x)^2)")
    print(f"    int = sqrt(pi/c) = pi/10 requires c = 100/pi = {100/float(pi):.4f}")
    c = 100 / pi
    val = quad(lambda x: exp(-c * log(x) ** 2) / x, [0, 1, mp.inf])
    print(f"    Numerical: {val}    target {pi10}")
    print()

    # ----- (D) Rectangular window in log: g(x) = 1 if x in [a,b], 0 else -----
    # int = log(b/a) = pi/10 requires b/a = exp(pi/10) ~ 1.3691
    print("(D) Log-rectangular: g(x) = 1 if x in [a, b]")
    print(f"    int = log(b/a) = pi/10 -> b/a = exp(pi/10) = {float(exp(pi10)):.6f}")
    print(f"    NOT NATURAL: requires irrational ratio.")
    print()

    # ----- (E) sin(pi log(x) / 10) / log(x) ? -----
    print("(E) sinc in log: g(x) = sin(a log(x))/log(x), with measure dx/x")
    print("    int_{-inf}^inf sin(a u)/u du = pi for a > 0 (with u = log(x))")
    print("    So int g(x) dx/x = pi for ANY a > 0. NOT pi/10.")
    print("    To get pi/10, would need to scale: g(x) = sin(log(x)) / (10 log(x))")
    val = quad(lambda x: sin(log(x)) / (10 * log(x) * x), [0, 0.5, 1, 2, mp.inf])
    print(f"    Numerical: {val}    target {pi10}")
    print()

    # ----- (F) Mellin inverse of pi/10 at s=0 -----
    # If M[g](s) = pi/10 for all s, then g(x) = (pi/10) * delta(log x) by Mellin inversion.
    # i.e. g(x) = (pi/10) at x=1, 0 else (a delta function).
    print("(F) Mellin-constant: M[g](s) = pi/10 -> g(x) = (pi/10) delta(log x)")
    print("    Pathological; only natural if 'pi/10' is the amplitude of a delta-resonance at x=1.")
    print()

    # ----- (G) What about an integral over a finite domain? -----
    # int_1^{exp(pi/10)} dx/x = pi/10
    # int_0^{tan(pi/10)} dx/(1+x^2) = pi/10
    # arctan-based: arctan(tan(pi/10)) = pi/10.
    print("(G) Arctan: int_0^{tan(pi/10)} dx/(1+x^2) = pi/10")
    print(f"    tan(pi/10) = {float(np.tan(np.pi/10)):.6f}")
    print(f"    sqrt(1 - 2/sqrt(5)) = {float(sqrt(1 - 2/sqrt(5))):.6f}  -- is this tan(pi/10)?")
    # tan(pi/10) has closed form: sqrt(5 - 2*sqrt(5))/... actually
    # tan(pi/10) = sqrt(1 - 2/sqrt(5)) is wrong. Real formula:
    # tan(18 deg) = sqrt(5 - 2 sqrt(5)) / ... let's just check numerically
    print(f"    tan(pi/10) numerically = {float(np.tan(np.pi/10)):.10f}")
    print()

    # ----- The clean takeaway -----
    print("CLEAN SUMMARY:")
    print("Natural g with int g(x) dx/x = pi/10:")
    print("  (B) Cauchy in log-coords with scale 1/10  -- WIDTH = 1/10")
    print("  (C) Gaussian in log-coords with variance ~ pi/(2*100) = pi/200")
    print("  (G) Lorentzian truncation at tan(pi/10) -- inverse-tangent")
    print("  (E) sinc in log with scaling 1/10")
    print()
    print("ALL of these involve a SCALE PARAMETER OF 1/10 — i.e. they encode '10' explicitly.")
    print("None of them produce '10' from a deeper structure; they assume it.")
    print()
    print("VERDICT (TEST 5): the Mellin route to pi/10 requires either:")
    print("  (i) Explicit dialation parameter 1/10 (Cauchy/Gaussian/Lorentzian in log)")
    print("  (ii) Pentagonal/5-fold structure via arctan(tan(pi/10))")
    print("Neither is more natural than the others — '10' must come from elsewhere.")

if __name__ == "__main__":
    main()
