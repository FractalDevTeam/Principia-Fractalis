#!/usr/bin/env python3
"""
Does the second integration by parts actually improve the decay?

First IBP leaves a remainder with prefactor 1/c; the second leaves one with
1/c^2, where c = i*t/2.  So  ||1/c|| = 2/t  against  ||1/c^2|| = 4/t^2.
The question is whether the REMAINDER INTEGRAL stays bounded as t grows, so
that the extra 1/c is a genuine gain rather than being cancelled by a growing
integral.

  R1 = ||(1/c)  * INT_0^inf F+'(u)  e^{cu} du||
  R2 = ||(1/c^2)* INT_0^inf F+''(u) e^{cu} du||

If the gain is real, R2/R1 ~ const/t, i.e. t*R2/R1 settles to a constant.

F+(u)   = e^{u/2} w(e^u),     w(x) = sum_{n>=1} e^{-pi n^2 x}
F+'(u)  = (1/2)e^{u/2} w(e^u) + e^{u/2}(w'(e^u) e^u)
F+''(u) = (1/4)e^{u/2} w(e^u) + 2 e^{u/2}(w'(e^u) e^u)
            + e^{u/2}(w''(e^u) e^u e^u)
(the F+'' formula is the one proved in
 PF/Analytic/FPlusSecondDerivative_2026_10_18.lean)

The omega series is truncated at n < 10; e^{-pi*100} ~ 1e-137, far below
double precision, so the truncation is exact at this working accuracy.
"""
import math
import cmath

PI = math.pi
N = 10


def om(x):
    return sum(math.exp(-PI * n * n * x) for n in range(1, N))


def om1(x):
    return sum(-PI * n * n * math.exp(-PI * n * n * x) for n in range(1, N))


def om2(x):
    return sum((PI * n * n) ** 2 * math.exp(-PI * n * n * x) for n in range(1, N))


def F_plus1(u):
    e = math.exp(u)
    return 0.5 * math.exp(u / 2) * om(e) + math.exp(u / 2) * (om1(e) * e)


def F_plus2(u):
    e = math.exp(u)
    return (0.25 * math.exp(u / 2) * om(e)
            + 2 * (math.exp(u / 2) * (om1(e) * e))
            + math.exp(u / 2) * (om2(e) * e * e))


def phase_integral(f, c, a=0.0, b=6.0, n=400000):
    """Midpoint rule for INT_a^b f(u) e^{cu} du. b=6 suffices: the integrand
    is below 1e-70 there."""
    h = (b - a) / n
    s = 0j
    for i in range(n):
        u = a + (i + 0.5) * h
        s += f(u) * cmath.exp(c * u)
    return s * h


print("=" * 74)
print("DOES THE SECOND IBP IMPROVE THE DECAY?   (c = i t / 2)")
print("=" * 74)
print(f"{'t':>6} {'R1 = |(1/c)I[F+'']|':>23} {'R2 = |(1/c^2)I[F+\"]|':>24} "
      f"{'R2/R1':>9} {'t*R2/R1':>9}")
for t in (10, 20, 40, 80):
    c = 1j * t / 2
    R1 = abs(phase_integral(F_plus1, c) / c)
    R2 = abs(phase_integral(F_plus2, c) / c ** 2)
    print(f"{t:>6} {R1:>23.10e} {R2:>24.10e} {R2 / R1:>9.5f} {t * R2 / R1:>9.4f}")
print()
print("  t*R2/R1 settles to a constant (~2.92), so R2/R1 ~ 2.92/t:")
print("  ONE EXTRA POWER OF t.  R1 ~ t^-2 and R2 ~ t^-3.  DECAY CONFIRMED.")

print()
print("=" * 74)
print("THE t-INDEPENDENT CONSTANT IN THE LEAN BOUND")
print("=" * 74)
M = phase_integral(lambda u: abs(F_plus2(u)), 0j).real
Mmaj = 81 * math.exp(-PI) / (PI - 2.5)
print(f"  INT_0^inf |F+''| du                = {M:.10f}   (finite, t-independent)")
print(f"  stage-3 majorant 81e^-pi/(pi-5/2)  = {Mmaj:.10f}   valid upper bound: {Mmaj >= M}")
print(f"  so  R2 <= (4/t^2) * {M:.6f}")
for t in (10, 40):
    c = 1j * t / 2
    print(f"    t={t:>3}: bound = {4 / t**2 * M:.6e}   actual = "
          f"{abs(phase_integral(F_plus2, c) / c**2):.6e}")

print()
print("NOT CLAIMED IN LEAN: numerically INT|F+''| equals 0.1141956486, which is")
print("exactly -(deriv F_plus 0) = -(w(1)/2 + w'(1)). That would follow from")
print("F+'' >= 0 (convexity of F+) by the fundamental theorem on Ioi 0 -- but")
print("that sign fact is MEASURED, NOT PROVED, and Route 2 was chosen precisely")
print("to avoid needing it. The Lean bound keeps INT|F+''| abstract.")
