#!/usr/bin/env python3
"""
Checks for PF/Analytic/Lambda0IBP2Combined_2026_10_18.lean.

  (1) The combined second-order identity
        Lambda_0(1+it) = (1/c^2) * [ (w(1)/2 + 2 w'(1)) + I+ + I- ],  c = i t/2
      against mpmath's Lambda_0.  I+- = INT_{Ioi 0} F+-'' e^{+-icu} du.

  (2) The boundary constant w(1)/2 + 2 w'(1) = -1/4, which is the theta
      functional equation differentiated at x = 1:
        theta(x) = 1 + 2 w(x),  theta(1/x) = sqrt(x) theta(x)
        => theta'(1) = -theta(1)/4  =>  2 w'(1) = -1/4 - w(1)/2.
      This is MEASURED here and NOT proved in Lean: the tree has no
      differentiated theta functional equation. With it, the identity becomes
        Lambda_0(1+it) = 1/t^2 - (4/t^2)(I+ + I-),
      pinning the leading coefficient exactly at 1 rather than O(t^-2).

The omega series is truncated at n < 10 (e^{-pi*100} ~ 1e-137).
"""
import math
import cmath
import mpmath as mp

PI = math.pi
N = 10
mp.mp.dps = 25


def om(x):
    return sum(math.exp(-PI * n * n * x) for n in range(1, N))


def om1(x):
    return sum(-PI * n * n * math.exp(-PI * n * n * x) for n in range(1, N))


def om2(x):
    return sum((PI * n * n) ** 2 * math.exp(-PI * n * n * x) for n in range(1, N))


def F_plus2(u):
    e = math.exp(u)
    return (0.25 * math.exp(u / 2) * om(e)
            + 2 * (math.exp(u / 2) * (om1(e) * e))
            + math.exp(u / 2) * (om2(e) * e * e))


def F_minus2(u):
    e = math.exp(u)
    return om2(e) * e * e + om1(e) * e


def phase_integral(f, c, b=6.0, n=400000):
    h = b / n
    s = 0j
    for i in range(n):
        u = (i + 0.5) * h
        s += f(u) * cmath.exp(c * u)
    return s * h


def Lambda0(t):
    s = mp.mpc(1, t)
    return (mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)
            + 1 / s + 1 / (1 - s))


A = om(1) / 2 + 2 * om1(1)

print("=" * 74)
print("(2) THE COMBINED SECOND-ORDER BOUNDARY CONSTANT")
print("=" * 74)
print(f"  w(1)      = {om(1):.16f}")
print(f"  w'(1)     = {om1(1):.16f}")
print(f"  w(1)/2 + 2w'(1) = {A:.16f}")
print(f"  -1/4            = {-0.25:.16f}      |difference| = {abs(A + 0.25):.2e}")
print("  => exactly -1/4 to machine precision. NOT proved in Lean (needs the")
print("     differentiated theta functional equation, absent from the tree).")

print()
print("=" * 74)
print("(1) THE COMBINED IDENTITY, against mpmath")
print("=" * 74)
print(f"  {'t':>5} {'|Lambda_0 - RHS|':>18}   {'Lambda_0':>44}")
for t in (10.0, 20.0, 40.0):
    c = 1j * t / 2
    Ip = phase_integral(F_plus2, c)
    Im = phase_integral(F_minus2, -c)
    rhs = (A + Ip + Im) / c ** 2
    lhs = complex(Lambda0(t))
    print(f"  {t:>5.0f} {abs(lhs - rhs):>18.3e}   {lhs!r:>44}")
print()
print("  The two FIRST-order boundary terms cancel (both w(1), opposite phases);")
print("  only the second-order constant survives. 1/c^2 = -4/t^2 exactly.")

print()
print("=" * 74)
print("WHAT THE -1/4 WOULD BUY:  Lambda_0(1+it) = 1/t^2 - (4/t^2)(I+ + I-)")
print("=" * 74)
for t in (10.0, 40.0):
    c = 1j * t / 2
    Ip = phase_integral(F_plus2, c)
    Im = phase_integral(F_minus2, -c)
    sharp = 1 / t ** 2 - 4 / t ** 2 * (Ip + Im)
    print(f"  t={t:>5.0f}: sharp form = {sharp!r}")
    print(f"           Lambda_0   = {complex(Lambda0(t))!r}")
