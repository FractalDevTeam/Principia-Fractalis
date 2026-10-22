#!/usr/bin/env python3
"""The 91a1 doubling orbit in x-coordinates, exactly, and where its height
clears the duplication constant.

Phi and Psi are transcribed from PF/DuplicationBezoutUniversal_r174.lean:59,62
verbatim (two lines each), and nh from r176:61. The curve is 91a1,
y^2 + y = x^3 + x, so b = (0, 2, 1, -1) -- the values already PROVED in
PF/E91a1RankOne_2026_10_21.lean as b2_eq .. b8_eq.

Base point P = (0, 0): 0^2 + 0 = 0^3 + 0. X(P) = 0.
"""
from fractions import Fraction as F

B2, B4, B6, B8 = 0, 2, 1, -1


def Phi(X, Y):
    return X**4 - X**2 * Y**2 * B4 - 2 * X * Y**3 * B6 - Y**4 * B8


def Psi(X, Y):
    return 4 * X**3 * Y + X**2 * Y**2 * B2 + 2 * X * Y**3 * B4 + Y**4 * B6


def dblQ(x):
    return F(Phi(x.numerator, x.denominator), Psi(x.numerator, x.denominator))


def nh(x):
    return max(abs(x.numerator), x.denominator)


def Disc():
    return -B2**2 * B8 + 9 * B2 * B4 * B6 - 8 * B4**3 - 27 * B6**2


print("Disc 0 2 1 (-1) = %d   (the curve's discriminant; must be nonzero)"
      % Disc())
print("Psi 0 2 1 X Y   = 4X^3Y + 4XY^3 + Y^4 = Y(4X^3 + 4XY^2 + Y^3)")
print("  -> at Y = x.den, the bracket is the 2-torsion cubic 4p^3+4pq^2+q^3,")
print("     which no_int_solution proves is never 0. So Psi never vanishes")
print("     on a rational x, and the orbit never hits the identity.")
print("")

x = F(0)
print("%3s  %-46s %s" % ("n", "x(2^n P)", "nh"))
rows = []
for n in range(9):
    h = nh(x)
    s = str(x)
    if len(s) > 46:
        s = s[:21] + "..." + s[-22:]
    print("%3d  %-46s %d" % (n, s, h))
    rows.append((n, h))
    x = dblQ(x)

print("")
# the driver needs kappa < naiveHeight (f 0) for the SHIFTED sequence
for kappa in (24388, 100000, 1000000):
    k = next((n for n, h in rows if h > kappa), None)
    print("first n with nh > %-8d : n = %s" % (kappa, k))
print("")
print("growth check (the driver needs nh(n)^4 <= kappa * nh(n+1)):")
for n in range(len(rows) - 1):
    hn, hn1 = rows[n][1], rows[n + 1][1]
    need = F(hn**4, hn1) if hn1 else None
    print("  n=%d: nh^4/nh(n+1) = %s" % (n, float(need) if need else "-"))
