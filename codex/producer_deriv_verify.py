#!/usr/bin/env python3
"""THE decisive measurement: do the derivative constants let a higher-order
rule actually beat O(h)?

Classical remainders on [0, 3/2] with N panels, h = (3/2)/N:
  trapezoid : |err| <= (b-a) h^2 /12  * max|g''|   = 0.28125  * M2 / N^2
  Simpson   : |err| <= (b-a) h^4 /180 * max|g''''| = 0.0421875 * M4 / N^4

Risk: g = (exp(u/2)+1) omega_3(exp u) cos(t u/2) carries t/2 per
differentiation, so M4 ~ t^4/16 -- at t=14 that is ~2900. Does the h^4/180
gain beat it? Measure, do not guess.
"""
from mpmath import mp, mpf, exp, cos, pi, diff

mp.dps = 40
NTERM = 3
omega3 = lambda x: sum(exp(-pi * n ** 2 * x) for n in range(1, NTERM + 1))


def g(u, t):
    return (exp(u / 2) + 1) * omega3(exp(u)) * cos(mpf(t) * u / 2)


def maxabs_deriv(order, t, lo=mpf(0), hi=mpf(3) / 2, n=300):
    best = mpf(0)
    for i in range(n + 1):
        u = lo + (hi - lo) * mpf(i) / n
        v = abs(diff(lambda z: g(z, t), u, order))
        if v > best:
            best = v
    return best


print("=" * 86)
print("measured derivative maxima over u in [0, 3/2]")
print("%-8s %-16s %-16s %-16s" % ("t", "max|g|", "max|g''|", "max|g''''|"))
M = {}
for t in [mpf(51) / 8, mpf(13), mpf("14.5")]:
    m0 = maxabs_deriv(0, t)
    m2 = maxabs_deriv(2, t)
    m4 = maxabs_deriv(4, t)
    M[str(t)] = (m0, m2, m4)
    print("%-8s %-16.6e %-16.6e %-16.6e" % (str(t), float(m0), float(m2), float(m4)))

print()
print("=" * 86)
print("panels needed to hit the Gate-1 budget, with REAL constants")
print("  (O(h) row uses the measured C1 = 0.1858 : N = C1/B)")
print()
print("%-10s %-12s %-14s %-14s %-14s" % ("t", "budget B", "O(h) now", "trapezoid", "Simpson"))
C1 = mpf("0.1858")
for t, B in [(mpf(13), mpf("1.407e-5")), (mpf("14.5"), mpf("1.877e-6"))]:
    m0, m2, m4 = M[str(t)]
    n1 = C1 / B
    n2 = (mpf("0.28125") * m2 / B) ** mpf("0.5")
    n4 = (mpf("0.0421875") * m4 / B) ** mpf("0.25")
    print("%-10s %-12.3e %-14.0f %-14.0f %-14.0f"
          % (str(t), float(B), float(n1), float(n2), float(n4)))

print()
print("=" * 86)
print("VERDICT on the risk")
for t, B in [(mpf(13), mpf("1.407e-5")), (mpf("14.5"), mpf("1.877e-6"))]:
    m0, m2, m4 = M[str(t)]
    n1 = float(C1 / B)
    n2 = float((mpf("0.28125") * m2 / B) ** mpf("0.5"))
    n4 = float((mpf("0.0421875") * m4 / B) ** mpf("0.25"))
    print("  t = %-6s : trapezoid %.0fx fewer panels, Simpson %.0fx fewer"
          % (str(t), n1 / n2, n1 / n4))
print()
print("  at ~153 Lean lines per panel, per-box line counts:")
for t, B in [(mpf(13), mpf("1.407e-5")), (mpf("14.5"), mpf("1.877e-6"))]:
    m0, m2, m4 = M[str(t)]
    n1 = float(C1 / B)
    n2 = float((mpf("0.28125") * m2 / B) ** mpf("0.5"))
    n4 = float((mpf("0.0421875") * m4 / B) ** mpf("0.25"))
    print("    t = %-6s  O(h) %.2fM   trapezoid %.0fk   Simpson %.0fk"
          % (str(t), n1 * 153 / 1e6, n2 * 153 / 1e3, n4 * 153 / 1e3))
print()
print("  the t^4 growth in M4, for the record:")
for t in [mpf(51) / 8, mpf(13), mpf("14.5")]:
    print("    t = %-8s M4 = %.4e   (t^4/16 = %.1f)"
          % (str(t), float(M[str(t)][2]), float(t ** 4 / 16)))
