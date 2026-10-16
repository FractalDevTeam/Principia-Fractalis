#!/usr/bin/env python3
"""Cost comparison for passing the Gate-2 ceiling at |t| = 6.886.

The scaffold hard-codes L = 1 and r = 1/16 and Mc_lb = 1/8. The ceiling
|t| <= 6.8863 is the ceiling FOR THAT TRIPLE, not for the method:

    L(t) = [ (1+2t) B + (t^2+t) B' ] / 2        (derivative bound on Re xi)
    gate 2 :  L * r < Mc_lb
    gate 1 :  Mc_lb <= Re xi(centre)

So with B = B' = 50/1727 (the EXISTING theorems) one can still march past
6.886 by letting L grow and shrinking r. Scenario A prices that.
Scenario B prices the same march with a decaying bound (new mathematics).
"""
from mpmath import mp, mpf, mpc, pi, gamma, zeta, power, diff, fabs

mp.dps = 30
UNIF = mpf(50) / 1727


def Lambda0(s):
    return power(pi, -s / 2) * gamma(s / 2) * zeta(s) + 1 / s + 1 / (1 - s)


L0 = lambda t: Lambda0(mpc(1, t))
re_xi = lambda t: (1 - mpf(t) ** 2 * L0(t).real - mpf(t) * L0(t).imag) / 2


def Lbound(t, B, Bp):
    t = mpf(t)
    return ((1 + 2 * t) * B + (t ** 2 + t) * Bp) / 2


def march(T, Bfun, Bpfun, label, start=mpf("6.886"), rcap=mpf("0.5"), safety=mpf("0.8")):
    """Greedy march: at each centre take Mc_lb = safety*Re xi(c), r = Mc_lb/L."""
    c, n, rows = start, 0, []
    while c < T and n < 100000:
        rx = re_xi(c)
        if rx <= 0:
            break
        Mc = safety * rx
        L = Lbound(c + mpf("0.05"), Bfun(c), Bpfun(c))   # evaluated near upper edge
        r = Mc / L
        if r > rcap:
            r = rcap
        if r < mpf("1e-6"):
            break
        if n < 6 or c > T - 1:
            rows.append((float(c), float(rx), float(L), float(r)))
        c = c + 2 * r
        n += 1
    return n, c, rows


print("=" * 86)
print("SCENARIO A -- EXISTING theorems only (B = B' = 50/1727), variable r and Mc_lb")
print("  no new mathematics: just stop hard-coding L = 1 and r = 1/16")
print()
print("  %-8s %-12s %-12s %-14s %-12s" % ("centre", "Re xi", "L(uniform)", "r attainable", "~1/r"))
for t in [7, 8, 9, 10, 11, 12, 13, 13.5]:
    rx = re_xi(t)
    if rx <= 0:
        continue
    L = Lbound(t, UNIF, UNIF)
    r = mpf("0.8") * rx / L
    print("  %-8s %-12.6f %-12.4f %-14.6f %-12.1f" % (t, float(rx), float(L), float(r), float(1 / r)))
print()
for T in [8, 10, 12, 13, 13.5, 13.9]:
    n, reached, _ = march(mpf(T), lambda c: UNIF, lambda c: UNIF, "A")
    print("  cover [6.886, %-5s] : %5d boxes   (reached %.4f)" % (T, n, float(reached)))

print()
print("=" * 86)
print("SCENARIO B -- with a DECAYING strip bound (the new mathematics)")
print("  model the attainable bound as the TRUE size times a 1.5x certification")
print("  slack: B(t) = 1.5|Lambda0(1+it)| , B'(t) = 1.5|Lambda0'(1+it)|")
L0p = lambda t: diff(Lambda0, mpc(1, t))
Bf = lambda c: mpf("1.5") * fabs(L0(c))
Bpf = lambda c: mpf("1.5") * fabs(L0p(c))
print()
print("  %-8s %-12s %-12s %-14s %-12s" % ("centre", "Re xi", "L(local)", "r attainable", "~1/r"))
for t in [7, 9, 11, 13, 13.5]:
    rx = re_xi(t)
    if rx <= 0:
        continue
    L = Lbound(t, Bf(t), Bpf(t))
    r = mpf("0.8") * rx / L
    print("  %-8s %-12.6f %-12.4f %-14.6f %-12.1f" % (t, float(rx), float(L), float(r), float(1 / r)))
print()
for T in [8, 10, 12, 13, 13.5, 13.9]:
    n, reached, _ = march(mpf(T), Bf, Bpf, "B")
    print("  cover [6.886, %-5s] : %5d boxes   (reached %.4f)" % (T, n, float(reached)))

print()
print("=" * 86)
print("THE HARD BOUNDARY (independent of either scenario)")
print("  Re xi(1+it) first vanishes at t = 13.9883806982 (this project's")
print("  established value). Past it Re xi < 0 and a POSITIVITY march is")
print("  not merely harder -- its conclusion is FALSE.")
for t in ["13.9", "13.98", "13.9883", "13.99", "14.1"]:
    print("    Re xi(1+i%-9s) = %+.3e" % (t, float(re_xi(mpf(t)))))
print()
print("  So the reachable target for ANY version of this march is t < 13.9884,")
print("  and the margin Re xi -> 0 there forces r -> 0: the box count diverges")
print("  as the endpoint is approached, in BOTH scenarios.")
