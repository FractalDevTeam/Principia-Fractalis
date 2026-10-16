#!/usr/bin/env python3
"""What does a t-PARAMETRIC producer actually buy? Measure the 2-D cost.

A t-ranging producer must bound each panel's integrand range over
u in [a,b] AND t in [c-r, c+r] jointly. That widens every panel by the
t-variation. Total enclosure width then splits:

    W(N, r)  ~  C1 / N   +   C2 * r
                (u-part)     (t-part)

and must fit the Gate-1 budget B(c) = max allowed dR at centre c.
This measures C1 and C2 and prices the trade-off.
"""
from mpmath import mp, mpf, exp, cos, pi

mp.dps = 40
NTERM = 3
omega3 = lambda x: sum(exp(-pi * n ** 2 * x) for n in range(1, NTERM + 1))
g = lambda u, c: (exp(mpf(u) / 2) + 1) * omega3(exp(mpf(u))) * cos(mpf(c) * mpf(u) / 2)


def box_range(a, b, c, r, nu=60, nt=24):
    lo = hi = None
    for i in range(nu + 1):
        u = a + (b - a) * mpf(i) / nu
        for j in range(nt + 1):
            t = (c - r) + 2 * r * mpf(j) / nt if r > 0 else c
            v = g(u, t)
            if lo is None or v < lo:
                lo = v
            if hi is None or v > hi:
                hi = v
            if r == 0:
                break
    return lo, hi


def W(c, npan, r, U=mpf(3) / 2):
    h = U / npan
    tot = mpf(0)
    for k in range(npan):
        lo, hi = box_range(k * h, (k + 1) * h, c, r)
        tot += h * (hi - lo)
    return tot


print("=" * 84)
print("FLAG 2 (quantitative half) -- the t-ranging penalty C2")
print("  enclosure width at 48 panels, c = 13, as the t-halfwidth r grows:")
print("  %-12s %-20s %-18s" % ("r", "W(48, r)", "t-part = W(r)-W(0)"))
W0 = W(mpf(13), 48, mpf(0))
print("  %-12s %-20.6e %-18s" % ("0 (pointwise)", float(W0), "--"))
pts = []
for r in ["0.0005", "0.002", "0.008", "0.03"]:
    w = W(mpf(13), 48, mpf(r))
    pts.append((float(r), float(w - W0)))
    print("  %-12s %-20.6e %-18.6e" % (r, float(w), float(w - W0)))
C2 = sum(d / rr for rr, d in pts) / len(pts)
print()
print("  => t-part is linear in r with C2 ~ %.4e  (per unit t-halfwidth)" % C2)
C1 = float(W0) * 48
print("  => u-part C1/N with C1 ~ %.4f  (so W ~ %.4f/N + %.3e*r)" % (C1, C1, C2))

print()
print("=" * 84)
print("WHAT THE PRODUCER BUYS -- panels and t-reach at the required budgets")
print("  Need W(N,r) <= B. Solve for the largest r at a given N.")
for label, B in [("t=13   R1 endpoint", 1.407e-05), ("t=14.5 R2 worst", 1.877e-06)]:
    print()
    print("  %s : budget B = %.3e" % (label, B))
    print("    %-12s %-16s %-16s %-14s" % ("panels N", "u-part C1/N", "r affordable", "covers width"))
    for N in [8928, 20000, 50000, 200000]:
        upart = C1 / N
        if upart >= B:
            print("    %-12d %-16.3e %-16s %-14s" % (N, upart, "NONE", "u-part alone busts B"))
            continue
        r = (B - upart) / C2
        print("    %-12d %-16.3e %-16.3e %-14.3e" % (N, upart, r, 2 * r))

print()
print("=" * 84)
print("THE DECISIVE COMPARISON -- quadrature ORDER beats parametricity")
print("  panels needed to hit each budget, by scheme order (from measured p=1):")
print("  %-22s %-14s %-14s %-14s" % ("budget", "O(h) now", "O(h^2)", "O(h^4)"))
for label, B in [("t=13   1.407e-05", 1.407e-05), ("t=14.5 1.877e-06", 1.877e-06)]:
    n1 = C1 / B
    n2 = 48 * (float(W0) / B) ** 0.5
    n4 = 48 * (float(W0) / B) ** 0.25
    print("  %-22s %-14.0f %-14.0f %-14.0f" % (label, n1, n2, n4))
print()
print("  -> at O(h) the u-part ALONE needs ~10^4-10^5 panels per box, and the")
print("     t-part then leaves almost no reach. At O(h^4) it is ~10^2.")
print("     The binding lever is the QUADRATURE ORDER, not the parametricity.")
