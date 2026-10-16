#!/usr/bin/env python3
"""Scoping the box-local Gate-2 bound.

DERIVATION of the gate-2 inequality as it stands in the scaffold.
  2 xi(s) = s(s-1) Lambda0(s) + 1 ,   s = 1 + i t ,   s(s-1) = -t^2 + i t
  d/dt [2 xi(1+it)] = (-2t + i) Lambda0 + (-t^2 + i t) * i * Lambda0'
  => |d/dt 2 xi| <= sqrt(1+4t^2) |Lambda0| + |t| sqrt(t^2+1) |Lambda0'|
  and since sqrt(1+4t^2) <= 1 + 2|t| and |t|sqrt(t^2+1) <= t^2 + |t| :
       |d/dt 2 Re xi| <= (1 + 2|t|) B + (t^2 + |t|) B'
  with B >= |Lambda0|, B' >= |Lambda0'| on the box.
  Gate 2 wants |d/dt Re xi| <= L = 1, i.e. the above <= 2:
       (1 + 2|t|) B + (t^2 + |t|) B' <= 2
  The scaffold takes B = B' = 50/1727, giving exactly
       50(1+2|t|) + 50(t^2+|t|) <= 2*1727 ,  ceiling |t| <= 6.8863.

KEY QUESTION: the uniform route uses a CONSTANT for B and B'. But
Lambda0(1+it) ~ 1/t^2 (this project's own L4 decay result), so the truth
DECAYS. Does the gate-2 quantity actually stay bounded?
"""
from mpmath import mp, mpf, mpc, pi, gamma, zeta, power, diff, fabs, sqrt

mp.dps = 30


def Lambda0(s):
    return power(pi, -s / 2) * gamma(s / 2) * zeta(s) + 1 / s + 1 / (1 - s)


L0 = lambda t: Lambda0(mpc(1, t))
L0p = lambda t: diff(Lambda0, mpc(1, t))          # Lambda0'(1+it), complex deriv
re_xi = lambda t: (1 - mpf(t) ** 2 * L0(t).real - mpf(t) * L0(t).imag) / 2

UNIF = mpf(50) / 1727

print("=" * 84)
print("1. how loose is the uniform constant, separately for Lambda0 and Lambda0' ?")
print("   uniform bound used for BOTH:  50/1727 = %.8f" % float(UNIF))
print()
print("   %-6s %-14s %-14s %-10s %-10s" % ("t", "|Lambda0|", "|Lambda0'|", "loose L0", "loose L0'"))
for t in [6, 6.5, 7, 8, 10, 12, 14]:
    a, b = fabs(L0(t)), fabs(L0p(t))
    print("   %-6s %-14.3e %-14.3e %-10.1fx %-10.1fx"
          % (t, float(a), float(b), float(UNIF / a), float(UNIF / b)))
print()
print("   -> the uniform constant is modestly loose on Lambda0 but")
print("      ORDERS loose on Lambda0'. Using one constant for both is the defect.")

print()
print("=" * 84)
print("2. the gate-2 quantity with TRUE values:  (1+2t)|L0| + (t^2+t)|L0'|  vs 2")
print("   %-6s %-16s %-16s %-14s %-8s" % ("t", "(1+2t)|L0|", "(t^2+t)|L0'|", "total", "<= 2 ?"))
worst = mpf(0)
for t in [6.886, 7, 8, 9, 10, 11, 12, 13, 13.99, 15, 20, 30, 50]:
    a, b = fabs(L0(t)), fabs(L0p(t))
    t1 = (1 + 2 * mpf(t)) * a
    t2 = (mpf(t) ** 2 + mpf(t)) * b
    tot = t1 + t2
    worst = max(worst, tot)
    print("   %-6s %-16.6f %-16.6f %-14.6f %-8s"
          % (t, float(t1), float(t2), float(tot), "YES" if tot <= 2 else "** NO **"))
print()
print("   worst value over the whole sampled range: %.6f  (budget 2)" % float(worst))
print("   -> both terms are O(1/t): (1+2t)/t^2 -> 0 and (t^2+t)*2/t^3 -> 0.")
print("      The gate-2 ceiling at 6.886 is an ARTIFACT of the constant bound.")

print()
print("=" * 84)
print("3. so what actually binds? the TRUE derivative L and the box width")
print("   gate 2 needs L*r < Mc_lb ; gate 1 needs Re xi(centre) >= Mc_lb.")
print("   Taking Mc_lb = Re xi(c) (the most generous choice) gives")
print("        r < Re xi(c) / L(c)        -- the attainable half-width")
print()
print("   %-6s %-12s %-14s %-14s %-12s" % ("t", "Re xi", "L_true", "r attainable", "vs r=1/16"))
for t in [6.5, 7, 7.5, 8, 9, 10, 12, 13, 13.9]:
    rx = re_xi(t)
    Lt = fabs(diff(re_xi, mpf(t)))
    if rx <= 0:
        print("   %-6s %-12.6f  (Re xi <= 0 -- past the first sign change)" % (t, float(rx)))
        continue
    r_att = rx / Lt
    print("   %-6s %-12.6f %-14.6f %-14.4f %-12s"
          % (t, float(rx), float(Lt), float(r_att), "%.0fx wider" % float(r_att * 16)))
print()
print("   -> with a box-local L the attainable half-width is O(1), not 1/16.")
print("      The current L = 1 is the loose part, not the geometry.")

print()
print("=" * 84)
print("4. how many boxes to cover [6.886, T] with box-local bounds?")
print("   N(T) ~ integral of L(c)/(2 Re xi(c)) dc   (half-width r = Re xi/L)")
for T in [8, 10, 12, 13, 13.5, 13.9]:
    n, c, steps = 0, mpf("6.886"), 0
    while c < T and steps < 100000:
        rx = re_xi(c)
        if rx <= 0:
            break
        Lt = fabs(diff(re_xi, c))
        r = rx / Lt
        r = min(r, mpf("0.5"))           # cap: keep the local model honest
        c = c + 2 * r
        n += 1
        steps += 1
    print("   cover up to T = %-6s : %3d boxes  (reached c = %.4f)" % (T, n, float(c)))
print()
print("   -> single digits of boxes to reach t ~ 13, versus the current 1/16")
print("      spacing which would need ~57 boxes just for [6.886, 13].")
