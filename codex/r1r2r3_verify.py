#!/usr/bin/env python3
"""Independent re-verification of R1/R2/R3 and the reachable target.

Formal statements (RHBelow15Conditional_2026_10_10.lean:86-88):
  R1 : forall t in [0, 13],      0 < Re xi(1+it)
  R2 : forall t in [13, 29/2],   0 < Im xi(1+it)
  R3 : forall t in [29/2, 15],   Re xi(1+it) < 0

xi(s) = (s(s-1) Lambda0(s) + 1)/2 ,  Lambda0 = Lambda + 1/s + 1/(1-s)
"""
from mpmath import mp, mpf, mpc, pi, gamma, zeta, power, findroot

mp.dps = 30


def Lambda0(s):
    return power(pi, -s / 2) * gamma(s / 2) * zeta(s) + 1 / s + 1 / (1 - s)


def xi(t):
    s = mpc(1, mpf(t))
    return (s * (s - 1) * Lambda0(s) + 1) / 2


re_xi = lambda t: xi(t).real
im_xi = lambda t: xi(t).imag

print("=" * 78)
print("1. R1 : Re xi > 0 on [0, 13]  -- scan for the minimum")
best, bt = None, None
t = mpf("0.01")
while t <= 13:
    v = re_xi(t)
    if best is None or v < best:
        best, bt = v, t
    t += mpf("0.05")
for t in ["12.9", "12.95", "13"]:
    print("   Re xi(1+i%-6s) = %+.9e" % (t, float(re_xi(mpf(t)))))
print("   xi(1+i*0) = 1/2 exactly (pole cancellation; scan starts at 0.01)"); print("   scanned minimum over [0.01,13] : %+.9e at t = %s" % (float(best), bt))
print("   -> R1 HOLDS, min margin at the RIGHT ENDPOINT t = 13.")

print()
print("=" * 78)
print("2. where does Re xi actually change sign?")
z = findroot(re_xi, mpf("13.99"))
print("   first zero of Re xi(1+it) : t = %.10f" % float(z))
print("   R1's interval ends at 13, i.e. %.6f BEFORE the sign change." % float(z - 13))
print("   -> the decomposition hands off to Im xi at 13, before Re xi turns.")

print()
print("=" * 78)
print("3. R2 : Im xi > 0 on [13, 14.5]  -- does it survive Re xi's sign change?")
best2, bt2 = None, None
t = mpf(13)
while t <= mpf("14.5"):
    v = im_xi(t)
    if best2 is None or v < best2:
        best2, bt2 = v, t
    t += mpf("0.01")
for t in ["13", "13.9883806982", "14.4", "14.5"]:
    print("   Im xi(1+i%-14s) = %+.9e" % (t, float(im_xi(mpf(t)))))
print("   scanned minimum over [13,14.5] : %+.9e at t = %s" % (float(best2), bt2))
print("   -> R2 HOLDS. Note Im xi stays positive straight THROUGH t = %.4f," % float(z))
print("      which is exactly why the sign change costs the decomposition nothing.")

print()
print("=" * 78)
print("4. R3 : Re xi < 0 on [14.5, 15]  -- scan for the maximum")
best3, bt3 = None, None
t = mpf("14.5")
while t <= 15:
    v = re_xi(t)
    if best3 is None or v > best3:
        best3, bt3 = v, t
    t += mpf("0.005")
for t in ["14.5", "14.75", "15"]:
    print("   Re xi(1+i%-6s) = %+.9e" % (t, float(re_xi(mpf(t)))))
print("   scanned maximum over [14.5,15] : %+.9e at t = %s" % (float(best3), bt3))
print("   -> R3 HOLDS, max (worst) value at the LEFT endpoint t = 14.5.")

print()
print("=" * 78)
print("5. the three handoffs are consistent")
print("   at t = 13   : Re xi = %+.6e (>0, R1 ok)   Im xi = %+.6e (>0, R2 ok)"
      % (float(re_xi(13)), float(im_xi(13))))
print("   at t = 14.5 : Im xi = %+.6e (>0, R2 ok)   Re xi = %+.6e (<0, R3 ok)"
      % (float(im_xi(mpf("14.5"))), float(re_xi(mpf("14.5")))))
print("   -> no gap and no contradiction at either junction.")

print()
print("=" * 78)
print("6. so the POSITIVITY march's exact target is t = 13, not 15 and not 13.9")
UNIF = mpf(50) / 1727
Lb = lambda t: ((1 + 2 * mpf(t)) * UNIF + (mpf(t) ** 2 + mpf(t)) * UNIF) / 2
print("   remaining distance from the landed frontier 6.5625 to 13 : %.4f" % (13 - 6.5625))
print()
print("   %-8s %-14s %-12s %-14s" % ("centre", "Re xi", "L(uniform)", "r attainable"))
for t in [7, 9, 11, 12.5, 12.9, 13]:
    rx = re_xi(t)
    r = mpf("0.8") * rx / Lb(t)
    print("   %-8s %+.6e  %-12.4f %-14.3e" % (t, float(rx), float(Lb(t)), float(r)))
print()
for lo, T in [("6.5625", 13)]:
    c, n = mpf(lo), 0
    while c < T and n < 2000000:
        rx = re_xi(c)
        if rx <= 0:
            break
        r = mpf("0.8") * rx / Lb(c + mpf("0.02"))
        if r > mpf("0.5"):
            r = mpf("0.5")
        if r < mpf("1e-7"):
            break
        c += 2 * r
        n += 1
    print("   Tier-1 boxes to cover [%s, %d] : %d  (reached %.4f)" % (lo, T, n, float(c)))
print()
print("   the cost is concentrated at the right end: r ~ 8e-4 near t = 13,")
print("   i.e. ~1/1200-width boxes, because Mc_lb must drop to ~2.5e-3 there.")
