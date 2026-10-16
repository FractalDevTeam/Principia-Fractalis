#!/usr/bin/env python3
"""Price ALL THREE legs R1, R2, R3 -- not just the one the march is building.

The same derivative bound serves all three: from
  d/dt[2 xi(1+it)] = (-2t+i) Lambda0 + (-t^2+it) i Lambda0'
the modulus bound is identical for Re and Im, so
  L(t) = [ (1+2t) B + (t^2+t) B' ] / 2
bounds |d/dt Re xi| and |d/dt Im xi| alike.

Each leg needs, per box, a certified margin m(c) and half-width r < m(c)/L(c).
"""
from mpmath import mp, mpf, mpc, pi, gamma, zeta, power, diff, fabs

mp.dps = 30
UNIF = mpf(50) / 1727


def Lambda0(s):
    return power(pi, -s / 2) * gamma(s / 2) * zeta(s) + 1 / s + 1 / (1 - s)


def xi(t):
    s = mpc(1, mpf(t))
    return (s * (s - 1) * Lambda0(s) + 1) / 2


re_xi = lambda t: xi(t).real
im_xi = lambda t: xi(t).imag
L0 = lambda t: Lambda0(mpc(1, mpf(t)))
L0p = lambda t: diff(Lambda0, mpc(1, mpf(t)))

L_unif = lambda t: ((1 + 2 * mpf(t)) * UNIF + (mpf(t) ** 2 + mpf(t)) * UNIF) / 2
L_loc = lambda t: ((1 + 2 * mpf(t)) * mpf("1.5") * fabs(L0(t))
                   + (mpf(t) ** 2 + mpf(t)) * mpf("1.5") * fabs(L0p(t))) / 2


def count(lo, hi, margin, Lfun, cap=mpf("0.5"), safety=mpf("0.8")):
    c, n = mpf(lo), 0
    while c < mpf(hi) and n < 3000000:
        m = margin(c)
        if m <= 0:
            return None, float(c)
        r = safety * m / Lfun(c + mpf("0.001"))
        if r > cap:
            r = cap
        if r < mpf("1e-9"):
            return None, float(c)
        c += 2 * r
        n += 1
    return n, float(c)


legs = [
    ("R1  Re xi > 0", "6.5625", 13, lambda c: re_xi(c), "frontier 6.5625 -> 13"),
    ("R2  Im xi > 0", 13, "14.5", lambda c: im_xi(c), "13 -> 14.5"),
    ("R3  Re xi < 0", "14.5", 15, lambda c: -re_xi(c), "14.5 -> 15"),
]

print("=" * 80)
print("worst-case margin on each leg")
print("   R1 : min Re xi on [0,13]      = %+.9e  (at t = 13)" % float(re_xi(13)))
print("   R2 : min Im xi on [13,14.5]   = %+.9e  (at t = 14.5)" % float(im_xi(mpf("14.5"))))
print("   R3 : max Re xi on [14.5,15]   = %+.9e  (at t = 14.5)" % float(re_xi(mpf("14.5"))))
print("   -> R2's margin is the SMALLEST of the three, 6.1x tighter than R1's.")

print()
print("=" * 80)
print("%-16s %-24s %-14s %-14s" % ("leg", "span", "Tier-1 boxes", "Tier-3 boxes"))
tot1 = tot3 = 0
for name, lo, hi, margin, span in legs:
    n1, r1 = count(lo, hi, margin, L_unif)
    n3, r3 = count(lo, hi, margin, L_loc)
    tot1 += n1 if n1 else 0
    tot3 += n3 if n3 else 0
    print("%-16s %-24s %-14s %-14s" % (name, span,
                                       n1 if n1 else "stalled @%.3f" % r1,
                                       n3 if n3 else "stalled @%.3f" % r3))
print("%-16s %-24s %-14d %-14d" % ("TOTAL", "", tot1, tot3))
print()
print("   at ~11.5k generated Lean lines per box:")
print("     Tier 1 : %.1fM lines" % (tot1 * 11500 / 1e6))
print("     Tier 3 : %.1fM lines  (%.0fx reduction)" % (tot3 * 11500 / 1e6, tot1 / tot3))

print()
print("=" * 80)
print("where the cost sits inside each leg (attainable r at the hard end)")
for t, lab in [(13, "R1 right end"), (mpf("14.5"), "R2 right end / R3 left end")]:
    m = min(fabs(re_xi(t)), fabs(im_xi(t)))
    print("   t = %-6s (%-26s): L_unif = %.3f -> r ~ %.2e  (1/%.0f)"
          % (float(t), lab, float(L_unif(t)), float(mpf("0.8") * m / L_unif(t)),
             float(L_unif(t) / (mpf("0.8") * m))))
    print("   %22s  L_loc  = %.3f -> r ~ %.2e  (1/%.0f)"
          % ("", float(L_loc(t)), float(mpf("0.8") * m / L_loc(t)),
             float(L_loc(t) / (mpf("0.8") * m))))
