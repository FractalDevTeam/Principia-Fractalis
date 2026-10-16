#!/usr/bin/env python3
"""Can the Gate-1 ENCLOSURE even fit inside the margin at the hard ends?

Gate 1 needs   c^2 R_ub + c I_ub <= 1 - 2 Mc_lb   with Mc_lb <= Re xi(c).
True values satisfy c^2 R + c I = 1 - 2 Re xi(c) exactly.
So the enclosure error must fit in the slack:

   c^2 (R_ub - R) + c (I_ub - I)  <=  2 (Re xi(c) - Mc_lb)

Taking Mc_lb = Re xi/2 (half the true margin) leaves slack = Re xi(c).
Achieved at c = 51/8 (CLOSED box, line 893): R_ub - R = 2.62e-3, I_ub - I = 1.89e-3.
"""
from mpmath import mp, mpf, mpc, pi, gamma, zeta, power

mp.dps = 30


def Lambda0(s):
    return power(pi, -s / 2) * gamma(s / 2) * zeta(s) + 1 / s + 1 / (1 - s)


def RI(t):
    L = Lambda0(mpc(1, mpf(t)))
    return L.real, L.imag


def re_xi(t):
    R, I = RI(t)
    t = mpf(t)
    return (1 - t ** 2 * R - t * I) / 2


# achieved enclosure excess at c = 51/8
R_ub_h32 = mpf(542831867) / 32000000000
I_ub_h32 = mpf(60314889) / 32000000000
ADDON = mpf(231) / 279841 + mpf(1) / 10 ** 6 + mpf(1) / 10 ** 4
R0, I0 = RI("6.375")
dR_now = (R_ub_h32 + ADDON) - R0
dI_now = (I_ub_h32 + ADDON) - I0

print("=" * 82)
print("achieved enclosure excess at c = 51/8 (the landed CLOSED box)")
print("   R_ub_f - R_true = %.4e      I_ub_f - I_true = %.4e" % (float(dR_now), float(dI_now)))
print("   its cost in the gate budget there: c^2 dR + c dI = %.6f"
      % float(mpf("6.375") ** 2 * dR_now + mpf("6.375") * dI_now))

print()
print("=" * 82)
print("required enclosure as t grows (slack = Re xi(c), i.e. Mc_lb = Re xi/2)")
print("%-8s %-14s %-14s %-16s %-14s" % ("t", "Re xi", "slack", "max allowed dR", "vs now"))
for t in [6.375, 7, 8, 9, 10, 11, 12, 12.5, 13]:
    rx = re_xi(t)
    c = mpf(t)
    # assume the same dR:dI ratio as achieved now
    ratio = dI_now / dR_now
    # c^2 dR + c (ratio*dR) <= slack  =>  dR <= slack / (c^2 + c*ratio)
    dR_max = rx / (c ** 2 + c * ratio)
    print("%-8s %-14.6e %-14.6e %-16.4e %-14s"
          % (t, float(rx), float(rx), float(dR_max),
             "%.0fx tighter" % float(dR_now / dR_max)))

print()
print("=" * 82)
print("THE BINDING NUMBER")
rx13 = re_xi(13)
ratio = dI_now / dR_now
dR13 = rx13 / (mpf(169) + 13 * ratio)
print("   at t = 13 the enclosure must satisfy dR <= %.3e" % float(dR13))
print("   currently achieved                     dR  = %.3e" % float(dR_now))
print("   => %.0fx tighter enclosure needed at the R1 endpoint alone." % float(dR_now / dR13))
print()
rx145 = fabs = abs(float(re_xi(mpf("14.5"))))
im145 = 4.141834185e-4
dR145 = mpf(im145) / (mpf("14.5") ** 2 + mpf("14.5") * ratio)
print("   at t = 14.5 (R2's worst point, margin %.3e) : dR <= %.3e" % (im145, float(dR145)))
print("   => %.0fx tighter than now." % float(dR_now / dR145))
print()
print("   For scale: the residue tightening identified for c=13/2 buys 32.8x on")
print("   the residue TERM only (8.25e-4 -> 2.51e-5), i.e. it removes the add-on")
print("   but not the panel width (%.2e of the %.2e total)." % (float(dR_now - ADDON), float(dR_now)))
print("   Panel width must come down by its own large factor, which means many")
print("   more panels per box ON TOP of many more boxes.")
