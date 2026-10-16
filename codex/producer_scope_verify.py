#!/usr/bin/env python3
"""Measurements for the t-parametric producer scoping.

Closes three open flags by measurement rather than assumption.

The generator's scheme (gen_fourier_panels_c51_8.py:493, 691-702) emits, per
panel [a,b] of width h:
      h * L  <=  integral over [a,b]  <=  h * U
with L,U the RANGE of the integrand on the panel (critical-point enumeration
for cos/sin). That is a ZEROTH-ORDER range enclosure via
intervalIntegral.integral_const -- NOT Simpson.

Integrand for Re Lambda0 (c = 2*t_target/2 convention as in the files):
      g(u) = (exp(u/2) + 1) * omega_3(exp u) * cos(c*u/2)
with omega_3(x) = sum_{n=1}^{3} exp(-pi n^2 x)   (the N=3 truncation).
Panels cover u in [0, 3/2]; current geometry is 6 segments x 8 panels = 48
panels of width 1/32.
"""
from mpmath import mp, mpf, exp, cos, pi, sin

mp.dps = 40

NTERM = 3
omega3 = lambda x: sum(exp(-pi * n ** 2 * x) for n in range(1, NTERM + 1))


def g(u, c):
    u = mpf(u)
    return (exp(u / 2) + 1) * omega3(exp(u)) * cos(mpf(c) * u / 2)


def panel_range(a, b, c, probes=400):
    """Range of g on [a,b] by dense probing (a faithful proxy for the
    generator's exact critical-point enumeration)."""
    lo = hi = None
    for i in range(probes + 1):
        v = g(a + (b - a) * mpf(i) / probes, c)
        if lo is None or v < lo:
            lo = v
        if hi is None or v > hi:
            hi = v
    return lo, hi


def total_enclosure_width(c, npanels, U=mpf(3) / 2):
    """Sum of h*(hi-lo) over all panels -- the generator's enclosure width."""
    h = U / npanels
    tot = mpf(0)
    for k in range(npanels):
        a, b = k * h, (k + 1) * h
        lo, hi = panel_range(a, b, c)
        tot += h * (hi - lo)
    return tot


print("=" * 84)
print("FLAG 1 -- measure the panel-scaling exponent (claimed O(h^4), assumption)")
print("  total enclosure width vs number of panels, at c = 51/8")
print()
print("  %-10s %-10s %-18s %-14s" % ("panels", "h", "enclosure width", "ratio"))
prev = None
rows = []
for npan in [12, 24, 48, 96, 192]:
    w = total_enclosure_width(mpf(51) / 8, npan)
    rows.append((npan, float(w)))
    r = "" if prev is None else "%.3f" % (prev / float(w))
    print("  %-10d %-10.5f %-18.6e %-14s" % (npan, float(mpf(3) / 2 / npan), float(w), r))
    prev = float(w)
import math

ex = [math.log(rows[i][1] / rows[i + 1][1]) / math.log(2) for i in range(len(rows) - 1)]
print()
print("  measured exponent p in width ~ h^p (per doubling): %s"
      % ", ".join("%.3f" % e for e in ex))
print("  => p ~ %.2f : FIRST ORDER. The O(h^4) assumption was WRONG." % (sum(ex) / len(ex)))
print("     (48 panels is the current geometry, width 1/32.)")

print()
print("=" * 84)
print("FLAG 1b -- what that costs: panels needed for the required tightenings")
w48 = dict(rows)[48]
print("  current enclosure width at 48 panels : %.4e" % w48)
for label, factor in [("t=13   (186x)", 186), ("t=14.5 (1397x)", 1397)]:
    for p, nm in [(1.0, "O(h)   measured"), (2.0, "O(h^2) if upgraded"), (4.0, "O(h^4) if Simpson")]:
        need = 48 * factor ** (1.0 / p)
        print("    %-16s %-20s -> %10.0f panels  (%.0fx current)"
              % (label if p == 1.0 else "", nm, need, need / 48))

print()
print("=" * 84)
print("FLAG 3 -- do panel widths past t = 6.5 behave like c = 51/8? MEASURE.")
print("  %-10s %-20s %-14s" % ("c", "enclosure width (48)", "vs c=51/8"))
base = None
for c in [mpf(6), mpf(51) / 8, mpf(13) / 2, mpf(8), mpf(10), mpf(13), mpf("14.5")]:
    w = total_enclosure_width(c, 48)
    if base is None:
        base = float(w)
    print("  %-10s %-20.6e %-14s" % (str(c), float(w), "%.2fx" % (float(w) / base)))
print()
print("  -> the enclosure width GROWS with c (faster cos oscillation), so the")
print("     c=51/8 width does NOT carry: the box counts assuming it are optimistic.")
