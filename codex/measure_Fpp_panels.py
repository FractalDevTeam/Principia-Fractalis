#!/usr/bin/env python3
"""
STEP 1: measure the F'' panel enclosure width against the F panel width.

The S-route claim being tested is that panels enclosing

    S = int F+'' e^{itu/2} + int F-'' e^{-itu/2}

achieve the same ABSOLUTE enclosure width as the existing panels, which
enclose Lambda0 via

    nodeR_plus = (F+ + F-) cos((c/2)u),  nodeR_minus = (F+ - F-) sin((c/2)u).

The S integrands are

    nodeS_R = (F+'' + F-'') cos((c/2)u)      -> Re S
    nodeS_I = (F+'' - F-'') sin((c/2)u)      -> Im S

with, writing x = exp u and E = exp(u/2),

    F+'' = E [ (1/4) om + 2 om' x + om'' x^2 ]
    F-'' = om'' x^2 + om' x

and om, om', om'' the N=3 truncations. Everything below reuses the SHIPPED
interval arithmetic from scripts/gen_fourier_panels_c27_4.py verbatim -- same
outward rounding, same series_terms, same panel grid -- so the two widths are
measured on identical machinery and differ only in the integrand.

Reported: the total range-brick enclosure width of int_0^{3/2} for each
integrand, the implied delta (half-width), and what that delta does to
Mc_lb(c) = Re xi(c) - (2 + 2/c) delta_S on the S route.
"""
import io
import os
import sys
from fractions import Fraction as F

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, "gen", "gen_fourier_panels_c27_4.py")

g = {"__name__": "_g", "__file__": GEN}
exec(compile(io.open(GEN, encoding="utf-8").read(), GEN, "exec"), g)

I = g["I"]
PI = g["PI"]
exp_neg_interval = g["exp_neg_interval"]
exp_pos_interval = g["exp_pos_interval"]
cos_interval = g["cos_interval"]
sin_interval = g["sin_interval"]
omega_N3_interval = g["omega_N3_interval"]
SEGMENTS = g["SEGMENTS"]
N_PANELS = g["N_PANELS"]
panel_endpoints = g["panel_endpoints"]

ST = 50          # series_terms, as the generator uses


def omega_derivs(exp_u):
    """(om, om', om'') as intervals, on x = exp_u, N = 3 truncation."""
    pi_x = (PI * exp_u).rounded()
    pi4_x = (I.point(4) * pi_x).rounded()
    pi9_x = (I.point(9) * pi_x).rounded()
    e1 = exp_neg_interval(pi_x, series_terms=ST)
    e2 = exp_neg_interval(pi4_x, series_terms=ST)
    e3 = exp_neg_interval(pi9_x, series_terms=ST)
    om = (e1 + e2 + e3).rounded()
    PI2 = (PI * PI).rounded()
    om1 = (-((PI * e1).rounded()
             + (I.point(4) * (PI * e2).rounded()).rounded()
             + (I.point(9) * (PI * e3).rounded()).rounded())).rounded()
    om2 = ((PI2 * e1).rounded()
           + (I.point(16) * (PI2 * e2).rounded()).rounded()
           + (I.point(81) * (PI2 * e3).rounded()).rounded()).rounded()
    return om, om1, om2


def nodeS_bounds(u_interval, c_half):
    """(Re-integrand interval, Im-integrand interval) for the S panels."""
    exp_u = exp_pos_interval(u_interval, series_terms=ST)
    u_half = I(u_interval.lo * F(1, 2), u_interval.hi * F(1, 2))
    E = exp_pos_interval(u_half, series_terms=ST)
    om, om1, om2 = omega_derivs(exp_u)
    x = exp_u
    x2 = (x * x).rounded()
    inner = ((I.point(F(1, 4)) * om).rounded()
             + (I.point(2) * (om1 * x).rounded()).rounded()
             + (om2 * x2).rounded()).rounded()
    Fpp = (E * inner).rounded()
    Fmp = ((om2 * x2).rounded() + (om1 * x).rounded()).rounded()
    cu = I(c_half * u_interval.lo, c_half * u_interval.hi)
    cos_cu = cos_interval(cu, series_terms=ST)
    sin_cu = sin_interval(cu, series_terms=ST)
    SR = ((Fpp + Fmp) * cos_cu).rounded()
    SI = ((Fpp - Fmp) * sin_cu).rounded()
    return SR, SI


def nodeR_bounds(u_interval, c_half):
    """The SHIPPED nodeR integrands, with c_half made explicit."""
    exp_u = exp_pos_interval(u_interval, series_terms=ST)
    u_half = I(u_interval.lo * F(1, 2), u_interval.hi * F(1, 2))
    E = exp_pos_interval(u_half, series_terms=ST)
    om = omega_N3_interval(exp_u, series_terms=ST)
    Fp = (E * om).rounded()
    Fm = om
    cu = I(c_half * u_interval.lo, c_half * u_interval.hi)
    cos_cu = cos_interval(cu, series_terms=ST)
    sin_cu = sin_interval(cu, series_terms=ST)
    return ((Fp + Fm) * cos_cu).rounded(), ((Fp - Fm) * sin_cu).rounded()


def nodeT_bounds(u_interval, c_half):
    """The ONE-IBP rung: F+' = (1/2)E om + E om' x,  F-' = om' x.
    xi(1+it) = 1/2 + (1+it) T  with T = int F-' e^{-} - int F+' e^{+}, so the
    amplification is (1+c) rather than c^2/2 -- but the 1/2 does NOT cancel
    here, which is the separate reason this rung is badly conditioned."""
    exp_u = exp_pos_interval(u_interval, series_terms=ST)
    u_half = I(u_interval.lo * F(1, 2), u_interval.hi * F(1, 2))
    E = exp_pos_interval(u_half, series_terms=ST)
    om, om1, om2 = omega_derivs(exp_u)
    x = exp_u
    Fp1 = ((I.point(F(1, 2)) * (E * om).rounded()).rounded()
           + (E * (om1 * x).rounded()).rounded()).rounded()
    Fm1 = (om1 * x).rounded()
    cu = I(c_half * u_interval.lo, c_half * u_interval.hi)
    cos_cu = cos_interval(cu, series_terms=ST)
    sin_cu = sin_interval(cu, series_terms=ST)
    return ((Fp1 + Fm1) * cos_cu).rounded(), ((Fp1 - Fm1) * sin_cu).rounded()


def total_width(c, which):
    """Range-brick enclosure of int_0^{3/2}: sum over all 48 panels of
    h*(hi-lo). Returns (plus_width, minus_width, plus_lo, plus_hi)."""
    c_half = F(c) / 2
    fn = {"S": nodeS_bounds, "T": nodeT_bounds}.get(which, nodeR_bounds)
    wR = wI = F(0)
    loR = hiR = F(0)
    for seg in range(1, 7):
        lo, hi = SEGMENTS[seg]
        for k in range(N_PANELS):
            a, b = panel_endpoints(lo, hi, k)
            h = b - a
            A, B = fn(I(a, b), c_half)
            wR += h * A.width()
            wI += h * B.width()
            loR += h * A.lo
            hiR += h * A.hi
    return wR, wI, loR, hiR


mp.mp.dps = 25


def xi(s):
    return mp.mpf(1) / 2 * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


Re_xi = lambda t: mp.re(xi(mp.mpc(1, t)))
W1 = mp.mpf("0.0432174056066540072876580607551")
L0 = lambda c: 2 * W1 * (1 + 1 / mp.mpf(c)) + 1 / (2 * mp.mpf(c) ** 2)

print("=" * 78)
print("F'' PANEL WIDTH vs F PANEL WIDTH -- identical panels, identical arithmetic")
print("=" * 78)
print(f"{'c':>7} {'which':>6} {'width(Re)':>13} {'width(Im)':>13} {'delta=w/2':>12}")
res = {}
for c in ("27/4", "13"):
    for which in ("R", "T", "S"):
        wR, wI, loR, hiR = total_width(F(c), which)
        res[(c, which)] = (wR, wI)
        print(f"{c:>7} {which:>6} {float(wR):>13.6e} {float(wI):>13.6e} "
              f"{float(wR / 2):>12.6e}")
print()
for c in ("27/4", "13"):
    rR = res[(c, "R")][0]
    rS = res[(c, "S")][0]
    print(f"  c = {c:<6} S/R width ratio (Re) = {float(rS / rR):.2f}x"
          f"   (Im) = {float(res[(c,'S')][1] / res[(c,'R')][1]):.2f}x")
print()
print("=" * 78)
print("WHAT THAT delta_S DOES: Mc_lb(c) = Re xi(c) - (2 + 2/c) * delta_S")
print("=" * 78)
print(f"{'c':>6} {'Re xi':>11} {'delta_S':>11} {'(2+2/c)dS':>11} {'Mc_lb':>12}"
      f" {'L0*r 1/128':>11} {'verdict':>9}")
for c in (11, 12, 13):
    # delta_S measured at that c (recompute: the width depends on c via the phase)
    wR, wI, _, _ = total_width(F(c), "S")
    dS = mp.mpf(wR.numerator) / wR.denominator / 2
    cc = mp.mpf(c)
    m = Re_xi(cc) - (2 + 2 / cc) * dS
    lr = L0(cc) / 128
    print(f"{c:>6} {float(Re_xi(cc)):>11.6f} {float(dS):>11.6e} "
          f"{float((2 + 2 / cc) * dS):>11.6f} {float(m):>12.6f} {float(lr):>11.6f}"
          f" {'PASS' if m > lr else 'FAIL':>9}")
print()
print("  (delta_S here is HALF the summed range-brick width, the same convention")
print("   under which the shipped hybrid pack has delta_R = 4.31e-4.)")


print()
print("=" * 78)
print("THE IBP LADDER: amplification x integrand-width, at c = 13")
print("=" * 78)
print("  Re xi expressed three ways, each with its own amplification of the")
print("  panel enclosure error, and its own integrand to enclose:")
print()
HYB = mp.mpf("0.2507")   # hybrid/all-range width ratio, measured on the F panels
                         # (4.307e-4 / 1.717973e-3)
print(f"{'rung':>22} {'amplif.':>9} {'delta (all-rng)':>16} {'delta (hybrid)':>15}"
      f" {'error':>10}")
rows = []
for name, which, amp in (("Lambda0 (no IBP)", "R", mp.mpf(13) ** 2 / 2),
                         ("T (one IBP)", "T", 1 + mp.mpf(13)),
                         ("S (two IBPs)", "S", 2 + 2 / mp.mpf(13))):
    w, _, _, _ = total_width(F(13), which)
    d = mp.mpf(w.numerator) / w.denominator / 2
    dh = d * HYB
    rows.append((name, amp, d, dh, amp * dh))
    print(f"{name:>22} {float(amp):>9.2f} {float(d):>16.4e} {float(dh):>15.4e}"
          f" {float(amp * dh):>10.5f}")
print()
need = 2 * (Re_xi(13) - L0(13) / 128)
print(f"  needed (so Mc_lb > L0*r at r=1/128): error < {float(need / 2):.6f}")
print(f"  best measured rung:                  error = "
      f"{float(min(r[4] for r in rows)):.6f}")
print(f"  shortfall: {float(min(r[4] for r in rows) / (need / 2)):.1f}x")
print()
print("  amplification x delta is flat to within a factor of ~1.5 across all")
print("  three rungs -- integrating by parts trades amplification for integrand")
print("  difficulty at essentially a fixed exchange rate. So NO change of")
print("  representation reaches c = 13; only more panels do.")
