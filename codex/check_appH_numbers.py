#!/usr/bin/env python3
"""Recompute every closed-form number in appH from scratch. mpmath where
precision matters. Verdicts are computed from residuals, never printed as
strings (feedback_verification_harness_can_lie)."""
import pathlib, re
from mpmath import mp, mpf, pi, e, exp, sqrt, zetazero

mp.dps = 40
H = pathlib.Path("/home/xluxx/pf-push-20261120/Principia_Fractalis_master_folder/appendices/appH_numerical_validation.tex")
src = H.read_text(encoding="utf-8")
lines = src.split("\n")

def show(label, printed, computed, places):
    """Compare to the printed precision. Verdict from the residual."""
    p = mpf(printed)
    c = mpf(computed)
    tol = mpf(10) ** (-places)
    d = abs(p - c)
    ok = d <= tol
    print("   %-46s printed %-22s computed %-22s  %s"
          % (label, printed, mp.nstr(c, places + 3), "OK" if ok else ("OFF by %s" % mp.nstr(d, 4))))
    return ok

print("########## A. the critical Reynolds number, appH:486")
ctx = [l for l in lines if "328" in l and "e^{-3.5" in l]
for l in ctx:
    print("   source: %s" % l.strip()[:120])
val = mpf(10) ** 6 * exp(-mpf("3.5") / pi)
print("   10^6 * exp(-3.5/pi) = %s" % mp.nstr(val, 12))
show("10^6 e^(-3.5/pi)", "328215.6", val, 1)
print("   (3.5/pi = %s ; exp(-that) = %s)" % (mp.nstr(mpf('3.5')/pi, 12), mp.nstr(exp(-mpf('3.5')/pi), 12)))

print()
print("########## B. the alpha-formula values, appH:66-78")
phi = (1 + sqrt(5)) / 2
print("   phi                       = %s" % mp.nstr(phi, 16))
print("   phi + 1/4                 = %s" % mp.nstr(phi + mpf(1)/4, 16))
show("pi/(10*sqrt(2))      [line 66/75]", "0.222144146908", pi / (10 * sqrt(2)), 12)
show("pi/(10*(phi+1/4))    [line 78 fix]", "0.168176418", pi / (10 * (phi + mpf(1)/4)), 9)
show("the WITHDRAWN value  [line 78 old]", "0.1330222423", pi / (10 * (phi + mpf(1)/4)), 10)
a, b, c = mpf("0.222144146908"), mpf("0.133022242308"), mpf("0.089121904600")
print("   identity check  0.222144146908 - 0.133022242308 = %s" % mp.nstr(a - b, 15))
print("                   vs printed 0.089121904600        -> residual %s" % mp.nstr(abs(a - b - c), 4))
print("   so 0.1330222423 is a DIFFERENCE of two printed values, not pi/(10(phi+1/4))")
# what IS 0.1330222423 as pi/(10x)?
x = pi / (10 * b)
print("   pi/(10*0.133022242308) implies x = %s   (phi+1/4 = %s)"
      % (mp.nstr(x, 12), mp.nstr(phi + mpf(1)/4, 12)))
show("pi/(10*0.0891219046) implies", "3.5254", pi / (10 * c), 4)

print()
print("########## C. the convergence table t-value, appH:20-27")
for n in range(1, 4):
    print("   true zetazero(%d) imaginary part = %s" % (n, mp.nstr(zetazero(n).imag, 14)))
print("   appH prints t = 14.2267 on all eight rows.")
z1 = zetazero(1).imag
print("   |14.2267 - 14.134725...| = %s" % mp.nstr(abs(mpf("14.2267") - z1), 6))
print("   relative error vs zero 1  = %s %%" % mp.nstr(100 * abs(mpf("14.2267") - z1) / z1, 4))
print("   --- table context, appH:5-33:")
for i in range(4, 34):
    if i < len(lines):
        print("      %4d  %s" % (i + 1, lines[i][:118]))

print()
print("########## D. other closed forms")
show("2^(-2/3)             [line 146?]", "0.6299", mpf(2) ** (-mpf(2)/3), 4)
print("   line 146/147 context:")
for i in (143, 144, 145, 146, 147, 148):
    if i < len(lines):
        print("      %4d  %s" % (i + 1, lines[i][:118]))
print("   line 499-500 context:")
for i in (496, 497, 498, 499, 500):
    if i < len(lines):
        print("      %4d  %s" % (i + 1, lines[i][:118]))

print()
print("########## E. appH's own verification-status section, 476-506")
for i in range(475, min(506, len(lines))):
    print("   %4d  %s" % (i + 1, lines[i][:126]))
