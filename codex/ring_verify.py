#!/usr/bin/env python3
"""Verification for RING_AB_SECTOR_2026-10-16.md

1. Indicial exponents of the radial Madelung equation, with V bounded and with
   V = c/r^2 -- gives the exact condition under which smoothness forces ell in Z.
2. Aharonov-Bohm: what is actually quantized is the CANONICAL circulation, so
   the circulation of m*v lies in a Z-lattice SHIFTED by the flux.
3. Numeric: the regular branch really does go like r^|ell| for non-integer ell
   too, so neither the ODE nor normalisability is the obstruction -- smoothness
   at the origin is.
4. The order-of-limits point: every finite-barrier problem forces ell in Z, and
   Z is closed, so the annulus's non-integer states are not limits of
   finite-barrier states.
"""
import sympy as sp
import numpy as np

r = sp.Symbol("r", positive=True)
ell = sp.Symbol("ell", real=True)
c = sp.Symbol("c", positive=True)
m, hbar = sp.symbols("m hbar", positive=True)
f = sp.Function("f")

print("=" * 74)
print("1. indicial exponents of the radial Madelung equation")
print("   f_rr + f_r/r - (ell^2/r^2) f = (2m/hbar^2)(V - E) f ,   f = sqrt(rho)")
print()
print("   (a) V BOUNDED near r = 0, so the right-hand side is subleading:")
ode = sp.Eq(sp.diff(f(r), r, 2) + sp.diff(f(r), r) / r - (ell ** 2 / r ** 2) * f(r), 0)
print("      ", sp.dsolve(ode, f(r)))
print("       -> exponents +/- ell. The REGULAR branch is f ~ r^|ell|, so")
print("          rho ~ r^(2|ell|): there IS a node at r = 0 whenever ell =/= 0.")
print()
print("   (b) V = c/r^2, a centrifugal core of the SAME order as the ell term:")
print("       (sympy's dsolve returns a trivial answer for this one, so the")
print("        exponent is obtained by substituting f = r^s and solving the")
print("        indicial equation directly -- not taken from dsolve.)")
s = sp.Symbol("s")
lhs = (sp.diff(r ** s, r, 2) + sp.diff(r ** s, r) / r
       - (ell ** 2 / r ** 2) * r ** s - (2 * m / hbar ** 2) * (c / r ** 2) * r ** s)
indicial = sp.simplify(sp.expand(lhs * r ** (2 - s)))
print("       indicial equation:", sp.Eq(indicial, 0))
roots = sp.solve(indicial, s)
print("       roots s =", roots)
eff = sp.sqrt(ell ** 2 + 2 * m * c / hbar ** 2)
print("       -> effective exponent ell_eff =", eff,
      " (matches:", sp.simplify(roots[1] - eff) == 0 or sp.simplify(roots[0] - eff) == 0, ")")
print("          smoothness then forces ell_eff in Z, NOT ell in Z.")
print("          So a 1/r^2 or stronger core BREAKS the argument.")
print("          EXACT CONDITION NEEDED:  V = o(1/r^2) as r -> 0.")

print()
print("=" * 74)
print("2. Aharonov-Bohm: what is actually quantized?")
print("   With an EM field the gauge-covariant velocity is")
print("       v = (1/m)(grad S - (q/c) A)")
print("   Single-valuedness of psi = sqrt(rho) exp(iS/hbar) constrains S, not v:")
print("       oint grad S . dl = 2 pi hbar n ,   n in Z")
print("   hence")
print("       oint (m v + (q/c) A) . dl = 2 pi hbar n")
print("       oint m v . dl = 2 pi hbar n - (q/c) Phi ,   Phi = enclosed flux")
print()
hb, q_, Phi, cl = sp.symbols("hbar q Phi c_light", positive=True)
n = sp.Symbol("n", integer=True)
print("   oint m v . dl =", 2 * sp.pi * hb * n - q_ * Phi / cl)
print("   -> a Z-lattice SHIFTED by -q*Phi/c. For generic flux this is NOT")
print("      2*pi*hbar*Z. The quantized object is the CANONICAL circulation,")
print("      which depends on A -- data that (rho, v) does not contain.")
print("      So in this sub-sector the naive target 'oint m v in 2 pi hbar Z'")
print("      is FALSE, not merely unproved.")

print()
print("=" * 74)
print("3. numeric: the leading exponent is |ell| for NON-INTEGER ell too")
print("   f ~ r^|ell| is an r -> 0 statement, so it must be tested THERE.")
print("   (Away from the origin a finite barrier makes f grow exponentially,")
print("    which says nothing about the exponent -- an earlier run of this")
print("    check probed r ~ 0.2-0.6 and measured that growth instead.)")
print("   Method: integrate outward from r0 = 1e-8 with f = r^|ell|, then fit")
print("   the slope of log f vs log r over a decade still inside r << 1.")


def logslope(ellv, V0=400.0, a=1.0, Ev=5.0, r0=1e-8, R=1e-4, N=400000):
    """Return the fitted exponent d log f / d log r over [R/10, R]."""
    rs = np.linspace(r0, R, N)
    h = rs[1] - rs[0]
    y = r0 ** abs(ellv)
    yp = abs(ellv) * r0 ** (abs(ellv) - 1)
    rec_r, rec_y = [], []
    for i in range(N - 1):
        rr = rs[i]
        V = V0 if rr < a else 0.0
        ypp = -yp / rr + (ellv ** 2 / rr ** 2) * y + 2.0 * (V - Ev) * y
        y = y + h * yp
        yp = yp + h * ypp
        if rr >= R / 10.0 and y > 0:
            rec_r.append(rs[i + 1])
            rec_y.append(y)
    lr = np.log(np.array(rec_r))
    ly = np.log(np.array(rec_y))
    return np.polyfit(lr, ly, 1)[0]


ok = True
for ellv in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]:
    s = logslope(ellv)
    err = abs(s - abs(ellv))
    ok &= err < 1e-3
    print("     ell = %-4s  fitted d log f / d log r = %.6f   (|ell| = %.1f, err %.2e)"
          % (ellv, s, abs(ellv), err))
print("   [%s] the exponent equals |ell| for half-integers exactly as for integers."
      % ("PASS" if ok else "FAIL"))
print("      So neither the ODE nor normalisability objects to non-integer ell.")
print("      The obstruction is smoothness of rho ~ (x^2+y^2)^|ell| at the")
print("      origin, which by the nodal lemma holds iff |ell| is in Z_{>=0}.")

print()
print("=" * 74)
print("4. the order-of-limits point -- a LOGICAL argument, not a numeric one")
print("   On a simply connected domain with V = o(1/r^2), every admissible")
print("   SMOOTH state has ell in Z (section 1a + the nodal lemma; section 3")
print("   shows nothing weaker than smoothness will do it).")
print("   The annulus / excised configuration space is the V0 -> infinity limit")
print("   of such problems. Z is closed in R, so any convergent limit of")
print("   integer-ell states has integer ell.")
print("   Hence the annulus's non-integer-circulation states are NOT limits of")
print("   finite-barrier states. They exist only if the excision is performed")
print("   BEFORE the physics rather than as a limit of it.")
print("   No numerical check is offered here: the content is the closedness of")
print("   Z plus section 1a, and a barrier-height sweep would only re-measure")
print("   the exponential growth of section 3's note above.")
