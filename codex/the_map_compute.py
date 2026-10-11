#!/usr/bin/env python3
# Grounding + review cross-check for THE_MAP. The substrate base-3 abscissa
#   sigma(alpha) = log_3 | 1 + 2 cos(pi alpha) |   (r212; kernel-verified exact values).
# No value fitted or searched. Corrections from the 2026-10-11 hand review are folded in.
from mpmath import mp, mpf, cos, pi, log, sqrt
mp.dps = 30
def sigma(a): return log(abs(1 + 2*cos(pi*mpf(a))))/log(3)
phi = (1+sqrt(5))/2

print("mpmath dps =", mp.dps)
print("=== kernel-verified exact sigma identities (r212-r239) ===")
print("  sigma(1/3) = log2/log3 =", mp.nstr(sigma(mpf(1)/3),12),
      " == Cantor Hausdorff dim", mp.nstr(log(2)/log(3),12), " (sigma EQUALS the dimension)")
print("  1+2cos(pi/4) = 1+sqrt2 (silver) =", mp.nstr(1+sqrt(2),12),
      " ; sigma(1/4)=log_3(silver) =", mp.nstr(sigma(mpf(1)/4),12),
      " (silver is the ARGUMENT, not sigma)")
print("  1+2cos(pi/5) = phi^2 =", mp.nstr(phi**2,12),
      " ; sigma(1/5)=2log_3 phi =", mp.nstr(sigma(mpf(1)/5),12),
      " (golden phi in the ARGUMENT)")
print("  sigma at anchors 1/2,1,3/2,5 = 0 ; sigma(2)=1 (zeta pole):",
      [mp.nstr(sigma(a),3) for a in (mpf(1)/2,1,mpf(3)/2,5,2)])
print()
print("=== the nine alpha-skeleton sectors (alpha_X is a POSTULATE) ===")
nine = [("Poincare",mpf(1)),("RH",mpf(3)/2),("YM",mpf(2)),("P",sqrt(2)),
        ("NP",phi+mpf(1)/4),("Hodge",phi),("BSD",3*pi/4),("NS",3*pi/2),("QG",sqrt(2*pi))]
for name,a in nine:
    rat = "rational (closed form)" if name in ("Poincare","RH","YM") else "irrational (numeric)"
    print("  %-9s alpha=%-14s sigma=% .4f   %s" % (name, mp.nstr(a,8), float(sigma(a)), rat))
print()
print("=== obstruction: alpha_NS/alpha_RH = pi (irrational, not in Z[1/3]) ===")
print("  =", mp.nstr((3*pi/2)/(mpf(3)/2), 15))
print()
print("=== density caveat: Z[1/3] dense => ternary-rational law needs a fixed level K ===")
x = mpf('0.137035999')
best=None
for k in range(0,20):
    m=round(x*3**k); e=abs(x-mpf(m)/3**k)
    if best is None or e<best[2]: best=(m,k,e)
print("  0.137036 within", mp.nstr(best[2],3), "of %d/3^%d" % (best[0],best[1]),
      "-> any x ~ m/3^k for large k; law is vacuous unless K fixed in advance")

# --- QG row (filled): primordial spectral tilt P(k) ~ k^{n_s-1} ---
aQG = sqrt(2*pi); sQG = sigma(aQG)
ns, ns_err = mpf('0.9649'), mpf('0.0042')          # Planck 2018
print()
print("=== QG row: predict n_s-1 = sigma(sqrt2pi) vs Planck ===")
print("  sigma(QG) =", mp.nstr(sQG,6), " ; Planck n_s-1 =", mp.nstr(ns-1,6), "+/-", mp.nstr(ns_err,4),
      " ; agreement", mp.nstr(abs(sQG-(ns-1))/ns_err,3), "sigma")
