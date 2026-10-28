#!/usr/bin/env python3
"""Independently recompute the nine-sector sigma table of THE_MAP_2026-10-11.md.

sigma(alpha) = log_3 |1 + 2 cos(pi alpha)|

Verdicts are computed from residuals against the document's stated values, not
printed as strings.
"""
from decimal import Decimal, getcontext
from mpmath import mp, mpf, cos, log, pi, sqrt, fabs

mp.dps = 40

PHI = (1 + sqrt(5)) / 2

# sector, alpha expression, alpha value, sigma as STATED in THE_MAP
ROWS = [
    ("Poincare", "1",          mpf(1),              mpf("0")),
    ("RH",       "3/2",        mpf(3) / 2,          mpf("0")),
    ("Yang-Mills","2",         mpf(2),              mpf("1")),
    ("P",        "sqrt(2)",    sqrt(2),             mpf("-0.692")),
    ("NP",       "phi + 1/4",  PHI + mpf(1) / 4,    mpf("0.947")),
    ("Hodge",    "phi",        PHI,                 mpf("0.496")),
    ("BSD",      "3*pi/4",     3 * pi / 4,          mpf("0.571")),
    ("NS",       "3*pi/2",     3 * pi / 2,          mpf("-1.308")),
    ("QG",       "sqrt(2*pi)", sqrt(2 * pi),        mpf("-0.039")),
]


def sigma(alpha):
    m = fabs(1 + 2 * cos(pi * alpha))
    if m == 0:
        return None  # log of zero: sigma is -infinity, a real distinction
    return log(m) / log(3)


print(f"{'sector':<11}{'alpha':<12}{'sigma computed':>20}{'stated':>12}{'resid':>12}  ok")
print("-" * 80)
worst = mpf(0)
nbad = 0
for name, expr, a, stated in ROWS:
    s = sigma(a)
    if s is None:
        print(f"{name:<11}{expr:<12}{'-inf (modulus 0)':>20}{str(stated):>12}{'n/a':>12}  CHECK")
        nbad += 1
        continue
    resid = fabs(s - stated)
    # stated values are given to 3dp, so tolerance is half a unit in the last place
    ok = resid <= mpf("0.0005")
    if not ok:
        nbad += 1
    worst = max(worst, resid)
    print(f"{name:<11}{expr:<12}{mp.nstr(s, 12):>20}{str(stated):>12}"
          f"{mp.nstr(resid, 3):>12}  {'ok' if ok else 'MISMATCH'}")

print("-" * 80)
print(f"worst residual = {mp.nstr(worst, 6)}   rows failing = {nbad}")

# --- the closed forms claimed as PROVEN, checked independently ---
print("\nclosed-form identities claimed PROVEN (r234-r239):")
checks = [
    ("sigma(1/3) = Cantor dim log2/log3", sigma(mpf(1) / 3), log(2) / log(3)),
    ("sigma(1/4) = log_3(1+sqrt2)",       sigma(mpf(1) / 4), log(1 + sqrt(2)) / log(3)),
    ("sigma(1/5) = 2 log_3 phi",          sigma(mpf(1) / 5), 2 * log(PHI) / log(3)),
    ("sigma(2/5) = log_3 phi",            sigma(mpf(2) / 5), log(PHI) / log(3)),
    ("sigma(2)   = 1",                    sigma(mpf(2)),     mpf(1)),
]
for label, got, want in checks:
    r = fabs(got - want)
    print(f"  {label:<36} resid {mp.nstr(r, 3):>12}  {'ok' if r < mpf('1e-30') else 'MISMATCH'}")

# --- the QG row, the one claimed hit ---
print("\nQG row (the one claimed hit):")
s_qg = sigma(sqrt(2 * pi))
ns_meas, ns_err = mpf("-0.0351"), mpf("0.0042")
dev = (s_qg - ns_meas) / ns_err
print(f"  predicted n_s - 1 = {mp.nstr(s_qg, 8)}")
print(f"  Planck 2018        = {ns_meas} +/- {ns_err}")
print(f"  deviation          = {mp.nstr(fabs(dev), 3)} sigma")

# --- the NS row, the claimed miss ---
print("\nNS row (the claimed miss):")
s_ns = sigma(3 * pi / 2)
print(f"  predicted      = {mp.nstr(s_ns, 8)}")
print(f"  Kolmogorov -5/3= {mp.nstr(mpf(-5)/3, 8)}")
print(f"  difference     = {mp.nstr(fabs(s_ns - mpf(-5)/3), 4)}")
print(f"  IK -3/2        = -1.5, difference {mp.nstr(fabs(s_ns + mpf(3)/2), 4)}")
