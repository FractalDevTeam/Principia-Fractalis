#!/usr/bin/env python3
# Grounding computation for THE_MAP: the substrate base-3 abscissa
#   sigma(alpha) = log_3 | 1 + 2 cos(pi alpha) |   (r212; kernel-verified exact values)
# and the trace-range / obstruction facts. No value is fitted or searched.
from mpmath import mp, mpf, cos, pi, log, sqrt
mp.dps = 30

def sigma(a):
    return log(abs(1 + 2*cos(pi*mpf(a)))) / log(3)

phi = (1+sqrt(5))/2
print("mpmath dps =", mp.dps)
print("=== kernel-verified exact sigma values (r212-r239), numeric cross-check ===")
table = [
    ("1/3  Cantor Hausdorff dim log2/log3", mpf(1)/3, log(2)/log(3)),
    ("1/4  silver  log_3(1+sqrt2)",          mpf(1)/4, log(1+sqrt(2))/log(3)),
    ("1/5  golden  2 log_3 phi",             mpf(1)/5, 2*log(phi)/log(3)),
    ("2/5  golden  log_3 phi",               mpf(2)/5, log(phi)/log(3)),
    ("1/2  anchor  0",                        mpf(1)/2, mpf(0)),
    ("1    Poincare 0",                       mpf(1),   mpf(0)),
    ("3/2  RH       0",                        mpf(3)/2, mpf(0)),
    ("2    YM       1 (zeta pole)",            mpf(2),   mpf(1)),
    ("5    HN       0",                        mpf(5),   mpf(0)),
]
for name, a, claimed in table:
    s = sigma(a)
    ok = "OK" if abs(s - claimed) < mpf('1e-25') else "MISMATCH"
    print("  sigma(%-32s) = % .12f   closed-form %s %s" % (name, float(s), mp.nstr(claimed,8), ok))
print()
print("=== obstruction: alpha_NS/alpha_RH = (3pi/2)/(3/2) = pi (irrational, not in Z[1/3]) ===")
print("  =", mp.nstr((3*pi/2)/(mpf(3)/2), 15))
print("=== structural law: trace of level-k projections in Z[1/3] cap [0,1] = {m/3^k} ===")
for k in range(5):
    print("  level %d: multiples of 1/3^%d = %s" % (k, k, mp.nstr(mpf(1)/3**k, 8)))
