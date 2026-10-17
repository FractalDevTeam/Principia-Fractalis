#!/usr/bin/env python3
"""Does the Fourier integrand's |D2| <= M bound close cleanly?

The one structural difference from the Hardy thetaTerm is the e^u INSIDE the
exponential: thetaTerm has e^{-pi n^2 u}, the Fourier term has e^{-pi n^2 e^u}.
Differentiating the latter brings (pi n^2 e^u) factors, so D2 carries
(pi n^2 e^u)^2 -- which at u=3/2, n=3 is ~16000. The question is whether the
exponential crushes it.

g_n(u,t) = A(u) * B_n(u) * C(u,t)
   A = e^{u/2} + 1         A'  = (1/2)e^{u/2}        A'' = (1/4)e^{u/2}
   B = e^{-pi n^2 e^u}     B'  = -(pi n^2 e^u) B     B'' = (pi n^2 e^u)((pi n^2 e^u) - 1) B
   C = cos(t u / 2)        C'  = -(t/2) sin          C'' = -(t^2/4) cos

Provable majorant (|C|,|sin| <= 1, each factor at its worst on the segment):
   |g''| <= Bmax * [ A''  + A*P*(P+1) + A*t^2/4 + 2*A'*P + A'*t + A*P*t ]
with P = pi n^2 e^u at the segment's RIGHT end, A,A',A'' at the right end,
Bmax = e^{-pi n^2 e^u} at the segment's LEFT end.
"""
from mpmath import mp, mpf, exp, cos, pi, diff, fabs
import math

mp.dps = 30
NT = 3


def g(u, t):
    u = mpf(u)
    return (exp(u / 2) + 1) * sum(exp(-pi * n ** 2 * exp(u)) for n in range(1, NT + 1)) \
        * cos(mpf(t) * u / 2)


def measured_M2(lo, hi, t, n=120):
    best = mpf(0)
    for i in range(n + 1):
        u = lo + (hi - lo) * mpf(i) / n
        v = fabs(diff(lambda z: g(z, t), u, 2))
        if v > best:
            best = v
    return best


def majorant_M2(lo, hi, t):
    """Clean provable majorant on [lo,hi], summed over n = 1..3."""
    t = mpf(t)
    A = exp(hi / 2) + 1
    Ap = exp(hi / 2) / 2
    App = exp(hi / 2) / 4
    tot = mpf(0)
    for n in range(1, NT + 1):
        P = pi * n ** 2 * exp(hi)              # worst (largest) at right end
        Bmax = exp(-pi * n ** 2 * exp(lo))     # worst (largest) at left end
        tot += Bmax * (App + A * P * (P + 1) + A * t ** 2 / 4
                       + 2 * Ap * P + Ap * t + A * P * t)
    return tot


SEGS = [(mpf(k) / 4, mpf(k + 1) / 4) for k in range(6)]

for t, B in [(mpf(13), mpf("1.407e-5")), (mpf("14.5"), mpf("1.877e-6"))]:
    print("=" * 88)
    print("t = %s,  gate-1 budget B = %.3e" % (t, float(B)))
    print("%-14s %-16s %-16s %-10s %-12s" % ("segment", "measured M2", "majorant M2", "loose", "panels n_i"))
    tot_meas = tot_maj = 0
    npanels_maj = npanels_meas = 0
    for lo, hi in SEGS:
        m = measured_M2(lo, hi, t)
        j = majorant_M2(lo, hi, t)
        # per-segment budget B/6 ; error_i = M_i w^3/(24 n_i^2), w = 1/4
        w = hi - lo
        ni = math.ceil(math.sqrt(float(j * w ** 3 / (24 * (B / 6)))))
        nm = math.ceil(math.sqrt(float(m * w ** 3 / (24 * (B / 6)))))
        npanels_maj += ni
        npanels_meas += nm
        print("%-14s %-16.4e %-16.4e %-10.1fx %-12d"
              % ("[%s,%s]" % (lo, hi), float(m), float(j), float(j / m), ni))
    print("  total panels with PROVABLE per-segment M : %d" % npanels_maj)
    print("  total panels with MEASURED per-segment M : %d  (floor)" % npanels_meas)
    gM = majorant_M2(mpf(0), mpf(3) / 2, t)
    n_glob = math.ceil(math.sqrt(float(gM * (mpf(3) / 2) ** 3 / (24 * B))))
    print("  for contrast, ONE interval with a GLOBAL majorant: %d panels" % n_glob)

print()
print("=" * 88)
print("does the e^u inside the exponential break the bound? NO -- here is why:")
for n in range(1, 4):
    P = float(pi * n ** 2 * exp(mpf(3) / 2))
    Bm = float(exp(-pi * n ** 2 * exp(mpf(3) / 2)))
    print("  n=%d at u=3/2 : (pi n^2 e^u)^2 = %.3e   but e^{-pi n^2 e^u} = %.3e"
          % (n, P ** 2, Bm))
    print("        product  = %.3e" % (P ** 2 * Bm))
print("  -> the exponential beats the polynomial by tens of orders. The n>=2")
print("     terms are numerically irrelevant; only n=1 near u=0 matters.")
