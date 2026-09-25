#!/usr/bin/env python3
"""r331c RECON — right edge sigma = 1, t in [0,15].

Tests the two staged targets named in RiemannXiThetaBoxEnclosure_r331a.lean:32-34
    RIGHT LOW  : Re xi(1+it) > 1/1000
    RIGHT HIGH : Im xi(1+it) > 1/20000

Disprove-before-prove (FLT lessons section 5): reviewers who compute beat
reviewers who argue. This runs BEFORE any Lean proof work.

xi(s) = (s(s-1)*Lambda0(s) + 1)/2  with Lambda0 = completedRiemannZeta0.
Since Lambda0(s) = Lambda(s) + 1/s + 1/(1-s), this collapses to the classical
    xi(s) = s(s-1)*Lambda(s)/2,   Lambda(s) = pi^(-s/2) Gamma(s/2) zeta(s)
which is what we evaluate (mpmath has all three factors to arbitrary precision).
"""
import sys
try:
    from mpmath import mp, mpf, mpc, gamma, zeta, pi, power
except ImportError:
    print("mpmath not available"); sys.exit(2)

mp.dps = 40


def Lam(s):
    return power(pi, -s / 2) * gamma(s / 2) * zeta(s)


def xi(s):
    # s(s-1)*Lambda(s)/2, written so the removable singularity at s=1 is safe:
    # (s-1)*zeta(s) is entire with value 1 at s=1.
    d = s - 1
    if abs(d) < mpf('1e-30'):
        sz = mpf(1)                      # lim_{s->1} (s-1) zeta(s) = 1
    else:
        sz = d * zeta(s)
    return s * power(pi, -s / 2) * gamma(s / 2) * sz / 2


def scan(n=1501):
    lo_re = None; lo_im = None
    rows = []
    for i in range(n):
        t = mpf(15) * i / (n - 1)
        v = xi(mpc(1, t))
        re, im = v.real, v.imag
        rows.append((t, re, im))
        if lo_re is None or re < lo_re[1]:
            lo_re = (t, re)
        if lo_im is None or im < lo_im[1]:
            lo_im = (t, im)
    return rows, lo_re, lo_im


rows, lo_re, lo_im = scan()

TGT_RE = mpf(1) / 1000
TGT_IM = mpf(1) / 20000

print("=== r331c RIGHT EDGE RECON: sigma = 1, t in [0,15], %d samples ===" % len(rows))
print()
print("xi(1)        = %s   (expect exactly 1/2: s(s-1)=0 so xi=(0+1)/2)" % xi(mpc(1, 0)))
print()
print("--- RIGHT LOW target: Re xi(1+it) > 1/1000 ---")
print("  min Re over scan : %.12e   at t = %.6f" % (float(lo_re[1]), float(lo_re[0])))
print("  target           : %.12e" % float(TGT_RE))
print("  VERDICT          : %s" % ("HOLDS on the scan (margin %.3e)" % float(lo_re[1] - TGT_RE)
                                   if lo_re[1] > TGT_RE else "*** FAILS ***"))
print()
print("--- RIGHT HIGH target: Im xi(1+it) > 1/20000 ---")
print("  min Im over scan : %.12e   at t = %.6f" % (float(lo_im[1]), float(lo_im[0])))
print("  target           : %.12e" % float(TGT_IM))
print("  VERDICT          : %s" % ("HOLDS (margin %.3e)" % float(lo_im[1] - TGT_IM)
                                   if lo_im[1] > TGT_IM else "*** FAILS ***"))
print()
print("  Im at the endpoints:")
for t in (0, mpf('0.001'), mpf('0.01'), mpf('0.1'), 1, 15):
    v = xi(mpc(1, mpf(t)))
    print("    t=%-8s Im = %+.6e   Re = %+.6e" % (str(t), float(v.imag), float(v.real)))
print()
# where does Im first exceed the target?
first = None
for (t, re, im) in rows:
    if im > TGT_IM:
        first = t; break
print("  first scan point with Im > 1/20000 : t = %s" % (("%.6f" % float(first)) if first else "NONE"))
print()
print("--- sector/argument geometry (what the winding argument actually needs) ---")
minre = min(r[1] for r in rows)
print("  min Re over [0,15]        : %+.6e" % float(minre))
print("  Re > 0 everywhere?        : %s" % (minre > 0))
maxabsarg = max(abs(float(mp.atan2(r[2], r[1]))) for r in rows)
print("  max |arg xi(1+it)|        : %.6f rad  (pi/2 = %.6f)" % (maxabsarg, float(pi / 2)))
print("  stays in open right half-plane (no principal-log wrap)? : %s"
      % (minre > 0 and maxabsarg < float(pi / 2)))
print()
print("  |xi| range: min %.4e  max %.4e"
      % (min(float(abs(mpc(r[1], r[2]))) for r in rows),
         max(float(abs(mpc(r[1], r[2]))) for r in rows)))
