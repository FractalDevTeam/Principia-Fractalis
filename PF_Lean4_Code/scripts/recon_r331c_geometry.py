#!/usr/bin/env python3
"""r331c RECON pass 2 — what is ACTUALLY true on the right edge sigma=1, t in [0,15].

Pass 1 refuted both staged targets. This pass finds the true geometry, which is
what the winding / principal-log argument actually needs: xi must avoid the
NEGATIVE REAL AXIS along the contour, not stay in a half-plane.
"""
from mpmath import mp, mpf, mpc, gamma, zeta, pi, power, atan2, fabs

mp.dps = 40


def xi(s):
    d = s - 1
    sz = mpf(1) if abs(d) < mpf('1e-30') else d * zeta(s)
    return s * power(pi, -s / 2) * gamma(s / 2) * sz / 2


N = 6001
rows = []
for i in range(N):
    t = mpf(15) * i / (N - 1)
    v = xi(mpc(1, t))
    rows.append((t, v.real, v.imag))

print("=== r331c RIGHT EDGE, pass 2: %d samples, dps=%d ===" % (N, mp.dps))
print()

# 1. Im positivity away from 0
print("--- Im xi(1+it): sign structure ---")
neg_im = [(t, im) for (t, re, im) in rows if im <= 0]
print("  samples with Im <= 0 : %d  %s" % (len(neg_im), [("t=%.4f" % float(t)) for t, _ in neg_im[:5]]))
for d in ('0.001', '0.01', '0.1', '0.5', '1.0'):
    dd = mpf(d)
    sub = [im for (t, re, im) in rows if t >= dd]
    print("  min Im on [%-5s,15] = %+.6e" % (d, float(min(sub))))
print()

# 2. Re sign structure
print("--- Re xi(1+it): sign structure ---")
neg_re = [(t, re) for (t, re, im) in rows if re <= 0]
if neg_re:
    print("  Re <= 0 on %d samples, first at t = %.4f, last at t = %.4f"
          % (len(neg_re), float(neg_re[0][0]), float(neg_re[-1][0])))
    print("  min Re = %+.6e" % float(min(r[1] for r in rows)))
else:
    print("  Re > 0 throughout")
print()

# 3. THE ACTUAL REQUIREMENT: distance from the negative real axis
#    xi hits the negative real axis iff Im = 0 and Re < 0.
print("--- negative-real-axis avoidance (what the principal log needs) ---")
worst = None
for (t, re, im) in rows:
    if re < 0:
        d = abs(im)          # distance to the axis when in the left half plane
    else:
        d = mpf(0) if False else (im if im >= 0 else -im)
        d = (re**2 + im**2) ** mpf('0.5') if im == 0 else abs(im)
    if worst is None or d < worst[1]:
        worst = (t, d, re, im)
print("  closest approach to the negative real axis:")
print("    t = %.6f   |Im| = %.6e   Re = %+.6e" % (float(worst[0]), float(worst[1]), float(worst[2])))
args = [atan2(im, re) for (t, re, im) in rows]
print("  arg range: [%.6f, %.6f] rad   (pi = %.6f)" % (float(min(args)), float(max(args)), float(pi)))
print("  crosses the negative real axis? : %s"
      % any(re < 0 and im == 0 for (t, re, im) in rows))
print()

# 4. candidate provable targets
print("--- CANDIDATE ROOT STATEMENTS (with margins) ---")
for d in ('0.01', '0.05', '0.1'):
    dd = mpf(d)
    sub = [im for (t, re, im) in rows if t >= dd]
    print("  Im xi(1+it) > 0 on [%s, 15]   min = %+.6e" % (d, float(min(sub))))
sub_all = [im for (t, re, im) in rows if t > 0]
print("  Im xi(1+it) > 0 on (0, 15]     min = %+.6e" % float(min(sub_all)))
print()
print("  Re xi(1) = %.6f  (t=0 endpoint is real and positive)" % float(rows[0][1]))
print()
print("--- corner consistency with r331b (top edge, t=15) ---")
v = xi(mpc(1, 15))
print("  xi(1+15i) = %+.6e %+.6ei" % (float(v.real), float(v.imag)))
print("  r331b asserts Re xi(sigma+15i) < -1e-4 for sigma in [1/2,1]; at sigma=1: %s"
      % ("CONSISTENT" if v.real < -mpf(1)/10000 else "INCONSISTENT"))
