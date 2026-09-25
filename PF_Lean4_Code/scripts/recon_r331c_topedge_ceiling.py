#!/usr/bin/env python3
"""r331c RECON pass 3 — checks demanded by the root-statement read-back.

(1) min Im xi on [0.01,15] — the number statement A actually needs. Pass 2
    reported the GLOBAL min at t=0.0025, which is below A's range. Real gap.
(2) TOP EDGE: is xi(1/2+15i) real and NEGATIVE, i.e. arg = pi exactly, landing
    on the principal branch cut? If so a slitPlane-shaped top-edge lemma is FALSE
    and the campaign needs a different device there.
(3) The T ceiling: where does arg xi(1+it) first reach pi?
(4) The cancellation in the Lean definition (s(s-1)*Lambda0 + 1)/2.
"""
from mpmath import mp, mpf, mpc, gamma, zeta, pi, power, atan2, mpmathify

mp.dps = 40


def xi(s):
    d = s - 1
    sz = mpf(1) if abs(d) < mpf('1e-30') else d * zeta(s)
    return s * power(pi, -s / 2) * gamma(s / 2) * sz / 2


def Lam0(s):
    # completedRiemannZeta0 = Lambda(s) + 1/s + 1/(1-s), entire
    d = s - 1
    if abs(d) < mpf('1e-30'):
        return None
    return power(pi, -s / 2) * gamma(s / 2) * zeta(s) + 1 / s + 1 / (1 - s)


print("=== (1) min Im xi on A's ACTUAL interval [0.01, 15] ===")
N = 30001
best = None
for i in range(N):
    t = mpf('0.01') + (mpf(15) - mpf('0.01')) * i / (N - 1)
    im = xi(mpc(1, t)).imag
    if best is None or im < best[1]:
        best = (t, im)
print("  min Im on [0.01,15] = %+.6e at t = %.6f" % (float(best[1]), float(best[0])))
print("  Im at t=0.01        = %+.6e" % float(xi(mpc(1, mpf('0.01'))).imag))
print("  Im at t=15          = %+.6e" % float(xi(mpc(1, 15)).imag))
print()

print("=== (2) TOP EDGE sigma in [0,1] at t=15 — is the critical point on the cut? ===")
for sg in ('0', '0.25', '0.5', '0.75', '1'):
    v = xi(mpc(mpf(sg), 15))
    a = atan2(v.imag, v.real)
    print("  sigma=%-5s xi = %+.6e %+.6ei   |Im|=%.3e  arg=%+.6f" %
          (sg, float(v.real), float(v.imag), float(abs(v.imag)), float(a)))
vc = xi(mpc(mpf('0.5'), 15))
print()
print("  AT THE CRITICAL LINE sigma=1/2, t=15:")
print("    Re = %+.10e" % float(vc.real))
print("    Im = %+.10e" % float(vc.imag))
print("    real (|Im| < 1e-30)? : %s" % (abs(vc.imag) < mpf('1e-30')))
print("    negative?            : %s" % (vc.real < 0))
print("    => arg = pi exactly, ON THE BRANCH CUT : %s"
      % (abs(vc.imag) < mpf('1e-30') and vc.real < 0))
print()
print("  Xi(t) = xi(1/2+it) sign change (first zero ~14.1347):")
for t in ('13', '14', '14.1347', '14.2', '15', '21', '21.022', '21.1'):
    v = xi(mpc(mpf('0.5'), mpf(t)))
    print("    t=%-8s Xi = %+.6e" % (t, float(v.real)))
print()

print("=== (3) T ceiling: where does arg xi(1+it) reach pi? ===")
prev = None
cross = None
for i in range(4001):
    t = mpf(30) * i / 4000
    v = xi(mpc(1, t))
    if v.imag <= 0 and t > 0 and v.real < 0:
        cross = t; break
    prev = t
print("  first t>0 with Im<=0 and Re<0 on sigma=1 (arg reaches pi): %s"
      % (("%.4f" % float(cross)) if cross else "none up to t=30"))
mx = max(float(atan2(xi(mpc(1, mpf(15) * i / 2000)).imag,
                     xi(mpc(1, mpf(15) * i / 2000)).real)) for i in range(1, 2001))
print("  max arg on [0,15]  = %.6f  (pi = %.6f, gap %.4f)" % (mx, float(pi), float(pi) - mx))
print()

print("=== (4) cancellation in the Lean definition at s=1+15i ===")
s = mpc(1, 15)
L0 = Lam0(s)
prod = s * (s - 1) * L0
print("  |s(s-1)|        = %.6f" % float(abs(s * (s - 1))))
print("  |Lambda0|       = %.6e" % float(abs(L0)))
print("  s(s-1)*Lambda0  = %+.10e %+.10ei" % (float(prod.real), float(prod.imag)))
print("  +1 then /2      = %+.6e %+.6ei" % (float((prod + 1).real / 2), float((prod + 1).imag / 2)))
print("  digits cancelled in Re: ~%d" % int(abs(mp.log10(abs(prod.real) / abs((prod + 1).real / 2)))))
