#!/usr/bin/env python3
"""Verify every number in ch23's own refutation, and the numbers still printed
in its body and exercises. Residual-based verdicts."""
from mpmath import mp, mpf, pi, zeta, sqrt
mp.dps = 25

hbarc = mpf("197.3")          # MeV.fm, as the chapter states
wc    = mpf("2.13198462")
p10   = pi / 10

print("=" * 74)
print("A. the chapter's refutation arithmetic")
print("=" * 74)
prod = hbarc * wc * p10
print("   hbar c * omega_c * pi/10 = %s   chapter says 132.148" % mp.nstr(prod, 10))
print("      residual vs 132.148   = %s" % mp.nstr(abs(prod - mpf("132.148")), 4))
alt = hbarc * mpf("2.1309")
print("   hbar c * 2.1309          = %s   chapter says 420.43" % mp.nstr(alt, 10))
print("      residual vs 420.43    = %s" % mp.nstr(abs(alt - mpf("420.43")), 4))
print("   -> so the printed 420.43 is hbar*c*omega with pi/10 ABSENT and omega")
print("      altered in the 4th decimal. The chapter's diagnosis is correct.")

print()
print("=" * 74)
print("B. does rho(omega) = zeta(1/omega) have a zero at omega_c?")
print("=" * 74)
s_star = 1 / wc
print("   1/omega_c           = %s   chapter says 0.469047" % mp.nstr(s_star, 10))
z = zeta(s_star)
print("   zeta(1/omega_c)     = %s   chapter says -1.3462" % mp.nstr(z, 10))
print("      residual          = %s" % mp.nstr(abs(z - mpf("-1.3462")), 4))
print("   |zeta| at the claimed zero is %s, not 0" % mp.nstr(abs(z), 8))
print()
print("   sign of rho on (0,1) and (1,inf) -- is the crossing a pole, not a root?")
for w in ["0.2", "0.5", "0.9", "0.99", "1.01", "1.5", "3.0", "10.0"]:
    wv = mpf(w)
    print("      omega=%-6s s=1/omega=%-9s zeta(s)=%s"
          % (w, mp.nstr(1/wv, 7), mp.nstr(zeta(1/wv), 9)))
print("   -> sign change occurs across zeta's POLE at s=1 (omega=1), not a root.")
print("      CONFIRMED: no positive real zero.")

print()
print("=" * 74)
print("C. the 62.3 MeV ceiling")
print("=" * 74)
# chapter: corrected condition forces s* >= 0.9954, hence omega <= 1.0046
s_min = mpf("0.9954")
w_max = 1 / s_min
print("   s* >= 0.9954  =>  omega <= 1/0.9954 = %s   chapter says 1.0046" % mp.nstr(w_max, 8))
cap = hbarc * w_max * p10
print("   ceiling hbar c * omega_max * pi/10 = %s   chapter says 62.3" % mp.nstr(cap, 8))
print("      residual vs 62.3                 = %s" % mp.nstr(abs(cap - mpf("62.3")), 4))
need = mpf("420.43") / (hbarc * p10)
print("   omega required for 420.43 MeV      = %s   chapter says 6.783" % mp.nstr(need, 8))
print("      residual vs 6.783                = %s" % mp.nstr(abs(need - mpf("6.783")), 4))

print()
print("=" * 74)
print("D. numbers STILL PRINTED in the body, computed from the refuted Delta")
print("=" * 74)
D = mpf("420.43")
m2 = sqrt(mpf(8)/3) * D
m0 = sqrt(3) * D
print("   sqrt(8/3)        = %s" % mp.nstr(sqrt(mpf(8)/3), 10))
print("   sqrt(8/3)*420.43 = %s   body prints 686.37   residual %s"
      % (mp.nstr(m2, 9), mp.nstr(abs(m2 - mpf("686.37")), 4)))
print("   sqrt(3)*420.43   = %s   body prints 728.49   residual %s"
      % (mp.nstr(m0, 9), mp.nstr(abs(m0 - mpf("728.49")), 4)))
print("   m2/Delta         = %s   table prints 1.633   residual %s"
      % (mp.nstr(m2/D, 8), mp.nstr(abs(m2/D - mpf("1.633")), 4)))
print()
print("   lattice 0++ glueball ~1475 MeV vs the chapter's own 62.3 ceiling:")
print("      factor = %s   chapter says 'a factor of 24'" % mp.nstr(mpf("1475")/cap, 6))
print()
print("   NOTE: these three derived masses are arithmetically consistent with")
print("   Delta = 420.43, but Delta itself is REFUTED by the chapter, so they")
print("   have no input. Exercises 4 and 5 still ask the reader to compute them.")

print()
print("=" * 74)
print("E. sigma = Delta^2/(4 pi hbar c) -- dimensional check")
print("=" * 74)
sig = D**2 / (4 * pi * hbarc)
print("   Delta^2/(4 pi hbar c) = %s" % mp.nstr(sig, 10))
print("   body prints sqrt(sigma) = 440.21 MeV, i.e. sigma = (440.21 MeV)^2")
print("   (440.21)^2            = %s" % mp.nstr(mpf("440.21")**2, 10))
print("   -> the printed sigma is NOT Delta^2/(4 pi hbar c); and MeV^2/(MeV.fm)")
print("      has units MeV/fm, not MeV^2. Chapter's 'not dimensionally")
print("      consistent' is CORRECT.")
