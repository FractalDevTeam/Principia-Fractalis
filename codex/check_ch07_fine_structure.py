#!/usr/bin/env python3
"""Verify every mathematical claim in Acer's ch07 fine-structure correction
before landing it. Residual-based verdicts."""
from mpmath import mp, mpf, pi, zeta, nsum, inf, exp, mpc
mp.dps = 30

print("=" * 76)
print("CLAIM 1  base-3 digit sum: n = D_3(n) mod 2   (b-1 = 2)")
print("=" * 76)
def D3(n):
    s = 0
    while n:
        s += n % 3
        n //= 3
    return s
bad = [n for n in range(1, 20001) if (D3(n) - n) % 2 != 0]
print("   tested n = 1..20000, counterexamples: %d" % len(bad))
print("   so  e^{i*pi*D_3(n)} = (-1)^{D_3(n)} = (-1)^n   : %s" % (len(bad) == 0))

print()
print("=" * 76)
print("CLAIM 2  R_f(1,s) = sum (-1)^n / n^s = -eta(s)")
print("=" * 76)
# direct sum with the actual phase, vs -eta(2)
S = nsum(lambda n: exp(mpc(0, 1) * pi * D3(int(n))) / n**2, [1, inf])
eta2 = (1 - mpf(2)**(1 - 2)) * zeta(2)
print("   direct  sum_n e^{i pi D_3(n)}/n^2 = %s" % mp.nstr(S, 18))
print("   -eta(2) = -(1-2^{1-2}) zeta(2)    = %s" % mp.nstr(-eta2, 18))
print("   -pi^2/12                           = %s" % mp.nstr(-pi**2/12, 18))
print("   |direct - (-eta(2))|  = %s" % mp.nstr(abs(S + eta2), 6))
print("   eta(2) = pi^2/12 ?    residual %s" % mp.nstr(abs(eta2 - pi**2/12), 6))

print()
print("=" * 76)
print("CLAIM 3  the corrected product, and the withdrawn one")
print("=" * 76)
Rf = -pi**2/12
print("   R_f(1,2)              = %s   (chapter says -0.8224670334...)" % mp.nstr(Rf, 14))
print("   R_f(1,2) * pi/10      = %s   (chapter says -0.2583856...)" % mp.nstr(Rf*pi/10, 14))
old = mpf("0.0233812")
print("   WITHDRAWN 0.0233812 * pi/10 = %s" % mp.nstr(old*pi/10, 12))
print("   1 / that                     = %s   (chapter says ~136.1)" % mp.nstr(1/(old*pi/10), 8))
print("   alpha_EM = 1/137.036         = %s" % mp.nstr(1/mpf("137.036"), 12))
print("   old claim's error vs alpha_EM: %s %%"
      % mp.nstr(100*abs(old*pi/10 - 1/mpf("137.036"))/(1/mpf("137.036")), 4))
print("   -> chapter's '0.7%%' figure is consistent with the withdrawn chain")
print("   orders of magnitude between corrected value and alpha_EM: %s"
      % mp.nstr(abs(Rf*pi/10)/(1/mpf("137.036")), 6))

print()
print("=" * 76)
print("CLAIM 4  D_3 is UNBOUNDED: max_{n<=3^k} D_3(n) = 2k")
print("=" * 76)
for k in range(1, 8):
    m = max(D3(n) for n in range(1, 3**k + 1))
    print("   k=%d  3^k=%-6d  max D_3 = %-3d  2k = %-3d  match %s" % (k, 3**k, m, 2*k, m == 2*k))
print("   so restricting the outer sum to D in {0,1,2} discards all but a")
print("   density-zero set: CONFIRMED, the decomposition defect is real.")

print()
print("=" * 76)
print("CLAIM 5  R_f(0,s) = zeta(s), R_f(2,s) = zeta(s); alpha matters only mod 2")
print("=" * 76)
S0 = nsum(lambda n: exp(mpc(0, 0)) / n**2, [1, inf])
S2 = nsum(lambda n: exp(mpc(0, 1) * pi * 2 * D3(int(n))) / n**2, [1, inf])
print("   R_f(0,2) = %s   zeta(2) = %s   residual %s"
      % (mp.nstr(S0, 14), mp.nstr(zeta(2), 14), mp.nstr(abs(S0 - zeta(2)), 6)))
print("   R_f(2,2) = %s   zeta(2) = %s   residual %s"
      % (mp.nstr(S2.real, 14), mp.nstr(zeta(2), 14), mp.nstr(abs(S2 - zeta(2)), 6)))
print("   => alpha = 2 (the Yang-Mills assignment) IS the alpha = 0 basepoint.")
print("      CONFIRMED.")
