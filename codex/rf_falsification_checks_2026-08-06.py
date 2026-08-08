#!/usr/bin/env python3
"""Independent re-check of the three falsifications reported by the audit.

Definitions taken verbatim from the book:
  ch03:49   D_3(n) = sum of base-3 digits of n
  ch03:93   R_f(alpha, s) = sum_{n>=1} e^{i pi alpha D_3(n)} / n^s
"""
import numpy as np, mpmath as mp
mp.mp.dps = 30

print("=" * 74)
print("0. digit-block identity  sum_{n<3^k} w^{D_3(n)} = (1+w+w^2)^k   [the tool]")
print("=" * 74)
ds = np.zeros(1, dtype=np.int16)
for k in range(1, 13):
    ds = np.concatenate([ds, ds + 1, ds + 2])
    if k in (3, 6, 9, 12):
        w = np.exp(1j * np.pi * 1.5)                      # alpha = 3/2  ->  w = -i
        lhs = np.sum(w ** ds.astype(np.float64))
        rhs = (1 + w + w * w) ** k
        print(f"  k={k:2d}  lhs={lhs:.10f}  rhs={rhs:.10f}  diff={abs(lhs-rhs):.2e}")

print()
print("=" * 74)
print("1. ch03:255 / ch09:202  'R_f(3/2, 1/2+it) = 0  <=>  zeta(1/2+it) = 0'")
print("=" * 74)
K = 15                                                     # n < 3^15 = 14 348 907
ds = np.zeros(1, dtype=np.int16)
for _ in range(K):
    ds = np.concatenate([ds, ds + 1, ds + 2])
phase = np.exp(1j * np.pi * 1.5 * ds.astype(np.float64))   # e^{i pi alpha D_3(n)}
del ds
zeros = [mp.mpf(str(z)) for z in
         ("14.134725141734693", "21.022039638771555", "25.010857580145688",
          "30.424876125859513", "32.935061587739190")]
print(f"  direct summation, n < 3^{K} = {3**K}, checked for stability at 3^13")
print(f"  {'gamma':>20} {'|R_f| at 3^13':>16} {'|R_f| at 3^15':>16}   verdict")
NN = np.arange(1, 3 ** K, dtype=np.float64)
cut13 = 3 ** 13 - 1
for g in zeros:
    s = 0.5 + 1j * float(g)
    terms = phase[1:] * NN ** (-s)
    v13 = np.sum(terms[:cut13]); v15 = np.sum(terms)
    verdict = "ZERO" if abs(v15) < 1e-2 else "NOT zero"
    print(f"  {float(g):>20.9f} {abs(v13):>16.6f} {abs(v15):>16.6f}   {verdict}")
del terms

print()
print("  where R_f(3/2, .) actually does vanish on the line (scan t in [0,35]):")
ts = np.arange(0.5, 35.0, 0.25)
vals = np.array([abs(np.sum(phase[1:] * NN ** (-(0.5 + 1j * t)))) for t in ts])
loc = [ts[i] for i in range(1, len(ts) - 1)
       if vals[i] < vals[i - 1] and vals[i] < vals[i + 1] and vals[i] < 0.35]
print(f"    local minima with |R_f| < 0.35 at t = {[round(t,2) for t in loc]}")
print(f"    zeta ordinates in the same range = {[round(float(z),3) for z in zeros]}")
del phase, NN

print()
print("=" * 74)
print("2. ch24:512  'Sha bound'  |Sha(E)| <= [R_f(pi, N_E)]^2")
print("=" * 74)
print("  alpha = pi  ->  phase = e^{i pi^2 D_3(n)}, |n^{-N_E}| tiny for N_E >= 11")
for NE, label, sha in ((11, "11a1", 1), (571, "571a1", 4), (681, "681c1", 9)):
    tot = mp.mpc(0)
    for n in range(1, 60):
        d = 0; m = n
        while m: d += m % 3; m //= 3
        tot += mp.e ** (1j * mp.pi * mp.pi * d) / mp.mpf(n) ** NE
    b = abs(tot) ** 2
    print(f"  N_E={NE:>5} ({label:>6})  bound = |R_f(pi,N_E)|^2 = {mp.nstr(b, 12)}"
          f"   actual |Sha| = {sha}   {'HOLDS' if sha <= b else 'VIOLATED'}")

print()
print("=" * 74)
print("3. ch23:335/342  rho(omega) = Re[R_f(2, 1/omega)],  claimed zero omega_c")
print("=" * 74)
print("  alpha = 2  ->  e^{2 pi i D_3(n)} = 1 for every n, so R_f(2,s) = zeta(s)")
chk = sum(mp.e ** (2j * mp.pi * sum(int(d) for d in mp.nstr(0, 1))) for _ in [])  # noqa
for w in ("0.25", "0.50", "0.90", "1.10", "2.13198462", "3.00", "10.0"):
    w = mp.mpf(w)
    print(f"    omega={float(w):>12}   1/omega={float(1/w):>10.6f}"
          f"   rho = zeta(1/omega) = {mp.nstr(mp.re(mp.zeta(1/w)), 12)}")
print()
print("  real zeros of zeta are the trivial ones at s = -2,-4,-6,...")
print("  1/omega = -2  =>  omega = -0.5 < 0.  So rho has NO zero for omega > 0.")
print(f"  at the claimed omega_c = 2.13198462:  rho = "
      f"{mp.nstr(mp.re(mp.zeta(1/mp.mpf('2.13198462'))), 12)}  (not 0)")
print("  omega = 1 is a POLE of rho (zeta's pole at s=1), not a zero;")
print("  rho > 0 on (0,1) since 1/omega > 1, and rho < 0 on (1,inf) since")
print("  zeta < 0 on (0,1).  Sign change is through the pole, not a root.")
