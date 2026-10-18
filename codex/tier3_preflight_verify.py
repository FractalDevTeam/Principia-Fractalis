#!/usr/bin/env python3
"""
Tier-3 pre-flight measurements (codex/TIER3_PREFLIGHT_2026-10-18.md).

Two questions the gap list turns on:
  Q1  Is F_plus convex on [0,inf)?  If F_plus'' changes sign, the cheap
      integrability route (integrableOn_Ioi_deriv_of_nonneg, which needs a SIGN
      on the derivative) does NOT transfer from the first-order proof.
  Q2  What are the new boundary constants a second IBP introduces?

F_plus u = exp(u/2) * omega(exp u),  omega(x) = sum_{n>=1} exp(-pi n^2 x).
"""
import mpmath as mp

mp.mp.dps = 30


def omega(x):
    return mp.nsum(lambda n: mp.e**(-mp.pi * n * n * x), [1, mp.inf])


def F_plus(u):
    return mp.e**(u / 2) * omega(mp.e**u)


def F_minus(u):
    return omega(mp.e**u)


print("=" * 72)
print("Q1 - is F_plus convex?  (sign of D2 decides the integrability route)")
print("=" * 72)
print(f"{'u':>5} {'F+':>14} {'D1 F+':>14} {'D2 F+':>14} {'sgn D2':>7}")
signs = []
for k in range(0, 17):
    u = mp.mpf(k) / 4
    d1, d2 = mp.diff(F_plus, u, 1), mp.diff(F_plus, u, 2)
    s = '+' if d2 > 0 else '-'
    signs.append(s)
    if k <= 8 or k % 4 == 0:
        print(f"{float(u):>5.2f} {float(F_plus(u)):>14.6e} {float(d1):>14.6e} "
              f"{float(d2):>14.6e} {s:>7}")
if len(set(signs)) == 1:
    print(f"\n  NO SIGN CHANGE on [0,4] -- D2 is {signs[0]} throughout.")
    print("  => F_plus is convex there, so integrableOn_Ioi_deriv_of_nonneg")
    print("     (mathlib IntegralEqImproper.lean:755) is the right tool and the")
    print("     existing integrableOn_deriv_F_plus proof transfers with")
    print("     nonpos -> nonneg.  NOTE: measured, not proved, and only on [0,4].")
else:
    print("\n  SIGN CHANGE FOUND -- the sign route does NOT transfer.")

print()
print("=" * 72)
print("Q2 - the new boundary constants for a second IBP")
print("=" * 72)
w1 = omega(1)
w1p = mp.nsum(lambda n: -mp.pi * n * n * mp.e**(-mp.pi * n * n), [1, mp.inf])
print(f"  omega(1)          = {float(w1):.10f}")
print(f"  omega'(1)         = {float(w1p):.10f}")
print(f"  F_plus(0)         = {float(F_plus(0)):.10f}   "
      f"(= omega 1; existing F_plus_zero)")
print(f"  deriv F_plus  0   = {float(mp.diff(F_plus, 0, 1)):.10f}   "
      f"(= omega(1)/2 + omega'(1) = {float(w1 / 2 + w1p):.10f})")
print(f"  deriv F_minus 0   = {float(mp.diff(F_minus, 0, 1)):.10f}   "
      f"(= omega'(1))")
print("  -> both NONZERO: the second IBP introduces a genuinely new boundary")
print("     constant, needing its own lemma (the analogue of F_plus_zero).")
