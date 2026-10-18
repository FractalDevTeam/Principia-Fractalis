#!/usr/bin/env python3
"""
Audit every row of the R1R2R3 'Re xi' table against Re xi(1+it), and find
where Re xi(1+it) first changes sign -- which is where Gate 1's margin
2*(Re xi - Mc_lb) stops being positive, i.e. the real ceiling.

Table (codex/R1R2R3_TARGET_REACHABLE_2026-10-16.md:120-127):
   t=6.375 -> 1.868e-1 ; 8 -> 1.019e-1 ; 10 -> 3.681e-2 ;
   12 -> 8.194e-3 ; 13 -> 2.509e-3 ; 14.5 -> 4.142e-4
"""
import mpmath as mp

mp.mp.dps = 40


def xi(s):
    return mp.mpf(1) / 2 * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def re_xi(t):
    return mp.re(xi(mp.mpc(1, t)))


TABLE = [(6.375, 1.868e-1), (8.0, 1.019e-1), (10.0, 3.681e-2),
         (12.0, 8.194e-3), (13.0, 2.509e-3), (14.5, 4.142e-4)]

print("=" * 72)
print("ROW-BY-ROW AUDIT of the table's 'Re xi'")
print("=" * 72)
print(f"  {'t':>7} {'table':>12} {'Re xi(1+it)':>14} {'match?':>10}")
for t, v in TABLE:
    a = float(re_xi(t))
    ok = "YES" if abs(a - v) <= 1.5e-3 * max(abs(v), 1e-12) + 5e-7 else "NO"
    print(f"  {t:>7} {v:>12.4e} {a:>14.4e} {ok:>10}")

print()
print("=" * 72)
print("WHERE DOES Re xi(1+it) FIRST VANISH?  (Gate 1 needs Re xi > 0)")
print("=" * 72)
prev_t, prev_v = 6.0, float(re_xi(6.0))
root = None
t = 6.0
while t < 30.0:
    t += 0.01
    v = float(re_xi(t))
    if prev_v > 0 >= v:
        root = mp.findroot(lambda x: re_xi(x), mp.mpf(t) - mp.mpf("0.005"))
        break
    prev_t, prev_v = t, v
print(f"  first sign change of Re xi(1+it) above t=6:  t = {float(root):.10f}")
print(f"  Re xi just below: {float(re_xi(float(root) - 0.01)):+.4e}   "
      f"just above: {float(re_xi(float(root) + 0.01)):+.4e}")

print()
print(f"  {'t':>8} {'Re xi(1+it)':>14} {'budget = Rexi/(t^2+t)':>24}")
for t in (13.0, 13.5, 13.9883806982, 14.0, float(root), 14.2, 14.5, 15.0):
    v = float(re_xi(t))
    b = v / (t**2 + t)
    print(f"  {t:>8.4f} {v:>+14.4e} {b:>24.4e}" + ("   <-- NO BUDGET" if v <= 0 else ""))

print()
print("Cross-check against the repo's own hard boundary t = 13.9883806982:")
print(f"  Re xi(1+13.9883806982i) = {float(re_xi(13.9883806982)):+.6e}")
print(f"  distance to the root    = {float(root) - 13.9883806982:+.6e}")
