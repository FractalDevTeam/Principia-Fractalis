#!/usr/bin/env python3
"""
CORRECTED per-leg budget analysis.

The three sign facts (R1R2R3_TARGET_REACHABLE:40-42) are:
  R1 : Re xi(1+it) > 0  on [0, 13]
  R2 : Im xi(1+it) > 0  on [13, 14.5]
  R3 : Re xi(1+it) < 0  on [14.5, 15]

So the Gate-1 margin is a DIFFERENT quantity on each leg, and the decomposition
deliberately routes around the Re xi zero at t = 13.9883806982 using Im xi.
My first reading of the t=14.5 table row as a sign error was WRONG: 4.142e-04
is Im xi(1+14.5i), R2's worst margin, correctly. The column header "Re xi" is
what does not apply to that row.

Budget on each leg = margin(t) / (t^2 + t), since the add-on enters R_ub and
I_ub equally.
"""
import math
import mpmath as mp

mp.mp.dps = 30
PI = math.pi
A, B = 1.5, 5.0


def xi(t):
    s = mp.mpc(1, t)
    return mp.mpf(1) / 2 * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def margin(t):
    """The quantity Gate 1 must fit inside, per leg."""
    if t <= 13.0:
        return float(mp.re(xi(t)))            # R1
    if t <= 14.5:
        return float(mp.im(xi(t)))            # R2
    return -float(mp.re(xi(t)))               # R3 (Re xi < 0, margin is |Re xi|)


def budget(t):
    return margin(t) / (t**2 + t)


def g(u):
    return (math.exp(u / 2) + 1) * 3 * math.exp(-PI * math.exp(u))


def residue_equal(n):
    h = (B - A) / n
    return h * sum(g(A + i * h) for i in range(n))


def residue_lnk():
    cuts = [A] + [math.log(k) for k in range(5, 200) if A < math.log(k) < B] + [B]
    tot = 0.0
    for i in range(len(cuts) - 1):
        a, b = cuts[i], cuts[i + 1]
        k = math.floor(math.exp(a) + 1e-12)
        tot += (b - a) * (math.exp(b / 2) + 1) * 3 * (1 / 23) ** k
    return tot


# residue floor = exact integral of the majorant
N = 400000
h = (B - A) / N
RES_FLOOR = h * sum(g(A + (i + 0.5) * h) for i in range(N))
TAIL_FREE, OM_FREE = 1.1326e-07, 4.3790e-22
CUR = 1e-4 + 1e-6 + 231 / 10**6

print("=" * 78)
print("PER-LEG MARGIN AND BUDGET  (the global worst point governs everything)")
print("=" * 78)
print(f"  {'leg':>4} {'t':>8} {'margin':>14} {'budget':>12}")
# scan each leg for its minimum budget
legs = [("R1", 6.5, 13.0), ("R2", 13.0, 14.5), ("R3", 14.5, 15.0)]
worst = None
for name, lo, hi in legs:
    best_t, best_b = None, None
    t = lo
    while t <= hi + 1e-12:
        b = budget(t)
        if best_b is None or b < best_b:
            best_b, best_t = b, t
        t += 0.005
    print(f"  {name:>4} {best_t:>8.3f} {margin(best_t):>14.4e} {best_b:>12.4e}"
          + "   <-- leg minimum")
    if worst is None or best_b < worst[1]:
        worst = (best_t, best_b, name)
print()
print(f"  GLOBAL WORST: {worst[2]} at t = {worst[0]:.3f}, add-on budget = {worst[1]:.4e}")
print(f"  (t=13 budget for comparison: {budget(13.0):.4e} -- "
      f"{budget(13.0)/worst[1]:.1f}x looser)")

print()
print("=" * 78)
print("ADD-ON CONFIGURATIONS vs the two decision points")
print("=" * 78)
configs = [
    ("current", CUR),
    ("free omega+tail only", 231 / 10**6 + TAIL_FREE + OM_FREE),
    ("+ residue 1 piece (endpoint-correct)", residue_equal(1) + TAIL_FREE + OM_FREE),
    ("+ residue 2 equal pieces", residue_equal(2) + TAIL_FREE + OM_FREE),
    ("+ residue ln-k design (no new consts)", residue_lnk() + TAIL_FREE + OM_FREE),
    ("+ first piece refined 40x", 7.1218e-07 + TAIL_FREE + OM_FREE),
    ("residue at its FLOOR (architecture limit)", RES_FLOOR + TAIL_FREE + OM_FREE),
]
b13, bw = budget(13.0), worst[1]
print(f"  {'configuration':>42} {'add-on':>11} {'% of t=13':>11} "
      f"{'% of worst':>11}")
for name, a in configs:
    print(f"  {name:>42} {a:>11.4e} {100*a/b13:>10.1f}% {100*a/bw:>10.1f}%")

print()
print(f"  residue majorant floor = {RES_FLOOR:.4e}")
print(f"  tail floor (U=5)       = {TAIL_FREE:.4e}")
print(f"  => architecture floor  = {RES_FLOOR+TAIL_FREE+OM_FREE:.4e} "
      f"= {100*(RES_FLOOR+TAIL_FREE+OM_FREE)/bw:.1f}% of the global-worst budget")
print()
print("So: t=13 is comfortable; the GLOBAL worst point is R2's far end, where the")
print("add-on ARCHITECTURE floor already eats a third of the budget. Getting the")
print("add-ons under 10% there needs a better majorant -- i.e. keeping the")
print("oscillation instead of |cos|,|sin| <= 1. That IS new mathematics.")

print()
print("=" * 78)
print("DO THE CURRENT ADD-ONS BIND AT THE LANDED PILOTS?  (t = 6.0 .. 6.886)")
print("=" * 78)
for t in (6.5, 6.75, 6.886):
    b = budget(t)
    print(f"  t={t:>6}: budget = {b:.4e}   current add-on {CUR:.4e} "
          f"= {100*CUR/b:.1f}% of budget")
print("  -> No. This is preparatory work for t ~ 10-13, not a fire.")
