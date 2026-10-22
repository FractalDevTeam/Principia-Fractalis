#!/usr/bin/env python3
"""
Price the march to 13 against the criterion the DEPLOYED producer actually
asserts, at sub-segment granularity, with and without the free boundary
extension.

Why this supersedes make_schedule.py. That script priced the `mmrrrr` scheme at
BASE-segment granularity, against Q with a 1.25x safety factor, and it STOPPED
at c = 12.906250 -- it does not reach 13. Three things in it do not match the
deployed gate:

  1. Rio section 0.8: "the deployed march applies no 1.25x safety factor."
     True -- gen_box.py asserts `Q*r < Mc_lb` bare; only --pick-r applies a
     safety ratio, and the march passes an explicit --r. So pricing with 1.25x
     is pricing a gate that is not deployed.
  2. The midpoint boundary. --extend-midpoint (committed, free, no new tier)
     takes midpoint out to u = 0.6875 instead of 1/2, worth 2.08-2.36x at the
     top of the march. A base-segment scheme string cannot express it, so
     make_schedule.py could not price it at all.
  3. My earlier claim that "mmrrrr reaches c = 13 at every centre" came from
     price7, which used the TIGHT L0 and allowed D = 64. The emitted proof
     carries Q (from omega(1) <= 1/22), not L0, and Q is ~5% larger. On the Q
     scale that claim was wrong -- which is section 0.8's 1.06x correction.

So: four variants, same machinery, so the differences are attributable.
"""
import io
import os
import sys
from fractions import Fraction as F

import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from price_boundary import TIER_A_MAX, Q_of, mc_lb_sub   # noqa: E402

mp.mp.dps = 30

DLAD = [1, 2, 4, 8, 16, 32]
RLAD = [F(1, 16), F(1, 32), F(1, 64)]
MIN_PER_MODULE = 7.5
START = F(161, 16)        # 10.0625, the D=1 band edge
TARGET = F(13)


def n_mid_of(D, extend):
    return int(TIER_A_MAX * 4 * D) if extend else 2 * D


def run(extend, safety):
    """Walk the frontier; return (rows, frontier)."""
    saf = mp.mpf(safety)
    rows = []
    f = START
    guard = 0
    while f < TARGET and guard < 300:
        guard += 1
        best = None
        for r in RLAD:
            c = f + r
            qr = Q_of(c, r) * r
            need = saf * (mp.mpf(qr.numerator) / qr.denominator)
            for D in DLAD:
                if mc_lb_sub(c, D, n_mid_of(D, extend)) > need:
                    cost = (6 * D + 1) * MIN_PER_MODULE + 3.0
                    key = cost / (2.0 * float(r))
                    if best is None or key < best[0]:
                        best = (key, c, r, D, cost)
                    break
        if best is None:
            return rows, f, False
        _, c, r, D, cost = best
        rows.append((c, r, D, cost))
        f = c + r
    return rows, f, f >= TARGET


if __name__ == "__main__":
    print("=" * 96)
    print("MARCH TO 13, priced against the criterion the producer asserts "
          "(Q*r < Mc_lb)")
    print("=" * 96)
    print(f"{'boundary':>10} {'safety':>7} {'reaches':>9} {'frontier':>10} "
          f"{'boxes':>6} {'modules':>8} {'hours':>8} {'days':>6}")
    results = {}
    for extend in (False, True):
        for safety in ("1.25", "1.0"):
            rows, f, ok = run(extend, safety)
            mods = sum(6 * D + 1 for _, _, D, _ in rows)
            h = sum(cost for _, _, _, cost in rows) / 60
            results[(extend, safety)] = (rows, f, ok, mods, h)
            print(f"{'u<=0.6875' if extend else 'u<=0.5':>10} {safety:>7} "
                  f"{'YES' if ok else 'NO':>9} {float(f):>10.6f} "
                  f"{len(rows):>6} {mods:>8} {h:>8.1f} {h/24:>6.1f}")
    print()
    # THE DECIDED CONFIGURATION (Pablo, 2026-10-21): extend-midpoint ON,
    # safety 1.25x. Not the cheapest variant -- extend+1.0x is 225.3 h against
    # 287.5 h -- but the default boundary does not reach 13 under ANY safety
    # factor, so the extension is what makes a margin affordable at all.
    rows, f, ok, mods, h = results[(True, "1.25")]
    if ok:
        print("DECIDED CONFIGURATION (--extend-midpoint ON, safety 1.25x): "
              "reaches 13")
        print(f"  {len(rows)} boxes, {mods} panel modules, {h:.1f} h "
              f"({h/24:.1f} days serial)")
        grp = {}
        for c, r, D, cost in rows:
            grp.setdefault(D, []).append((float(c), str(r)))
        print()
        print(f"  {'D':>3} {'boxes':>6} {'c range':>24} {'radii':>16} {'h':>7}")
        for D in sorted(grp):
            cs = [x[0] for x in grp[D]]
            rs = sorted(set(x[1] for x in grp[D]), key=lambda s: -eval(s))
            hh = len(cs) * ((6 * D + 1) * MIN_PER_MODULE + 3.0) / 60
            print(f"  {D:>3} {len(cs):>6} [{min(cs):>9.4f},{max(cs):>9.4f}] "
                  f"{','.join(rs):>16} {hh:>7.1f}")
        out = ["# march schedule: D=1 band edge -> c = 13",
               "# codex/make_schedule2.py -- DECIDED CONFIG (Pablo 2026-10-21): "
               "--extend-midpoint ON, safety 1.25x on Q*r < Mc_lb",
               "# a PROPOSAL: gen_box.py asserts the criterion itself and "
               "refuses infeasible rows",
               "# columns: centre radius density"]
        for c, r, D, cost in rows:
            out.append(f"{c} {r} {D}")
        io.open("march_schedule.txt", "w", encoding="utf-8",
                newline="\n").write("\n".join(out) + "\n")
        print()
        print(f"  wrote march_schedule.txt ({len(rows)} rows)")
    else:
        print(f"DEPLOYED CONFIGURATION DOES NOT REACH 13 -- stops at "
              f"{float(f):.6f}")
        print("  Report this rather than raising density silently.")
