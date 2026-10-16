#!/usr/bin/env python3
"""Verification for GATE_c13_2_PAPER_GATE_2026-10-16.md

Paper gate for the c = 13/2 box, computed before any Lean is written.
Run:  python3 gate_c13_2_verify.py       (needs mpmath)

Sections:
  1. calibrate the reported margin series against the REAL rational constants
     (R1_c51_8_r1_16_pointwise_CLOSED_2026_10_16.lean:893-896), and show the
     stale section-0 comment was inconsistent.
  2. gate-1 true-value headroom, and the crossings of 1/8, 1/16, 0.
  3. projection of the gate-1 slack to c = 13/2 at current enclosure quality.
  4. lever ranking: residue vs omega-gap vs analytic tail.
  5. residue looseness, and what evaluating the same majorant correctly buys.
  6. GATE 2 ceiling -- the march's actual binding constraint.
"""
from fractions import Fraction as F
from mpmath import mp, mpf, mpc, pi, gamma, zeta, power, exp, quad

mp.dps = 50

R_ub_h32 = F(542831867, 32000000000)
I_ub_h32 = F(60314889, 32000000000)
RESID, TAIL, OMGAP = F(231, 279841), F(1, 10 ** 6), F(1, 10 ** 4)
ADDON = RESID + TAIL + OMGAP
BUDGET = F(3, 4)


def Lambda0(s):
    """Lambda0 = Lambda + 1/s + 1/(1-s),  Lambda = pi^(-s/2) Gamma(s/2) zeta(s)."""
    return power(pi, -s / 2) * gamma(s / 2) * zeta(s) + 1 / s + 1 / (1 - s)


def true_RI(c):
    L0 = Lambda0(mpc(1, mpf(c)))
    return L0.real, L0.imag


def re_xi(c):
    c = mpf(c)
    R, I = true_RI(c)
    return (1 - c ** 2 * R - c * I) / 2


print("=" * 76)
print("1. calibrate the margin series (it is the GATE-1 SLACK)")
c = F(51, 8)
R_ub_f, I_ub_f = R_ub_h32 + ADDON, I_ub_h32 + ADDON
lhs = c ** 2 * R_ub_f + c * I_ub_f
print("   R_ub_f = %.10f ,  I_ub_f = %.10f" % (float(R_ub_f), float(I_ub_f)))
print("   (2601/64)R_ub_f + (51/8)I_ub_f = %.8f" % float(lhs))
print("   slack = 3/4 - that = %+.8f        <-- reported margin +0.0050"
      % float(BUDGET - lhs))
print()
print("   the stale section-0 comment claimed R_ub_f ~ 0.018418 and product ~0.6909:")
print("     40.6406 x 0.018418 = %.4f  (not 0.6909, and > 0.75 budget share)"
      % (float(c ** 2) * 0.018418))
print("     0.6909 / 40.6406   = %.6f  (not 0.018418)" % (0.6909 / float(c ** 2)))
print("   -> mutually inconsistent; repaired in the Lean file (comment only).")

print()
print("=" * 76)
print("2. gate-1 TRUE-VALUE headroom (not the certified slack)")
for cc in ["6.375", "6.4375", "6.5", "6.5625"]:
    print("   Re xi(1+i%-8s) = %+.10f   vs 1/8: %+.10f"
          % (cc, float(re_xi(cc)), float(re_xi(cc) - mpf(1) / 8)))


def cross(target, lo=mpf(6), hi=mpf(14)):
    f = lambda z: re_xi(z) - target
    for _ in range(300):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if f(mid) > 0 else (lo, mid)
    return (lo + hi) / 2


for nm, thr in [("1/8", mpf(1) / 8), ("1/16", mpf(1) / 16), ("0", mpf(0))]:
    print("   true Re xi crosses %-5s at c = %.6f" % (nm, float(cross(thr))))
print("   (the 0-crossing reproduces this project's established first sign")
print("    change at t = 13.9883806982 -- cross-checks the Lambda0 convention)")

print()
print("=" * 76)
print("3. PROJECTION to c = 13/2 at current enclosure quality")
Rt, It = true_RI("6.375")
wR, wI = float(R_ub_h32) - float(Rt), float(I_ub_h32) - float(It)
print("   achieved panel widths at c=51/8:  dR = %.3e , dI = %.3e" % (wR, wI))
c2 = F(13, 2)
Rt2, It2 = true_RI("6.5")
Rp = F(float(Rt2) + wR).limit_denominator(10 ** 12) + ADDON
Ip = F(float(It2) + wI).limit_denominator(10 ** 12) + ADDON
lhs2 = c2 ** 2 * Rp + c2 * Ip
short = float(lhs2 - BUDGET)
print("   projected: c^2 R_ub_f + c I_ub_f = %.8f  vs 0.75" % float(lhs2))
print("   => slack %+.8f  : %s" % (-short, "FAILS, shortfall %.5f" % short if short > 0 else "passes"))
print("   (optimistic -- cos(cu/2) oscillates faster at larger c, so the real")
print("    width is larger and the true shortfall is at least this)")

print()
print("=" * 76)
print("4. LEVER RANKING at c = 13/2   (weight c^2 + c = 48.75)")
W = float(c2 ** 2 + c2)
for nm, v in [("residue 231/279841", RESID), ("omega-gap 1/10^4", OMGAP),
              ("analytic tail 1/10^6", TAIL)]:
    print("   %-22s %.3e   costs %.6f of budget" % (nm, float(v), W * float(v)))
print("   needed recovery: %.6f" % short)
print("   tail + omega-gap together buy %.6f = %.0f%% of need -> INSUFFICIENT"
      % (W * float(TAIL + OMGAP), 100 * W * float(TAIL + OMGAP) / short))
print("   residue alone costs %.6f = %.1fx the need -> THIS is the lever"
      % (W * float(RESID), W * float(RESID) / short))

print()
print("=" * 76)
print("5. why the residue is loose, and what correct evaluation buys")
a, b = mpf(3) / 2, mpf(5)
g = lambda u: (exp(u / 2) + 1) * 3 * exp(-pi * exp(u))
print("   current bound 231/279841 = %.6e" % float(RESID))
print("   over-loosening, both at the WRONG endpoint:")
print("     exp(-pi e^u) <= exp(-4pi) = %.3e  but true at u=3/2 is %.3e  (x%.1f)"
      % (float(exp(-4 * pi)), float(exp(-pi * exp(a))), float(exp(-4 * pi) / exp(-pi * exp(a)))))
print("     exp(u/2)+1   <= 22                but at u=3/2 it is %.3f        (x%.1f)"
      % (float(exp(a / 2) + 1), 22 / float(exp(a / 2) + 1)))
print("   integral of the same majorant = %.6e  (looseness %.1fx)"
      % (float(quad(g, [a, b])), float(RESID) / float(quad(g, [a, b]))))
print()
print("   plain max x width, piecewise (g is decreasing -> left endpoints valid):")
for n in [1, 2, 4, 7]:
    h = (b - a) / n
    tot = sum(g(a + k * h) * h for k in range(n))
    saved = W * (float(RESID) - float(tot))
    print("     %2d piece(s): bound %.6e  (%.1fx tighter)  frees %.6f  %s"
          % (n, float(tot), float(RESID) / float(tot), saved,
             "ENOUGH" if saved > short else "not enough"))
print()
print("   g decreasing on [3/2,5]?  g'/g = (1/2)e^(u/2)/(e^(u/2)+1) - pi e^u :")
for u in ["1.5", "2", "3", "4", "5"]:
    u = mpf(u)
    print("     u=%-4s  %+.4f" % (u, float((mpf(1) / 2 * exp(u / 2)) / (exp(u / 2) + 1) - pi * exp(u))))
print("   all negative -> decreasing -> left-endpoint maxima sound.")

print()
print("=" * 76)
print("6. GATE 2 -- the march's actual binding constraint")
print("   50(1+2|t|) + 50(t^2+|t|) <= 2*1727  <=>  t^2 + 3t + 1 <= 1727/25 = 69.08")
RHS = 2 * 1727
tmax = (-3 + (9 + 4 * (RHS / 50 - 1)) ** 0.5) / 2
print("   ceiling: |t| <= %.6f  (evaluated at the box UPPER EDGE)" % tmax)
print("   %-8s %-12s %-13s %-10s %s" % ("centre", "upper edge", "50(t^2+3t+1)", "slack", "verdict"))
for cs in ["51/8", "13/2", "53/8", "27/4", "55/8", "7"]:
    hi = F(cs) + F(1, 16)
    v = (1 + 2 * hi) * 50 + (hi * hi + hi) * 50
    print("   %-8s %-12.4f %-13.2f %-10.2f %s" % (cs, float(hi), float(v), float(RHS - v),
                                                  "PASS" if v <= RHS else "**FAIL**"))
print()
print("   => gate 2 fails first, at centre 55/8 = 6.875, three boxes after")
print("      13/2 -- while gate 1's true headroom runs to c = 7.5019.")
print("      Gate-1 enclosure tightening does NOT move this: gate 2 uses the")
print("      uniform ||Lambda0|| <= 50/1727 derivative route, a different object.")
