#!/usr/bin/env python3
"""
Gate-1 arithmetic at c = 27/4, and what the midpoint scheme would need.

Gate-1 as the pilots write it (R1_c13_2_...:60):
    c^2 * R_ub_f + c * I_ub_f  <=  3/4          (i.e. Mc_lb = 1/8)
and identically  c^2 * R + c * I = 1 - 2*Re xi(c),
so the budget for (enclosure error + add-ons) is

    c^2*(R_ub - R) + c*(I_ub - I)  <=  3/4 - (1 - 2*Re xi(c)) = 2*Re xi(c) - 1/4.

First identify R and I against the landed c=13/2 constants, then do c=27/4.
"""
import mpmath as mp

mp.mp.dps = 30


def Lambda0(t):
    s = mp.mpc(1, t)
    return mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s) + 1 / s + 1 / (1 - s)


def xi(t):
    s = mp.mpc(1, t)
    return mp.mpf(1) / 2 * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


print("=" * 78)
print("0. IDENTIFY R and I against the landed c=13/2 constants")
print("=" * 78)
R_ub_132 = mp.mpf(1339441331) / 80000000000
I_ub_132 = mp.mpf(302372667) / 160000000000
print(f"  c=13/2 landed:  R_ub_h32 = {float(R_ub_132):.10f}   I_ub_h32 = {float(I_ub_132):.10f}")
for t in (6.5,):
    print(f"  Re Lambda0(1+{t}i) = {float(mp.re(Lambda0(t))):.10f}   "
          f"Im Lambda0(1+{t}i) = {float(mp.im(Lambda0(t))):.10f}")
    # the identity the gate rests on
    c = mp.mpf(t)
    lhs = c**2 * mp.re(Lambda0(t)) + c * mp.im(Lambda0(t))
    print(f"  c^2*Re + c*Im = {float(lhs):.10f}   vs  1 - 2*Re xi = "
          f"{float(1 - 2*mp.re(xi(t))):.10f}")

print()
print("=" * 78)
print("1. THE REAL GATE-1 BUDGET AT c = 27/4  (and the claimed 0.0143)")
print("=" * 78)
for t in (6.5, 6.75):
    c = mp.mpf(t)
    rexi = mp.re(xi(t))
    budget = 2 * rexi - mp.mpf(1) / 4
    print(f"\n  c = {t}:  Re xi = {float(rexi):.8f}")
    print(f"    Gate-1 budget for (enclosure + add-ons) = 2*Re xi - 1/4 = "
          f"{float(budget):.8f}")
    print(f"    weights: c^2 = {float(c**2):.4f}, c = {float(c):.4f}")

print()
print("=" * 78)
print("2. ACHIEVED ENCLOSURE (landed range-brick) AND WHAT IT COSTS AT c=27/4")
print("=" * 78)
# R1R2R3 note, measured at the landed c=51/8 box:
dR, dI = mp.mpf("2.6217e-3"), mp.mpf("1.8874e-3")
ADDON = mp.mpf(231) / 10**6 + mp.mpf(1) / 10**6 + mp.mpf(1) / 10**4
print(f"  achieved at the landed box:  R_ub - R = {float(dR):.4e}   "
      f"I_ub - I = {float(dI):.4e}")
print(f"  of which add-ons (equal in both):      {float(ADDON):.4e}")
panelR, panelI = dR - ADDON, dI - ADDON
print(f"  so the PANEL part is:        R {float(panelR):.4e}   I {float(panelI):.4e}")

for t in (6.5, 6.75):
    c = mp.mpf(t)
    budget = 2 * mp.re(xi(t)) - mp.mpf(1) / 4
    cost = c**2 * dR + c * dI
    print(f"\n  c = {t}:  cost = c^2*dR + c*dI = {float(cost):.6f}"
          f"   budget = {float(budget):.6f}")
    print(f"    -> {'PASS' if cost <= budget else 'FAIL'}"
          f", {'margin' if cost <= budget else 'shortfall'} = "
          f"{float(abs(budget - cost)):.6f}")

print()
print("=" * 78)
print("3. DOES MIDPOINT CLOSE IT?  by the M actually used, and by a tight M")
print("=" * 78)
H = mp.mpf(1) / 32
# range-brick per-panel half-width on nodeR, panel 0 plus (measured from the file)
RB_HALF = mp.mpf("0.03125") * (mp.mpf("0.0871153865") - mp.mpf("0.0777946458")) / 2
print(f"  range-brick per-panel half-width (on nodeR) = {float(RB_HALF):.4e}")
print(f"  {'M':>8} {'midpt half-width':>18} {'vs range-brick':>16} "
      f"{'panel part':>12} {'cost at c=27/4':>15} {'verdict':>9}")
c = mp.mpf(27) / 4
budget = 2 * mp.re(xi(6.75)) - mp.mpf(1) / 4
for M, lab in ((mp.mpf(3000), "3000 (landed)"), (mp.mpf("229.1"), "229 (break-even)"),
               (mp.mpf("7.5"), "7.5 (provable)"), (mp.mpf("1.3773"), "1.377 (true)")):
    half = M * H**3 / 24 / 2            # /2 to convert f_plus -> nodeR
    ratio = RB_HALF / half
    # scale the panel part of the enclosure by the improvement factor
    pR, pI = panelR / ratio, panelI / ratio
    nR, nI = pR + ADDON, pI + ADDON
    cost = c**2 * nR + c * nI
    print(f"  {lab:>8} {float(half):>18.4e} {float(ratio):>15.1f}x "
          f"{float(pR):>12.3e} {float(cost):>15.6f} "
          f"{'PASS' if cost <= budget else 'FAIL':>9}")
print(f"\n  budget at c=27/4 = {float(budget):.6f}")
print(f"  NOTE: the add-on floor alone costs c^2*A + c*A = "
      f"{float((c**2 + c) * ADDON):.6f} of it "
      f"({float(100*(c**2+c)*ADDON/budget):.1f}%)")


# ---------------------------------------------------------------------------
# Final table: panel enclosure held at the CURRENT BEST (landed c=13/2 pilot),
# which is what section 3 of the step-4 note reports.
print()
print("=" * 78)
print("4. FINAL TABLE  (panel enclosure at the landed c=13/2 quality)")
print("=" * 78)
R_ub = mp.mpf(1339441331) / 80000000000
I_ub = mp.mpf(302372667) / 160000000000
A_now = mp.mpf(231) / 10**6 + mp.mpf(1) / 10**6 + mp.mpf(1) / 10**4
Rt, It = mp.re(Lambda0(6.5)), mp.im(Lambda0(6.5))
pR, pI = R_ub - Rt - A_now, I_ub - It - A_now
c65 = mp.mpf(6.5)
chk = mp.mpf(3)/4 - (c65**2 * (R_ub + A_now) + c65 * (I_ub + A_now))
print(f"  model check: landed c=13/2 margin = {float(chk):.7f}  (pilot says +0.0141387)")
print(f"  panel-only dR = {float(pR):.4e}   dI = {float(pI):.4e}")
A_fix = mp.mpf(231) / 10**6 + mp.mpf("1.1326e-7")
A_lnk = mp.mpf("4.1016e-6") + mp.mpf("1.1326e-7")
c = mp.mpf(27) / 4
bud = 2 * mp.re(xi(6.75)) - mp.mpf(1) / 4
print(f"  budget at c=27/4 = {float(bud):.7f}")
for lab, A, imp in (("current add-ons, range-brick", A_now, mp.mpf(1)),
                    ("+ the two one-line fixes", A_fix, mp.mpf(1)),
                    ("+ residue ln-k", A_lnk, mp.mpf(1)),
                    ("midpoint as landed (M=3000)", A_now, mp.mpf("0.0763")),
                    ("two fixes + midpoint M=7.5", A_fix, mp.mpf("30.5"))):
    cost = c**2 * (pR / imp + A) + c * (pI / imp + A)
    m = bud - cost
    print(f"  {lab:>32}: cost={float(cost):.7f}  "
          f"{'PASS' if m >= 0 else 'FAIL'} by {float(abs(m)):.7f}")
