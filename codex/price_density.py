#!/usr/bin/env python3
"""
STEP 1, exact: price the panel-density ladder for the march to c = 13.

The producer's all-midpoint upper bound decomposes EXACTLY as

    R_ub(c, D) = sum_seg sum_k [ h * U_node(m_k) ]  +  sum_seg 8D * err_seg/2
               = Rnode(c, D)                        +  Terr(c, D)

    h = 1/(32D),  err_seg = M_seg(c, T_seg) * h^3 / 24

and the two pieces are priced separately because they behave differently:

  * Terr(c, D) = sum_seg M_seg(c) / (196608 D^2)  -- CLOSED FORM, exactly 1/D^2.
  * Rnode(c, D) -> int_0^{3/2} nodeR  as D -> inf, from ABOVE, with excess
    bounded by the node rounding (10 digits outward, ~1e-10 per node) plus the
    midpoint quadrature's own signed error -- which is already covered by
    Terr, since Terr is a bound on exactly that. So for pricing purposes
    Rnode(c, D) = R_true(c) + O(1e-9), five to six orders of magnitude below
    every Mc_lb in play.

So  Mc_lb(c, D) = (1 - c^2(R_true + Terr_R + ADDON) - c(I_true + Terr_I + ADDON))/2
and the only c-dependent work per centre is the true integral, done in mpmath.

VALIDATED against the shipped interval arithmetic (option --check) and against
the producer's own measured hybrid Mc_lb (codex/mclb_scan.txt).

D must be a POWER OF 2: err = M/(2^18 * 3 * D^3) must terminate as a decimal
literal (gen_box.dec) and the panel endpoints must stay dyadic.
"""
import io
import os
import sys
from fractions import Fraction as F

import mpmath as mp

mp.mp.dps = 30

HERE = os.path.dirname(os.path.abspath(__file__))
ADDON = F(7, 10**7) + F(12, 10**8) + F(1, 10**21)
OMEGA1 = F(4321741, 10**8)
PI_UB = F(4)
B_UB = {n: F(1, 23) ** ((n + 1) ** 2) for n in range(3)}
SEGMENTS = {i: (F(i - 1, 4), F(i, 4)) for i in range(1, 7)}   # [0,3/2], six x 1/4


def L0_val(c):
    return 2 * OMEGA1 * (1 + 1 / F(c)) + 1 / (2 * F(c) ** 2)


def tier(T):
    """Tier A (T<=1/2): E<=2, expT<=2.  B (T<=1): E<=2, expT<=3.
       C (T<=3/2): E<=3, expT<=9.   (midpoint generator, lines 92-96)"""
    if T <= F(1, 2):
        return F(2), F(2)
    if T <= F(1):
        return F(2), F(3)
    return F(3), F(9)


def termM_coarse(c, n, T):
    A = PI_UB * (n + 1) ** 2
    E, Th = tier(T)
    B, G = B_UB[n], abs(F(c)) / 2
    return (E / 4 * (2 * B)
            + (E + 1) * (2 * A * (A * Th - 1) * B)
            + (E + 1) * (2 * B) * G ** 2
            + 2 * (E / 2) * (2 * A * B)
            + 2 * (E / 2) * (2 * B) * G
            + 2 * (E + 1) * (2 * A * B) * G)


def M_of(c, T):
    s = sum(int(termM_coarse(c, n, T)) + 1 for n in range(3))
    return s + (-s) % 3


def Terr(c, D):
    """sum over the six segments of 8D * (M h^3/24) / 2, h = 1/(32D)."""
    h = F(1, 32 * D)
    t = F(0)
    for seg in range(1, 7):
        M = M_of(c, SEGMENTS[seg][1])
        t += 8 * D * (F(M) * h ** 3 / 24) / 2
    return t


# --- the true node integrals, mpmath ---------------------------------------
def omega3(x):
    return (mp.e ** (-mp.pi * x) + mp.e ** (-4 * mp.pi * x)
            + mp.e ** (-9 * mp.pi * x))


def true_nodes(c):
    """(int_0^{3/2} nodeR_plus, int_0^{3/2} nodeR_minus) for this c."""
    ch = mp.mpf(F(c).numerator) / F(c).denominator / 2
    fR = lambda u: ((mp.e ** (u / 2) + 1) * omega3(mp.e ** u) * mp.cos(ch * u))
    fI = lambda u: ((mp.e ** (u / 2) - 1) * omega3(mp.e ** u) * mp.sin(ch * u))
    return (mp.quad(fR, [0, mp.mpf(3) / 2]), mp.quad(fI, [0, mp.mpf(3) / 2]))


_tc = {}


def mc_lb(c, D):
    """Mc_lb(c, D) = (1 - gate)/2, gate = c^2(R_ub+ADDON) + c(I_ub+ADDON)."""
    if c not in _tc:
        _tc[c] = true_nodes(c)
    tR, tI = _tc[c]
    te = mp.mpf(Terr(c, D).numerator) / Terr(c, D).denominator
    ad = mp.mpf(ADDON.numerator) / ADDON.denominator
    cc = mp.mpf(F(c).numerator) / F(c).denominator
    gate = cc ** 2 * (tR + te + ad) + cc * (tI + te + ad)
    return (1 - gate) / 2


DLAD = [1, 2, 4, 8, 16, 32, 64]
RLAD = [F(1, 2 ** k) for k in range(4, 13)]
SAFETY = mp.mpf("1.25")
MIN_PER_MODULE = 7.5


# ---------------------------------------------------------------------------
def check():
    """Validate Terr and the node integral against the SHIPPED interval
    arithmetic, at c = 27/4, D = 1."""
    RG = os.path.join(HERE, "gen", "gen_fourier_panels_c27_4.py")
    _g = {"__name__": "_g", "__file__": RG}
    exec(compile(io.open(RG, encoding="utf-8").read(), RG, "exec"), _g)
    I, ST = _g["I"], 50
    epi, ci, si = (_g["exp_pos_interval"], _g["cos_interval"], _g["sin_interval"])
    oi = _g["omega_N3_interval"]
    c = F(27, 4)
    ch = c / 2
    h = F(1, 32)
    Rn = In = F(0)
    for seg in range(1, 7):
        lo, hi = SEGMENTS[seg]
        for k in range(8):
            m = lo + k * h + h / 2
            mi = I(m, m)
            E = epi(I(m * F(1, 2), m * F(1, 2)), series_terms=ST)
            om = oi(epi(mi, series_terms=ST), series_terms=ST)
            Fp = (E * om).rounded()
            R = ((Fp + om) * ci(I(ch * m, ch * m), series_terms=ST)).rounded()
            S = ((Fp - om) * si(I(ch * m, ch * m), series_terms=ST)).rounded()
            Rn += h * R.hi
            In += h * S.hi
    tR, tI = true_nodes(c)
    print("  VALIDATION at c = 27/4, D = 1 (shipped interval arithmetic vs mpmath)")
    print(f"    node sum, interval  R = {float(Rn):.12f}   I = {float(In):.12f}")
    print(f"    true integral mpmath R = {float(tR):.12f}   I = {float(tI):.12f}")
    print(f"    node-sum excess over true: R {float(Rn)-float(tR):+.3e}  "
          f"I {float(In)-float(tI):+.3e}")
    print(f"    Terr(27/4, 1) = {float(Terr(c,1)):.3e}   "
          f"(must dominate the excess above)")
    print(f"    M per segment: "
          f"{[M_of(c, SEGMENTS[s][1]) for s in range(1,7)]}")
    print()


if __name__ == "__main__":
    if "--check" in sys.argv:
        check()

    print("  cross-check vs producer-measured HYBRID Mc_lb (mclb_scan.txt):")
    print(f"  {'c':>8} {'all-mid D=1':>13} {'D=2':>13} {'D=4':>13}"
          f" {'hybrid(meas)':>13}")
    for c, mv in ((F(55, 8), 0.14684818), (F(8), 0.08528181),
                  (F(10), 0.00751429), (F(21, 2), -0.00538046)):
        print(f"  {str(c):>8} {float(mc_lb(c,1)):>13.8f} "
              f"{float(mc_lb(c,2)):>13.8f} {float(mc_lb(c,4)):>13.8f}"
              f" {mv:>13.8f}")
    print()
    print("  Mc_lb(13) by density  (the ceiling question):")
    for D in DLAD:
        m = mc_lb(F(13), D)
        lr = L0_val(F(13) - F(1, 128)) * F(1, 128)
        print(f"    D = {D:>3}  Mc_lb = {float(m):>+12.8f}   "
              f"L0*r(1/128) = {float(lr):.8f}   "
              f"{'PASS ' + format(float(m/lr), '.1f') + 'x' if m > lr else 'FAIL'}")
    print()

    print("=" * 96)
    print("DENSITY LADDER TO c = 13   (all-midpoint, 6D modules of 8 panels, "
          "~7m30s each, serial)")
    print("=" * 96)
    f = F(109, 16)
    boxes = []
    while f < 13 and len(boxes) < 500:
        best = None
        for r in RLAD:
            c = f + r
            if r >= c:
                continue
            lr = L0_val(c - r) * r
            for D in DLAD:
                m = mc_lb(c, D)
                if m <= 0 or not (m > SAFETY * mp.mpf(lr.numerator) / lr.denominator):
                    continue
                cost = 6 * D * MIN_PER_MODULE
                key = cost / (2.0 * float(r))
                if best is None or key < best[0]:
                    best = (key, c, r, D, m, lr, cost)
                break
        if best is None:
            print(f"  STOP: no (r, D) works at frontier {float(f):.6f}")
            break
        _, c, r, D, m, lr, cost = best
        boxes.append((c, r, D, m, lr, cost))
        f = c + r
    print(f"{'#':>4} {'centre c':>11} {'r':>9} {'D':>4} {'Mc_lb':>12}"
          f" {'L0*r':>11} {'ratio':>8} {'mods':>6} {'h/box':>7}")
    tot_h = 0.0
    tot_mod = 0
    for i, (c, r, D, m, lr, cost) in enumerate(boxes, 1):
        tot_h += cost / 60.0
        tot_mod += 6 * D
        if i <= 8 or i > len(boxes) - 10:
            print(f"{i:>4} {str(c):>11} {str(r):>9} {D:>4} {float(m):>12.8f}"
                  f" {float(lr):>11.8f} {float(m)/float(lr):>7.1f}x {6*D:>6}"
                  f" {cost/60.0:>7.2f}")
        elif i == 9:
            print(f"{'':>4} {'...':>11}")
    print("-" * 96)
    print(f"  {len(boxes)} boxes, frontier {float(f):.6f}  "
          f"{'REACHED 13' if f >= 13 else 'STOPPED SHORT of 13'}")
    print(f"  {tot_mod} panel modules, {tot_h:.1f} h serial "
          f"({tot_h/24:.1f} days continuous)")
    print()
    grp = {}
    for c, r, D, m, lr, cost in boxes:
        grp.setdefault(D, []).append(float(c))
    print("  THE LADDER (density vs centre):")
    for D in sorted(grp):
        cs = grp[D]
        print(f"    D = {D:>2}   {6*D:>3} modules  {6*D*MIN_PER_MODULE/60:>4.1f} h/box"
              f"   : {len(cs):>3} boxes, c in [{min(cs):.4f}, {max(cs):.4f}]")
    print()
    print(f"  vs Rio's ~6 h x boxes = {len(boxes)*6} h : ladder is {tot_h:.0f} h"
          f"  ({tot_h/(len(boxes)*6 or 1):.2f}x)")
