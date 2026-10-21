#!/usr/bin/env python3
"""
Price moving the midpoint/range boundary from T <= 1/2 to the actual Tier-A
limit T <= 693/1000 < log 2.

The producer currently puts midpoint on the first 2D sub-segments, i.e. u up to
1/2. But the tier constant it emits is `exp(T) <= 2`, which is valid for every
T <= log 2 = 0.693147..., and the preamble already asserts T <= 693/1000. So
sub-segments out to u = 0.6875 are Tier A and could be on midpoint TODAY, with
no new tier, no new Lean, and no change to the M-bound proof.

That matters because midpoint beats range-brick on this region from D >= 4
(measured, price5: at c = 13 base segment 3 is 3.9x better on midpoint at
D = 4 and 15.8x at D = 16), and base segment 3 is exactly where the
per-segment optimum wanted midpoint -- the thing I had priced as needing the
Tier-B M bound. Most of that benefit turns out to be free.

This prices it at SUB-SEGMENT granularity, which the earlier models could not:
the new boundary cuts base segment 3 partway (11 of 12 sub-segments at D = 4),
so a 6-character per-base-segment scheme cannot express it.

Byte-identity at D = 1 is preserved: floor(4*1*693/1000) = 2, unchanged.
"""
import io
import os
import sys
from fractions import Fraction as F

import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from price_density import ADDON, M_of, tier          # noqa: E402

mp.mp.dps = 30
HERE = os.path.dirname(os.path.abspath(__file__))
RG = os.path.join(HERE, "gen", "gen_fourier_panels_c27_4.py")
_g = {"__name__": "_g", "__file__": RG}
exec(compile(io.open(RG, encoding="utf-8").read(), RG, "exec"), _g)
I = _g["I"]
epi, ci, si = _g["exp_pos_interval"], _g["cos_interval"], _g["sin_interval"]
oi = _g["omega_N3_interval"]
ST = 50
TIER_A_MAX = F(693, 1000)

_fc = {}


def fcache(a, b):
    k = (a, b)
    if k not in _fc:
        E = epi(I(a * F(1, 2), b * F(1, 2)), series_terms=ST)
        om = oi(epi(I(a, b), series_terms=ST), series_terms=ST)
        Fp = (E * om).rounded()
        _fc[k] = ((Fp + om).rounded(), (Fp - om).rounded())
    return _fc[k]


def subseg_ub(c, s, D, scheme):
    """(R_ub, I_ub) for sub-segment s (1-based, of 6D) at density D.
    Sub-segment s covers [(s-1)/(4D), s/(4D)] with 8 panels of width 1/(32D) --
    exactly the producer's geometry."""
    ch = F(c) / 2
    h = F(1, 32 * D)
    lo = F(s - 1, 4 * D)
    hi = F(s, 4 * D)
    R = Iv = F(0)
    if scheme == "mid":
        # the producer uses the SUB-segment's own T, which is smaller than the
        # base segment's and so gives a smaller M
        assert hi <= TIER_A_MAX, f"sub-segment {s} T={hi} exceeds Tier A"
        err = F(M_of(c, hi)) * h ** 3 / 24
    for k in range(8):
        a = lo + k * h
        if scheme == "rng":
            P, Q = fcache(a, a + h)
            cu = I(ch * a, ch * (a + h))
            R += h * (P * ci(cu, series_terms=ST)).rounded().hi
            Iv += h * (Q * si(cu, series_terms=ST)).rounded().hi
        else:
            m = a + h / 2
            P, Q = fcache(m, m)
            cu = I(ch * m, ch * m)
            R += h * (P * ci(cu, series_terms=ST)).rounded().hi + err / 2
            Iv += h * (Q * si(cu, series_terms=ST)).rounded().hi + err / 2
    return R, Iv


def mc_lb_sub(c, D, n_mid):
    """Mc_lb with the first n_mid of 6D sub-segments on midpoint."""
    R = Iv = F(0)
    for s in range(1, 6 * D + 1):
        a, b = subseg_ub(c, s, D, "mid" if s <= n_mid else "rng")
        R += a
        Iv += b
    cc = mp.mpf(F(c).numerator) / F(c).denominator
    ad = mp.mpf(ADDON.numerator) / ADDON.denominator
    gate = cc ** 2 * (mp.mpf(R.numerator) / R.denominator + ad) \
        + cc * (mp.mpf(Iv.numerator) / Iv.denominator + ad)
    return (1 - gate) / 2


def Q_of(c, r):
    x = c - r
    return F(1, 11) * (1 + 1 / x) + F(1, 2) / x ** 2


if __name__ == "__main__":
    print("=" * 84)
    print("MIDPOINT BOUNDARY: first 2D sub-segments (u<=1/2) vs Tier-A limit "
          "(u<=0.6875)")
    print("=" * 84)
    print(f"{'c':>7} {'D':>3} {'n_mid now':>10} {'n_mid max':>10} "
          f"{'Mc_lb now':>12} {'Mc_lb max':>12} {'gain':>7} {'r':>7} {'verdict':>22}")
    SAFETY = mp.mpf("1.25")
    for c, D, r in ((F(41, 4), 2, F(1, 16)), (F(11), 4, F(1, 16)),
                    (F(23, 2), 4, F(1, 32)), (F(12), 8, F(1, 32)),
                    (F(25, 2), 8, F(1, 64)), (F(13), 16, F(1, 64))):
        now = 2 * D
        mx = int(TIER_A_MAX * 4 * D)
        m_now = mc_lb_sub(c, D, now)
        m_max = mc_lb_sub(c, D, mx)
        qr = Q_of(c, r) * r
        need = SAFETY * mp.mpf(qr.numerator) / qr.denominator
        v_now = "PASS" if m_now > need else "FAIL"
        v_max = "PASS" if m_max > need else "FAIL"
        verdict = f"{v_now} -> {v_max}"
        if v_now == "FAIL" and v_max == "PASS":
            verdict += "  RUNG SAVED"
        print(f"{str(c):>7} {D:>3} {now:>10} {mx:>10} "
              f"{float(m_now):>12.8f} {float(m_max):>12.8f} "
              f"{float(m_max/m_now) if m_now > 0 else float('nan'):>6.2f}x "
              f"{str(r):>7} {verdict:>22}")
