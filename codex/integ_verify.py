#!/usr/bin/env python3
"""
Riemann integration scoping: how do the landed pieces combine?

Parses the c=27/4 range-brick and midpoint segment files theorem by theorem and
compares, PER SEGMENT, the enclosure half-width each scheme delivers for
int_0^1.5 nodeR_{plus,minus}. Then does the Gate-1 arithmetic.

Key structural point this tests: the midpoint error is M*h^3/24 per panel with M
GROWING with u (24,24,30,30,72,72 over the six segments), while the range-brick
spread SHRINKS with u because the integrand decays. So midpoint need not win
everywhere, and the right scheme may be per-segment.

Convention: both schemes are normalised onto nodeR. The midpoint files integrate
f_plus = 2*nodeR (verified 2026-10-18), so midpoint widths are halved.
"""
import re
import os
import mpmath as mp

mp.mp.dps = 25
BASE = ("/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code/"
        "PF/Analytic/FourierPanels/")
H = 1.0 / 32
MIDPOINT_M = {1: 24, 2: 24, 3: 30, 4: 30, 5: 72, 6: 72}
NPANEL = 8


def parse_range(seg):
    """Range brick: width*min <= int <= width*max per panel. Returns
    (plus_total_width, minus_total_width) for the segment, on nodeR."""
    path = f"{BASE}Seg0{seg}Range_c27_4_2026_10_16.lean"
    txt = open(path, encoding="utf-8").read()
    out = {}
    for m in re.finditer(
            r"theorem (s\d+p\d+_(plus|minus))_integral_bound\s*:(.*?):= by",
            txt, re.DOTALL):
        name, side, body = m.group(1), m.group(2), m.group(3)
        vals = re.findall(r"\(0\.03125 : ℝ\) \* \((-?[0-9.]+) : ℝ\)", body)
        assert len(vals) == 2, (name, vals)
        lo, hi = float(vals[0]), float(vals[1])
        out.setdefault(side, []).append(H * (hi - lo))
    return sum(out["plus"]), sum(out["minus"]), len(out["plus"])


def midpoint_width(seg):
    """Midpoint: 2*(M h^3/24) per panel on f_plus = 2*nodeR, so on nodeR the
    half-width is M h^3/24/2 and the full width is M h^3/24."""
    M = MIDPOINT_M[seg]
    per_panel_on_nodeR = M * H ** 3 / 24          # full width on nodeR
    return NPANEL * per_panel_on_nodeR


print("=" * 86)
print("Q1a — PER-SEGMENT ENCLOSURE WIDTH on nodeR (lower is better)")
print("=" * 86)
print(f"{'seg':>4} {'u-range':>14} {'M':>4} {'range-brick +':>15} "
      f"{'range-brick -':>15} {'midpoint':>12} {'winner':>12}")
rb_p_tot = rb_m_tot = mp_tot_p = mp_tot_m = 0.0
best_p = best_m = 0.0
ranges = {1: "[0, .25]", 2: "[.25, .5]", 3: "[.5, .75]",
          4: "[.75, 1]", 5: "[1, 1.25]", 6: "[1.25, 1.5]"}
for seg in range(1, 7):
    rp, rm, n = parse_range(seg)
    mw = midpoint_width(seg)
    assert n == NPANEL, (seg, n)
    rb_p_tot += rp
    rb_m_tot += rm
    mp_tot_p += mw
    mp_tot_m += mw
    best_p += min(rp, mw)
    best_m += min(rm, mw)
    win = "midpoint" if mw < min(rp, rm) else (
        "range" if mw > max(rp, rm) else "mixed")
    print(f"{seg:>4} {ranges[seg]:>14} {MIDPOINT_M[seg]:>4} {rp:>15.4e} "
          f"{rm:>15.4e} {mw:>12.4e} {win:>12}")
print(f"{'TOT':>4} {'[0, 1.5]':>14} {'':>4} {rb_p_tot:>15.4e} "
      f"{rb_m_tot:>15.4e} {mp_tot_p:>12.4e}")
print()
print(f"  all range brick : dR = {rb_p_tot:.4e}   dI = {rb_m_tot:.4e}")
print(f"  all midpoint    : dR = {mp_tot_p:.4e}   dI = {mp_tot_m:.4e}")
print(f"  PER-SEGMENT BEST: dR = {best_p:.4e}   dI = {best_m:.4e}")

# ---------------------------------------------------------------- Gate 1
def xi(t):
    s = mp.mpc(1, t)
    return (mp.mpf(1) / 2 * s * (s - 1) * mp.power(mp.pi, -s / 2)
            * mp.gamma(s / 2) * mp.zeta(s))


ADDON = 8.2e-7          # after the 405x campaign (223354b9 chain)
ADDON_OLD = 3.32e-4     # before it

print()
print("=" * 86)
print("Q1b — GATE-1 ARITHMETIC.  budget = 2*Re xi(c) - 1/4 ; cost = c^2 dR + c dI")
print("=" * 86)
for c in (6.5, 6.75):
    budget = float(2 * mp.re(xi(c)) - mp.mpf(1) / 4)
    print(f"\n  c = {c}   budget = {budget:.7f}")
    rows = [
        ("range brick, old add-ons", rb_p_tot, rb_m_tot, ADDON_OLD),
        ("range brick, new add-ons", rb_p_tot, rb_m_tot, ADDON),
        ("all midpoint, new add-ons", mp_tot_p, mp_tot_m, ADDON),
        ("PER-SEGMENT BEST, new add-ons", best_p, best_m, ADDON),
    ]
    for label, dr, di, a in rows:
        cost = c ** 2 * (dr + a) + c * (di + a)
        m = budget - cost
        print(f"    {label:>32}: cost={cost:.7f}  "
              f"{'PASS' if m >= 0 else 'FAIL'} by {abs(m):.7f}")
