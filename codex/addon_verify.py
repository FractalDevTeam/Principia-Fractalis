#!/usr/bin/env python3
"""
Add-on tightening arithmetic for Gate-1, verified against the Lean source.

Sources (all quoted in the note):
  residue : PF/Analytic/FourierPanels/ResidueBound_c13_2_three_halves_to_5_2026_10_16.lean
            |f(u)| <= (exp(u/2)+1) * 3 * exp(-pi*exp u) on [3/2,5]
            current proven bound: (66/10^6)*(7/2) = 231/10^6
  omega   : PF/Analytic/PilotBoxes/R1_c13_2_r1_16_pointwise_CLOSED_2026_10_16.lean:700-736
            exp(-16pi)*(1/(16pi-1/2)+1/(16pi))*(23/22) <= (1/10^20)*(1/47.5+1/48)*(23/22)
            then DISCARDED to <= 1/10^4
  tail    : PF/Analytic/FourierPanels/AnalyticTailBound_c13_2_2026_10_16.lean:499
            1150/(2904*6436343) + 1150/(3454*6436343) <= 1/10^6

Budget (codex/R1R2R3_TARGET_REACHABLE_2026-10-16.md:106-127):
  Gate 1 needs  c^2*(R_ub-R) + c*(I_ub-I) <= 2*(Re xi(c) - Mc_lb) = Re xi(c)
  The add-on enters R_ub AND I_ub equally, so it costs addon*(c^2+c).
"""
import math

PI = math.pi
print("=" * 78)
print("1. THE OMEGA-GAP  -- Rio: 'the 100x is the hard one'")
print("=" * 78)
om_true_integrand = math.exp(-16 * PI) * (1 / (16 * PI - 0.5) + 1 / (16 * PI)) * (23 / 22)
om_proven = (1e-20) * (1 / (16 * 3 - 0.5) + 1 / (16 * 3)) * (23 / 22)
om_exported = 1e-4
print(f"  exact value of the bounded quantity      = {om_true_integrand:.4e}")
print(f"  value the Lean chain actually PROVES     = {om_proven:.4e}")
print(f"  value the Lean chain EXPORTS (epsOm)     = {om_exported:.4e}")
print(f"  slack discarded in the final norm_num    = {om_exported/om_proven:.3e} x")
print(f"  -> reaching 1e-6 needs a factor          = {om_exported/1e-6:.0f}x")
print(f"     and {1e-6/om_proven:.3e}x of headroom is ALREADY PROVEN. One norm_num bound.")

print()
print("=" * 78)
print("2. THE ANALYTIC TAIL  -- Rio: 'needs 10x'")
print("=" * 78)
t1 = 1150 / (2904 * 6436343)
t2 = 1150 / (3454 * 6436343)
tail_proven = t1 + t2
print(f"  value the Lean chain actually PROVES     = {tail_proven:.4e}")
print(f"  value it EXPORTS                         = {1e-6:.4e}")
print(f"  free slack in the final norm_num         = {1e-6/tail_proven:.2f} x")
print(f"  so 1e-6 -> {tail_proven:.3e} is free; 1e-7 is NOT reachable this way")
print(f"  (1.2e-7 is: {tail_proven:.4e} <= 1.2e-7 is {tail_proven <= 1.2e-7})")
# how tight is the underlying analysis?
print(f"  underlying sharpness: exp(-5pi)={math.exp(-5*PI):.4e} vs 1/23^5={1/23**5:.4e}"
      f"  ({(1/23**5)/math.exp(-5*PI):.3f}x)")

print()
print("=" * 78)
print("3. THE RESIDUE  -- Rio: '2-piece subdivision is free (32.8x)'")
print("=" * 78)


def g(u):
    """The majorant actually used in Lean."""
    return (math.exp(u / 2) + 1) * 3 * math.exp(-PI * math.exp(u))


A, B = 1.5, 5.0
res_current = 231 / 10**6
# g is strictly decreasing on [3/2,5] (verified in GATE_c13_2 note via g'/g < 0),
# so the left endpoint of each piece is its max.
print(f"  current proven bound                     = {res_current:.4e}")
print(f"  g(3/2) = {g(A):.4e}   g(5) = {g(B):.4e}   (decreasing: {g(A) > g(B)})")
print(f"  what the current bound really uses: 22*3*1e-6*3.5 "
      f"= {22*3*1e-6*3.5:.4e}  (22 is e^(u/2)+1 at u=5, 1e-6 is e^-14 rounded)")
print()
print("  n-piece left-endpoint bound on |int_{3/2}^{5} f|:")
print(f"  {'n':>4} {'bound':>12} {'gain vs current':>16} {'x over t=13 addon budget':>26}")
C13_BUDGET = 2.509e-3 / (13**2 + 13)      # addon alone, full budget
for n in (1, 2, 4, 7, 14, 28, 56):
    h = (B - A) / n
    bound = h * sum(g(A + i * h) for i in range(n))
    print(f"  {n:>4} {bound:>12.4e} {res_current/bound:>15.1f}x {bound/C13_BUDGET:>25.2f}x")
true_int = 0.0
N = 2000000
h = (B - A) / N
for i in range(N):
    true_int += g(A + (i + 0.5) * h)
true_int *= h
print(f"  true value of int g du                   = {true_int:.4e}  (the floor)")
print(f"  max possible gain from subdivision alone = {res_current/true_int:.1f}x")

print()
print("=" * 78)
print("4. THE BUDGET, and where the add-ons stand")
print("=" * 78)
for t, rexi in ((6.5, None), (13.0, 2.509e-3), (14.5, 4.142e-4)):
    if rexi is None:
        continue
    w = t**2 + t
    budget = rexi / w
    print(f"\n  t = {t}:  Re xi = {rexi:.4e},  add-on weight (c^2+c) = {w:.2f}")
    print(f"    full add-on budget (leaves 0 for panels) = {budget:.4e}")
    stale = 231 / 279841 + 1e-6 + 1e-4
    cur = 231 / 10**6 + 1e-6 + 1e-4
    print(f"    STALE add-on total (c=51/8 residue)      = {stale:.4e}"
          f"   -> {stale/budget:.1f}x over")
    print(f"    CURRENT add-on total (c=13/2 residue)    = {cur:.4e}"
          f"   -> {cur/budget:.1f}x over")
    # after free fixes
    for n in (1, 2, 4, 7, 14, 28):
        hh = (B - A) / n
        rb = hh * sum(g(A + i * hh) for i in range(n))
        tot = rb + tail_proven + om_proven
        flag = "FITS with room for panels" if tot < 0.1 * budget else (
            "fits, no panel room" if tot < budget else "STILL OVER")
        print(f"    free omega+tail, residue {n:>2} pieces        = {tot:.4e}"
              f"   -> {tot/budget:>7.2f}x   {flag}")
