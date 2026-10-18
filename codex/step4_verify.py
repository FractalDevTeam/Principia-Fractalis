#!/usr/bin/env python3
"""
Step-4 chain-closure measurement: midpoint vs range-brick at c = 27/4,
on the ONE segment where both exist (u in [0, 0.25], 8 panels of width 1/32).

CRITICAL: the two files integrate DIFFERENT functions.
  Seg01Range   : nodeR_fourier_plus_at_c27_4_N3 u = (e^(u/2)+1)*omega_N3(e^u)*cos(3.375u)
  Seg01Midpoint: f_plus u = sum_{n<3} fourier_plus_term(27/4,n,u)
                          = (e^(u/2)+1)*[sum_{n<3} 2 e^{-pi(n+1)^2 e^u}]*cos(3.375u)
Since omega_N3(x) = sum_{m=1..3} e^{-pi m^2 x}, we get f_plus = 2*nodeR.
(The Midpoint file's header says "Equal to nodeR.../2" -- that is BACKWARDS.
 Verified numerically below.)
So midpoint enclosures are divided by 2 to compare on nodeR.
"""
import math
import mpmath as mp

mp.mp.dps = 30
PI = math.pi
H = 0.03125
NP = 8

# ---------------------------------------------------------------- integrands
def omega_N3(x):
    return sum(math.exp(-PI * m * m * x) for m in (1, 2, 3))


def nodeR_plus(u):
    return (math.exp(u / 2) + 1) * omega_N3(math.exp(u)) * math.cos(3.375 * u)


def nodeR_minus(u):
    return (math.exp(u / 2) - 1) * omega_N3(math.exp(u)) * math.sin(3.375 * u)


def f_plus(u):
    return sum((math.exp(u / 2) + 1) * (2 * math.exp(-(PI * (n + 1) ** 2) * math.exp(u)))
               * math.cos(27 / 4 / 2 * u) for n in range(3))


def f_minus(u):
    return sum((math.exp(u / 2) - 1) * (2 * math.exp(-(PI * (n + 1) ** 2) * math.exp(u)))
               * math.sin(27 / 4 / 2 * u) for n in range(3))


print("=" * 78)
print("0. WHICH FACTOR?  (the Midpoint header's claim, checked)")
print("=" * 78)
for u in (0.0, 0.125, 0.25):
    print(f"  u={u:<6} nodeR_plus={nodeR_plus(u):.8f}  f_plus={f_plus(u):.8f}"
          f"   f_plus/nodeR = {f_plus(u)/nodeR_plus(u):.6f}")
print("  => f_plus = 2 * nodeR.  The header's 'f_plus = nodeR/2' is INVERTED.")

# ---------------------------------------------------------------- the data
# Seg01Range: (min, max) per panel; enclosure = H*min .. H*max, on nodeR
RB_PLUS = [(0.0777946458, 0.0871153865), (0.0695584332, 0.0790293797),
           (0.0612768597, 0.0706710692), (0.0531429430, 0.0622646233),
           (0.0453200966, 0.0540061776), (0.0379412643, 0.0460618751),
           (0.0311090392, 0.0385669683), (0.0248966753, 0.0316259207)]
RB_MINUS = [(-0.0004319087, 0.0005035551), (-0.0006845017, 0.0010608281),
            (-0.0007925833, 0.0016329981), (-0.0007892608, 0.0021862658),
            (-0.0007050125, 0.0026925839), (-0.0005669926, 0.0031300677),
            (-0.0003985704, 0.0034831003), (-0.0002190928, 0.0037421586)]
# Seg01Midpoint: already-integrated enclosures, on f_plus = 2*nodeR
MP_PLUS = [(0.001339650265625, 0.008969044815625), (0.000827672609375, 0.008457067159375),
           (0.000306030540625, 0.007935425090625), (-0.000212225671875, 0.007417168878125),
           (-0.000715855959375, 0.006913538590625), (-0.001195518153125, 0.006433876396875),
           (-0.001643791459375, 0.005985603090625), (-0.002055140646875, 0.005574253903125)]
MP_MINUS = [(-0.003813634534375, 0.003815760015625), (-0.003806018453125, 0.003823376096875),
            (-0.003792973084375, 0.003836421465625), (-0.003776597634375, 0.003852796915625),
            (-0.003758747446875, 0.003870647103125), (-0.003740995534375, 0.003888399015625),
            (-0.003724610871875, 0.003904783678125), (-0.003710552546875, 0.003918842003125)]

print()
print("=" * 78)
print("1. PER-PANEL ENCLOSURE WIDTH, both on nodeR  (lower is better)")
print("=" * 78)
print(f"  {'panel':>5} {'range-brick':>14} {'midpoint/2':>14} {'ratio':>10}  (plus side)")
rb_w_tot = mp_w_tot = 0.0
for i in range(NP):
    rb_w = H * (RB_PLUS[i][1] - RB_PLUS[i][0])
    mp_w = (MP_PLUS[i][1] - MP_PLUS[i][0]) / 2
    rb_w_tot += rb_w
    mp_w_tot += mp_w
    print(f"  {i:>5} {rb_w:>14.4e} {mp_w:>14.4e} {mp_w/rb_w:>9.1f}x")
print(f"  {'TOTAL':>5} {rb_w_tot:>14.4e} {mp_w_tot:>14.4e} {mp_w_tot/rb_w_tot:>9.1f}x")

print()
print(f"  {'panel':>5} {'range-brick':>14} {'midpoint/2':>14} {'ratio':>10}  (minus side)")
rb_wm_tot = mp_wm_tot = 0.0
for i in range(NP):
    rb_w = H * (RB_MINUS[i][1] - RB_MINUS[i][0])
    mp_w = (MP_MINUS[i][1] - MP_MINUS[i][0]) / 2
    rb_wm_tot += rb_w
    mp_wm_tot += mp_w
    print(f"  {i:>5} {rb_w:>14.4e} {mp_w:>14.4e} {mp_w/rb_w:>9.1f}x")
print(f"  {'TOTAL':>5} {rb_wm_tot:>14.4e} {mp_wm_tot:>14.4e} {mp_wm_tot/rb_wm_tot:>9.1f}x")

print()
print("=" * 78)
print("2. IS THE M = 3000 BOUND THE CAUSE?  true M measured")
print("=" * 78)
# true max |f''| on [0, 0.25] -- computed in mpmath-native arithmetic
# (mp.diff on a float-returning lambda silently returns 0).
def fp_mp(u):
    return sum((mp.e**(u / 2) + 1) * (2 * mp.e**(-(mp.pi * (n + 1)**2) * mp.e**u))
               * mp.cos(mp.mpf(27) / 8 * u) for n in range(3))


def fm_mp(u):
    return sum((mp.e**(u / 2) - 1) * (2 * mp.e**(-(mp.pi * (n + 1)**2) * mp.e**u))
               * mp.sin(mp.mpf(27) / 8 * u) for n in range(3))


grid = [mp.mpf(1) / 4 * k / 400 for k in range(401)]
Mp = float(max(abs(mp.diff(fp_mp, u, 2)) for u in grid))
Mm = float(max(abs(mp.diff(fm_mp, u, 2)) for u in grid))
print(f"  true max|f_plus''|  on [0,0.25] = {Mp:.4f}")
print(f"  true max|f_minus''| on [0,0.25] = {Mm:.4f}")
print(f"  M used in the landed file        = 3000  -> crude by {3000/max(Mp,Mm):.0f}x")
err3000 = 3000 * H**3 / 24
print(f"  per-panel error at M=3000        = {err3000:.9e}"
      f"   matches the file literal 0.003814697265625: "
      f"{abs(err3000 - 0.003814697265625) < 1e-15}")
rb_half_plus = H * (RB_PLUS[0][1] - RB_PLUS[0][0]) / 2
Mbreak = rb_half_plus * 2 * 24 / H**3
print(f"  range-brick per-panel half-width (nodeR) = {rb_half_plus:.4e}")
print(f"  break-even M = {Mbreak:.1f}  -> 3000 is {3000/Mbreak:.1f}x too big")
for M, lab in ((7.5, "7.5 (provable)"), (Mp, "true")):
    half = M * H**3 / 24 / 2
    print(f"  at M={lab:<16}: half-width {half:.4e} -> "
          f"{rb_half_plus/half:.1f}x TIGHTER than the range brick")

print()
print("=" * 78)
print("3. SEGMENT TOTALS on nodeR, and do they even enclose the truth?")
print("=" * 78)
true_p = float(mp.quad(lambda x: nodeR_plus(float(x)), [0, 0.25]))
true_m = float(mp.quad(lambda x: nodeR_minus(float(x)), [0, 0.25]))
rb_lo = sum(H * a for a, _ in RB_PLUS); rb_hi = sum(H * b for _, b in RB_PLUS)
mp_lo = sum(a for a, _ in MP_PLUS) / 2; mp_hi = sum(b for _, b in MP_PLUS) / 2
print(f"  true   int_0^0.25 nodeR_plus  = {true_p:.8f}")
print(f"  range-brick  [{rb_lo:.8f}, {rb_hi:.8f}]  width {rb_hi-rb_lo:.4e}"
      f"  encloses: {rb_lo <= true_p <= rb_hi}")
print(f"  midpoint/2   [{mp_lo:.8f}, {mp_hi:.8f}]  width {mp_hi-mp_lo:.4e}"
      f"  encloses: {mp_lo <= true_p <= mp_hi}")
rb_lom = sum(H * a for a, _ in RB_MINUS); rb_him = sum(H * b for _, b in RB_MINUS)
mp_lom = sum(a for a, _ in MP_MINUS) / 2; mp_him = sum(b for _, b in MP_MINUS) / 2
print(f"  true   int_0^0.25 nodeR_minus = {true_m:.8f}")
print(f"  range-brick  [{rb_lom:.8f}, {rb_him:.8f}]  width {rb_him-rb_lom:.4e}"
      f"  encloses: {rb_lom <= true_m <= rb_him}")
print(f"  midpoint/2   [{mp_lom:.8f}, {mp_him:.8f}]  width {mp_him-mp_lom:.4e}"
      f"  encloses: {mp_lom <= true_m <= mp_him}")
