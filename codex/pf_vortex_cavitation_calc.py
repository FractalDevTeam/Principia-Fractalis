#!/usr/bin/env python3
"""Reproducible numbers for codex/PF_VORTEX_CAVITATION_WHOLE_TOE_INVESTIGATION.md.

Stdlib only.  Every PF coefficient used here is read off the book at the cited
line; none is chosen to reproduce an effect.  Benchmark inputs are the values
extracted from Madabhushi & Mahesh (JFM 1027 A15, 2026) and Knister, Ganesh &
Ceccio (JFM 1034 A37, 2026); they are marked EXTRACTED and must be re-checked
against the PDFs before any external use.

Run:  python codex/pf_vortex_cavitation_calc.py
"""
import math

PI = math.pi

# ---------------------------------------------------------------- constants
c = 2.99792458e8          # m/s
G = 6.67430e-11           # m^3 kg^-1 s^-2
kB = 1.380649e-23         # J/K
LAMBDA_OBS = 1.1e-52      # m^-2 (Planck 2018 order of magnitude)
rho_w = 998.0             # kg/m^3, water ~20 C
nu_w = 1.0e-6             # m^2/s

# ------------------------------------------------- PF postulated constants
CH2_THRESHOLD = 0.95      # ch06:180, ch08:79
PI_OVER_10 = PI / 10      # ch10 Lemma (Consciousness Regularization)
CH2_RING, CH2_HAIRPIN, CH2_ISO = 0.85, 0.70, 0.60   # ch10:493-495 (asserted)


def section(t):
    print("\n" + "=" * 72 + "\n" + t + "\n" + "=" * 72)


# ------------------------------------------------------------------ S1
section("S1  PF effective viscosity (ch10 Thm Enhanced Energy Inequality)")


def nu_eff_ratio(ch2):
    """nu_eff/nu = 1 + (pi/10)(0.95 - ch2)   [ch10:197-200]"""
    return 1 + PI_OVER_10 * (CH2_THRESHOLD - ch2)


for name, v in [("ch2=0 (book: 'no consciousness')", 0.0),
                ("isotropic turbulence 0.60", CH2_ISO),
                ("hairpin 0.70", CH2_HAIRPIN),
                ("vortex ring 0.85", CH2_RING),
                ("threshold 0.95", 0.95),
                ("ch2=1.00 (book: 'effect reverses')", 1.0)]:
    print(f"  {name:38s} nu_eff/nu = {nu_eff_ratio(v):.5f}")
print(f"  note: 1 + 0.095*pi = {1 + 0.095 * PI:.5f}  (0.095 = 0.95/10; the only"
      " in-tree source of the digits '0.095')")

# ------------------------------------------------------------------ S2
section("S2  ch10 Step 3 vs Step 4: opposite monotonicity in ch2")
print("  Step 3 coefficient (10/pi)*ch2*0.95   vs   Step 4 claim (pi/10)*(0.95-ch2)")
for v in (0.0, 0.3, 0.6, 0.85, 0.95):
    print(f"  ch2={v:4.2f}   step3={10 / PI * v * 0.95:7.4f}   step4={PI_OVER_10 * (0.95 - v):7.4f}")
print("  -> step3 increases from 0; step4 decreases to 0.  The 'approx' at ch10:131-136 is false"
      " for every ch2 except one crossing point:")
x = 0.95 * PI_OVER_10 / (10 / PI * 0.95 + PI_OVER_10)
print(f"     crossing at ch2 = {x:.5f}")

# ------------------------------------------------------------------ S3
section("S3  ch10 consciousness length scale: unit dependence")


def ell_c(nu, ch2, omega_c):
    return math.sqrt((CH2_THRESHOLD - ch2) * nu / omega_c)


print("  ell_c = sqrt(nu_c/omega_c), omega_c = pi/10 with NO stated unit [ch10:442].")
for unit, w in (("pi/10 per second", PI_OVER_10),
                ("pi/10 per millisecond", PI_OVER_10 * 1e3),
                ("pi/10 per hour", PI_OVER_10 / 3600)):
    print(f"  water, ch2=0.60, omega_c={unit:22s} ell_c = {ell_c(nu_w, 0.60, w):.3e} m")
print(f"  book's air example (nu=1.5e-5, ch2=0.90, per second): "
      f"{ell_c(1.5e-5, 0.90, PI_OVER_10):.3e} m   (book prints 1.0e-3 m, ch10:461)")

# ------------------------------------------------------------------ S4
section("S4  Benchmark vortex: Lamb-Oseen core pressure and PF perturbation")
# EXTRACTED benchmark values (Madabhushi & Mahesh; Knister et al.)
U = 10.0                  # m/s      (Knister: U0 = 10 m/s at Re_c = 1.67e6)
chord = 0.169             # m        (M&M: c = 169 mm; Knister: 167 mm)
rc_weak = 6.4e-3          # m        (M&M: weaker core radius at x/c = 0.67)
Cp_mean_min = -0.75       # M&M: mean minimum core Cp at x/c = 0.7
Cp_vap = -2.0             # M&M: vapour-pressure threshold
x_incep = (1.1, 1.7)      # M&M: most probable inception region x/c
q = 0.5 * rho_w * U * U
a0 = rc_weak / 1.12091    # Lamb-Oseen: u_theta max at r = 1.12091 a
dp = -Cp_mean_min * q
Gamma = math.sqrt(dp * 4 * PI * PI * a0 * a0 / (rho_w * math.log(2)))
print(f"  dynamic pressure q = {q:.0f} Pa;  a0 = {a0 * 1e3:.2f} mm")
print(f"  circulation inferred from Cp_min=-0.75 via dp = rho Gamma^2 ln2/(4 pi^2 a^2):"
      f" Gamma = {Gamma:.3f} m^2/s (Re_Gamma = {Gamma / nu_w:.2e})   [INFERRED, not a paper value]")
t_transit = (x_incep[1] - 0.67) * chord / U
lam_growth = 4 * nu_w * t_transit / a0 ** 2
print(f"  transit time x/c 0.67 -> 1.7: {t_transit * 1e3:.2f} ms")
print(f"  laminar core growth 4 nu t / a0^2 = {lam_growth:.3e}")
for name, v in (("ch2=0", 0.0), ("ring 0.85", CH2_RING)):
    extra = (nu_eff_ratio(v) - 1) * lam_growth
    print(f"  PF extra growth ({name:9s}): d(a^2)/a^2 = {extra:.3e}"
          f"  -> |dCp/Cp| = {extra:.3e}  -> |dCp| at Cp=-2: {2 * extra:.3e}")
print("  benchmark uncertainties (EXTRACTED): pressure reconstruction ~10% (Knister);"
      " LES grid convergence <3% in Cp_min (M&M); nuclei factor ~4 (Knister).")
worst = (nu_eff_ratio(0.0) - 1) * lam_growth
print(f"  ratio (10% measurement uncertainty)/(largest PF shift) = {0.10 / worst:.0f}x")
# Stretching, by contrast (ordinary hydrodynamics):
print("  ordinary mechanism for comparison: core radius reduction x1.5 by stretching"
      f" -> Cp scales by 1.5^2 = {1.5 ** 2:.2f} (M&M report 3-4x drop).")

# ------------------------------------------------------------------ S5
section("S5  ch06:476 matrix formula applied to a velocity gradient")
print("  ch2(W) = (Tr(W^2) - (Tr W)^2) / (2 ||W||_F^2).  For W = grad u = S + A,")
print("  Tr W = 0 (incompressible):  ch2 = (|S|^2 - |A|^2)/(2(|S|^2+|A|^2)) = -Q/|grad u|^2.")
print("  Range [-1/2, +1/2]; the 0.95 gate is unreachable (Lean: ch2Matrix_lt_threshold).")


def lamb_oseen_ch2(r, a=1.0, Gam=1.0):
    e = math.exp(-(r / a) ** 2)
    ut_over_r = Gam / (2 * PI * r * r) * (1 - e)
    dut_dr = Gam / (2 * PI) * (-(1 - e) / r ** 2 + 2 * e / a ** 2)
    s = 0.5 * (dut_dr - ut_over_r)        # S_r_theta
    w = 0.5 * (dut_dr + ut_over_r)        # rotation rate = omega/2
    S2, A2 = 2 * s * s, 2 * w * w
    return (S2 - A2) / (2 * (S2 + A2))


for r in (1e-4, 0.5, 1.0, 1.12091, 1.5, 2.0, 4.0):
    print(f"  Lamb-Oseen r/a = {r:7.4f}   ch2 = {lamb_oseen_ch2(r):+.4f}")
lo, hi = 0.5, 3.0
for _ in range(80):
    mid = 0.5 * (lo + hi)
    if lamb_oseen_ch2(mid) < 0:
        lo = mid
    else:
        hi = mid
print(f"  Q = 0 (ch2 = 0) at r/a = {lo:.4f}")
print("  -> vortex axis (the book's 'emergence point', v=0, omega!=0) has ch2 = -1/2,")
print("     the value FARTHEST from the 0.95 gate under this map.")

# ------------------------------------------------------------------ S6
section("S6  Checks (a),(b): counter-rotation, angular momentum, energy")
b = 0.011                 # m, EXTRACTED trailing-edge separation (M&M)
print(f"  side-by-side pair, +-Gamma, separation b: velocity at midpoint = 2 Gamma/(pi b)"
      f" = {2 * Gamma / (PI * b):.2f} m/s  (NOT zero: induced velocities ADD)")
print(f"  linear impulse per unit length rho*Gamma*b = {rho_w * Gamma * b:.3f} kg/s (nonzero)")
Ro, Ri, Gam = 2.0, 1.0, 1.0
L = -0.5 * (Gam * Ro ** 2 / 2 - Gam * Ri ** 2 / 2)
print(f"  nested uniform patches (ch22 Def), Gamma_in=-Gamma_out, R_out=2 R_in:"
      f" L_z/rho = -1/2 * int r^2 omega dA = {L:+.3f} Gamma R_in^2  (nonzero unless R_out=R_in)")
print("  two rotors I1,I2 with w2=-w1:  L = (I1-I2) w1,  E = (I1+I2) w1^2/2 > 0.")

# ------------------------------------------------------------------ S7
section("S7  Checks (c),(d): what Lambda-suppression can do locally")
rho_L = LAMBDA_OBS * c ** 2 / (8 * PI * G)
print(f"  observed vacuum density  rho_Lambda = {rho_L:.2e} kg/m^3 = {rho_L * c * c:.2e} J/m^3")
print(f"  de Sitter acceleration Lambda c^2 r/3 at r=1 m: {LAMBDA_OBS * c * c / 3:.2e} m/s^2")
ke = 0.5 * rho_w * U * U
print(f"  vortex kinetic energy density (u=10 m/s): {ke:.2e} J/m^3;"
      f" ratio vacuum/KE = {rho_L * c * c / ke:.1e}")
print(f"  ordinary GR: KE mass-equivalent / rest mass = {ke / (rho_w * c * c):.1e}")
X = 78 * PI * 0.95 * 1.1875
print(f"  Lean 'zeroPointReservoir' = exp({X:.3f}) = 10^{X / math.log(10):.2f}"
      "  (dimensionless; compared in Lean against omega^2 in unstated units)")
V_P = (1.616255e-35) ** 3
beta_lab = (1e-3 / V_P) * 0.85 * 1e-55
print(f"  ch26:246 normalisation transplanted to a 1-litre ch2=0.85 vortex:"
      f" exponent = {beta_lab:.1e}  (vs 276 for the whole universe) -> not transplantable")

# ------------------------------------------------------------------ S8
section("S8  ch08:290 conversion formula: units and arithmetic")
val = c * c * kB * 1.0 * 1e11
print(f"  c^2 * k_B * (1 Hz) * 1e11 = {val:.3e}  in units J*m^2/(K*s^3)  (not watts)")
print("  book prints 1e-16 J/s (ch08:297).  Neither the unit nor the number follows.")

# ------------------------------------------------------------------ S9
section("S9  Pressure-offset observable Pi = p_true - p_NS (doc section 5)")
print("  ch10 Step-3 closure with uniform Psi: force = -grad[(5/pi) ch2 Psi Phi^2]")
print("  -> zero work on incompressible flow; only a pressure offset Pi.")
Pi_scale = 0.10 * abs(Cp_vap) * q
print(f"  scale below which the benchmarks cannot see Pi: 10% of |Cp_v| q = {Pi_scale:.0f} Pa")
print("  (order of magnitude only: nuclei-population uncertainty is a factor ~4,")
print("   and velocimetry-reconstructed pressure is p_NS, blind to Pi by construction)")
