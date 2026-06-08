"""
MOND vs framework C^μν comparison.

MOND (Milgrom 1983):
  - Below a_0 = 1.2e-10 m/s^2, gravity transitions from Newtonian to
    sqrt(g_N * a_0) regime.
  - Interpolation: nu(y) = (1 + sqrt(1 + 4/y))/2 with y = g_N/a_0.
  - Predicts flat rotation curves WITHOUT dark matter.
  - Successful at galaxy scale, problematic at cluster scale (Bullet etc.).

Framework C^μν:
  - Modifies T^μν → T^μν + C^μν in Einstein equation.
  - C^μν tied to consciousness substrate (galaxies, stars).
  - Predicts flat rotation curves via enclosed C-mass.

Both modify the effective gravity at galaxy scales without invoking
particulate dark matter. Both face the cluster-scale challenge.

This script:
  (a) compares rotation curve predictions for an NGC 3198-like baryon mass
  (b) identifies the a_0 / consciousness coupling translation
  (c) characterises where they agree / differ
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

G_NEWTON = 4.302e-6   # kpc (km/s)^2 / Msun
KPC_M = 3.0857e19
KMS_MS = 1e3
a0 = 1.2e-10 * (KPC_M / KMS_MS**2)  # convert m/s^2 → kpc/(km/s)^2/s^2 units
# Easier: keep a0 in m/s^2, convert g_N to m/s^2.

# Baryon point-mass approximation for outer rotation curve
M_baryon = 4.5e10  # Msun (NGC 3198-ish total disk+gas)

def g_newton_si(r_kpc, M):
    """Newtonian acceleration in m/s^2."""
    r_m = r_kpc * KPC_M
    return 6.674e-11 * (M * 1.989e30) / r_m**2

def v_circ_kms(g_si, r_kpc):
    """v = sqrt(g*r), converted to km/s."""
    return np.sqrt(g_si * r_kpc * KPC_M) / 1e3

def mond_nu(y):
    """Simple-ish MOND interpolation: nu(y) = 1/2 + sqrt(1/4 + 1/y)."""
    return 0.5 + np.sqrt(0.25 + 1.0/y)

def v_mond(r_kpc, M):
    g_n = g_newton_si(r_kpc, M)
    y = g_n / 1.2e-10
    g_eff = g_n * mond_nu(y)
    return v_circ_kms(g_eff, r_kpc)

def v_newton(r_kpc, M):
    g = g_newton_si(r_kpc, M)
    return v_circ_kms(g, r_kpc)

def v_framework(r_kpc, M_baryon, rho_C0, r_C):
    """v_total^2 = G M_b/r + G M_C(<r)/r."""
    rgrid = np.linspace(1e-3, r_kpc.max(), 2000)
    integrand = 4*np.pi * rho_C0 * 0.95 * np.exp(-(rgrid/r_C)**2) * rgrid**2
    M_C_enc = np.cumsum(integrand) * (rgrid[1]-rgrid[0])
    M_C_r = np.interp(r_kpc, rgrid, M_C_enc)
    v2 = G_NEWTON*(M_baryon + M_C_r)/r_kpc
    return np.sqrt(v2)

r = np.linspace(0.5, 40, 200)

v_n = v_newton(r, M_baryon)
v_m = v_mond(r, M_baryon)
# Use framework fit from NGC 3198
v_f = v_framework(r, M_baryon, rho_C0=2.7e6, r_C=22.0)

# Asymptotic flat velocity from MOND: v_inf^4 = G*M*a_0
v_inf_mond = (6.674e-11 * M_baryon*1.989e30 * 1.2e-10)**0.25 / 1e3
print(f"=== MOND vs framework ===")
print(f"M_baryon = {M_baryon:.2e} Msun")
print(f"MOND asymptotic v_flat = (GMa_0)^(1/4) = {v_inf_mond:.1f} km/s")
print(f"Framework v(30 kpc)    = {v_framework(np.array([30.0]), M_baryon, 2.7e6, 22.0)[0]:.1f} km/s")
print(f"Newton  v(30 kpc)      = {v_newton(np.array([30.0]), M_baryon)[0]:.1f} km/s")

# Comparison plot
fig, ax = plt.subplots(figsize=(8,5))
ax.plot(r, v_n, 'g--', label='Newton (baryon only)')
ax.plot(r, v_m, 'r-.', lw=2, label=f'MOND (a_0=1.2e-10, v_flat={v_inf_mond:.0f})')
ax.plot(r, v_f, 'b-', lw=2, label='Framework C^μν')
ax.axhline(150, color='k', ls=':', alpha=0.5, label='NGC 3198 obs (~150 km/s)')
ax.set_xlabel('r [kpc]')
ax.set_ylabel('v [km/s]')
ax.set_title("MOND vs Framework C^μν vs Newton (NGC 3198 baryon)")
ax.legend()
ax.set_ylim(0, 220)
fig.tight_layout()
fig.savefig('/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/dark_matter_prediction/MOND_comparison.png', dpi=130)

# --- Where do they differ ---
print("\n=== Agreement / Disagreement ===")
print("AGREE (galaxy scale, flat rotation):")
print("  - Both predict flat v(r) without particulate DM")
print("  - Both have a single effective scale (a_0 for MOND, r_C for framework)")

print("\nDIFFER:")
print("  - MOND: pure modification of g(N), curve depends only on M_baryon enclosed")
print("    → Tully-Fisher relation v^4 ∝ M_baryon exact prediction")
print("  - Framework: independent C^μν field, can have any (rho_C0, r_C) per system")
print("    → Tully-Fisher emerges only if C-distribution scales with baryons consistently")
print("  - MOND fails at cluster scale (residual factor ~2 missing mass)")
print("    → Bullet Cluster requires non-baryonic mass even in MOND")
print("  - Framework places that excess in C^μν, can in principle absorb it")

# Tully-Fisher predicted slope
print("\n=== Tully-Fisher test ===")
print("MOND: v_flat^4 = G * M_baryon * a_0  (exact)")
print("Framework: v_flat^2 = G * M_C / r_C  (depends on rho_C0 * r_C^3 fit)")
print("→ Framework must DERIVE M_C ∝ M_baryon^(1/2) for TF agreement.")
print("  No first-principles derivation in current framework — fit-by-system.")
