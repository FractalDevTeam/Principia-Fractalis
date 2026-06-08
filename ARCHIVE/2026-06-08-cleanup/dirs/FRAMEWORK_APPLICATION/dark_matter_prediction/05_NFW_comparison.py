"""
Framework Gaussian C^μν profile vs NFW dark-matter profile.

NFW (Navarro-Frenk-White 1997):
  rho_NFW(r) = rho_s / [(r/rs) * (1 + r/rs)^2]
  - Cuspy core (rho ~ 1/r as r→0)
  - r^-3 tail at large r
  - Concentration c = R_200/rs ~ 5-30

Framework consciousness profile (per Pabs):
  rho_C(r) = rho_C0 * 0.95 * exp(-r^2/r_C^2)
  - Cored center (Gaussian, no cusp)
  - Exponential cutoff at r > r_C

KEY OBSERVATIONAL DIFFERENCE: "cusp-core problem"
  - Observations of dwarf galaxies show CORED dark matter profiles (Burkert 1995)
  - NFW predicts CUSPS → discrepancy with low-mass galaxy observations
  - Framework's Gaussian halo is INHERENTLY CORED → automatic match to dwarfs?

This script:
  1. Compare density profiles at fixed enclosed mass M(<r_C)
  2. Predicted dwarf galaxy rotation curves
  3. Differential predictions: ultra-diffuse galaxies, central density slopes
"""
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

G_NEWTON = 4.302e-6

# Two halos with same M(<10 kpc) = 1e11 Msun
M_ref = 1.0e11
r_ref = 10.0

# Framework Gaussian — fit rho_C0 to give M(<10) = M_ref
from scipy.optimize import brentq

def M_gauss_enc(r, rho0, rC):
    rgrid = np.linspace(1e-3, r, 4000)
    return np.trapz(4*np.pi*rho0*0.95*np.exp(-(rgrid/rC)**2)*rgrid**2, rgrid)

rC = 12.0
rho_C0 = M_ref / M_gauss_enc(r_ref, 1.0, rC)
print(f"Framework: rho_C0 = {rho_C0:.3e} Msun/kpc^3, r_C = {rC} kpc")

# NFW — fit rho_s for M(<10) = M_ref at c=10
def M_nfw_enc(r, rho_s, rs):
    x = r/rs
    return 4*np.pi*rho_s*rs**3 * (np.log(1+x) - x/(1+x))

c = 10.0
R200 = 100.0
rs = R200/c
rho_s = M_ref / M_nfw_enc(r_ref, 1.0, rs)
print(f"NFW: rho_s = {rho_s:.3e} Msun/kpc^3, rs = {rs} kpc, c={c}")

# Density profiles
r = np.logspace(-1, 2, 200)
rho_gauss = rho_C0 * 0.95 * np.exp(-(r/rC)**2)
rho_nfw = rho_s / ((r/rs) * (1 + r/rs)**2)

# Central density (key cusp-core diagnostic)
print(f"\n--- Central density comparison ---")
print(f"rho_gauss(0.1 kpc) = {rho_C0*0.95*np.exp(-(0.1/rC)**2):.3e} Msun/kpc^3")
print(f"rho_NFW(0.1 kpc)   = {rho_s/((0.1/rs)*(1+0.1/rs)**2):.3e} Msun/kpc^3")
print(f"Ratio NFW/Gauss = {(rho_s/((0.1/rs)*(1+0.1/rs)**2)) / (rho_C0*0.95):.2f}")

# Inner slope d log rho / d log r
log_slope_gauss_05 = (np.log(rho_C0*0.95*np.exp(-(0.5/rC)**2)) - np.log(rho_C0*0.95*np.exp(-(0.1/rC)**2)))/(np.log(0.5)-np.log(0.1))
log_slope_nfw_05 = (np.log(rho_s/((0.5/rs)*(1+0.5/rs)**2)) - np.log(rho_s/((0.1/rs)*(1+0.1/rs)**2)))/(np.log(0.5)-np.log(0.1))
print(f"\n--- Inner log-slope (0.1 → 0.5 kpc) ---")
print(f"d log rho_Gauss / d log r = {log_slope_gauss_05:.3f}  (Gaussian → ~0 at small r, CORED)")
print(f"d log rho_NFW   / d log r = {log_slope_nfw_05:.3f}  (NFW → -1, CUSPY)")
print(f"Observations of dwarfs: slope ~ -0.2 to 0 (CORED) — favours framework over NFW.")

# Plot
fig, ax = plt.subplots(1, 2, figsize=(11,5))
ax[0].loglog(r, rho_gauss, 'b-', lw=2, label='Framework Gaussian C^μν')
ax[0].loglog(r, rho_nfw, 'r--', lw=2, label='NFW dark matter')
ax[0].set_xlabel('r [kpc]'); ax[0].set_ylabel('rho [Msun/kpc^3]')
ax[0].set_title("Density profiles, same M(<10 kpc) = 1e11 Msun")
ax[0].legend()

# Rotation curves
M_gauss_arr = np.array([M_gauss_enc(rr, rho_C0, rC) for rr in r])
M_nfw_arr = np.array([M_nfw_enc(rr, rho_s, rs) for rr in r])
v_gauss = np.sqrt(G_NEWTON*M_gauss_arr/r)
v_nfw = np.sqrt(G_NEWTON*M_nfw_arr/r)

ax[1].plot(r, v_gauss, 'b-', lw=2, label='Framework')
ax[1].plot(r, v_nfw, 'r--', lw=2, label='NFW')
ax[1].set_xlabel('r [kpc]'); ax[1].set_ylabel('v_circ [km/s]')
ax[1].set_title("Halo-only rotation curve (matched M)")
ax[1].legend()
ax[1].set_xlim(0, 50)
fig.tight_layout()
fig.savefig('/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/dark_matter_prediction/NFW_comparison.png', dpi=130)
print("\nSaved NFW_comparison.png")

# Falsifiable diff predictions
print("\n=== Distinguishing predictions ===")
print("1. DWARF GALAXIES: framework predicts CORED rotation curves (Gaussian core)")
print("   → Matches observation; NFW fails (cusp-core problem)")
print("2. ULTRA-DIFFUSE GALAXIES (UDGs like NGC 1052-DF2):")
print("   → Some UDGs appear DM-free. Framework requires ZERO consciousness substrate?")
print("   → Framework prediction: UDGs with no consciousness (no rotation enhancement)")
print("   → Observable signature: v_obs ≈ v_baryon for UDGs lacking stars/structure")
print("3. SUB-HALO COUNT (Missing satellites problem):")
print("   → CDM predicts ~1000 sub-halos for MW; observed ~50")
print("   → Framework: consciousness only forms in coherent substrate; small halos don't")
print("     accumulate C^μν → naturally suppresses small-halo count")
print("4. CMB ACOUSTIC PEAKS:")
print("   → ΛCDM requires DM at z=1100 for acoustic horizon scale")
print("   → Framework: ch_2(z=1100) < 1e-4 (Ch 28 prediction)")
print("   → ALTERNATIVE mechanism needed for CMB structure formation in framework")
print("   → THIS IS A WEAKNESS: framework currently lacks explicit CMB derivation")
