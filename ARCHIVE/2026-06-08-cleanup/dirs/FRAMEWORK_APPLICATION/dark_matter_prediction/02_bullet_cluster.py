"""
Bullet Cluster 1E 0657-558: framework C^μν vs collisional gas separation.

Observed (Clowe et al 2006):
  - X-ray gas (hot ICM) is shocked, lagging behind subcluster after collision.
  - Weak-lensing mass peaks are coincident with the GALAXY peaks, OFFSET
    from the gas peaks. Interpreted as collisionless dark matter following
    the galaxies.

Framework prediction:
  - C^μν consciousness stress-energy lives in the GALAXIES (where consciousness
    substrate — stars, planets, biology — resides), not in the diffuse gas.
  - C^μν is collisionless (no electromagnetic interaction), so behaves
    dynamically like collisionless DM.
  - Therefore the lensing peak should track the galaxy peak, NOT the gas.

Test: build two-component model
  Sub-cluster + main cluster, each with: galaxy distribution + gas distribution.
  Apply ram-pressure offset to gas after collision.
  Compute (a) total mass = baryons + C-contribution; (b) project to lensing kappa.
  Check whether lensing peak coincides with galaxy peak.
"""
from __future__ import annotations
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# Configuration (simplified 1D cut along collision axis)
# Distances in Mpc, masses in 1e14 Msun
x = np.linspace(-1.5, 1.5, 600)  # Mpc

def gauss(x, x0, sigma, amp):
    return amp * np.exp(-0.5*((x-x0)/sigma)**2)

# Galaxy distributions (collisionless)
gal_main = gauss(x, -0.25, 0.25, 1.0)   # main cluster galaxies
gal_sub  = gauss(x, +0.35, 0.15, 0.3)   # bullet sub-cluster galaxies

# Gas distributions (collisional → lagged after passage)
# Sub-cluster gas is shocked, displaced toward main; main gas pushed out.
gas_main = gauss(x, -0.10, 0.30, 0.8)
gas_sub  = gauss(x, +0.10, 0.20, 0.4)   # bullet gas lagging galaxies

# Baryonic mass distribution = gas (dominant ~80% of baryons in clusters) + galaxies (stars)
Sigma_baryon = 0.15*(gal_main + gal_sub) + 0.85*(gas_main + gas_sub)

# --- Framework C^μν "consciousness mass" ---
# Framework: ch_2 lives in matter-organised substrate (stars, planets, biology),
# i.e. tracks GALAXIES not diffuse gas. Coupling amplitude calibrated so that
# C-mass / baryon-mass ~ M_DM/M_baryon ~ 5-6 in cluster (observed cosmic ratio).
A_C = 5.5  # consciousness coupling amplitude (per unit galaxy density)
Sigma_C = A_C * (gal_main + gal_sub)  # framework consciousness mass

Sigma_total = Sigma_baryon + Sigma_C

# Standard LCDM dark matter (collisionless, follows galaxies)
Sigma_DM = 5.5 * (gal_main + gal_sub)  # same prescription
Sigma_total_LCDM = Sigma_baryon + Sigma_DM

# Convergence kappa ∝ projected surface mass density.
kappa_framework = Sigma_total / Sigma_total.max()
kappa_LCDM      = Sigma_total_LCDM / Sigma_total_LCDM.max()
kappa_baryon    = Sigma_baryon / Sigma_baryon.max()

# To probe the BULLET sub-cluster: subtract a fitted main-cluster contribution
# (centred at x=-0.25). The residual peak position is what observations would
# attribute to the sub-cluster's lensing mass.
def subtract_main(field):
    main_template = gauss(x, -0.25, 0.27, 1.0)
    # Fit amplitude via dot product
    amp = np.dot(field, main_template) / np.dot(main_template, main_template)
    return field - amp * main_template

resid_fw = subtract_main(kappa_framework)
resid_baryon = subtract_main(kappa_baryon)

# Peaks
def peak_region(arr, x, mask):
    """argmax restricted to mask (x positions where mask is True)."""
    arr_m = np.where(mask, arr, -np.inf)
    return x[np.argmax(arr_m)]

# main = left side; sub = right side
left = x < 0.0
right = x > 0.0
p_gal_main = peak_region(gal_main, x, left)
p_gal_sub = peak_region(gal_sub, x, right)
p_gas_main = peak_region(gas_main, x, left)
p_gas_sub = peak_region(gas_sub, x, right)
p_lens_fw_main = peak_region(kappa_framework, x, left)
p_lens_fw_sub  = peak_region(resid_fw, x, right)
p_lens_baryon_main = peak_region(kappa_baryon, x, left)
p_lens_baryon_sub  = peak_region(resid_baryon, x, right)

print("=== Bullet Cluster 1E 0657-558 (framework C^μν) ===")
print(f"Galaxy peaks: main = {p_gal_main:+.2f} Mpc, sub = {p_gal_sub:+.2f} Mpc")
print(f"Gas peaks:    main = {p_gas_main:+.2f} Mpc, sub = {p_gas_sub:+.2f} Mpc")
print(f"Framework lensing peaks: main = {p_lens_fw_main:+.2f}, sub = {p_lens_fw_sub:+.2f}")
print(f"  Δ(lens_sub - gas_sub) = {p_lens_fw_sub - p_gas_sub:+.2f} Mpc (observed: ~+0.2 Mpc)")
print(f"  Δ(lens_sub - gal_sub) = {p_lens_fw_sub - p_gal_sub:+.2f} Mpc (observed: ~0.0 Mpc)")
print(f"Baryon-only lensing peaks would be: main = {p_lens_baryon_main:+.2f}, sub = {p_lens_baryon_sub:+.2f}")
print(f"  Baryon-only would coincide with gas (collisional) — RULED OUT by obs.")

# Plot
fig, ax = plt.subplots(2, 1, figsize=(9, 6), sharex=True)
ax[0].fill_between(x, 0, gas_main + gas_sub, color='red', alpha=0.3, label='X-ray gas (collisional)')
ax[0].plot(x, gal_main + gal_sub, 'b-', lw=2, label='Galaxies (collisionless)')
ax[0].set_ylabel("Surface density (arbitrary)")
ax[0].legend(loc='upper right')
ax[0].set_title("Bullet Cluster components along collision axis")
ax[0].axvline(p_gas_sub, color='red', ls=':', alpha=0.6)
ax[0].axvline(p_gal_sub, color='blue', ls=':', alpha=0.6)

ax[1].plot(x, kappa_framework, 'k-', lw=2, label='Lensing κ (framework: baryon + C^μν)')
ax[1].plot(x, kappa_baryon, 'orange', ls='--', lw=2, label='Lensing κ (baryon only)')
ax[1].plot(x, kappa_LCDM, 'g-.', lw=1.5, alpha=0.7, label='Lensing κ (LCDM: baryon + DM)')
ax[1].axvline(p_gas_sub, color='red', ls=':', alpha=0.6, label='Gas peak (sub)')
ax[1].axvline(p_gal_sub, color='blue', ls=':', alpha=0.6, label='Galaxy peak (sub)')
ax[1].set_xlabel('x [Mpc]')
ax[1].set_ylabel('κ (normalised)')
ax[1].legend(loc='upper right', fontsize=8)
fig.tight_layout()
fig.savefig('/home/xluxx/Principia-Fractalis/FRAMEWORK_APPLICATION/dark_matter_prediction/bullet_cluster.png', dpi=130)
print("Saved bullet_cluster.png")
