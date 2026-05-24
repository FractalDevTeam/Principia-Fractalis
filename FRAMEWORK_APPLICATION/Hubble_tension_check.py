"""
Verify the framework's Hubble tension resolution claim from Ch 27.

Framework asserts (Prop 27.x):
  H_0^modified = 69.8 ± 0.8 km/s/Mpc

Framework uses:
  ch_2(z) = 0.95 · exp(-(z/0.5)^2)
  δE(z) = -0.03 · exp(-(z/0.5)^2)
  H_0^SN_modified = H_0^SN_std · (1 - <δE>)

We want to check: does <δE> over SN redshift range give the claimed 69.8?
"""
import numpy as np
from scipy import integrate

# Measured values
H0_CMB = 67.4  # km/s/Mpc, Planck 2018
H0_SH0ES = 73.0  # km/s/Mpc, SH0ES

# Framework parameters
def ch2(z, ch2_0=0.95, z_star=0.5):
    return ch2_0 * np.exp(-(z/z_star)**2)

def delta_E(z, delta_max=-0.03, z_star=0.5):
    """Fractional correction to E(z) = H(z)/H_0."""
    return delta_max * np.exp(-(z/z_star)**2)

# SN redshift range
z_min, z_max = 0.01, 2.0

# Method 1: simple average of δE(z) over SN range
def average_delta_E_simple(z_min, z_max):
    val, _ = integrate.quad(delta_E, z_min, z_max)
    return val / (z_max - z_min)

# Method 2: weighted by SN sample distribution
# Most SNs are at low-to-moderate z; weight by 1/(1+z)^2 (cosmological volume element rough)
def average_delta_E_weighted(z_min, z_max):
    num, _ = integrate.quad(lambda z: delta_E(z) / (1+z)**2, z_min, z_max)
    denom, _ = integrate.quad(lambda z: 1 / (1+z)**2, z_min, z_max)
    return num / denom

# Method 3: weighted by distance modulus contribution (lower z dominate)
def average_delta_E_distance_weighted(z_min, z_max):
    num, _ = integrate.quad(lambda z: delta_E(z) / (z + 0.1), z_min, z_max)
    denom, _ = integrate.quad(lambda z: 1 / (z + 0.1), z_min, z_max)
    return num / denom

print("="*60)
print("Hubble Tension Framework Check (Ch 27)")
print("="*60)
print(f"H_0 (CMB Planck):   {H0_CMB} km/s/Mpc")
print(f"H_0 (SH0ES SN):     {H0_SH0ES} km/s/Mpc")
print(f"Tension: {(H0_SH0ES - H0_CMB)/np.sqrt(0.5**2 + 1.0**2):.2f}σ")
print(f"Framework target: H_0^mod = 69.8 ± 0.8 km/s/Mpc")
print()

for method_name, method in [
    ("Simple average", average_delta_E_simple),
    ("Cosmological weighted (1/(1+z)^2)", average_delta_E_weighted),
    ("Distance-weighted (1/(z+0.1))", average_delta_E_distance_weighted),
]:
    avg = method(z_min, z_max)
    H0_SN_modified = H0_SH0ES * (1 - avg)  # The framework's correction
    H0_combined = (H0_CMB + H0_SN_modified) / 2
    print(f"{method_name}:")
    print(f"  <δE> over [0.01, 2.0] = {avg:.4f}")
    print(f"  H_0^SN_mod = {H0_SH0ES} · (1 - {avg:.4f}) = {H0_SN_modified:.2f}")
    print(f"  H_0^combined = ({H0_CMB} + {H0_SN_modified:.2f})/2 = {H0_combined:.2f}")
    print(f"  Diff from framework target 69.8: {abs(H0_combined - 69.8):.2f}")
    print()

# Try fitting for δ_max to GET 69.8
print("="*60)
print("Reverse engineer: what δ_max gives H_0^combined = 69.8?")
print("="*60)
# H_0^combined = (67.4 + 73.0·(1 - <δE>))/2 = 69.8
# 67.4 + 73.0 - 73.0·<δE> = 139.6
# 73.0·<δE> = 0.8
# <δE> = 0.8/73 = 0.01096
needed_avg = 0.01096
print(f"<δE> needed = {needed_avg:.5f}")
# With ch2(z) shape, δ_max needed:
# <δE> = -δ_max · <exp(-(z/0.5)^2)>
avg_gauss, _ = integrate.quad(lambda z: np.exp(-(z/0.5)**2), z_min, z_max)
avg_gauss /= (z_max - z_min)
print(f"<exp(-(z/0.5)^2)> over [0.01, 2.0] = {avg_gauss:.4f}")
needed_delta_max = needed_avg / avg_gauss
print(f"Framework's δ_max needed = {-needed_delta_max:.4f}")
print(f"Framework's stated δ_max = -0.03")
print(f"Discrepancy factor: {0.03/needed_delta_max:.2f}× (framework's stated is {0.03/needed_delta_max:.2f}× too big)")
