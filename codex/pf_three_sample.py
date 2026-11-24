#!/usr/bin/env python3
"""The three-SNe-sample robustness check, in both coordinates.

Published w0waCDM rows (DESI DR2, arXiv:2503.14738):
    + Pantheon+   w0 = -0.838 +/- 0.055   wa = -0.62     2.8 sigma   dchi2 -10.7
    + DESY5       w0 = -0.752 +/- 0.057   wa = -0.86     4.2 sigma   dchi2 -21.0
    + Union3      w0 = -0.667 +/- 0.088   wa = -1.09     3.8 sigma   dchi2 -17.4

PF ansatz (r78, EXACT): w0 = -phi/2, wa = -1/phi, so R = (1+w0)/|wa| = (phi-1)/2.
"""
import math

phi = (1 + math.sqrt(5)) / 2
W0_PF, WA_PF = -phi / 2, -1 / phi
R_PF = (phi - 1) / 2
Z_PF = 1 / (1 - R_PF) - 1

SAMPLES = [
    ("Pantheon+", -0.838, 0.055, -0.62, "2.8s", -10.7),
    ("DESY5",     -0.752, 0.057, -0.86, "4.2s", -21.0),
    ("Union3",    -0.667, 0.088, -1.09, "3.8s", -17.4),
]

print("=" * 86)
print(f"PF ansatz, EXACT:  w0 = -phi/2 = {W0_PF:.6f}   wa = -1/phi = {WA_PF:.6f}")
print(f"                   R  = (phi-1)/2 = {R_PF:.9f}     z* = 1/sqrt(5) = {Z_PF:.9f}")
print("=" * 86)

print()
print("### A. w0 ALONE — single parameter, marginal sigma is CORRECT, no covariance")
print()
print(f"   {'sample':<11} {'w0 meas':>16} {'LCDM':>8} {'PF action':>11} {'PF ansatz':>11}  DESI joint")
print(f"   {'-'*11} {'-'*16} {'-'*8} {'-'*11} {'-'*11}  {'-'*10}")
for name, w0, s, wa, sig, dchi in SAMPLES:
    d_l = abs(-1.0 - w0) / s
    d_a = abs(-0.93 - w0) / s          # action branch, most favourable edge
    d_p = abs(W0_PF - w0) / s
    print(f"   {name:<11} {w0:>8.3f}+/-{s:<5.3f} {d_l:>7.2f}s {d_a:>10.2f}s {d_p:>10.2f}s  {sig:>10}")

print()
print("   METHOD CHECK: the 1-D LCDM column vs DESI's own JOINT significance")
for name, w0, s, wa, sig, dchi in SAMPLES:
    print(f"      {name:<11} mine {abs(-1.0-w0)/s:>5.2f}s   DESI {sig:>5}")
print("   Agreement across all three => the 1-D method recovers the published")
print("   result by an independent route and is not inflating anything.")

print()
print("### B. the CROSSING — the discriminating coordinate (DESI's signal is in wa)")
print()
print(f"   {'sample':<11} {'R = (1+w0)/|wa|':>17} {'z_cross':>9} {'|R-R_PF|':>10} {'|z-z*|':>9}")
print(f"   {'-'*11} {'-'*17} {'-'*9} {'-'*10} {'-'*9}")
for name, w0, s, wa, sig, dchi in SAMPLES:
    R = (1 + w0) / (-wa)
    z = 1 / (1 - R) - 1
    print(f"   {name:<11} {R:>17.6f} {z:>9.6f} {abs(R-R_PF):>10.6f} {abs(z-Z_PF):>9.6f}")
print(f"   {'PF (exact)':<11} {R_PF:>17.6f} {Z_PF:>9.6f} {'--':>10} {'--':>9}")
print(f"   {'LCDM':<11} {'undefined':>17} {'none':>9} {'--':>10} {'--':>9}")

print()
print("### C. summary")
print()
devs = [abs(W0_PF - w0) / s for _, w0, s, _, _, _ in SAMPLES]
print(f"   PF ansatz vs w0, all three samples : {devs[0]:.2f}s, {devs[1]:.2f}s, {devs[2]:.2f}s")
print(f"                              max dev : {max(devs):.2f}s   -> under 2 sigma in ALL THREE")
print(f"   LCDM vs w0                         : {abs(-1.0-SAMPLES[0][1])/SAMPLES[0][2]:.2f}s, "
      f"{abs(-1.0-SAMPLES[1][1])/SAMPLES[1][2]:.2f}s, {abs(-1.0-SAMPLES[2][1])/SAMPLES[2][2]:.2f}s")
print(f"   PF action branch (-0.93 edge)      : {abs(-0.93-SAMPLES[0][1])/SAMPLES[0][2]:.2f}s, "
      f"{abs(-0.93-SAMPLES[1][1])/SAMPLES[1][2]:.2f}s, {abs(-0.93-SAMPLES[2][1])/SAMPLES[2][2]:.2f}s")
print()
Rs = [(1 + w0) / (-wa) for _, w0, _, wa, _, _ in SAMPLES]
print(f"   closest crossing match: {SAMPLES[Rs.index(min(Rs, key=lambda r: abs(r-R_PF)))][0]}"
      f"  |R - R_PF| = {min(abs(r-R_PF) for r in Rs):.6f}")
print()
print("   NOT established, unchanged:")
print("     * published rho(w0,wa) still not in hand -> section B is a point")
print("       comparison, not yet a significance.")
print("     * Pantheon+ and Union3 wa uncertainties not yet read off Table 3;")
print("       only their central values are used in B.")
print("     * -phi/2 is an ANSATZ, not derived (r389, four obstructions), and")
print("       r389 PROVES PF's own action derivation excludes it.")
print("     * 'under 2 sigma' is not-excluded, never confirmed.")
