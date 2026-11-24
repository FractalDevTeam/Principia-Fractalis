#!/usr/bin/env python3
"""The covariance-FREE test: w0 alone.

A comparison of w0 against its own published marginal uncertainty is a
single-parameter test. The marginal sigma IS the correct error -- no
correlation coefficient enters, so none has to be assumed or obtained.
This sidesteps the exact defect that forced the withdrawal of PF's earlier
2.23-2.69 sigma figure.

Equivalently in g: r219 gives w = -1 + g/(3H), so g0/H0 = 3(1 + w0).

Published: arXiv:2503.14738, DESI+CMB+DESY5 (4.2 sigma vs LCDM):
    w0 = -0.752 +/- 0.057
"""
import math

phi = (1 + math.sqrt(5)) / 2
W0, S0 = -0.752, 0.057

def g_over_H(w0):
    return 3.0 * (1.0 + w0)

rows = [
    ("LCDM",                          -1.0,            None),
    ("PF action branch, best edge",    -0.93,           "derived window [-0.99,-0.93], r389"),
    ("PF action branch, far edge",     -0.99,           "derived window, r389"),
    ("PF golden-ratio ansatz",         -phi/2,          "r78, = -phi/2 EXACT"),
    ("measured g-inversion, low edge", -0.753,          "COSMOLOGY_W_BRIDGE, r389 table"),
    ("measured g-inversion, high edge",-0.650,          "COSMOLOGY_W_BRIDGE, r389 table"),
]

print("=" * 78)
print(f"Single-parameter test against DESI+CMB+DESY5:  w0 = {W0} +/- {S0}")
print(f"   implied g0/H0 = 3(1+w0) = {g_over_H(W0):.4f} +/- {3*S0:.4f}")
print("   NO covariance needed: this is a 1-D comparison on w0's own marginal.")
print("=" * 78)
print(f"   {'model / branch':<34} {'w0':>9} {'g0/H0':>8} {'deviation':>11}")
print(f"   {'-'*34} {'-'*9} {'-'*8} {'-'*11}")
best = None
for name, w0, note in rows:
    dev = abs(w0 - W0) / S0
    print(f"   {name:<34} {w0:>9.4f} {g_over_H(w0):>8.4f} {dev:>10.2f}s")
    if 'ansatz' in name or name == 'LCDM' or 'best edge' in name:
        if best is None or dev < best[1]:
            best = (name, dev)

print()
print("=" * 78)
print("Reading")
print("=" * 78)
print(f"   LCDM is {abs(-1.0 - W0)/S0:.2f} sigma from the DESY5 central value.")
print(f"   PF's OWN action branch is {abs(-0.93 - W0)/S0:.2f}-{abs(-0.99 - W0)/S0:.2f} sigma away")
print( "      -- so crossing-vs-touch CANNOT rescue it. The action branch misses")
print( "         the measured w0 by 3+ sigma regardless of how the zero is read.")
print(f"   PF's golden-ratio ansatz is {abs(-phi/2 - W0)/S0:.2f} sigma away.")
print()
print(f"   Ranking against DESY5:  ansatz {abs(-phi/2-W0)/S0:.2f}s  <  action {abs(-0.93-W0)/S0:.2f}s  <  LCDM {abs(-1.0-W0)/S0:.2f}s")
print()
print("   The ansatz value -phi/2 = %.6f sits almost exactly one marginal" % (-phi/2))
print("   sigma from the published central value, and it was fixed by phi")
print("   before the measurement existed.")
print()
print("   CAVEATS that still stand (unchanged by this test):")
print("     * -phi/2 is an ANSATZ, not derived from the substrate (r389, 4 obstructions).")
print("     * r389 proves PF's action derivation EXCLUDES -phi/2.")
print("     * one data combination; Pantheon+ and Union3 give different w0.")
print("     * agreement at 1 sigma is 'not excluded', never 'confirmed'.")
