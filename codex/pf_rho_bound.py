#!/usr/bin/env python3
"""Can the unknown correlation rho(w0,wa) destroy the crossing agreement?

R = (1+w0)/|wa|.  Both partials positive, so rho < 0 shrinks Var(R) and makes
the test SHARPER. The question is whether any rho makes PF's exact R
inconsistent with the data. Scan rho to the degenerate limit per sample.

wa uncertainties: DESY5 +0.23/-0.20 (published, mean 0.215). Pantheon+ and
Union3 half-widths are NOT yet read off Table 3; the values used here are
flagged PROVISIONAL and the conclusion is stated so as not to depend on them
delicately.
"""
import math

phi = (1 + math.sqrt(5)) / 2
R_PF = (phi - 1) / 2

SAMPLES = [
    ("Pantheon+", -0.838, 0.055, -0.62, 0.215, "PROVISIONAL wa sigma"),
    ("DESY5",     -0.752, 0.057, -0.86, 0.215, "published +0.23/-0.20"),
    ("Union3",    -0.667, 0.088, -1.09, 0.290, "PROVISIONAL wa sigma"),
]

print(f"PF exact:  R = (phi-1)/2 = {R_PF:.9f}")
print()
for name, w0, s0, wa, sa, note in SAMPLES:
    R = (1 + w0) / (-wa)
    A = (1.0 / (-wa)) * s0
    B = ((1 + w0) / (wa * wa)) * sa
    print("=" * 70)
    print(f"{name}    R = {R:.6f}   |R - R_PF| = {abs(R-R_PF):.6f}   [{note}]")
    print("=" * 70)
    print(f"   {'rho':>7} {'sigma_R':>10} {'deviation':>11}")
    worst = 0.0
    for rho in (0.0, -0.5, -0.8, -0.9, -0.95, -0.98, -0.99, -0.995, -0.999):
        var = A*A + B*B + 2*A*B*rho
        if var <= 1e-12:
            print(f"   {rho:>7.3f} {'degenerate':>10} {'--':>11}")
            continue
        sR = math.sqrt(var)
        dev = abs(R_PF - R) / sR
        worst = max(worst, dev)
        print(f"   {rho:>7.3f} {sR:>10.5f} {dev:>10.2f}s")
    print(f"   -> worst deviation over the whole scan: {worst:.2f} sigma")
    print()

print("=" * 70)
print("CONCLUSION -- and it does NOT favour the prediction")
print("=" * 70)
print("   rho IS load-bearing. It cannot be bounded away. At low |rho| all")
print("   three samples agree with PF's closed form (0.38s, 0.21s, 0.03s); at")
print("   high |rho| they diverge sharply:")
print()
print("       Union3      worst  0.96 sigma   -- survives every rho")
print("       DESY5       worst  3.14 sigma")
print("       Pantheon+   worst 10.76 sigma   -- strongly EXCLUDED")
print()
print("   So the honest statement is NOT 'rho cannot hurt us'. It is: the")
print("   crossing comparison is strongly rho- AND sample-dependent, and the")
print("   published rho must be obtained before any sigma is quoted.")
print()
print("   THE DEEPER POINT, which is about the data and not about PF:")
print("   the three SNe samples disagree with EACH OTHER on R by more than PF")
print("   differs from the best of them.")
print()
R_vals = [(1 + w0) / (-wa) for _, w0, _, wa, _, _ in SAMPLES]
print(f"       sample-to-sample spread in R : {max(R_vals) - min(R_vals):.6f}")
print(f"       PF offset from closest (U3)  : {min(abs(r - R_PF) for r in R_vals):.6f}")
print(f"       ratio                        : "
      f"{(max(R_vals)-min(R_vals)) / min(abs(r-R_PF) for r in R_vals):.1f}x")
print()
print("   PF's exact value sits at the TOP of the data's own range. Until the")
print("   SNe samples agree with one another, the discriminating test is not")
print("   available at all -- SNe systematics dominate the comparison. That is")
print("   the referee-proof reading: not a confirmation, not a refutation, and")
print("   the limiting factor is the data's internal scatter.")
print()
print("   Unchanged: the pair is an ANSATZ, not derived (r389, four")
print("   obstructions), and r389 PROVES PF's action derivation excludes it.")
