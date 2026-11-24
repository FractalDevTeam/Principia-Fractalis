#!/usr/bin/env python3
"""The crossing comparison done in the RIGHT variable, with the correlation
treated honestly as a scan rather than assumed.

CPL:  w(a) = w0 + wa (1-a).   w = -1  <=>  1 - a = (1 + w0)/|wa| == R
So the crossing is a function of the RATIO R alone, not of w0 and wa
separately.  For PF:  R = (phi-1)/2 = 1/(2 phi)  EXACTLY.

Both partials of R are POSITIVE:
    dR/dw0 = 1/|wa|            > 0
    dR/dwa = (1+w0)/wa^2       > 0
so with rho(w0,wa) < 0 the covariance term is NEGATIVE and Var(R) SHRINKS.
The anti-correlation that invalidated the old marginal sigma makes THIS
variable tighter, not looser.  rho is scanned because the published value
is not yet in hand.

Published inputs (arXiv:2503.14738, DESI DR2 Results II):
  DESI+CMB+DESY5   w0 = -0.752 +/- 0.057 , wa = -0.86 (+0.23 -0.20)   4.2 sigma
  DESI+CMB         w0 = -0.42  +/- 0.21  , wa = -1.75 +/- 0.58        3.1 sigma
"""
import math

phi = (1 + math.sqrt(5)) / 2
R_PF = (phi - 1) / 2

print("=" * 74)
print("PF prediction, exact")
print("=" * 74)
print(f"   R_PF = (phi-1)/2 = 1/(2phi) = {R_PF:.10f}")
print(f"   a*   = 1 - R                = {1-R_PF:.10f}   = (3-phi)/2")
print(f"   z*   = 1/a* - 1             = {1/(1-R_PF)-1:.10f}   = 1/sqrt(5)")
print(f"   check 1/sqrt(5)             = {1/math.sqrt(5):.10f}")

def analyse(name, w0, s_w0, wa, s_wa, sig):
    R = (1 + w0) / (-wa)
    dR_dw0 = 1.0 / (-wa)
    dR_dwa = (1 + w0) / (wa * wa)
    A = dR_dw0 * s_w0
    B = dR_dwa * s_wa
    z = 1 / (1 - R) - 1
    print()
    print("=" * 74)
    print(f"{name}   ({sig} vs LCDM)")
    print("=" * 74)
    print(f"   w0 = {w0} +/- {s_w0}      wa = {wa} +/- {s_wa}")
    print(f"   quadrant w0 > -1 and wa < 0 : {w0 > -1 and wa < 0}")
    print(f"   R  = (1+w0)/|wa|            = {R:.6f}")
    print(f"   z_cross                     = {z:.6f}")
    print(f"   dR/dw0 = {dR_dw0:+.4f}   dR/dwa = {dR_dwa:+.4f}   (both positive)")
    print()
    print(f"   {'rho':>6} {'sigma_R':>10} {'|R_PF - R|/sigma_R':>20}")
    print(f"   {'-'*6} {'-'*10} {'-'*20}")
    for rho in (0.0, -0.5, -0.7, -0.8, -0.9, -0.95, -0.98):
        var = A*A + B*B + 2*A*B*rho
        if var <= 0:
            print(f"   {rho:>6.2f} {'(degenerate)':>10}")
            continue
        sR = math.sqrt(var)
        dev = abs(R_PF - R) / sR
        tag = "  <- marginal, INVALID here" if rho == 0.0 else ""
        print(f"   {rho:>6.2f} {sR:>10.5f} {dev:>20.2f}{tag}")

# DESY5 wa error is asymmetric (+0.23 -0.20); use the mean half-width and note it
analyse("DESI + CMB + DESY5", -0.752, 0.057, -0.86, (0.23 + 0.20) / 2, "4.2 sigma")
analyse("DESI + CMB",         -0.42,  0.21,  -1.75, 0.58,               "3.1 sigma")

print()
print("=" * 74)
print("LCDM")
print("=" * 74)
print("   w0 = -1, wa = 0  =>  R = 0/0 undefined; w == -1 identically.")
print("   LCDM predicts NO crossing. There is no entry for this column.")
print()
print("=" * 74)
print("WHAT IS AND IS NOT ESTABLISHED")
print("=" * 74)
print("   ESTABLISHED: R_PF is exact, parameter-free, from phi^2 = phi + 1.")
print("   ESTABLISHED: both DESI combinations lie in PF's quadrant and both")
print("                cross w = -1, so both have a crossing redshift to compare.")
print("   ESTABLISHED: the comparison variable R tightens under the known")
print("                anti-correlation, so rho < 0 cannot be hiding a failure.")
print("   NOT YET    : the published rho. The table above is a scan, not a result.")
print("   NOT YET    : whether the golden-ratio pair is DERIVED. It is an ansatz")
print("                (Agent 10, 2026-07-04); r389 lists four obstructions, and")
print("                PROVES PF's own action derivation excludes it.")
print("   ASYMMETRY  : DESY5's wa error is +0.23/-0.20; the mean half-width")
print("                0.215 is used above. Redo with the asymmetric likelihood")
print("                before any external use.")
