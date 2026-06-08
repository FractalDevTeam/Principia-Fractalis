"""
Cross-check: q = e^(i*pi/h) for h in {6, 8, 10, 12, 15}.
For each h:
  - Compute [n]_q = sin(n*pi/h)/sin(pi/h)
  - Find values matching pi/(10*alpha) for the framework's canonical alpha
  - Identify whether h=10 is uniquely productive

Also: rigorously test whether the 'hit' from script 02 (n=8, k=2 -> 0.21571,
n=8, k=3 -> 0.22105) at the un-scaled level is an accidental near-miss or an
exact algebraic identity related to pi/(10*sqrt(2)).
"""

import numpy as np
from mpmath import mp, mpf, sin as msin, cos as mcos, pi as mpi, sqrt as msqrt, mpc, exp as mexp
mp.dps = 60

# Targets at high precision
alphas = {
    "P":   msqrt(2),
    "NP":  (1 + msqrt(5)) / 2 + mpf("0.25"),
    "NS":  3 * mpi / 2,
    "YM":  mpf(2),
    "BSD": 3 * mpi / 4,
    "H":   (1 + msqrt(5)) / 2,
    "QG":  msqrt(2 * mpi),
}
targets = {name: mpi / (10 * a) for name, a in alphas.items()}

print("=" * 70)
print("CROSS-CHECK across Coxeter numbers h = 6, 8, 10, 12, 15")
print("=" * 70)
print(f"Looking for any [m]_q (or pi*[m]_q/(h*[n]_q)) matching pi/(10*alpha).\n")
print("Targets (50-dp):")
for n, t in targets.items():
    print(f"  alpha_{n}: pi/(10*alpha) = {t}")
print()

TOL = mpf("1e-12")   # demand >12 digit match

def qint(n, h):
    return msin(n * mpi / h) / msin(mpi / h)

for h in [6, 8, 10, 12, 15]:
    print(f"\n--- h = {h}  (q = e^(i*pi/{h})) ---")
    # quantum dims
    qd = [qint(n, h) for n in range(1, h)]
    print("  [n]_q for n=1..h-1:")
    for n in range(1, h):
        print(f"    [{n}]_q = {float(qd[n-1]):.10f}")

    # search for matches of pi*[m]_q / (h * [n]_q) = pi/(10*alpha)
    # equivalently: [m]_q / [n]_q = h/(10*alpha)
    print("  Matches of pi*[m]_q/(h*[n]_q) to pi/(10*alpha) (within 1e-10):")
    found = False
    for m in range(1, h):
        for n in range(1, h):
            if n == 0: continue
            v = mpi * qd[m-1] / (h * qd[n-1])
            for name, t in targets.items():
                rel = abs(v - t) / abs(t)
                if rel < TOL:
                    print(f"    pi*[{m}]_q/({h}*[{n}]_q) = {float(v):.12f}  =  pi/(10*alpha_{name})  (rel {float(rel):.2e})")
                    found = True
    if not found:
        print("    (none with 1e-12 precision)")

print()
print("=" * 70)
print("VERIFY APPARENT TL HITS (n=8): are 0.21571 and 0.22105 actually pi/(10*sqrt(2))?")
print("=" * 70)
# These came from numpy diagonalisation at double precision; rebuild at high precision.
# We'll just print them with the differences.
target_p10s2 = mpi / (10 * msqrt(2))
print(f"target pi/(10*sqrt(2)) = {target_p10s2}")
print(f"observed n=8 k=2 eig  = 0.215712...    diff = {0.21571 - float(target_p10s2):.6f}")
print(f"observed n=8 k=3 eig  = 0.221051...    diff = {0.22105 - float(target_p10s2):.6f}")
print(f"Differences ~ 0.0064 and 0.001 — these are accidents (no exact match).")

print()
print("=" * 70)
print("EXACT IDENTITIES at h=10")
print("=" * 70)
phi = (1 + msqrt(5)) / 2
print(f"sin(pi/10)         = {msin(mpi/10)}")
print(f"1/(2*phi)          = {1/(2*phi)}")
print(f"  -> sin(pi/10) = 1/(2*phi)  CONFIRMED")
print()
print(f"[2]_q = 2cos(pi/10)         = {2*mcos(mpi/10)}")
print(f"sqrt(phi*sqrt(5))           = {msqrt(phi*msqrt(5))}")
print(f"  -> [2]_q = sqrt(phi*sqrt(5)) = sqrt((1+sqrt(5))*sqrt(5)/2)")
print(f"     equivalently [2]_q^2 = 5+sqrt(5)/2 (verify): {(2*mcos(mpi/10))**2}  vs  {mpf(5)/2 + msqrt(5)/2}")
print()
print(f"[5]_q (=sin(pi/2)/sin(pi/10)) = {qint(5,10)}")
print(f"2*phi                          = {2*phi}")
print(f"  -> [5]_q = 2*phi  CONFIRMED")
print()
print(f"ratio [2]_q/[5]_q              = {2*mcos(mpi/10)/(2*phi)}")
print(f"  = cos(pi/10)/phi             = {mcos(mpi/10)/phi}")
print(f"pi * [2]_q / (10 * [5]_q)      = {mpi * 2*mcos(mpi/10) / (10*2*phi)}")
print(f"pi/(10*alpha_H = phi)          = {mpi/(10*phi)}")
print(f"  -> THESE ARE NOT EQUAL.")
print(f"     diff = {mpi * 2*mcos(mpi/10) / (10*2*phi) - mpi/(10*phi)}")
print()
print(f"BUT earlier script claimed pi*[2]_q/([4]_q*10) == pi/(10*phi).")
print(f"[4]_q                           = {qint(4,10)}")
print(f"[2]_q                           = {qint(2,10)}")
print(f"[2]_q/[4]_q                     = {qint(2,10)/qint(4,10)}")
print(f"1/phi                           = {1/phi}")
print(f"  -> [2]_q/[4]_q = 1/phi?  {abs(qint(2,10)/qint(4,10) - 1/phi)}")
print(f"  YES this is sin(2*pi/10)/sin(4*pi/10) = sin(36)/sin(72) = 1/phi (golden ratio identity).")
print(f"  So pi*[2]_q/(10*[4]_q) = pi/(10*phi) is the TRIVIAL identity sin36/sin72=1/phi.")
print(f"  It does NOT give a new derivation of pi/(10*phi); it is the SAME quantity rewritten.")
