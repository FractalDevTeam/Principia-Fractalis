"""
U_q(sl_2) at q = e^(i*pi/10): quantum dimensions and Casimir spectrum.

Verifies:
  [n]_q = sin(n*pi/10)/sin(pi/10)
  sin(pi/10) = 1/(2*phi)  where phi = (1+sqrt(5))/2
  Quantum dimensions for n=1..9.

Then computes the quadratic q-Casimir eigenvalues C_2(l) = [l]_q [l+1]_q for
half-integer spins l = 0, 1/2, 1, ..., 9/2 (10 truncated reps at level k=h-2=8).

Tests whether any C_2 or normalized variant matches pi/(10*alpha) for the
framework's canonical alpha values.
"""

import numpy as np
import sympy as sp
from mpmath import mp, mpf, mpc, sin as msin, cos as mcos, pi as mpi, sqrt as msqrt

mp.dps = 50

# ---------- symbolic ----------
phi_s = (1 + sp.sqrt(5)) / 2
pi10_s = sp.pi / 10

def qint_sym(n):
    """[n]_q for q=e^(i*pi/10), as a real symbolic expression."""
    return sp.sin(n * pi10_s) / sp.sin(pi10_s)

def qcas_sym(l):
    """C_2(l) = [l]_q [l+1]_q (symbolic)."""
    return sp.simplify(qint_sym(l) * qint_sym(l + 1))

# ---------- numeric ----------
def qint(n):
    return msin(n * mpi / 10) / msin(mpi / 10)

def qcas(l):
    return qint(l) * qint(l + 1)

# ---------- 1. quantum dimensions ----------
print("=" * 70)
print("1. QUANTUM DIMENSIONS [n]_q at q = e^(i*pi/10)")
print("=" * 70)
print(f"phi              = {(1+sp.sqrt(5))/2} = {float((1+sp.sqrt(5))/2):.15f}")
print(f"sin(pi/10)       = {msin(mpi/10)}")
print(f"1/(2*phi)        = {1/(2*((1+msqrt(5))/2))}")
match = abs(msin(mpi/10) - 1/(2*((1+msqrt(5))/2)))
print(f"|sin(pi/10) - 1/(2*phi)|  = {match}  -> {'CONFIRMED' if match < mpf('1e-40') else 'FAIL'}")
print()

# Conjectured values from prompt: (1, phi, 1+phi, 2phi, 2+phi, 2phi+1, 2+2phi, 2phi+2, 2+phi, 1)
phi_n = float((1+sp.sqrt(5))/2)
claimed = {
    1: 1.0,
    2: phi_n,
    3: 1+phi_n,
    4: 2*phi_n,
    5: 2+phi_n,
    6: 2*phi_n+1,
    7: 2+2*phi_n,
    8: 2*phi_n+2,
    9: 2+phi_n,
}
print(f"{'n':>3}  {'[n]_q numeric':>22}  {'symbolic (simplified)':<30}  {'claimed':>10}  match")
for n in range(0, 11):
    sym = sp.nsimplify(sp.simplify(qint_sym(n)), [phi_s], rational=False)
    num = float(qint(n))
    cl  = claimed.get(n, None)
    ok  = "" if cl is None else ("OK" if abs(num - cl) < 1e-12 else "MISMATCH")
    print(f"{n:>3}  {num:>22.15f}  {str(sym):<30}  {('-' if cl is None else f'{cl:.6f}'):>10}  {ok}")

# The prompt's claimed list is shifted. Real list for n=1..9:
# [1]=1, [2]=2cos(pi/10)=phi+1/(2phi)?  Let's just print and let the data speak.
print()
print("Note: 2cos(pi/10) = (1+sqrt(5))/2 * something? Let's check delta.")
delta = 2 * mcos(mpi/10)
print(f"  delta = [2]_q = 2cos(pi/10) = {delta}")
phi = (1 + msqrt(5)) / 2
print(f"  phi                          = {phi}")
print(f"  delta == phi?                  {abs(delta - phi) < mpf('1e-40')}  (delta - phi = {delta - phi})")
print(f"  Actually [2]_q = 2cos(pi/10) ~= 1.902, NOT phi (1.618). phi is [2]_q ONLY when q=e^(i*pi/5).")
print()

# ---------- 2. q-Casimir spectrum ----------
print("=" * 70)
print("2. q-CASIMIR EIGENVALUES C_2(l) = [l]_q [l+1]_q for l = 0, 1/2, ..., 9/2")
print("=" * 70)
print(f"{'l':>6}  {'C_2(l) numeric':>22}  {'symbolic simplified':<40}")
spins = [sp.Rational(k, 2) for k in range(0, 10)]
cas_values = []
for l in spins:
    sym = sp.simplify(qcas_sym(l))
    num = float(qcas(float(l)))
    cas_values.append((l, num, sym))
    print(f"{str(l):>6}  {num:>22.15f}  {str(sp.nsimplify(sym, [phi_s, sp.sqrt(5), sp.sqrt(2)], rational=False)):<40}")
print()

# ---------- 3. search for pi/(10*alpha) ----------
print("=" * 70)
print("3. SEARCH for pi/(10*alpha) in C_2 spectrum and normalized variants")
print("=" * 70)
targets = {
    "alpha_P = sqrt(2),         pi/(10*sqrt(2))": float(mpi / (10 * msqrt(2))),
    "alpha_NP = phi+1/4,        pi/(10*(phi+1/4))": float(mpi / (10 * (phi + mpf("0.25")))),
    "alpha_NS = 3*pi/2,         pi/(10*3pi/2) = 1/15": float(mpi / (10 * 3 * mpi / 2)),
    "alpha_YM = 2,              pi/20": float(mpi / 20),
    "alpha_BSD = 3*pi/4,        2/15": float(mpi / (10 * 3 * mpi / 4)),
    "alpha_H = phi,             pi/(10*phi)": float(mpi / (10 * phi)),
    "alpha_QG = sqrt(2*pi),     pi/(10*sqrt(2*pi))": float(mpi / (10 * msqrt(2 * mpi))),
}
print("TARGETS:")
for name, v in targets.items():
    print(f"  {name:<55}  = {v:.10f}")

print()
print("RAW C_2(l):")
for l, num, _ in cas_values:
    for name, v in targets.items():
        rel = abs(num - v) / max(v, 1e-30)
        if rel < 0.05:
            print(f"  C_2({l}) = {num:.6f} ~ {name}  (rel {rel*100:.3f}%)")

print()
print("NORMALIZED C_2(l) / [2l+1]_q  (quantum dim of rep V_l = [2l+1]_q):")
for l, num, _ in cas_values:
    qd = float(qint(2 * float(l) + 1))
    if qd <= 0:
        continue
    val = num / qd
    for name, v in targets.items():
        rel = abs(val - v) / max(v, 1e-30)
        if rel < 0.05:
            print(f"  C_2({l})/[{2*float(l)+1:g}]_q = {val:.6f} ~ {name}  (rel {rel*100:.3f}%)")

print()
print("RATIOS [m]_q / [n]_q  (small m,n):")
hits = []
for m in range(1, 10):
    for n in range(1, 10):
        if m == n: continue
        r = float(qint(m) / qint(n))
        for name, v in targets.items():
            rel = abs(r - v) / max(v, 1e-30)
            if rel < 0.02:
                hits.append((m, n, r, name, rel))
for m, n, r, name, rel in hits:
    print(f"  [{m}]_q / [{n}]_q = {r:.6f} ~ {name}  (rel {rel*100:.3f}%)")

print()
print("INVERSE quantum dims 1/[n]_q:")
for n in range(1, 10):
    val = float(1 / qint(n))
    for name, v in targets.items():
        rel = abs(val - v) / max(v, 1e-30)
        if rel < 0.02:
            print(f"  1/[{n}]_q = {val:.6f} ~ {name}  (rel {rel*100:.3f}%)")

print()
print("pi * [m]_q / ([n]_q * 10):")
for m in range(1, 10):
    for n in range(1, 10):
        val = float(mpi * qint(m) / (qint(n) * 10))
        for name, v in targets.items():
            rel = abs(val - v) / max(v, 1e-30)
            if rel < 0.005:
                print(f"  pi*[{m}]_q/([{n}]_q * 10) = {val:.7f} ~ {name}  (rel {rel*100:.4f}%)")

print()
print("DONE script 01.")
