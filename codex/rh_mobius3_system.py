#!/usr/bin/env python3
"""
RH front, stone 2: the depth-3 MOBIUS system -- the nonlinear replacement for
the affine base-3 shift that stone 1 closed.

Branches phi_k(x) = 1/(x+k), k in {1,2,3}: a finite-alphabet continued-fraction
system. Transfer operator, Mayer style, on H^2(D(1, 3/2)):

    (L_s f)(x) = sum_k (x+k)^(-2s) f(1/(x+k))

Each branch maps D(1,3/2) strictly inside itself (verified disc images:
k=1: D(1.143, 0.857); k=2: D(0.444, 0.222); k=3: D(0.291, 0.109)), weights
analytic on D (Re(x+k) >= 0.5) => L_s is NUCLEAR: discrete stable spectrum,
Fredholm determinant det(1 - L_s) entire in s. This is the exact structure
that, for the FULL alphabet k in {1,2,...}, gives Mayer's theorem:
det(1-L_s)det(1+L_s) = Z_Selberg(s) for PSL(2,Z).

Questions:
  Q1  Nuclear + NON-geometric spectrum? (The affine system was killed by
      forced geometric spectrum; nonlinearity must break that.)
  Q2  The system's zeta datum: s* with lambda_max(s*) = 1, i.e. the Hausdorff
      dimension of the k<=3 continued-fraction Cantor set E_3. Literature
      check available (Hensley-type estimates ~0.70-0.71).
  Q3  Framework graft: Z_3 phases omega^k (omega = e^{2pi i/3}, ch20's cube
      phases) on the branches -- does lambda_max(s) stay well-behaved (the
      prerequisite for a Chang-Mayer-type character/representation theory
      connecting to Gamma_0(3))?
"""
import numpy as np

C, R = 1.0, 1.5
KS = (1, 2, 3)

def build(s, N=60, M=2048, phases=(1.0, 1.0, 1.0)):
    th = 2*np.pi*np.arange(M)/M
    xs = C + R*np.exp(1j*th)
    A = np.zeros((N, N), dtype=complex)
    for k, ph in zip(KS, phases):
        y = 1.0/(xs + k)
        w = ph * (xs + k)**(-2*s)
        zb = (y - C)/R
        for n in range(N):
            coef = np.fft.fft(w * zb**n)/M
            A[:, n] += coef[:N]
    return A

print("=== Q1: nuclearity + NON-geometric spectrum at s = 1 ===")
for N in (40, 80):
    ev = np.linalg.eigvals(build(1.0, N))
    ev = ev[np.argsort(-np.abs(ev))][:6]
    print(f"  N={N:3d}  |lambda|: " + " ".join(f"{abs(l):.8f}" for l in ev))
ev = np.linalg.eigvals(build(1.0, 80)); ev = np.sort(np.abs(ev))[::-1][:6]
r = ev[:-1]/ev[1:]
print("  successive ratios |l_n|/|l_(n+1)|:", " ".join(f"{x:.4f}" for x in r))
print("  geometric would be CONSTANT ratio; affine system had exactly 3.0000")

print("\n=== Q2: the system's dimension datum, lambda_max(s*) = 1 ===")
from scipy.optimize import brentq
lam = lambda s: np.max(np.abs(np.linalg.eigvals(build(s, 60)))) - 1.0
s_star = brentq(lam, 0.4, 0.95, xtol=1e-12)
print(f"  s* = dim_H(E_3) = {s_star:.12f}")
print("  (Hensley/Jenkinson-Pollicott literature value for E_3 ~ 0.705)" )

print("\n=== Q3: Z_3 phases omega^k on the branches (framework graft) ===")
om = np.exp(2j*np.pi/3)
for s in (0.5, 0.75, 1.0):
    A  = build(s, 60, phases=(om, om**2, 1.0))
    ev = np.linalg.eigvals(A); l0 = ev[np.argmax(np.abs(ev))]
    print(f"  s={s:4.2f}  lambda_max = {l0.real:+.6f}{l0.imag:+.6f}i   |.|={abs(l0):.6f}")
A40 = build(0.75, 40, phases=(om, om**2, 1.0)); A80 = build(0.75, 80, phases=(om, om**2, 1.0))
l40 = np.max(np.abs(np.linalg.eigvals(A40))); l80 = np.max(np.abs(np.linalg.eigvals(A80)))
print(f"  twisted stability at s=0.75: |lambda_max| N=40 vs 80 drift = {abs(l40-l80):.2e}")
