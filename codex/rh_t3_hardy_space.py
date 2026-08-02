#!/usr/bin/env python3
"""
RH front, stone 1: Pablo's T3 transfer operator moved to its CORRECT carrier.

ch20 defines (T3 f)(x) = (1/3) sum_k w_k sqrt(x/y_k) f(y_k),  y_k = (x+k)/3,
phases w = {1, -i, -1}, on L^2([0,1], dx/x).  The corpus's own diagnosis
(codex/CH24_SPECTRAL_DIAGNOSIS_2026-07-31.md) identified L^2 as the defect:
expanding/contracting-map transfer operators have discrete stable spectrum
only on analytic or Hoelder spaces (Ruelle-Perron-Frobenius; Mayer 1991 did
exactly this for the Gauss map and the Selberg zeta).

THE REPAIR (new): conjugation by m(x) = sqrt(x).  For g = m*f,

  (T~ g)(x) = sum_k w_k/3 * sqrt(x/y_k) * sqrt(x)/sqrt(y_k) * g(y_k)
            = sum_k w_k/3 * (x/y_k) * g(y_k)
            = sum_k w_k * (x/(x+k)) * g((x+k)/3)      [since x/y_k = 3x/(x+k)]

Weights x/(x+k) are RATIONAL: analytic on any disc D(1/2, r), r < 3/2
(poles at -1, -2 stay outside).  Maps y_k contract D(1/2, 0.7) strictly into
itself (image radius 0.7/3, centers 1/6, 1/2, 5/6; max reach 1/3 + 0.2333 =
0.5667 < 0.7).  By the classical Ruelle argument this makes T~ NUCLEAR of
order zero on H^2(D): discrete spectrum, eigenvalues with geometric decay,
truncation-stable.  Conjugation preserves eigenvalues (m never 0 on D minus
the branch cut; on the common dense domain spec(T~) = spec(T)).

Test protocol (falsifiable, three questions):
  Q1  Is the spectrum truncation-STABLE on H^2 (unlike L^2, where the corpus
      measured q_max drift and density at 0)?               [nuclearity check]
  Q2  Is the spectrum REAL (ch20 claims self-adjointness) or complex?
  Q3  Does the ch20 readout s = 10/(pi*|lambda|*alpha*), alpha* = 5e-6, or ANY
      monotone rescaling, co-locate eigenvalues with zeta ordinates
      14.1347, 21.0220, 25.0109, 30.4249, 32.9351 better than a null?
Method: Taylor basis e_n(x) = ((x-1/2)/0.7)^n; matrix entries by FFT on the
boundary circle; N = 30, 60, 120; mpmath zeros hardcoded (first five, exact
to shown digits, Odlyzko).
"""
import numpy as np

R, C = 0.7, 0.5
PHASES = np.array([1.0, -1.0j, -1.0])
ZETA_ORD = np.array([14.134725, 21.022040, 25.010858, 30.424876, 32.935062])

def build(N, M=4096):
    th = 2*np.pi*np.arange(M)/M
    xs = C + R*np.exp(1j*th)                       # boundary circle
    A = np.zeros((N, N), dtype=complex)
    base = (xs - C)/R
    for k, w in enumerate(PHASES):
        yk = (xs + k)/3.0
        wt = (w/1.0) * (xs/(xs + k)) if k > 0 else w*np.ones_like(xs)
        # k = 0: weight x/(x+0) = 1 exactly
        zb = (yk - C)/R                            # image in basis coords
        for n in range(N):
            vals = wt * zb**n                      # T~ e_n sampled on circle
            coef = np.fft.fft(vals)/M              # Taylor coeffs about C
            A[:, n] += coef[:N]
    return A

print("=== Q1: truncation stability of spec(T~) on H^2(D(0.5,0.7)) ===")
tops = {}
for N in (30, 60, 120):
    ev = np.linalg.eigvals(build(N))
    ev = ev[np.argsort(-np.abs(ev))]
    tops[N] = ev[:8]
    print(f"  N={N:4d}  top |lambda|: " + " ".join(f"{abs(l):.6f}" for l in ev[:8]))
d = np.abs(np.abs(tops[60][:6]) - np.abs(tops[120][:6]))
print(f"  max drift of top-6 |lambda|, N=60 -> 120: {d.max():.2e}")
print(f"  STABLE (nuclear behaviour)" if d.max() < 1e-8 else "  UNSTABLE -- carrier still wrong")

print("\n=== Q2: reality of the spectrum (ch20 claims self-adjoint) ===")
ev = np.linalg.eigvals(build(120)); ev = ev[np.argsort(-np.abs(ev))][:10]
for l in ev[:6]:
    print(f"  lambda = {l.real:+.6f} {l.imag:+.6f}i   |Im|/|lambda| = {abs(l.imag)/abs(l):.3f}")

print("\n=== Q3: eigenvalue <-> zeta-ordinate co-location ===")
lam = np.abs(ev[np.abs(ev) > 1e-10])
print("  ch20 readout t = 10/(pi*|l|*5e-6):",
      " ".join(f"{10/(np.pi*l*5e-6):.3g}" for l in lam[:5]))
# best single scale c minimizing distance of c/|lambda_i| to SOME ordinate:
from itertools import product
best = None
for c in np.linspace(0.5, 500, 20000):
    t = c/lam[:5]
    err = np.mean([np.min(np.abs(ZETA_ORD - ti)) for ti in t])
    if best is None or err < best[1]: best = (c, err)
print(f"  best one-parameter rescale: c = {best[0]:.3f}, mean miss = {best[1]:.3f}")
print(f"  mean inter-ordinate spacing ~ {np.diff(ZETA_ORD).mean():.2f}; "
      f"null (uniform random in [14,33]) mean miss ~ {np.diff(ZETA_ORD).mean()/4:.2f}")
