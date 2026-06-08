"""
Task 2(b): Convolution-kernel construction on H_3-invariant L^2(S^2).

A zonal kernel K(x.y) acts on L^2(S^2) by  (K f)(x) = int_{S^2} K(x.y) f(y) dy.
By Funk-Hecke,  K is diagonalized by spherical harmonics:
     K Y_l^m  =  hat{K}_l Y_l^m,
where
     hat{K}_l = 2*pi * int_{-1}^{1} K(t) P_l(t) dt.

So on the H_3-invariant zonal basis psi_l, K is diagonal with eigenvalues hat{K}_l.

For K(t) = V_alpha(arccos(t)) = sum_n 2^(-n) cos(pi alpha^n arccos(t)),
the eigenvalues are explicit Funk-Hecke integrals:

     hat{K}_l(alpha) = 2 pi sum_n 2^(-n) int_{-1}^{1} cos(pi alpha^n arccos(t)) P_l(t) dt.

We compute these for l in the icosahedral spectrum and look for pi/(10 alpha).
"""

import numpy as np
from scipy.special import eval_legendre
from numpy.polynomial.legendre import leggauss

def funk_hecke_eigenvalue(K_fun, l, N=400):
    """hat{K}_l = 2 pi int_{-1}^{1} K(t) P_l(t) dt."""
    t, w = leggauss(N)
    return 2*np.pi * np.sum(w * K_fun(t) * eval_legendre(l, t))

def V_alpha_K(alpha, N_terms=8):
    def K(t):
        d = np.arccos(np.clip(t, -1, 1))
        s = np.zeros_like(d)
        for n in range(N_terms):
            s += (2.0**(-n)) * np.cos(np.pi * (alpha**n) * d)
        return s
    return K

SPECTRUM = [0, 6, 10, 12, 16, 18, 20, 22, 24, 26, 28, 30]

for alpha, name in [(np.sqrt(2),'sqrt(2)'), (1.5,'3/2'), (2.0,'2'), ((1+np.sqrt(5))/2,'phi'), (3.0,'3')]:
    print(f"\n===== alpha = {alpha:.6f} ({name}) =====")
    target = np.pi / (10*alpha)
    print(f"Target pi/(10 alpha) = {target:.10f}")
    K = V_alpha_K(alpha)
    eigs = []
    for l in SPECTRUM:
        ev = funk_hecke_eigenvalue(K, l)
        eigs.append((l, ev))
    print(f"{'l':>4} {'hat K_l':>14} {'gap to target':>16}")
    for l, ev in eigs:
        print(f"{l:>4} {ev:>14.6f} {abs(ev-target):>16.6f}")

    # Look at lowest positive and the smallest |.|
    all_eigs = np.array([e for _,e in eigs])
    print(f"\nSmallest |eig|: {all_eigs[np.argmin(np.abs(all_eigs))]:.6f}")
    print(f"Closest to target {target:.4f}: gap = {np.min(np.abs(all_eigs - target)):.4f}")
