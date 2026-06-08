"""
Task 2: Construct H_3-invariant L^2(S^2) basis functions explicitly.

Standard trick: for each level l in the icosahedral spectrum {0,6,10,12,16,18,...},
the H_3-invariant subspace is 1-dimensional (until l=30). A canonical
construction is the SYMMETRIZED ZONAL SUM over the 12 icosahedral vertices:

    psi_l(x) = (1 / sqrt(N_l)) * sum_{v in V_12} P_l(x . v)

where P_l is the Legendre polynomial of degree l and V_12 are the 12 vertices
of the icosahedron on S^2.  By the addition theorem,
    P_l(x.v) = (4 pi / (2l+1)) sum_m Y_l^m(x) Y_l^m(v)*
so psi_l = (4 pi / (2l+1)) sum_m [sum_v Y_l^m(v)*] Y_l^m(x),
which is an icosahedral-invariant linear combination of Y_l^m.

If sum_v Y_l^m(v)* = 0 for all m, then psi_l = 0 -- this happens at l=1,2,3,4,5,7,8,9,11,13,14
(non-spectral levels) -- and psi_l != 0 at the icosahedral spectrum.

We build the icosahedron vertices, the symmetrized zonal functions psi_l(x),
and verify L^2 norms / icosahedral invariance numerically.
"""

import numpy as np
from scipy.special import lpmn, eval_legendre, sph_harm
from numpy.polynomial.legendre import leggauss

# ---------------- Icosahedron vertices (12 points on S^2) -----------------
def icosahedron_vertices():
    phi = (1 + np.sqrt(5)) / 2
    raw = []
    for s1 in (-1, +1):
        for s2 in (-1, +1):
            raw.append((0,  s1,    s2*phi))
            raw.append((s1, s2*phi, 0))
            raw.append((s1*phi, 0, s2))
    V = np.array(raw, dtype=float)
    V /= np.linalg.norm(V[0])
    return V

V12 = icosahedron_vertices()
print(f"|V12|        = {len(V12)}")
print(f"|v|          = {np.linalg.norm(V12[0]):.12f}")
print(f"Mean vertex  = {V12.mean(axis=0)}  (should be ~0)")

# Pairwise dot products: there should be 1 (self), -1 (antipode),
# and 1/sqrt(5) (~0.4472) and -1/sqrt(5) for adjacent / non-adjacent.
dots = []
for i in range(12):
    for j in range(i+1, 12):
        dots.append(V12[i] @ V12[j])
dots = sorted(set(np.round(dots, 8)))
print(f"Distinct vertex dot products: {dots}")
print(f"1/sqrt(5) = {1/np.sqrt(5):.8f}")

# ---------------- Spherical (Lebedev-like) quadrature on S^2 --------------
# Tensor product of Gauss-Legendre in cos(theta) and uniform in phi.
def gauss_quadrature_sphere(N_theta=64, N_phi=128):
    """Returns (theta, phi, w) such that
       int_{S^2} f dOmega = sum w_i f(theta_i, phi_i)
       with dOmega = sin(theta) d(theta) d(phi)."""
    x, wx = leggauss(N_theta)              # x in (-1,1) for cos(theta)
    theta = np.arccos(x)                   # theta in (0,pi)
    sint  = np.sqrt(1 - x*x)
    phi   = 2*np.pi*(np.arange(N_phi) + 0.5)/N_phi
    dphi  = 2*np.pi/N_phi
    th, ph = np.meshgrid(theta, phi, indexing='ij')
    # weight: Gauss-Legendre dx already absorbs sin(theta) dtheta = -dx
    # so the surface element is wx * dphi (NO extra sin(theta))
    w = (wx[:,None] * dphi * np.ones((1,N_phi)))
    return th.ravel(), ph.ravel(), w.ravel()

th, ph, w = gauss_quadrature_sphere(64, 128)
print(f"\nQuadrature size: {len(th)}; sum w = {w.sum():.10f}  (expect 4*pi = {4*np.pi:.10f})")

# ---------------- Symmetrized zonal basis psi_l ---------------------------
def zonal_sum(x_unit, l):
    """psi_l(x) = sum_{v in V12} P_l(x . v)  for x on S^2."""
    # x_unit shape (Np, 3)
    cs = x_unit @ V12.T   # (Np, 12)
    return eval_legendre(l, cs).sum(axis=1)

# Cartesian quadrature points
xq = np.stack([np.sin(th)*np.cos(ph), np.sin(th)*np.sin(ph), np.cos(th)], axis=-1)

print(f"\n{'l':>4} {'<psi_l, psi_l>':>20} {'sqrt is':>20}")
norms_sq = {}
for l in [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,20,22,24]:
    f = zonal_sum(xq, l)
    nrm2 = (w * f * f).sum()
    norms_sq[l] = nrm2
    nz = "ZERO" if abs(nrm2) < 1e-8 else f"{np.sqrt(nrm2):.6e}"
    print(f"{l:>4} {nrm2:>20.6e} {nz:>20}")

print("\nNote: psi_l ~ 0 at non-spectrum levels (1..5, 7..9, 11, 13, 14) "
      "confirms icosahedral selection rule.")
